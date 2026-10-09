(ns datascript.storage
  (:require
    #?@(:clj [[clojure.edn :as edn]
              [clojure.java.io :as io]])
    [datascript.db :as db]
    [datascript.util :as util]
    [me.tonsky.persistent-sorted-set :as set])
  #?(:clj
     (:import
       [datascript.db Datom]
       [java.io BufferedOutputStream File FileOutputStream OutputStream PushbackReader] 
       [java.lang.ref WeakReference]
       [java.util ArrayList HashSet Iterator List]
       [me.tonsky.persistent_sorted_set ANode Branch Leaf PersistentSortedSet RefType Settings])))

(defprotocol IStorage
  :extend-via-metadata true
  
  (-store [_ addr+data-seq]
    "Gives you a sequence of `[addr data]` pairs to serialize and store.
     
     `addr`s are 64 bit integers.
     `data`s are clojure-serializable data structure (maps, keywords, lists, integers etc)")
  
  (-restore [_ addr]
    "Read back and deserialize data stored under single `addr`")
  
  (-list-addresses [_]
    "Return seq that lists all addresses currently stored in your storage.
     Will be used during GC to remove keys that are no longer used.")
  
  (-delete [_ addrs-seq]
    "Delete data stored under `addrs` (seq). Will be called during GC"))

(def ^:private ^:dynamic *store-buffer*)

(defn serializable-datom [^Datom d]
  [(.-e d) (.-a d) (.-v d) (.-tx d)])

(defn- deserialize-datom [[e a v tx]]
  (db/datom e a v tx))

(def ^:private root-addr
  0)

(def ^:private tail-addr
  1)

(defonce ^:private *max-addr
  (volatile! 1000000))

(defn- gen-addr []
  (vswap! *max-addr inc))

#?(:cljs
   (def ^:private datom-bytes
     "Estimated heap bytes per restored datom, excluding its value.
      Calibrated against V8 heap with transit-read nodes, errs slightly high"
     160))

#?(:cljs
   (defn- value-bytes [v]
     (cond
       (string? v) (+ 16 (.-length v))
       (number? v) 8
       :else       32)))

#?(:cljs
   (defn- node-bytes [node]
     (let [keys (.-keys node)
           len  (alength keys)]
       (loop [i 0, acc 64]
         (if (< i len)
           (recur (inc i) (+ acc datom-bytes (value-bytes (.-v ^Datom (aget keys i)))))
           acc)))))

;; LRU of addr -> #js [node bytes], evicts least recently used nodes above limit bytes
#?(:cljs
   (deftype NodeCache [^js/Map entries limit ^:mutable bytes]))

#?(:cljs
   (defn- cache-get [^NodeCache cache addr]
     (let [entries (.-entries cache)]
       (when-some [entry (.get entries addr)]
         (.delete entries addr)
         (.set entries addr entry)
         (aget entry 0)))))

#?(:cljs
   (defn- cache-put! [^NodeCache cache addr node]
     (let [entries (.-entries cache)
           size    (node-bytes node)]
       (.set entries addr #js [node size])
       (set! (.-bytes cache) (+ (.-bytes cache) size))
       (while (and (> (.-bytes cache) (.-limit cache)) (> (.-size entries) 1))
         (let [oldest (.-value (.next (.keys entries)))]
           (set! (.-bytes cache) (- (.-bytes cache) (aget (.get entries oldest) 1)))
           (.delete entries oldest))))))

#?(:clj
   (defrecord StorageAdapter [storage ^Settings settings]
     me.tonsky.persistent_sorted_set.IStorage
     (store [_ ^ANode node]
       (let [addr (gen-addr)
             _    (util/log "store" addr)
             keys (mapv serializable-datom (.keys node))
             data (cond-> {:level (.level node)
                           :keys  keys}
                    (instance? Branch node)
                    (assoc :addresses (.addresses ^Branch node)))]
         (vswap! *store-buffer* conj! [addr data])
         addr))
     (restore [_ addr]
       (util/log "restore" addr)
       (let [{:keys [level keys addresses]} (-restore storage addr)
             ^List keys' (map deserialize-datom keys)]
         (if addresses
           (Branch. (int level) keys' ^List addresses settings)
           (Leaf. keys' settings)))))
   
   :cljs
   ;; Set keeps no references to stored nodes, cache is what keeps them in memory
   (defrecord StorageAdapter [storage cache]
     set/IStorage
     (-store [_ node]
       (let [addr (gen-addr)
             _    (util/log "store" addr)
             keys (mapv serializable-datom (.-keys node))
             data (cond-> {:keys keys}
                    (instance? set/Node node)
                    (assoc :addresses (vec (.-pointers node))))]
         (vswap! *store-buffer* conj! [addr data])
         (cache-put! cache addr node)
         addr))
     (-restore [_ addr]
       (or
         (cache-get cache addr)
         (let [_    (util/log "restore" addr)
               {:keys [keys addresses]} (-restore storage addr)
               keys (into-array (map deserialize-datom keys))
               node (if addresses
                      (set/->Node keys (into-array addresses))
                      (set/->Leaf keys))]
           (cache-put! cache addr node)
           node)))))

(defn make-storage-adapter [storage opts]
  #?(:clj
     (let [settings (@#'set/map->settings opts)]
       (StorageAdapter. storage settings))
     :cljs
     (StorageAdapter. storage (NodeCache. (js/Map.) (or (:cache-bytes opts) (* 32 1024 1024)) 0))))

(defn maybe-adapt-storage [opts]
  (if-some [storage (:storage opts)]
    (update opts :storage make-storage-adapter opts)
    opts))

(defn storage-adapter ^StorageAdapter [db]
  (when db
    #?(:clj  (.-_storage ^PersistentSortedSet (:eavt db))
       :cljs (.-storage (:eavt db)))))

(defn storage [db]
  (when-some [adapter (storage-adapter db)]
    (:storage adapter)))

(def ^:private ^List stored-dbs
  #?(:clj (ArrayList.) :cljs #js []))

(defn- remember-db [db]
  #?(:clj  (.add stored-dbs (WeakReference. db))
     :cljs (when (exists? js/WeakRef)
             (.push stored-dbs (js/WeakRef. db)))))

(defn store-impl! [db adapter force?]
  (locking (:storage adapter)
    (remember-db db)
    (binding [*store-buffer* (volatile! (transient []))]
      (let [eavt-addr (set/store (:eavt db) adapter)
            aevt-addr (set/store (:aevt db) adapter)
            avet-addr (set/store (:avet db) adapter)
            meta (merge
                   {:schema   (:schema db)
                    :max-eid  (:max-eid db)
                    :max-tx   (:max-tx db)
                    :eavt     eavt-addr
                    :aevt     aevt-addr
                    :avet     avet-addr
                    :max-addr @*max-addr}
                   (set/settings (:eavt db)))]
        (when (or force? (pos? (count @*store-buffer*)))
          (vswap! *store-buffer* conj! [root-addr meta])
          (vswap! *store-buffer* conj! [tail-addr []])
          (-store (:storage adapter) (persistent! @*store-buffer*)))
        db))))

(defn store
  ([db]
   (if-some [adapter (storage-adapter db)]
     (store-impl! db adapter false)
     (throw (ex-info "Database has no associated storage" {}))))
  ([db storage]
   (if-some [adapter (storage-adapter db)]
     (let [current-storage (:storage adapter)]
       (if (identical? current-storage storage)
         (store-impl! db adapter false)
         (throw (ex-info "Database is already stored with another IStorage" {:storage current-storage}))))
     (let [adapter #?(:clj  (StorageAdapter. storage (.-_settings ^PersistentSortedSet (:eavt db)))
                      :cljs (make-storage-adapter storage {}))]
       (store-impl! db adapter false)))))

(defn store-tail [db tail]
  (-store (storage db) [[tail-addr (mapv #(mapv serializable-datom %) tail)]]))

(defn restore-impl [storage opts]
  (locking storage
    (when-some [root (-restore storage root-addr)]
      (let [tail    (-restore storage tail-addr)
            {:keys [schema eavt aevt avet max-eid max-tx max-addr]} root
            _       (vswap! *max-addr max max-addr)
            opts    (merge root opts)
            adapter (make-storage-adapter storage opts)
            db      (db/restore-db
                      {:schema  schema
                       :eavt    (set/restore-by db/cmp-datoms-eavt eavt adapter opts)
                       :aevt    (set/restore-by db/cmp-datoms-aevt aevt adapter opts)
                       :avet    (set/restore-by db/cmp-datoms-avet avet adapter opts)
                       :max-eid max-eid
                       :max-tx  max-tx})]
        (remember-db db)
        [db (mapv #(mapv deserialize-datom %) tail)]))))

(defn db-with-tail [db tail]
  (reduce
    (fn [db datoms]
      (if (empty? datoms)
        db
        (as-> db %
          (reduce db/with-datom % datoms)
          (assoc % :max-tx (:tx (first datoms))))))
    db tail))

(defn restore
  ([storage]
   (restore storage {}))
  ([storage opts]
   (let [[db tail] (restore-impl storage opts)]
     (db-with-tail db tail))))

(defn- addresses-impl [db visit-fn]
  {:pre [(db/db? db)]}
  (set/walk-addresses (:eavt db) visit-fn)
  (set/walk-addresses (:aevt db) visit-fn)
  (set/walk-addresses (:avet db) visit-fn))
  
(defn addresses [dbs]
  (let [*set     (volatile! (transient #{}))
        visit-fn #(vswap! *set conj! %)]
    (visit-fn root-addr)
    (visit-fn tail-addr)
    (doseq [db dbs]
      (addresses-impl db visit-fn))
    (persistent! @*set)))

(defn- read-stored-dbs [storage']
  #?(:clj
     (let [iter ^Iterator (.iterator stored-dbs)]
       (loop [res (transient [])]
         (if (.hasNext iter)
           (let [ref ^WeakReference (.next iter)
                 db  (.get ref)]
             (cond
               (nil? db)
               (do
                 (.remove iter)
                 (recur res))
            
               (identical? (storage db) storage')
               (recur (conj! res db))
            
               :else
               (recur res)))
           (persistent! res))))
     :cljs
     (loop [i   (dec (.-length stored-dbs))
            res (transient [])]
       (if (neg? i)
         (persistent! res)
         (let [db (.deref ^js (aget stored-dbs i))]
           (cond
             (nil? db)
             (do
               (.splice stored-dbs i 1)
               (recur (dec i) res))
             
             (identical? (storage db) storage')
             (recur (dec i) (conj! res db))
             
             :else
             (recur (dec i) res)))))))

(defn collect-garbage [storage']
  #?(:clj (System/gc)) ;; we want all unnecessary weak refs to die as much as possible
  (locking storage'
    (let [dbs    (conj
                   (read-stored-dbs storage')
                   (restore storage')) ;; make sure we won’t gc currently stored db
          used   (addresses dbs)
          all    (-list-addresses storage')
          unused (into [] (remove used) all)]
      (util/log "GC: found" (count dbs) "alive db refs," (count used) "used addrs," (count all) "total addrs," (count unused) "unused")
      (-delete storage' unused))))

#?(:clj
(defn- output-stream
  "OutputStream that ignores flushes. Workaround for slow transit-clj JSON writer.
   See https://github.com/cognitect/transit-clj/issues/43"
  ^OutputStream [^File file]
  (let [os (FileOutputStream. file)]
    (proxy [BufferedOutputStream] [os]
      (flush [])
      (close []
        (let [this ^BufferedOutputStream this]
          (proxy-super flush)
          (proxy-super close)))))))

#?(:clj
(defn file-storage
  ([dir]
   (file-storage dir {}))
  ([dir opts]
   (.mkdirs (io/file dir))
   (let [addr->filename-fn (or (:addr->filename-fn opts) #(format "%08x" %))
         filename->addr-fn (or (:filename->addr-fn opts) #(Long/parseLong % 16))
         write-fn  (or 
                     (:write-fn opts)
                     (when-some [freeze-fn (:freeze-fn opts)]
                       (fn [os o]
                         (spit os (freeze-fn o))))
                     (fn [os o]
                       (with-open [wrt (io/writer os)]
                         (binding [*out* wrt]
                           (pr o)))))
         read-fn   (or 
                     (:read-fn opts)
                     (when-some [thaw-fn (:thaw-fn opts)]
                       (fn [is]
                         (thaw-fn (slurp is))))
                     (fn [is]
                       (with-open [rdr (PushbackReader. (io/reader is))]
                         (edn/read rdr))))]
     (reify IStorage
       (-store [_ addr+data-seq]
         (doseq [[addr data] addr+data-seq]
           (util/log "store" (addr->filename-fn addr))
           (with-open [os (output-stream (io/file dir (addr->filename-fn addr)))]
             (write-fn os data))))
       
       (-restore [_ addr]
         (util/log "restore" (addr->filename-fn addr))
         (with-open [is (io/input-stream (io/file dir (addr->filename-fn addr)))]
           (read-fn is)))
       
       (-list-addresses [_]
         (into []
           (keep #(-> ^File %  .getName filename->addr-fn))
           (.listFiles (io/file dir))))
       
       (-delete [_ addrs-seq]
         (doseq [addr addrs-seq]
           (util/log "deleting" (addr->filename-fn addr))
           (.delete (io/file dir (addr->filename-fn addr))))))))))
