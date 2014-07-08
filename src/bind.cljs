(ns bind
  "Data-binding for ClojureScript apps."
  (:require [clojure.data :as data]
            [clojure.set :as set]
            [toolbox.dom :as dom]
            [toolbox.dom.class :as class]
            [toolbox.event :as e]
            hype)
  (:require-macros [clojure.template :refer [do-template]]
                   [hype :refer [defattr]]))

;; [Procedures]
(defmulti bind! (fn [node binding-type path & args] binding-type) :default ::default)

(let [!!watchers (atom {})
      find-match (fn [steps old new new-state]
                   (if (get-in new steps) 
                     (let [new-val (get-in new-state steps)]
                       [true new-val]) ;; Signal update.
                     (if (get-in old steps)
                       [true  nil] ;; Signal removal.
                       [false nil] ;; Nothing to signal.
                       )))
      get-values (fn [!!root steps]
                   (case (-> steps meta :type)
                     :val  (get-in @!!root steps)
                     :ptr  (let [[!!true-root & true-steps] (get-in @!!root steps)]
                             (get-in @!!true-root true-steps))
                     :ptrs (for [[!!true-root & true-steps] (get-in @!!root steps)]
                             (get-in @!!true-root true-steps))))
      apply-bindings! (fn [_ !!root old-state new-state]
                        (let [[old new unchanged] (data/diff old-state new-state)]
                          (doseq [[steps pairs] (get @!!watchers !!root)
                                  [node watcher-fn] pairs
                                  :let [[found? val-for-fn] (find-match steps old new new-state)]
                                  :when found?]
                            (watcher-fn node val-for-fn))))]
  (defn get-watchers [path]
    (get-in @!!watchers [(first path) (rest path)]))

  (defn add-watcher! [path node watcher]
    (let [!!root (doto (first path)
                   (add-watch (gensym) apply-bindings!))
          steps (rest path)]
      (swap! !!watchers update-in [!!root steps] conj [node watcher])
      (watcher node (get-in @!!root steps)))
    nil)
  )

(defn context [path]
  (let [!context (atom nil)]
    (add-watcher! path nil #(reset! !context %2))
    !context))

;; [Installation]
(do-template [<binding-type> <init-expr> <watch-expr>]
  (defmethod bind! <binding-type> [node _ config]
    (let [path (if (vector? config)
                 config
                 (get config :path))
          [!!root & steps] path]
      <init-expr>
      (add-watcher! path
                    node
                    (fn [node new-val]
                      <watch-expr>)))
    nil)
  ;; 1-way.
  :text    nil (assoc node :&text ((get config :pre identity) new-val))
  :attrs   nil (merge node ((get config :pre identity) new-val))
  :enabled nil (assoc node :disabled (not new-val))
  :classes nil (class/set-classes! node ((get config :pre identity) new-val))
  :css     nil (class/enable! node config new-val)
  ;; 2-way
  :value
  (e/on! node "change" (fn [e] (swap! !!root assoc-in steps (get node :&value))))
  (when (not= new-val (get node :&value))
    (assoc node :&value new-val))

  :checked
  (e/on! node "change" (fn [e] (swap! !!root assoc-in steps (get node :&value))))
  (when (not= (boolean new-val) (get node :&value))
    (assoc node :&value (boolean new-val)))

  :focused
  (doto node
    (e/on! "focus" (fn [e] (swap! !!root assoc-in steps true)))
    (e/on! "blur"  (fn [e] (swap! !!root assoc-in steps false))))
  (if new-val
    (.focus node)
    (.blur node))

  ;; Control-flow
  :if
  (let [[then else] (get node :&children)]
    (doto node
      (aset ::then-content (dom/remove! then))
      (aset ::else-content (dom/remove! else))))
  (let [? ((or (get config :test) identity) new-val)]
    (doto node
      dom/remove-children!
      (dom/append! (aget node (if ? ::then-content ::else-content)))))

  :when
  (assoc-in node [:&style :display] "none")
  (if ((or (get config :test) identity) new-val)
    (update-in node [:&style] dissoc :display)
    (assoc-in node [:&style :display] "none"))
  )

(defmethod bind! :hype/unroll [node _ {:keys [tag path id pre] :or {id identity pre identity}}]
  (add-watcher! path
                node
                (fn [node changes]
                  (let [id->data (into (array-map) (map (fn [x] [(id x) x])
                                                        (pre changes)))
                        id->dom  (into {} (map (fn [x] [(id @(aget x :$bind-model)) x])
                                               (aget node :$bind-model-elems)))
                        data-ids (set (keys id->data))
                        dom-ids (set (keys id->dom))
                        added-elems (set/difference data-ids dom-ids)
                        removed-elems (set/difference dom-ids data-ids)
                        preserved-elems (set/intersection data-ids dom-ids)
                        _before (:&previous node)
                        _after (:&next node)
                        _up (:&parent node)
                        unrolled (do (dom/remove! node)
                                   (for [[_id elem] (reduce #(assoc %1 %2 nil) id->data removed-elems)
                                         :let [dom-node (cond (added-elems _id)
                                                              (let [!!data (atom elem)]
                                                                [true (doto (hype/node [tag !!data])
                                                                        (aset :$bind-model !!data))])
                                                              
                                                              (removed-elems _id)
                                                              (do (dom/remove! (id->dom _id))
                                                                nil)

                                                              (preserved-elems _id)
                                                              (let [dom-node (id->dom _id)
                                                                    !!data (aget dom-node :$bind-model)]
                                                                (when (not= elem @!!data)
                                                                  (reset! !!data elem))
                                                                [false dom-node]))]
                                         :when dom-node]
                                     dom-node))]
                    (loop [last-existing nil
                           [[created? dom-node] & others] unrolled]
                      (when dom-node
                        (if created?
                          (if last-existing
                            (dom/insert-after! dom-node last-existing)
                            (dom/prepend! node dom-node))
                          (if last-existing
                            (dom/insert-after! dom-node last-existing)
                            nil))
                        (recur dom-node others)))
                    (aset node :$bind-model-elems (mapv second unrolled))
                    (cond _before (dom/insert-after! node _before)
                          _after  (dom/insert-before! node _after)
                          _up     (dom/append! _up node))
                    ;; (reduce #(doto %2
                    ;;            (dom/insert-after! %1))
                    ;;         (doto node
                    ;;           (aset :$bind-model-elems unrolled))
                    ;;         unrolled)
                    )))
  nil)

(defmethod bind! :hype/splice [node _ {:keys [tag path id pre] :or {id identity pre identity}}]
  (add-watcher! path
                (doto node
                  (assoc-in [:&style "display"] "none"))
                (fn [node changes]
                  (let [id->data (into (array-map) (map (fn [x] [(id x) x])
                                                        (pre changes)))
                        id->dom  (into {} (map (fn [x] [(id @(aget x ::bind-model)) x])
                                               (aget node ::hype-spliced)))
                        data-ids (set (keys id->data))
                        dom-ids (set (keys id->dom))
                        added-elems (set/difference data-ids dom-ids)
                        removed-elems (set/difference dom-ids data-ids)
                        preserved-elems (set/intersection data-ids dom-ids)
                        unrolled (loop [last-node node
                                        unrolled []
                                        pieces (reduce #(assoc %1 %2 nil) id->data removed-elems)]
                                   (if-let [[_id elem] (first pieces)]
                                     (cond (contains? added-elems _id)
                                           (let [!data (atom elem)
                                                 dom-node (doto (hype/node [tag !data])
                                                            (aset ::bind-model !data)
                                                            (dom/insert-after! last-node))]
                                             (recur dom-node (conj unrolled dom-node) (rest pieces)))
                                           
                                           (contains? removed-elems _id)
                                           (do (dom/remove! (id->dom _id))
                                             (recur last-node unrolled (rest pieces)))

                                           (contains? preserved-elems _id)
                                           (let [dom-node (doto (id->dom _id)
                                                            (dom/insert-after! last-node))
                                                 !data (aget dom-node ::bind-model)
                                                 new-data elem]
                                             (when (not= new-data @!data)
                                               (reset! !data new-data))
                                             (recur dom-node (conj unrolled dom-node) (rest pieces)))
                                           )
                                     unrolled))]
                    (aset node ::hype-spliced unrolled)
                    )))
  nil)

(do-template [<tag> <binding-type>]
  (defattr <tag> [node config]
    (bind! node <binding-type> config))

  ;; Normal
  :bind/text    :text
  :bind/checked :checked
  :bind/attrs   :attrs
  :bind/enabled :enabled
  :bind/focused :focused
  :bind/value   :value
  :bind/classes :classes
  :bind/css     :css
  :bind/if      :if
  :bind/when    :when
  
  ;; Special
  :hype/unroll  :hype/unroll
  :hype/splice  :hype/splice
  )
