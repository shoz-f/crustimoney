(ns crustimoney.parse)

(def grammar {:expr   [:sum]
              :sum    [:number :op :sum / :number]
              :op     #"^\+|-"
              :number #"^\d+"})

;; ;; model

;; {:grammar ...
;;  :input ...
;;  :steps
;;  [{:rule [:sum]
;;    :pos 0
;;    :value nil}

;;   {:rule :sum
;;    :pos 0
;;    :value nil}

;;   {:rule [:number :op :sum / :number]
;;    :pos 0
;;    :value nil}

;;   {:rule :number
;;    :pos 0
;;    :value nil}

;;   {:rule #"^\d+"
;;    :pos 0
;;    :value nil}

;;   {:rule :op
;;    :pos 2
;;    :value "42"}

;;   {:rule #"^\+|-"
;;    :pos 2
;;    :value "42"}

;;   {:rule :sum
;;    :pos 3
;;    :value "+"}

;;   {:rule [:number :op :sum / :number]
;;    :pos 3
;;    :value "+"}

;;   {:rule :number
;;    :pos 3
;;    :value "+"}

;;   {:rule #"^\d+"
;;    :pos 3
;;    :value "+"}

;;   {:rule :op
;;    :pos 4
;;    :value "2"}

;;   {:rule #"^\+|-"
;;    :pos 4
;;    :value "2"}

;;   {:rule :sum
;;    :pos 5
;;    :value "-"}

;;   {:rule [:number]
;;    :pos 5
;;    :value "-"}

;;   {:rule :number
;;    :pos 5
;;    :value "-"}

;;   {:rule #"^\d+"
;;    :pos 5
;;    :value "-"}

;;   {:rule nil
;;    :pos 8
;;    :value "100"}]}

;; value

;; 1. take "100", search for terminal (in this case #"^\d+") and add
;;    to map with non-terminal above (in this case :number) as key.
;; 2. take value of non-terminal from former step, so "-"
;; 3. search for terminal (#"^\+|-") and use non-terminal above :op,
;;    but as it has passed another non-terminal, first wrap current
;;    value with that as key.

;; {:sum {:number "42" :op "+" :sum {:number "2" :op "-" :sum {:number "100"}}}}

;; recursion

;; inside out: if a key holds a map, check whether that map holds a
;; map (or seq) with the same key, if so, put those maps in a seq as
;; the value.

(defn- regex? [v] (instance? java.util.regex.Pattern v))

(defn- mk-state [grammar start input]
  {:grammar grammar
   :input input
   :steps [{:rule (get grammar start)
            :pos 0}]})

(defn- forward [state value pos+]
  (prn state)
  (let [steps (:steps state)
        lstep (last steps)]
    (loop [i (dec (count steps))]
      (if (< i 0)
        {:done (update state :steps conj (assoc lstep
                                                :rule nil
                                                :value value
                                                :pos (+ (:pos lstep) (count value))))
         :success? true}
        (let [step (nth steps i)
              rule (:rule step)]
          (if (and (vector? rule) (not (contains? #{/ nil} (second rule))))
            (-> (update step :rule (comp vec rest))
                (->> (update state :steps assoc i))
                (update :steps conj (assoc lstep
                                           :rule (second rule)
                                           :value value
                                           :pos (+ (:pos lstep) pos+))))
            (recur (dec i))))))))

(defn- backward [state]
  (let [steps (:steps state)]
    (loop [i (dec (count steps))]
      (if (< i 0)
        {:done state
         :success? false}
        (let [step (nth steps i)
              rule (:rule step)]
          (if-let [alt (and (vector? rule) (seq (drop-while #(not= % /) rule)))]
            (-> state
                (update :steps #(vec (take i %)))
                (update :steps conj (assoc step :rule (vec alt)))
                (forward (:value step) 0))
            (recur (dec i))))))))

(defn- advance [state]
  (let [step  (-> state :steps last)
        rule  (-> step :rule)
        input (-> state :input)
        pos   (-> step :pos)]
    (cond (vector? rule)
          (update state :steps conj (assoc step :rule (first rule)))

          (keyword? rule)
          (update state :steps conj (assoc step :rule (get (:grammar state) rule)))

          (regex? rule)
          (if-let [found (re-find rule (subs input pos))]
            (forward state found (count found))
            (backward state)))))

(defn- mk-value [state]
  (loop [result {}
         value (-> state :steps last :value)
         steps (-> state :steps reverse rest)
         wrap? true]
    (if-let [step (first steps)]
      (let [rule (:rule step)]
        (cond (and (keyword? rule) wrap?)
              (recur {rule result} value (rest steps) true)

              (keyword? rule)
              (recur (assoc result rule value) (:value step) (rest steps) true)

              (regex? rule)
              (recur result value (rest steps) false)

              (vector? rule)
              (recur result value (rest steps) wrap?)))
      result)))

(defn parse [grammar start input]
  (loop [s (mk-state grammar start input)]
    (if-let [d (:done s)]
      (mk-value d)
      (recur (advance s)))))
