(ns crustimoney.parse
  (:require [clojure.walk :refer (postwalk)]))

(defn- regex? [v] (instance? java.util.regex.Pattern v))

(defn- mk-state [grammar start input]
  {:grammar grammar
   :input input
   :steps [{:rule (get grammar start)
            :pos 0}]})

(defn- forward [state value]
  (let [steps (:steps state)
        last-index (dec (count steps))
        last-step (nth steps last-index)]
    (loop [i last-index]
      (if (< i 0)
        {:done (cond-> state value (assoc-in [:steps last-index :value] value))
         :success? true}
        (let [step (nth steps i)
              rule (:rule step)]
          (if (and (vector? rule) (not (contains? #{/ nil} (second rule))))
            (-> state
                (update-in [:steps i :rule] (comp vec rest))
                (cond-> value (assoc-in [:steps last-index :value] value))
                (update :steps conj {:rule (second rule)
                                     :pos (+ (:pos last-step) (count value))}))
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
                (update :steps conj {:rule (vec alt) :pos (:pos step)})
                (forward nil))
            (recur (dec i))))))))

(defn- advance [state]
  (let [step  (-> state :steps last)
        rule  (-> step :rule)
        input (-> state :input)
        pos   (-> step :pos)]
    (cond (vector? rule)
          (update state :steps conj {:rule (first rule) :pos pos})

          (keyword? rule)
          (update state :steps conj {:rule (get (:grammar state) rule) :pos pos})

          (regex? rule)
          (if-let [found (re-find rule (subs input pos))]
            (forward state found)
            (backward state)))))


(defn- mk-value [state]
  (loop [value nil
         steps (-> state :steps reverse)
         result {}]
    (if-let [step (first steps)]
      (let [rule (:rule step)]
        (if (keyword? rule)
          (if value
            (recur nil (rest steps) (assoc result rule value))
            (recur nil (rest steps) {rule result}))
          (recur (:value step) (rest steps) result)))
      result)))

(defn- mk-flat [value]
  (postwalk (fn [form]
              (if (map? form)
                (reduce-kv (fn [a k v]
                             (if (and (map? v) (contains? v k))
                               (let [vv (get v k)]
                                 (if (vector? vv)
                                   (assoc a k (vec (cons (dissoc v k) vv)))
                                   (assoc a k [(dissoc v k) vv])))
                               a))
                           form
                           form)
                form))
            value))

(defn parse [grammar start input]
  (loop [s (mk-state grammar start input)]
    (if-let [d (:done s)]
      (when (:success? s)
        (-> (mk-value d) (mk-flat)))
      (recur (advance s)))))

(comment
  (def grammar {:expr   [:sum]
                :sum    [:number :op :sum / :number]
                :op     #"^\+|-"
                :number #"^\d+"})


  (mk-state grammar :expr "40+2")
  ;;=>
  {:grammar {:expr [:sum]
             :sum  [:number :op :sum / :number]
             :op   #"^\+|-" , :number #"^\d+"}
   :input   "40+2"
   :steps   [{:rule [:sum] , :pos 0}]}


  (advance *1) ;; until done
  ;;=>
  {:grammar ...
   :input   ...
   :steps   [{:rule [:sum]           :pos 0}
             {:rule :sum             :pos 0}
             {:rule [:sum / :number] :pos 0} ;; the rule was [:number :op :sum / :number] in the
                                             ;; beginning, but moving forward, next is called on it.
             {:rule :number          :pos 0}
             {:rule #"^\d+"          :pos 0 :value "40"}
             {:rule :op              :pos 2}
             {:rule #"^\+|-"         :pos 2 :value "+"}
             {:rule :sum             :pos 3}
             {:rule [:number]        :pos 3} ;; the rule was [:number :op :sum / :number] in the
                                             ;; beginning, but backtracking set it to the
                                             ;; alternative after the /.
             {:rule :number          :pos 3}
             {:rule #"^\d+"          :pos 3 :value "2"}]}


  (mk-value *1)
  ;;=>
  {:sum {:sum {:number "2"}, :op "+", :number "40"}}


  (mk-flat *1)
  ;;=>
  {:sum [{:op "+", :number "40"} {:number "2"}]}

  )
