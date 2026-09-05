(ns q-closure-predictive-v147)

(defn positive [n] n)

(defn weighted [h x] (* h x))

(defn cap [budget value]
  (cond
    (zero? budget) 0
    (zero? value) 0
    :else (inc (cap (dec budget) (dec value)))))

(defn project [budget h x]
  (cap budget (weighted h x)))

(assert (= (positive 7) 7))
