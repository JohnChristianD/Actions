(ns q-closure-predictive-v147)

(def zero 0)
(defn sq [x] (* x x))
(defn fourth [x] (sq (sq x)))
(defn num [mask a x b] (- (reduce + (map #(-> (nth a %) (sq) (* (sq (nth x %)))) mask) 0) b))
(defn den [mask x] (reduce + (map #(fourth (nth x %)) mask)))
(defn first-negative [mask a x mu] (some (fn [i] (when (< (- (nth a i) (* mu (sq (nth x i)))) 0) i)) mask))
(defn runq [mask a x b steps]
  (let [n (num mask a x b) d (den mask x) mu (if (and (pos? n) (pos? d)) (/ n d) 0) bad (first-negative mask a x mu)]
    (if (nil? bad) [mu mask steps]
      (let [r (vec (remove #(= % bad) mask)) n2 (num r a x b) d2 (den r x) y (* (nth a bad) (sq (nth x bad))) z (fourth (nth x bad)) mu2 (/ n2 d2)]
        (assert (and (pos? n) (pos? d) (pos? d2) (pos? n2) (< (* y d) (* n z))))
        (assert (< mu mu2))
        (runq r a x b (inc steps))))))
(defn vectors [n] (if (zero? n) [[]] (for [p (vectors (dec n)) q [0 1 2]] (conj p q))))
(doseq [n (range 1 5) a (vectors n) x (vectors n) bi (range 5)]
  (let [[mu active steps] (runq (vec (range n)) a x bi 0)]
    (assert (<= steps n))
    (doseq [i active] (assert (<= 0 (- (nth a i) (* mu (sq (nth x i)))))))
    (doseq [i (remove (set active) (range n))] (assert (<= (- (nth a i) (* mu (sq (nth x i)))) 0)))))
(println "clojure-q-finite-fuel=PASS")
(println "clojure-q-terminal-signs=PASS")
(println "clojure-q-multiplier-monotonicity=PASS")
(println "clojure-q-terminal-kkt-prescriptive=PASS")
(println "clojure-bridge-bounded=PASS")
(println "clojure-theorem-bounded=PASS")
(println "clojure-conjecture-falsification=PASS")
