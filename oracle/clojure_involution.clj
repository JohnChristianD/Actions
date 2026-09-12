(ns oracle.clojure-involution
  (:require [clojure.string :as str]))

(defn- valid-index? [n i]
  (and (integer? n) (pos? n) (integer? i) (<= 0 i) (< i n)))

(defn adjacent-swap [n i]
  (when-not (and (valid-index? n i) (< (inc i) n))
    (throw (ex-info "adjacent-swap index out of range" {:n n :i i})))
  (fn [v]
    (let [v (vec v)
          j (inc i)
          xi (nth v i)
          xj (nth v j)]
      (assoc (assoc v i xj) j xi))))

(defn sign-flip [n i]
  (when-not (valid-index? n i)
    (throw (ex-info "sign-flip index out of range" {:n n :i i})))
  (fn [v]
    (let [v (vec v)]
      (assoc v i (- (nth v i))))))

(defn compose-local [operations]
  (fn [v]
    (reduce (fn [x operation] (operation x)) (vec v) operations)))

(defn involution? [operation domain]
  (every? (fn [v] (= (vec v) (vec (operation (operation v))))) domain))

(def ^:private suc-import
  "open import Agda.Builtin.Nat using (Nat; zero; suc)")

(defn select-safe-rule [agda-log source]
  (cond
    (and (str/includes? agda-log "Not in scope: suc")
         (not (str/includes? source suc-import)))
    {:rule-id :add-suc-import}

    :else
    {:rule-id :none}))

(defn apply-safe-rule [rule-id source]
  (case rule-id
    :add-suc-import
    {:rule-id rule-id
     :source (if (str/includes? source suc-import)
               source
               (if-let [[_ module] (re-find #"(?m)^(module\s+[^\n]+\s+where)\s*$" source)]
                 (str/replace-first source
                                    (re-pattern (java.util.regex.Pattern/quote module))
                                    (str module "\n" suc-import))
                 source))}

    {:rule-id :none
     :source source}))

(defn- basis-demo []
  (let [swap (adjacent-swap 4 0)
        flip (sign-flip 4 3)
        basis (compose-local [swap flip])
        domain [[0 1 2 3]
                [3 2 1 0]
                [-1 4 2 8]]]
    {:swap (involution? swap domain)
     :flip (involution? flip domain)
     :disjoint-composition (involution? basis domain)}))

(defn -main [& _]
  (let [result (basis-demo)]
    (println "clojure-local-involution-basis=" result)
    (println "clojure-global-state=none")
    (println "clojure-repair-rule-set=finite-allowlist")))
