(ns oracle.clojure-involution-test
  (:require [clojure.test :refer :all]
            [oracle.clojure-involution :as involution]))

(deftest signed-permutation-involutions
  (let [swap (involution/adjacent-swap 4 0)
        flip (involution/sign-flip 4 3)
        domain [[0 1 2 3]
                [3 2 1 0]
                [-1 4 2 8]]
        basis (involution/compose-local [swap flip])]
    (is (involution/involution? swap domain))
    (is (involution/involution? flip domain))
    (is (involution/involution? basis domain))))

(deftest rule-selection-is-finite-and-local
  (let [log "Not in scope: suc\n"
        source "module Demo where\n"]
    (is (= :add-suc-import
           (:rule-id (involution/select-safe-rule log source)))))
  (is (= :none
         (:rule-id (involution/select-safe-rule "unrecognised error\n" "module Demo where\n")))))

(deftest rewrites-are-idempotent
  (let [source "module Demo where\n"
        once (:source (involution/apply-safe-rule :add-suc-import source))
        twice (:source (involution/apply-safe-rule :add-suc-import once))]
    (is (= once twice))
    (is (.contains once "open import Agda.Builtin.Nat using (Nat; zero; suc)"))))

(defn -main [& _]
  (let [result (run-tests 'oracle.clojure-involution-test)]
    (System/exit (if (zero? (+ (:fail result) (:error result))) 0 1))))
