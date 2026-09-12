(ns oracle.clojure-involution-test
  (:require [clojure.test :refer :all]
            [oracle.clojure-involution :as involution]))

(deftest signed-permutation-involutions
  (let [swap (involution/adjacent-swap 4 1)
        flip (involution/sign-flip 4 2)
        basis (involution/compose-local [swap flip])]
    (is (involution/involution? swap (range 4)))
    (is (involution/involution? flip (range 4)))
    (is (involution/involution? basis (range 4)))))

(deftest rule-selection-is-finite-and-local
  (let [log "Not in scope: suc\n"
        source "module Demo where\nopen import Agda.Builtin.Nat\n"]
    (is (= :add-suc-import
           (:rule-id (involution/select-safe-rule log source)))))
  (is (= :none
         (:rule-id (involution/select-safe-rule "unrecognised error\n" "module Demo where\n")))))

(deftest rewrites-are-idempotent
  (let [source "module Demo where\nopen import Agda.Builtin.Nat\n"
        once (:source (involution/apply-safe-rule :add-suc-import source))
        twice (:source (involution/apply-safe-rule :add-suc-import once))]
    (is (= once twice))))
