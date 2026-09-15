{-# OPTIONS --safe #-}
module Exotic.ERL.FullCoupled.SignReLUSemidirectCycleComposition_test where

open import Agda.Builtin.Equality using (_≡_)
open import Data.Nat using (zero; suc)
open import Exotic.efficient_chad.Int8 using (Int8; zero8)
open import Exotic.ERL.FullCoupled.SignReLUSemidirectCycleComposition
open import Exotic.ERL.FullCoupled.ConnectedGRUSemidirectQSA
open import Exotic.ERL.FullCoupled.DyadicGRU using
  ( GRUState
  ; gruCandidate
  ; signReLU8
  ; apply
  )

signReLU-zero-test :
  run signReLUWindow zero8 ≡ zero8
signReLU-zero-test = signReLUWindow-zero

deep-signReLU-zero-test :
  deepSignReLU (suc (suc zero)) zero8 ≡ zero8
deep-signReLU-zero-test = deepSignReLU-zero (suc (suc zero))

composition-law-test :
  ∀ (a b c : MobiusAction) (x : Int8) →
  run (composeAction (composeAction a b) c) x
  ≡ run (composeAction a (composeAction b c)) x
composition-law-test = deepWindow-assoc-one-step

gru-semidir-test :
  ∀ (x : Int8) (s : GRUState) →
  decodeFamily (carrierStep x (encodeFamily s)) ≡ gruStep s x
gru-semidir-test = carrierStep-encodes-gruStep

gru-signReLU-branch-test :
  ∀ x → gruCandidate x ≡ apply signReLU8 x
gru-signReLU-branch-test x = refl

hidden-persistent-semidir-test :
  ∀ x → SemidirectCycleEmbedding hiddenPersistentSemidirect GRUState
hidden-persistent-semidir-test = hiddenPersistentEmbedding

whole-energy-audit-test :
  ∀ (s : GRUState) (x : Int8) → ContributionAudit s x
whole-energy-audit-test = contributionAuditWitness
