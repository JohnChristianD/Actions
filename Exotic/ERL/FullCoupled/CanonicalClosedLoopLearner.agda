{-# OPTIONS --safe #-}

module Exotic.ERL.FullCoupled.CanonicalClosedLoopLearner where

open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; trans; sym)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)
open import Data.Nat using (_∸_)
open import Data.Fin using (Fin; toℕ; fromℕ<)
open import Data.Fin.Properties using ()
open import Data.Nat.DivMod using (m%n<n)
open import Data.Product using (_×_; _,_)
open import Data.Empty using (⊥)
open import Exotic.ERL.FullCoupled.CanonicalLearnerMonolith

policyRightWeight : Sparsemax2Pair → Int8
policyRightWeight (_ , r) = r

actionWeight8 : Sparsemax2Pair → Fin 2 → Int8
actionWeight8 (l , r) a with toℕ a
... | zero = l
... | _ = r

standardMunchausenScaleCode8 : Int8
standardMunchausenScaleCode8 = int8OfNat 16

negativeMunchausenScaleCode8 : Int8
negativeMunchausenScaleCode8 = lcbNegate standardMunchausenScaleCode8

negativeMunchausenScaleCode8-law :
  int8Add standardMunchausenScaleCode8 negativeMunchausenScaleCode8 ≡ zero8
negativeMunchausenScaleCode8-law = refl

finiteMaxEntQLog8 : Int8 → FiniteRational
finiteMaxEntQLog8 = finiteQLog8

negativeMunchausenBonus8 : Int8 → Int8
negativeMunchausenBonus8 logPi =
  int8Mul negativeMunchausenScaleCode8
    (rationalCode (finiteMaxEntQLog8 logPi))

standardMunchausenBonus8 : Int8 → Int8
standardMunchausenBonus8 logPi =
  int8Mul standardMunchausenScaleCode8
    (rationalCode (finiteMaxEntQLog8 logPi))

negativeMunchausenBonus8-sign-flip : ∀ logPi →
  negativeMunchausenBonus8 logPi ≡
  int8Mul (lcbNegate standardMunchausenScaleCode8)
    (rationalCode (finiteMaxEntQLog8 logPi))
negativeMunchausenBonus8-sign-flip logPi = refl

negativeMunchausenBonus8-order :
  toℕ (code negativeMunchausenScaleCode8) ≡ 240
negativeMunchausenBonus8-order = refl

finiteMaxEntQLog8-is-finite : ∀ x →
  finiteMaxEntQLog8 x ≡ finiteQLog8 x
finiteMaxEntQLog8-is-finite x = refl

negativeMunchausenReward8 : Int8 → Int8 → Int8
negativeMunchausenReward8 reward logPi =
  int8Add reward (negativeMunchausenBonus8 logPi)

negativeMunchausenReward8-standard-flip : ∀ reward logPi →
  negativeMunchausenReward8 reward logPi ≡
  int8Add reward
    (int8Mul (lcbNegate standardMunchausenScaleCode8)
      (rationalCode (finiteMaxEntQLog8 logPi)))
negativeMunchausenReward8-standard-flip reward logPi = refl

closedLoopCriticUpdate : CriticState → Fin 2 → Int8 → CriticState
closedLoopCriticUpdate q a shapedReward with toℕ a
... | zero = criticState (int8Add (qLeft q) shapedReward) (qRight q)
... | _ = criticState (qLeft q) (int8Add (qRight q) shapedReward)

closedLoopCountUpdate : Fin 2 → LCBCountState → LCBCountState
closedLoopCountUpdate a (lcbCountState l r t) with toℕ a
... | zero = lcbCountState (suc l) r (suc t)
... | _ = lcbCountState l (suc r) (suc t)

closedLoopLearnerStep : FullLearnerKernel → FullLearnerState → Fin 2 → Int8 → FullLearnerState
closedLoopLearnerStep K s action environmentReward =
  let policy = canonicalPolicy K s
      logPi = actionWeight8 policy action
      shapedReward = negativeMunchausenReward8 environmentReward logPi
      signal = int8Add (canonicalSignal K s) shapedReward
      nextCritic = closedLoopCriticUpdate (critic (watkins s)) action shapedReward
      nextWatkins = watkinsState
        nextCritic
        signal
        (trace (watkins s))
      nextAttention = attentionStep K (attention s) signal
      nextGRU =
        let p = learnedSparsemaxAttentionWeights nextAttention
            w = walshHadamardApply (liftAttention p)
        in gruStep (gru s) (int8Add signal (attentionToGRU K w))
      nextOptimizer = f4ThetaStep (optimizerKernel K) (optimizer s) signal
      nextCounts = closedLoopCountUpdate action (lcbCounts s)
      nextQLog = negativeFiniteQLog8 logPi
  in fullLearnerState
    (suc (clock s))
    nextWatkins
    nextAttention
    nextGRU
    nextOptimizer
    (norm s)
    nextCounts
    (canonicalQLogControl K s)
    nextQLog

closedLoopLearnerStep-clock : ∀ K s a r →
  clock (closedLoopLearnerStep K s a r) ≡ suc (clock s)
closedLoopLearnerStep-clock K s a r = refl

closedLoopLearnerStep-norm-preserved : ∀ K s a r →
  norm (closedLoopLearnerStep K s a r) ≡ norm s
closedLoopLearnerStep-norm-preserved K s a r = refl

closedLoopLearnerStep-persistent-GRU : ∀ K s a r →
  persistentGRU (closedLoopLearnerStep K s a r).gru ≡ persistentGRU (gru s)
closedLoopLearnerStep-persistent-GRU K s a r =
  persistent-preservation
    (gru s)
    (let p = learnedSparsemaxAttentionWeights
               (attentionStep K (attention s)
                 (int8Add (canonicalSignal K s)
                   (negativeMunchausenReward8 r (actionWeight8 (canonicalPolicy K s) a))))
         w = walshHadamardApply (liftAttention p)
     in int8Add
          (int8Add (canonicalSignal K s)
            (negativeMunchausenReward8 r (actionWeight8 (canonicalPolicy K s) a)))
          (attentionToGRU K w))

closedLoopLearnerStep-left-reward : ∀ (K : FullLearnerKernel) (s : FullLearnerState) (r : Int8) →
  qLeft (critic (closedLoopLearnerStep K s (fromℕ< (m%n<n 0 2)) r)) ≡
  int8Add (qLeft (critic (watkins s)))
    (negativeMunchausenReward8 r
      (policyLeftWeight (canonicalPolicy K s)))
closedLoopLearnerStep-left-reward K s r = refl

closedLoopLearnerStep-right-reward : ∀ (K : FullLearnerKernel) (s : FullLearnerState) (r : Int8) →
  qRight (critic (closedLoopLearnerStep K s (fromℕ< (m%n<n 1 2)) r)) ≡
  int8Add (qRight (critic (watkins s)))
    (negativeMunchausenReward8 r
      (policyRightWeight (canonicalPolicy K s)))
closedLoopLearnerStep-right-reward K s r = refl

closedLoopLearnerStep-respects-GRU-equivalence : ∀ (K : FullLearnerKernel)
  (s t : FullLearnerState) (a : Fin 2) (r : Int8) →
  persistentGRU (gru s) ≡ persistentGRU (gru t) →
  persistentGRU (closedLoopLearnerStep K s a r).gru ≡
  persistentGRU (closedLoopLearnerStep K t a r).gru
closedLoopLearnerStep-respects-GRU-equivalence K s t a r h =
  trans
    (closedLoopLearnerStep-persistent-GRU K s a r)
    (trans h (sym (closedLoopLearnerStep-persistent-GRU K t a r)))