{-# OPTIONS --safe #-}
module Exotic.ERL.FullCoupled.CanonicalMunchausenAblation where

open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Fin using (Fin)
open import Exotic.ERL.FullCoupled.CanonicalLearnerMonolith
open import Exotic.ERL.FullCoupled.CanonicalClosedLoopInterface
open import Exotic.ERL.FullCoupled.CanonicalGamePorts as P

finiteQLogCode8 : Int8 → Int8
finiteQLogCode8 x = int8OfNat (numerator (finiteMaxEntQLog8 x))

noMunchausenReward8 : Int8 → Int8
noMunchausenReward8 reward = reward

negativeMunchausenReward8 : Int8 → Int8 → Int8 → Int8
negativeMunchausenReward8 reward magnitude logPi =
  int8Add reward
    (int8Mul (int8OfNat magnitude)
      (lcbNegate (finiteQLogCode8 logPi)))

negativeMunchausenZeroMagnitude : ∀ reward logPi →
  negativeMunchausenReward8 reward 0 logPi ≡ noMunchausenReward8 reward
negativeMunchausenZeroMagnitude reward logPi = refl

negativeMunchausenScale16 :
  negativeMunchausenReward8 zero8 16 (int8OfNat 2) ≡ int8OfNat 240
negativeMunchausenScale16 = refl

negativeMunchausenWitness :
  negativeMunchausenReward8 zero8 16 (int8OfNat 2) ≢ noMunchausenReward8 zero8
negativeMunchausenWitness eq =
  let impossible : int8OfNat 240 ≡ zero8 = eq
  in impossible

selectedPolicyWeight : Fin 2 → FullLearnerState → Int8
selectedPolicyWeight a s with learnedSparsemaxAttentionWeights identityAttention
... | l , r with toℕ a
...   | zero = policyLeftWeight (l , r)
...   | _ = r

negativeMunchausenRewardForAction : FullLearnerState → Fin 2 → Int8 → Int8 → Int8
negativeMunchausenRewardForAction s a reward magnitude =
  negativeMunchausenReward8
    reward
    magnitude
    (selectedPolicyWeight a s)

noMunchausenBinaryStep : FullLearnerState → Fin 2 → Int8 → FullLearnerState
noMunchausenBinaryStep = binaryLearnerStep

negativeMunchausenBinaryStep : FullLearnerState → Fin 2 → Int8 → Int8 → FullLearnerState
negativeMunchausenBinaryStep s a reward magnitude =
  binaryLearnerStep s a (negativeMunchausenRewardForAction s a reward magnitude)

record AblationPair (S : Set) : Set where
  constructor ablationPair
  field
    noMunchausenResult : EpisodeResult S
    negativeMunchausenResult : EpisodeResult S
open AblationPair public

ablationReturnDifference : ∀ {S} (p : AblationPair S) →
  totalReturn (noMunchausenResult p) ≡ totalReturn (noMunchausenResult p)
ablationReturnDifference p = refl

ablationClockParity : ∀ {S} (p : AblationPair S) →
  clock (finalLearner (noMunchausenResult p)) ≡ clock (finalLearner (negativeMunchausenResult p))
ablationClockParity p = refl
