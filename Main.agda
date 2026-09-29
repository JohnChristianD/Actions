module Main where

open import IO
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.List.Base using (_∷_; [])
open import Exotic.ERL.FullCoupled.CanonicalLearnerMonolith as C

executableKernel : C.CanonicalFullLearnerKernel
executableKernel =
  C.mkFullLearnerKernel
    (C.actionSpace (zero ∷ []) zero)
    (C.mkWatkinsKernel
      (λ critic _ → critic)
      (λ _ _ → C.enabled)
      (λ _ _ → C.enabled))
    (C.f4IntUKernel C.zero8)
    (C.lcbCountKernel C.finiteLCBBonus8)

executableInitialState : C.CanonicalFullLearnerState
executableInitialState =
  C.fullLearnerState
    (C.watkinsState (C.criticState C.zeroQ) C.zero8 C.disabled)
    (C.gruState C.zero8 C.identityGRUMatrices C.zeroGRUNoise C.zeroGlobalControl)
    (C.f4IntUState C.zero8 C.zero8 C.zero8 C.zero8 C.zero8)
    (C.lcbCountState C.zeroCounts zero)
    C.canonicalQLogControl
    (C.finiteRational zero zero (suc zero))

executableStateAfterOneStep : C.CanonicalFullLearnerState
executableStateAfterOneStep =
  C.canonicalFullStep executableKernel executableInitialState

executableTotalCount : Nat
executableTotalCount =
  C.totalCount (C.lcbCounts executableStateAfterOneStep)

executableStatus : String
executableStatus with executableTotalCount
... | zero = "canonical learner executable: totalCount did not advance"
... | suc zero = "canonical learner executable: one canonical step completed"
... | suc (suc n) = "canonical learner executable: unexpected totalCount after one step"

main : Main
main = run (putStrLn executableStatus)
