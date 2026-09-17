{-# OPTIONS --safe #-}
module Exotic.ERL.FullCoupled.NegativeQMunchausenBench where

open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _∸_)
open import Data.Fin using (Fin; fromℕ<; toℕ)
open import Data.Nat.DivMod using (m%n<n)

open import Exotic.ERL.FullCoupled.GeneralFullCoupledLearnerMonolith as L
open import Exotic.ERL.FullCoupled.CanonicalGamePorts as P
open import Exotic.ERL.FullCoupled.AdditionalBenchmarkPorts as X
open import Exotic.ERL.FullCoupled.GeneralClosedLoopBenchV2 as B

negativeQMunchausen : L.Int8 → L.Int8
negativeQMunchausen q = L.int8Neg q

qMunchausenStep : ∀ {A : Nat} → L.LearnerKernel A → L.LearnerState A → L.Int8 → L.LearnerState A
qMunchausenStep K s reward =
  let a = L.generalPolicy K s
      shaped = L.int8Add reward (negativeQMunchausen (L.q s a))
  in L.learnerState
    (suc (L.clock s))
    (L.updateAt (L.q s) a shaped)
    (L.incAt (L.counts s) a)
    a
    (L.gruStep (L.gru s) shaped)
    (L.f4Step (L.optimizer s) shaped)
    (L.normStep (L.normState s) (L.q s a) shaped)

runQAux : ∀ {A : Nat} {S : Set} →
  B.BenchEnv A S →
  L.LearnerKernel A →
  Nat →
  L.LearnerState A →
  S →
  Nat →
  Nat →
  Nat →
  B.LoopResult
runQAux E K zero ls es total steps success =
  B.loopResult total (B.referenceReturn E ∸ total) success steps
runQAux E K (suc n) ls es total steps success with L.generalPolicy K ls
... | a with B.stepEnv E a es
...   | P.stepResult obs es' r P.yes =
  let total' = total + toℕ (P.code r)
  in B.loopResult total' (B.referenceReturn E ∸ total') 1 (suc steps)
...   | P.stepResult obs es' r P.no =
  runQAux E K n
    (qMunchausenStep K ls (L.int8OfNat (toℕ (P.code r))))
    es' (total + toℕ (P.code r)) (suc steps) success

runQ : ∀ {A : Nat} {S : Set} → B.BenchEnv A S → L.LearnerKernel A → Nat → B.LoopResult
runQ E K h = runQAux E K h (L.initialLearner (B.actionSpace E)) (B.initialState E) zero zero zero

record QMunchausenAblation : Set where
  constructor qMunchausenAblation
  field noQMunchausen negativeQMunchausen : B.LoopResult
open QMunchausenAblation public

compareQ : ∀ {A : Nat} {S : Set} → B.BenchEnv A S → Nat → QMunchausenAblation
compareQ E h =
  qMunchausenAblation
    (B.runLoop E (L.learnerKernel (B.actionSpace E) L.noMunchausen) h)
    (runQ E (L.learnerKernel (B.actionSpace E) L.noMunchausen) h)

uniformBanditEnv : B.BenchEnv 2 X.UniformBanditState
uniformBanditEnv = B.benchEnv
  L.actionSpace2
  X.uniformBanditInitial
  8
  X.uniformBanditStep

game2048Env : B.BenchEnv 4 X.Game2048State
game2048Env = B.benchEnv
  L.actionSpace4
  X.game2048Initial
  2048
  X.game2048Step

uniformBanditQ : QMunchausenAblation
uniformBanditQ = compareQ uniformBanditEnv 16

game2048Q : QMunchausenAblation
game2048Q = compareQ game2048Env 32

bernoulliBanditQ : QMunchausenAblation
bernoulliBanditQ = compareQ B.bernoulliBanditEnv 16

pongQ : QMunchausenAblation
pongQ = compareQ B.pongEnv 16

pobaxTMazeQ : QMunchausenAblation
pobaxTMazeQ = compareQ B.pobaxTMazeEnv 8
