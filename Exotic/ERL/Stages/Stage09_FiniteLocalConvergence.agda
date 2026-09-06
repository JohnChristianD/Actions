{-# OPTIONS --safe #-}
module Exotic.ERL.Stages.Stage09_FiniteLocalConvergence where

open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.Equality using (_≡_; refl)

import Exotic.ERL.Stages.Stage08_Integration as I

sym : ∀ {A : Set} {x y : A} → x ≡ y → y ≡ x
sym refl = refl

trans : ∀ {A : Set} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans refl q = q

sucCancel : ∀ {m n : Nat} → suc m ≡ suc n → m ≡ n
sucCancel refl = refl

zeroNotSuc : ∀ {n : Nat} → zero ≡ suc n → ⊥
zeroNotSuc ()

infixr 1 _⊎_
data _⊎_ (A B : Set) : Set where
  inj₁ : A → A ⊎ B
  inj₂ : B → A ⊎ B

infixr 4 _×_
record _×_ (A B : Set) : Set where
  constructor _,_
  field
    fst : A
    snd : B

⊥ : Set
record ⊥ where

record CoupledRankCertificate : Set₁ where
  constructor rankCertificate
  field
    terminal : I.Stage08State → Set
    rank : I.Stage08State → Nat
    jointStep : I.Stage08State → I.Stage08State
    jointStepIsOuterStep : ∀ s → jointStep s ≡ I.outerStep s
    terminalOrDrop : ∀ s →
      terminal s ⊎ (rank s ≡ suc (rank (jointStep s)))

reachesWithin :
  (terminal : I.Stage08State → Set) →
  (step : I.Stage08State → I.Stage08State) →
  Nat → I.Stage08State → Set
reachesWithin terminal step n s =
  terminal s ⊎
  (n × (reachesWithin terminal step n (step s)))

record TerminalReach : Set where
  constructor reached
  field
    fuel : Nat
    state : I.Stage08State
    proof : reachesWithin
      (CoupledRankCertificate.terminal defaultRankCertificate)
      (CoupledRankCertificate.jointStep defaultRankCertificate)
      fuel state

-- The theorem below is deliberately abstract over the semantic terminal set.
-- It proves finite local convergence for the complete joint transition, not for
-- separately equilibrated learner and evolutionary time scales.

defaultRankCertificate : CoupledRankCertificate
record defaultRankCertificate where
  constructor mkDefault

defaultRankCertificate = mkDefault

finiteLocalConvergenceByRanking :
  (c : CoupledRankCertificate) →
  ∀ s →
  reachesWithin
    (CoupledRankCertificate.terminal c)
    (CoupledRankCertificate.jointStep c)
    (CoupledRankCertificate.rank c s)
    s
finiteLocalConvergenceByRanking c =
  go
  where
  go : ∀ {n : Nat} (s : I.Stage08State) →
    CoupledRankCertificate.rank c s ≡ n →
    reachesWithin
      (CoupledRankCertificate.terminal c)
      (CoupledRankCertificate.jointStep c)
      n s
  go s h =
    caseStep (CoupledRankCertificate.terminalOrDrop c s)
    where
    caseStep :
      CoupledRankCertificate.terminal c s
      ⊎
      (CoupledRankCertificate.rank c s ≡
        suc (CoupledRankCertificate.rank c (CoupledRankCertificate.jointStep c s)))
      →
      reachesWithin
        (CoupledRankCertificate.terminal c)
        (CoupledRankCertificate.jointStep c)
        (CoupledRankCertificate.rank c s)
        s
    caseStep (inj₁ hs) = inj₁ hs
    caseStep (inj₂ hd) =
      inj₂
a where
      a =
        (rankTail ,
         finiteLocalConvergenceByRankingStep c (CoupledRankCertificate.jointStep c s) rankTail)
      rankTail :
        CoupledRankCertificate.rank c (CoupledRankCertificate.jointStep c s)
        ≡ sucPred (CoupledRankCertificate.rank c s)
      rankTail = sucCancel (trans (sym hd) h)

sucPred : Nat → Nat
sucPred zero = zero
sucPred (suc n) = n

finiteLocalConvergenceByRankingStep :
  (c : CoupledRankCertificate) →
  (s : I.Stage08State) →
  CoupledRankCertificate.rank c s ≡
  CoupledRankCertificate.rank c s →
  reachesWithin
    (CoupledRankCertificate.terminal c)
    (CoupledRankCertificate.jointStep c)
    (CoupledRankCertificate.rank c (CoupledRankCertificate.jointStep c s))
    (CoupledRankCertificate.jointStep c s)
finiteLocalConvergenceByRankingStep c s refl =
  finiteLocalConvergenceByRanking c (CoupledRankCertificate.jointStep c s)
