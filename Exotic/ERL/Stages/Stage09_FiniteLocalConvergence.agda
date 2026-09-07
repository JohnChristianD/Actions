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

data ⊥ : Set where

⊥-elim : ∀ {A : Set} → ⊥ → A
⊥-elim ()

infixr 1 _⊎_
data _⊎_ (A B : Set) : Set where
  inj₁ : A → A ⊎ B
  inj₂ : B → A ⊎ B

zeroNotSuc : ∀ {n : Nat} → zero ≡ suc n → ⊥
zeroNotSuc ()

reachesWithin :
  (terminal : I.Stage08State → Set) →
  (step : I.Stage08State → I.Stage08State) →
  Nat → I.Stage08State → Set
reachesWithin terminal step zero s = terminal s
reachesWithin terminal step (suc n) s =
  terminal s ⊎ reachesWithin terminal step n (step s)

record CoupledRankCertificate : Set₁ where
  constructor rankCertificate
  field
    terminal : I.Stage08State → Set
    rank : I.Stage08State → Nat
    jointStep : I.Stage08State → I.Stage08State
    jointStepIsOuterStep : ∀ s → jointStep s ≡ I.outerStep s
    terminalOrDrop : ∀ s →
      terminal s ⊎ (rank s ≡ suc (rank (jointStep s)))

finiteLocalConvergenceByRanking :
  (c : CoupledRankCertificate) →
  ∀ s →
  reachesWithin
    (CoupledRankCertificate.terminal c)
    (CoupledRankCertificate.jointStep c)
    (CoupledRankCertificate.rank c s)
    s
finiteLocalConvergenceByRanking c s = go s refl
  where
  go : ∀ {n : Nat} (s : I.Stage08State) →
    CoupledRankCertificate.rank c s ≡ n →
    reachesWithin
      (CoupledRankCertificate.terminal c)
      (CoupledRankCertificate.jointStep c)
      n s
  go {zero} s h with CoupledRankCertificate.terminalOrDrop c s
  ... | inj₁ hs = hs
  ... | inj₂ hd =
    ⊥-elim (zeroNotSuc (trans (sym h) hd))
  go {suc n} s h with CoupledRankCertificate.terminalOrDrop c s
  ... | inj₁ hs = inj₁ hs
  ... | inj₂ hd = inj₂
    (go
      (CoupledRankCertificate.jointStep c s)
      (sucCancel (trans (sym hd) h)))
