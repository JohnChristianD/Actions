module FullCoupled.ProofCompress where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Reflection
open import Agda.Builtin.Unit using (⊤)
open import Haskell.Prelude

import FullCoupled.CanonicalLearnerMonolith as C

𝓋𝓇𝒶 : {A : Set} → A → Arg A
𝓋𝓇𝒶 = arg (arg-info visible relevant)

≡-type-info : Term → TC (Arg Term × Arg Term × Term × Term)
≡-type-info
  (def (quote _≡_) (ℓ ∷ A ∷ arg _ l ∷ arg _ r ∷ [])) =
    returnTC (ℓ , A , l , r)
≡-type-info _ =
  typeError [ strErr "Term is not an equality type." ]

macro
  apply₃ : Term → Term → TC ⊤
  apply₃ p goal =
    try
      unify goal (def (quote sym) (𝓋𝓇𝒶 p ∷ []))
    or-else
      try
        unify goal p
      or-else
        unify goal (con (quote refl) [])

reflectionSelf :
  ∀ {A : Set} (x : A) →
  x ≡ x
reflectionSelf x = apply₃ refl

canonicalPolicySelf :
  ∀ {A : Set} (K : C.FullLearnerKernel A) (s : C.FullLearnerState A) →
  C.canonicalPolicy K s ≡ C.canonicalPolicy K s
canonicalPolicySelf K s = apply₃ refl

canonicalFullStep-watkins-short :
  ∀ {A : Set} (K : C.FullLearnerKernel A) (s : C.FullLearnerState A) →
  C.watkins (C.canonicalFullStep K s) ≡ C.canonicalWatkinsStep K s
canonicalFullStep-watkins-short K s = apply₃ refl

canonicalFullStep-gru-short :
  ∀ {A : Set} (K : C.FullLearnerKernel A) (s : C.FullLearnerState A) →
  C.gru (C.canonicalFullStep K s) ≡ C.canonicalGRUStep K s
canonicalFullStep-gru-short K s = apply₃ refl

canonicalFullStep-optimizer-short :
  ∀ {A : Set} (K : C.FullLearnerKernel A) (s : C.FullLearnerState A) →
  C.optimizer (C.canonicalFullStep K s) ≡ C.canonicalOptimizerStep K s
canonicalFullStep-optimizer-short K s = apply₃ refl

canonicalFullStep-counts-short :
  ∀ {A : Set} (K : C.FullLearnerKernel A) (s : C.FullLearnerState A) →
  C.lcbCounts (C.canonicalFullStep K s) ≡ C.canonicalCountStep K s
canonicalFullStep-counts-short K s = apply₃ refl

canonicalFullStep-qLog-short :
  ∀ {A : Set} (K : C.FullLearnerKernel A) (s : C.FullLearnerState A) →
  C.qLogValue (C.canonicalFullStep K s) ≡ C.canonicalQLogStep K s
canonicalFullStep-qLog-short K s = apply₃ refl

canonicalFullStep-qLogControl-short :
  ∀ {A : Set} (K : C.FullLearnerKernel A) (s : C.FullLearnerState A) →
  C.qLogControl (C.canonicalFullStep K s) ≡ C.canonicalQLogControlStep K s
canonicalFullStep-qLogControl-short K s = apply₃ refl


$-head : Term → Term
$-head (var v args) = var v []
$-head (con c args) = con c []
$-head (def f args) = def f []
$-head (pat-lam cs args) = pat-lam cs []
$-head t = t

macro
  apply₄ : Term → Term → TC ⊤
  apply₄ p goal =
    try
      do
        τ ← inferType goal
        _ , _ , l , r ← ≡-type-info τ
        unify
          goal
          (def (quote cong)
            (𝓋𝓇𝒶 ($-head l) ∷ 𝓋𝓇𝒶 p ∷ []))
    or-else
      unify goal p

cong-short :
  ∀ {A B : Set}
  (f : A → B)
  {x y : A} →
  x ≡ y →
  f x ≡ f y
cong-short f p = apply₄ p
