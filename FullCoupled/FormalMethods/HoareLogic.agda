------------------------------------------------------------------------
-- Vendored from iwilare/formal-methods (HoareLogic.agda), MIT-licensed upstream.
-- Namespaced locally so theorem-specific imports cannot collide with the
-- existing FullCoupled proof surface.
------------------------------------------------------------------------

module FullCoupled.FormalMethods.HoareLogic where

-- BEGIN MIRTH-SYNC COMMON IMPORTS
-- Mirth-generated contract: this exact block is shared by every tracked .agda source.
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; cong; cong₂; subst; trans)
open import Agda.Builtin.Nat using (Nat; zero; suc)

-- Solver-associated Base modules.
open import Data.Bool.Base hiding (_≤_; _<_)
open import Data.Nat.Base hiding (_≤_; _<_; _>_; _≥_)
open import Data.Integer.Base hiding (_≤_; _<_; _>_; _≥_; suc; neg; sign; _+_; _*_)
open import Data.List.Base using (List; []; _∷_; _++_; map; length)
open import Data.Product.Base
open import Data.Sum.Base
open import Data.Maybe.Base

-- Solver front ends.
import Data.Bool.Solver as BoolSolver
open import Data.Nat.Solver using (module +-*-Solver)
import Data.Integer.Solver as IntegerSolver
open import Data.List.Relation.Binary.Sublist.Heterogeneous as HeterogeneousSublistBase
import Data.List.Relation.Binary.Sublist.Heterogeneous.Solver as HeterogeneousSublistSolver
import Data.List.Relation.Binary.Sublist.DecSetoid.Solver as DecSetoidSublistSolver
import Data.List.Relation.Binary.Sublist.DecPropositional.Solver as DecPropositionalSublistSolver
import Function.Related.TypeIsomorphisms.Solver as TypeIsomorphismsSolver
open import Data.Nat.Tactic.RingSolver as NatRingSolver using (solve-∀)
open import Data.Integer.Tactic.RingSolver as IntegerRingSolver using (solve-∀)
open import Tactic.RingSolver as RingSolver using (solve-∀)
open import Tactic.RingSolver.Core.AlmostCommutativeRing as RingCore
open import Tactic.RingSolver.Core.Expression as RingExpression
open import Tactic.RingSolver.Core.NatSet as RingNatSet
open import Tactic.RingSolver.Core.Polynomial.Base as RingPolynomialBase
open import Tactic.MonoidSolver as MonoidSolver using (solve)

-- Existing shared semantics and container imports.
open import Data.Nat using (NonZero; _∸_; _<_; _≤_; _<ᵇ_; _/_; z≤n; s≤s)
open import Data.Nat.Properties using (+-identityʳ; +-suc; ≤-antisym; ≤-decTotalOrder)
open import Data.Integer using (ℤ; +_; -_; -[1+_]; _≤?_) renaming (_+_ to _+ℤ_; _*_ to _*ℤ_)
import Data.Integer.Properties as IntegerProperties
open import Level using (0ℓ)
open import Data.List.Sort as Sort
open import Relation.Binary.Bundles using (DecTotalOrder)
open import Relation.Binary.Construct.On as On
import Relation.Binary.Construct.Flip.EqAndOrd as Flip
open import Data.Product.Relation.Binary.Lex.NonStrict as Lex
open import Data.Nat.DivMod using (m%n<n; m<n⇒m%n≡m)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Empty using (⊥)
open import Data.Unit using (⊤; tt)
open import Relation.Nullary using (¬_)
open import Effect.Monad using (RawMonad)
open import Effect.Monad.State using (State; RawMonadState)
open import Data.Nat.Induction using (Acc; acc; <-wellFounded)
open import Data.Nat.Properties using (≤-refl; ≤-trans; n<1+n)
open import Data.Integer using () renaming (_≤_ to _≤ℤ_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)
open import Algebra.Bundles using (Monoid)
open import Data.List.Properties using (++-monoid)
import Data.List.Effectful as ListEffectful
import Data.List.Base as ListBase
-- END MIRTH-SYNC COMMON IMPORTS


open import Data.Nat using ()
open import Data.Bool using (true; false)
open import Data.Product using (_×_; _,_)
open import Data.String using (String; _≟_)
open import Data.Empty using ()
open import Level using (suc; _⊔_)
open import Relation.Nullary           using (yes; no)
open import Relation.Nullary.Decidable using (⌊_⌋)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym)

open import FullCoupled.FormalMethods.IMP
open import FullCoupled.FormalMethods.OperationalSemantics

assn : ∀{l} → Set (suc l)
assn {a} = state → Set a

data ⊢[_]_[_] {l} : assn {l} → com → assn {l} → Set (suc l) where
  Skip : ∀{P}
     → ⊢[ P ] SKIP [ P ]
  Loc : ∀{Q a x}
     → ⊢[ (λ s → Q (s [ x ::= aval a s ])) ] (x ::= a) [ Q ]
  Comp : ∀{P Q R c₁ c₂}
     → ⊢[ P ] c₁ [ Q ]
     → ⊢[ Q ] c₂ [ R ]
     → ⊢[ P ] c₁ :: c₂ [ R ]
  If : ∀{P b c₁ Q c₂}
     → ⊢[ (λ s → P s × bval b s ≡ true)  ] c₁ [ Q ]
     → ⊢[ (λ s → P s × bval b s ≡ false) ] c₂ [ Q ]
     → ⊢[ P ] (IF b THEN c₁ ELSE c₂) [ Q ]
  While : ∀{P b c}
     → ⊢[ (λ s → P s × bval b s ≡ true) ] c [ P ]
     → ⊢[ P ] (WHILE b DO c) [ (λ s → P s × bval b s ≡ false) ]
  Conseq : ∀{P Q P′ Q′ : assn} {c}
     → (∀ s → P′ s → P s)
     → ⊢[ P  ] c [ Q  ]
     → (∀ s → Q s → Q′ s)
     → ⊢[ P′ ] c [ Q′ ]

⊨[_]_[_] : assn → com → assn → Set
⊨[ P ] c [ Q ] = ∀{s t} → P s → ⦅ c , s ⦆⇒ t → Q t

soundness : ∀{P Q : assn} {c}
          → ⊢[ P ] c [ Q ]
          → ⊨[ P ] c [ Q ]
soundness Skip p Skip = p
soundness Loc p Loc = p
soundness (Comp r r₁) p (Comp z z₁) = soundness r₁ (soundness r p z) z₁
soundness (If r r₁) p (IfTrue x s) = soundness r (p , x) s
soundness (If r r₁) p (IfFalse x s) = soundness r₁ (p , x) s
soundness (While r) p (WhileFalse x₁) = p , x₁
soundness (While r) p (WhileTrue x₁ s s₁) = soundness (While r) (soundness r (p , x₁) s) s₁
soundness (Conseq x₁ r x₂) {s₁} {t} p s = x₂ t (soundness r (x₁ s₁ p) s)

wp : ∀{l} → com → assn {l} → assn {l}
wp c Q s = ∀ t → ⦅ c , s ⦆⇒ t → Q t

validity-wp : ∀{P Q : assn} {c}
      → ⊨[ P ] c [ Q ]
      → (∀ s → P s → wp c Q s)
validity-wp = λ z s z₁ t → z z₁

validity-wp-converse : ∀{P Q : assn} {c}
      → (∀ s → P s → wp c Q s)
      → ⊨[ P ] c [ Q ]
validity-wp-converse = (λ z {s} {t} z₁ → z s z₁ t)

wp-hoare : ∀ c {l} {Q : assn {l}}
  → ⊢[ wp c Q ] c [ Q ]
wp-hoare SKIP = Conseq (λ s z → z s Skip) Skip (λ s z → z)
wp-hoare (x ::= a) = Conseq (λ s wpe → wpe (s [ x ::= aval a s ]) Loc) Loc (λ s r → r)
wp-hoare (c :: c₁) = Comp (Conseq (λ s z x x₁ x₂ x₃ → z x₂ (Comp x₁ x₃)) (wp-hoare c) (λ s z → z)) (wp-hoare c₁)
wp-hoare (IF x THEN c ELSE c₁) = If (Conseq (λ s z x x₁ → proj₁ z x (IfTrue (proj₂ z) x₁)) (wp-hoare c) (λ s z → z))
                                    (Conseq (λ s z x x₁ → proj₁ z x (IfFalse (proj₂ z) x₁)) (wp-hoare c₁) (λ s z → z))
wp-hoare (WHILE b DO c) =
  Conseq (λ s x → x)
         (While (Conseq (λ s z x x₁ x₂ x₃ → proj₁ z x₂ (WhileTrue (proj₂ z) x₁ x₃))
                        (wp-hoare c)
                        (λ s z → z)))
         (λ s z → proj₁ z s (WhileFalse (proj₂ z)))

completeness : ∀ c {P Q : assn}
  → ⊨[ P ] c [ Q ]
  → ⊢[ P ] c [ Q ]
completeness c cc = Conseq (validity-wp cc) (wp-hoare c) (λ r x → x)
