------------------------------------------------------------------------
-- Vendored from iwilare/formal-methods (IMP.agda), MIT-licensed upstream.
-- Namespaced locally so theorem-specific imports cannot collide with the
-- existing FullCoupled proof surface.
------------------------------------------------------------------------

module FullCoupled.FormalMethods.IMP where
-- BEGIN MIRTH-SYNC COMMON IMPORTS
-- Mirth-generated contract: this exact block is shared by both monoliths.
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


open import Data.Nat     using (ℕ; _+_) renaming (_≤?_ to _≤?ₙ_)
open import Data.Bool    using (Bool; not; _∧_)
open import Data.String  using (String; _≟_)
open import Relation.Nullary           using (yes; no)
open import Relation.Nullary.Decidable using (⌊_⌋)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym)

vname = String
val = ℕ
bool = Bool
state = vname → val

data aexp : Set where
  N : ℕ → aexp
  V : vname → aexp
  Plus : aexp → aexp → aexp

_[_/_] : aexp → aexp → vname → aexp
N c [ a′ / X ] = N c
V Y [ a′ / X ] with Y ≟ X
... | yes _ = a′
... | no  _ = V Y
Plus a b [ a′ / X ] = Plus (a [ a′ / X ]) (b [ a′ / X ])

_[_::=_] : state → vname → val → state
(s [ X ::= n ]) Y with Y ≟ X
... | yes _ = n
... | no  _ = s Y

aval : aexp → state → val
aval (N c) s = c
aval (V v) s = s v
aval (Plus a b) s = aval a s + aval b s

substitution : ∀ a {X a′ s}
  → aval (a [ a′ / X ]) s ≡ aval a (s [ X ::= aval a′ s ])
substitution (N x) = refl
substitution (V Y) {X} with Y ≟ X
... | yes _ = refl
... | no  _ = refl
substitution (Plus a b) {X}{a′}{s}
  rewrite substitution a {X}{a′}{s}
        | substitution b {X}{a′}{s} = refl

substitution-equiv : ∀{a a₁ a₂ X s}
  → aval a₁ s             ≡ aval a₂ s
  → aval (a [ a₁ / X ]) s ≡ aval (a [ a₂ / X ]) s
substitution-equiv {a}{a₁}{a₂}{X}{s} hyp
  rewrite substitution a {X}{a₁}{s}
        | hyp
        | sym (substitution a {X}{a₂}{s}) = refl

data bexp : Set where
  Bc   : Bool → bexp
  Not  : bexp → bexp
  And  : bexp → bexp → bexp
  Less : aexp → aexp → bexp

_≤?_ : ℕ → ℕ → Bool
a ≤? b = ⌊ a ≤?ₙ b ⌋

bval : bexp → state → bool
bval (Bc x) s = x
bval (Not b) s = not (bval b s)
bval (And a b) s = bval a s ∧ bval b s
bval (Less a b) s = aval a s ≤? aval b s

data com : Set where
  SKIP  : com
  _::=_ : String → aexp → com
  _::_  : com → com → com
  IF_THEN_ELSE_ : bexp → com → com → com
  WHILE_DO_     : bexp → com → com
