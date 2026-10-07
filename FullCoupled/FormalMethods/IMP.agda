-- BEGIN MIRTH-SYNC GLOBAL OPTIONS
{-# OPTIONS
  --lossy-unification
  --backtracking-instance-search
  --experimental-lazy-instances
  --confluence-check
  --syntactic-equality
  --polarity
  --auto-inline
  --guarded
  --exact-split
  --no-infer-absurd-clauses
  --keep-covering-clauses
  --no-projection-like
  --erasure
#-}
-- END MIRTH-SYNC GLOBAL OPTIONS


------------------------------------------------------------------------
-- Vendored from iwilare/formal-methods (IMP.agda), MIT-licensed upstream.
-- Namespaced locally so theorem-specific imports cannot collide with the
-- existing FullCoupled proof surface.
------------------------------------------------------------------------

module FullCoupled.FormalMethods.IMP where

-- BEGIN MIRTH-SYNC COMMON IMPORTS
-- Merged external import surface; internal FullCoupled imports remain module-local.
open import Haskell.Law.Num.Def using (IsLawfulNum)
open import Haskell.Law.Num.Int using (iLawfulNumInt)
open import Addition
open import Agda.Builtin.Reflection as Builtin
open import Agda.Builtin.Sigma hiding (_,_)
open import Agda.Primitive as Level
open import Cantor
open import Rationals.Addition
open import Rationals.Multiplication
open import Rationals.Negation
open import Rationals.Order
open import Rationals.Type
open import Equality
open import Haskell.Prelude hiding (String; ⊥)
open import Haskell.Prelude.Nat.Properties using (add-assoc; add-suc-r; ≤-antisym; ≤-trans; n<1+n)
open import InfinitePigeon.Addition
open import InfinitePigeon.Cantor
open import InfinitePigeon.Equality
open import InfinitePigeon.Finite
open import InfinitePigeon.InfinitePigeon
open import InfinitePigeon.JK-LogicalFacts
open import InfinitePigeon.JK-Monads
open import InfinitePigeon.Logic
open import InfinitePigeon.LogicalFacts
open import InfinitePigeon.Naturals
open import InfinitePigeon.Order
open import InfinitePigeon.Two
open import Iterative.Multisets 𝓤
open import Iterative.Multisets-Addendum ua 𝓤
open import Iterative.Sets ua 𝓤
open import JK-LogicalFacts
open import JK-Monads
open import K-AC-N
open import Logic
open import LogicalFacts
open import MLTT.Athenian
open import MLTT.Spartan hiding (J)
open import MonadOnTypes.Definition
open import MonadOnTypes.J
open import MonadOnTypes.JK R
open import MonadOnTypes.K
open import Naturals
open import Naturals.Exponentiation
open import Naturals.Properties
open import Notation.CanonicalMap
open import Notation.Order
open import Order
open import Haskell.Prelude
open import Prelude.Char as Char
open import Prelude.Nat.Properties using (add-assoc; add-suc-r; ≤-antisym; ≤-trans; n<1+n)
open import Two
open import UF.Base
open import UF.ClassicalLogic
open import UF.FunExt
open import UF.Powerset
open import UF.PropTrunc
open import UF.Size
open import UF.Subsingletons
open import UF.Subsingletons-FunExt
open import UF.UA-FunExt
open import W.Type
-- END MIRTH-SYNC COMMON IMPORTS

-- BEGIN MIRTH-SYNC CANONICAL COMMAND
-- "$AGDA_COMMAND" -i .
-- END MIRTH-SYNC CANONICAL COMMAND


vname = String
val = Nat
bool = Bool
state = vname → val

data aexp : Set where
  N : Nat → aexp
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

_≤?_ : Nat → Nat → Bool
a ≤? b = a ≤?ₙ b

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
