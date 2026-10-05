-- BEGIN MIRTH-SYNC GLOBAL OPTIONS
{-# OPTIONS --lossy-unification --backtracking-instance-search --experimental-lazy-instances --confluence-check --syntactic-equality --polarity --auto-inline --guarded --without-K --exact-split --no-infer-absurd-clauses --level-universe --keep-covering-clauses --no-projection-like --erasure #-}
-- END MIRTH-SYNC GLOBAL OPTIONS


{-# OPTIONS --safe #-}

------------------------------------------------------------------------
-- Vendored from iwilare/formal-methods (IMP.agda), MIT-licensed upstream.
-- Namespaced locally so theorem-specific imports cannot collide with the
-- existing FullCoupled proof surface.
------------------------------------------------------------------------

module FullCoupled.FormalMethods.IMP where

-- BEGIN MIRTH-SYNC COMMON IMPORTS
-- Mirth-generated contract: this exact block is shared by both monoliths.
open import Prelude
open import Prelude.Nat.Properties using (add-assoc; add-suc-r; ≤-antisym; ≤-trans; n<1+n)
import Prelude.Int.Properties as IntegerProperties
-- END MIRTH-SYNC COMMON IMPORTS


open import Prelude.Nat using (Nat; _+_; _≤?_) renaming (_≤?_ to _≤?ₙ_)
open import Prelude.Bool using (Bool; not; _∧_; true; false)
open import Prelude.String using (String)
open import Prelude.Decidable using (yes; no)
open import Prelude.Decidable using (Dec)
open import Prelude.Equality using (_≡_; refl; sym)

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
