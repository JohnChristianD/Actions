{-# OPTIONS --safe #-}
module Exotic.ERL.FullCoupled.FiniteInverseVector where

open import Relation.Binary.PropositionalEquality using (_≡_)
open import Data.Fin using (Fin)
open import Data.Nat using (Nat)

open import Data.Vec.Functional as VF
  using (Vector; map)
open import Data.Vec.Functional.Relation.Binary.Pointwise as VFPW
  using (Pointwise)

open import Exotic.ERL.FullCoupled.GeneralFullCoupledLearnerMonolith as L

------------------------------------------------------------------------
-- Unit witnesses, not lookup tables.
--
-- Z/256Z is not a field: only the odd residues are units.  A Unit8 value
-- therefore packages an Int8 element together with an explicit inverse and
-- both multiplication identities.  This keeps inversion executable,
-- compositional, and proof-carrying without manufacturing inverses for
-- non-units such as 2 or 4.
------------------------------------------------------------------------

record Unit8 : Set where
  constructor unit8
  field
    value : L.Int8
    inverse : L.Int8
    leftInverse : L.int8Mul inverse value ≡ L.one8
    rightInverse : L.int8Mul value inverse ≡ L.one8
open Unit8 public

UnitVector : Nat → Set
UnitVector n = Vector Unit8 n

unitValues : ∀ {n} → UnitVector n → Vector L.Int8 n
unitValues = map value

unitInverses : ∀ {n} → UnitVector n → Vector L.Int8 n
unitInverses = map inverse

unitValuePointwise :
  ∀ {n} (u : UnitVector n) →
  Pointwise _≡_ (unitValues u) (map value u)
unitValuePointwise u = λ i → refl

unitInverseLaw :
  ∀ {n} (u : UnitVector n) (i : Fin n) →
  L.int8Mul (unitInverses u i) (unitValues u i) ≡ L.one8
unitInverseLaw u i = leftInverse (u i)

unitInverseLaw-right :
  ∀ {n} (u : UnitVector n) (i : Fin n) →
  L.int8Mul (unitValues u i) (unitInverses u i) ≡ L.one8
unitInverseLaw-right u i = rightInverse (u i)

unitInversePointwise :
  ∀ {n} (u : UnitVector n) →
  Pointwise
    (λ x y → L.int8Mul y x ≡ L.one8)
    (unitValues u)
    (unitInverses u)
unitInversePointwise u i = leftInverse (u i)

unitInversePointwise-right :
  ∀ {n} (u : UnitVector n) →
  Pointwise
    (λ x y → L.int8Mul x y ≡ L.one8)
    (unitValues u)
    (unitInverses u)
unitInversePointwise-right u i = rightInverse (u i)

------------------------------------------------------------------------
-- Future vector algebra can now state inversion coordinatewise without
-- lookup-table semantics.  The only obligation is that the coordinates
-- belong to the unit-certified subcarrier.
------------------------------------------------------------------------
