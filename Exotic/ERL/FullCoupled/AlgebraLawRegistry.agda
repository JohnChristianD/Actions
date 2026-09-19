{-# OPTIONS --safe #-}

module Exotic.ERL.FullCoupled.AlgebraLawRegistry where

open import Agda.Builtin.String using (String)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.List.Base using (List; []; _∷_)
open import Data.Empty using (⊥)

------------------------------------------------------------------------
-- Machine-readable algebra-law registry.
--
-- A primitive law names an imported or canonical theorem.
-- A composition law names a theorem whose proof depends on two or more
-- previously registered laws.  Reflexive identities are never classified
-- as compositions.
------------------------------------------------------------------------

data AlgebraLawKind : Set where
  primitiveLaw : AlgebraLawKind
  compositionLaw : Nat → AlgebraLawKind

record AlgebraLaw : Set where
  constructor algebraLaw
  field
    lawName : String
    moduleName : String
    lhsSignature : String
    rhsSignature : String
    kind : AlgebraLawKind
    dependencyNames : List String

canonicalPolicyNormLaw :
  AlgebraLaw
canonicalPolicyNormLaw =
  algebraLaw
    "canonicalPolicy-norm-invariant"
    "Exotic.ERL.FullCoupled.CanonicalLearnerMonolith"
    "canonicalPolicy K (replaceNorm s n)"
    "canonicalPolicy K s"
    primitiveLaw
    []

canonicalCountNormLaw :
  AlgebraLaw
canonicalCountNormLaw =
  algebraLaw
    "canonicalCountStep-norm-invariant"
    "Exotic.ERL.FullCoupled.TheoremsMonolith"
    "canonicalCountStep K (replaceNorm s n)"
    "canonicalCountStep K s"
    primitiveLaw
    []

canonicalQLogNormLaw :
  AlgebraLaw
canonicalQLogNormLaw =
  algebraLaw
    "canonicalQLogStep-norm-invariant"
    "Exotic.ERL.FullCoupled.TheoremsMonolith"
    "canonicalQLogStep K (replaceNorm s n)"
    "canonicalQLogStep K s"
    primitiveLaw
    []

canonicalAttentionClockLaw :
  AlgebraLaw
canonicalAttentionClockLaw =
  algebraLaw
    "canonicalAttentionMix-clock-period4"
    "Exotic.ERL.FullCoupled.TheoremsMonolith"
    "canonicalAttentionMix K (replaceClock s (clock + 4))"
    "canonicalAttentionMix K s"
    primitiveLaw
    []

canonicalAttentionEndogenousLaw :
  AlgebraLaw
canonicalAttentionEndogenousLaw =
  algebraLaw
    "novel-clockPlus4-endogenousFeedback-invariant"
    "Exotic.ERL.FullCoupled.TheoremsMonolith"
    "canonicalEndogenousFeedback K (replaceClock s (clock + 4))"
    "canonicalEndogenousFeedback K s"
    primitiveLaw
    [ "canonicalAttentionMix-clock-period4" ]

canonicalWatkinsEndogenousLaw :
  AlgebraLaw
canonicalWatkinsEndogenousLaw =
  algebraLaw
    "canonicalWatkinsTarget-law"
    "Exotic.ERL.FullCoupled.CanonicalLearnerMonolith"
    "canonicalWatkinsTarget K s"
    "canonicalWatkinsExpanded K s"
    primitiveLaw
    []

recurrentAssociativityLaw :
  AlgebraLaw
recurrentAssociativityLaw =
  algebraLaw
    "endomorphismAssociative"
    "Exotic.ERL.FullCoupled.CanonicalLearnerMonolith"
    "compose (compose f g) h"
    "compose f (compose g h)"
    primitiveLaw
    []

recurrentPrefixLaw :
  AlgebraLaw
recurrentPrefixLaw =
  algebraLaw
    "recurrentPrefix-split"
    "Exotic.ERL.FullCoupled.CanonicalLearnerMonolith"
    "prefix (m + n)"
    "prefix n (prefix m)"
    primitiveLaw
    []

reservoirLeftInverseLaw :
  AlgebraLaw
reservoirLeftInverseLaw =
  algebraLaw
    "finiteReservoir-leftInverse"
    "Exotic.ERL.FullCoupled.TheoremsMonolith"
    "inverse (observe s)"
    "s"
    primitiveLaw
    []

finiteInt8Law :
  AlgebraLaw
finiteInt8Law =
  algebraLaw
    "int8-no-countably-unbounded-injective"
    "Exotic.ERL.FullCoupled.CanonicalLearnerMonolith"
    "injective Nat-to-Int8"
    "false"
    primitiveLaw
    []

policyReplacementCompositionLaw :
  AlgebraLaw
policyReplacementCompositionLaw =
  algebraLaw
    "canonicalPolicy-learnerReplacement-composition"
    "Exotic.ERL.FullCoupled.TheoremsMonolith"
    "policy (r1 :: r2 :: rs)"
    "policy rs"
    (compositionLaw 2)
    [ "canonicalPolicy-norm-invariant"
    ]

------------------------------------------------------------------------
-- Imported ring-law registry slots.
--
-- These identify actual stdlib ring laws by module/name.  Their proofs are
-- supplied by the imported Ring structure at instantiation time.  They are
-- primitive laws here, so e-graph composition can build derived candidates
-- from them without confusing the primitive identities with compositions.
------------------------------------------------------------------------

ringAddAssociativityLaw :
  AlgebraLaw
ringAddAssociativityLaw =
  algebraLaw
    "ring-+-assoc"
    "Algebra.Properties.Ring"
    "(x + y) + z"
    "x + (y + z)"
    primitiveLaw
    []

ringAddCommutativityLaw :
  AlgebraLaw
ringAddCommutativityLaw =
  algebraLaw
    "ring-+-comm"
    "Algebra.Properties.Ring"
    "x + y"
    "y + x"
    primitiveLaw
    []

ringMulAssociativityLaw :
  AlgebraLaw
ringMulAssociativityLaw =
  algebraLaw
    "ring-*-assoc"
    "Algebra.Properties.Ring"
    "(x * y) * z"
    "x * (y * z)"
    primitiveLaw
    []

ringDistributivityLaw :
  AlgebraLaw
ringDistributivityLaw =
  algebraLaw
    "ring-distrib"
    "Algebra.Properties.Ring"
    "x * (y + z)"
    "x * y + x * z"
    primitiveLaw
    []

ringNegMultiplyLaw :
  AlgebraLaw
ringNegMultiplyLaw =
  algebraLaw
    "ring--distribl-*"
    "Algebra.Properties.Ring"
    "- (x * y)"
    "- x * y"
    primitiveLaw
    []

algebraLawRegistry : List AlgebraLaw
algebraLawRegistry =
  canonicalPolicyNormLaw ∷
  canonicalCountNormLaw ∷
  canonicalQLogNormLaw ∷
  canonicalAttentionClockLaw ∷
  canonicalAttentionEndogenousLaw ∷
  canonicalWatkinsEndogenousLaw ∷
  recurrentAssociativityLaw ∷
  recurrentPrefixLaw ∷
  reservoirLeftInverseLaw ∷
  finiteInt8Law ∷
  policyReplacementCompositionLaw ∷
  ringAddAssociativityLaw ∷
  ringAddCommutativityLaw ∷
  ringMulAssociativityLaw ∷
  ringDistributivityLaw ∷
  ringNegMultiplyLaw ∷
  []

data ValidCompositionArity : Set where
  validCompositionArity : ValidCompositionArity

compositionArityIsValid : AlgebraLawKind → Set
compositionArityIsValid primitiveLaw = ValidCompositionArity
compositionArityIsValid (compositionLaw (suc (suc n))) =
  ValidCompositionArity
compositionArityIsValid (compositionLaw zero) = ⊥
compositionArityIsValid (compositionLaw (suc zero)) = ⊥

policyReplacementCompositionLaw-valid :
  compositionArityIsValid (AlgebraLaw.kind policyReplacementCompositionLaw)
policyReplacementCompositionLaw-valid = validCompositionArity
