{-# OPTIONS --safe #-}
module Exotic.ERL.FullCoupled.EfficientCHAD_v162_test where

open import Agda.Builtin.Equality using (_≡_)
open import Exotic.ERL.FullCoupled.EfficientCHAD_v162

metaValueTest : ∀ {A : FiniteOrderedRational}
  (cfg : SoftsignQIDBDMetaDecay A) (p : ParameterCoordinate A) g →
  value (softsignQIDBDMetaStep cfg p g) ≡ value (softsignQIDBDStep p g)
metaValueTest = softsignQIDBDMetaDecayValueLaw

criticGlobalOptimizerTest : ∀ {A : FiniteOrderedRational}
  (cfg : SoftsignQIDBDMetaDecay A) (s : FullFiniteOrderedRationalLearner A) g →
  FullFiniteOrderedRationalLearner.critic (canonicalLearnerUpdate cfg s g) ≡
    mapOptimizer cfg (FullFiniteOrderedRationalLearner.critic s) g
criticGlobalOptimizerTest = canonicalCriticLaw

actorGlobalOptimizerTest : ∀ {A : FiniteOrderedRational}
  (cfg : SoftsignQIDBDMetaDecay A) (s : FullFiniteOrderedRationalLearner A) g →
  FullFiniteOrderedRationalLearner.actor (canonicalLearnerUpdate cfg s g) ≡
    mapOptimizer cfg (FullFiniteOrderedRationalLearner.actor s) g
actorGlobalOptimizerTest = canonicalActorLaw

transformerGlobalOptimizerTest : ∀ {A : FiniteOrderedRational}
  (cfg : SoftsignQIDBDMetaDecay A) (s : FullFiniteOrderedRationalLearner A) g →
  FullFiniteOrderedRationalLearner.transformer (canonicalLearnerUpdate cfg s g) ≡
    mapOptimizer cfg (FullFiniteOrderedRationalLearner.transformer s) g
transformerGlobalOptimizerTest = canonicalTransformerLaw

representationGlobalOptimizerTest : ∀ {A : FiniteOrderedRational}
  (cfg : SoftsignQIDBDMetaDecay A) (s : FullFiniteOrderedRationalLearner A) g →
  FullFiniteOrderedRationalLearner.representation (canonicalLearnerUpdate cfg s g) ≡
    mapOptimizer cfg (FullFiniteOrderedRationalLearner.representation s) g
representationGlobalOptimizerTest = canonicalRepresentationLaw

ffnLayeringTest : ∀ {A : FiniteOrderedRational}
  (f : CanonicalSoftsignSignReLUFFN A) x →
  runCanonicalSoftsignSignReLUFFN f x ≡ runCanonicalSoftsignSignReLUFFN f x
ffnLayeringTest = canonicalFFNLayeringLaw

normPairTest : ∀ {A : FiniteOrderedRational}
  (n : NormPair A) → canonicalNormPairSurface n ≡ n
normPairTest = canonicalNormPairLaw
