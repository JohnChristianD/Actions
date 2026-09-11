{-# OPTIONS --safe #-}
module Exotic.ERL.FullCoupled.EfficientCHAD_v164_test where

open import Agda.Builtin.Equality using (_≡_)
open import Exotic.ERL.FullCoupled.EfficientCHAD_v164

base2Test : ∀ {A : FiniteOrderedRational} (xs : FeatureVec A) →
  idbdLog2 A (idbdPow2 A xs) ≡ xs
base2Test = idbdBase2RoundTrip

momentumReconstructionTest : ∀ {A : FiniteOrderedRational}
  (cfg : F4IntSigmaDeltaConfig A) (s : F4IntSigmaDeltaState A) g →
  fullEffectiveState (f4IntSigmaDeltaStep cfg s g) ≡ fullPrequantizedState cfg s g
momentumReconstructionTest = f4IntSigmaDeltaMomentumReconstruction

integratorTest : ∀ {A : FiniteOrderedRational}
  (cfg : F4IntSigmaDeltaConfig A) (s : F4IntSigmaDeltaState A) g →
  intEmbed A (logStep (f4IntSigmaDeltaStep cfg s g))
    + rL (f4IntSigmaDeltaStep cfg s g)
    ≡ (intEmbed A (logStep s) + rL s) + fullPrequantizedState cfg s g
integratorTest = f4IntSigmaDeltaIntegratorLaw

criticGlobalOptimizerTest : ∀ {A : FiniteOrderedRational}
  (cfg : F4IntSigmaDeltaConfig A) (s : FullFiniteOrderedRationalLearner A) g →
  FullFiniteOrderedRationalLearner.critic (canonicalLearnerUpdate cfg s g) ≡
    mapOptimizer cfg (FullFiniteOrderedRationalLearner.critic s) g
criticGlobalOptimizerTest = canonicalCriticLaw

actorGlobalOptimizerTest : ∀ {A : FiniteOrderedRational}
  (cfg : F4IntSigmaDeltaConfig A) (s : FullFiniteOrderedRationalLearner A) g →
  FullFiniteOrderedRationalLearner.actor (canonicalLearnerUpdate cfg s g) ≡
    mapOptimizer cfg (FullFiniteOrderedRationalLearner.actor s) g
actorGlobalOptimizerTest = canonicalActorLaw

transformerGlobalOptimizerTest : ∀ {A : FiniteOrderedRational}
  (cfg : F4IntSigmaDeltaConfig A) (s : FullFiniteOrderedRationalLearner A) g →
  FullFiniteOrderedRationalLearner.transformer (canonicalLearnerUpdate cfg s g) ≡
    mapOptimizer cfg (FullFiniteOrderedRationalLearner.transformer s) g
transformerGlobalOptimizerTest = canonicalTransformerLaw

representationGlobalOptimizerTest : ∀ {A : FiniteOrderedRational}
  (cfg : F4IntSigmaDeltaConfig A) (s : FullFiniteOrderedRationalLearner A) g →
  FullFiniteOrderedRationalLearner.representation (canonicalLearnerUpdate cfg s g) ≡
    mapOptimizer cfg (FullFiniteOrderedRationalLearner.representation s) g
representationGlobalOptimizerTest = canonicalRepresentationLaw

ffnLayeringTest : ∀ {A : FiniteOrderedRational}
  (f : CanonicalSoftsignSignReLUFFN A) x →
  runCanonicalSoftsignSignReLUFFN f x ≡ runCanonicalSoftsignSignReLUFFN f x
ffnLayeringTest = canonicalFFNLayeringLaw
