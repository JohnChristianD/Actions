{-# OPTIONS --safe #-}

------------------------------------------------------------------------
-- Canonical theorem semantics and emergence layer.
--
-- This module is the single theorem consumer of the canonical learner.
-- Its propositions are derived from the actual learner definitions and
-- from explicit hypotheses supplied at each abstraction boundary.
--
-- The proof topology is intentionally directional:
--   learner definitions
--     -> exact scan / composition laws
--     -> observation, quotient, and factor structure
--     -> F4 stability and exact growth boundary
--     -> coupled factor-stability closure
--     -> explicit economic interpretation gates.
--
-- A discovered graph edge is not itself a proof. A theorem is authoritative
-- only when its proposition is present here and its proof is accepted by
-- safe Agda. Likewise, a semantic contract is not an existence theorem:
-- the generalized Walrasian and production-side interfaces record the
-- conditions of an equilibrium, while existence, convergence, market
-- clearing, or supporting-price conclusions require their own assumptions.
--
-- The comments in this file therefore describe semantic intention and
-- emergence from the current definitions, not historical theorem partitions,
-- search candidates, or superseded contract surfaces.
------------------------------------------------------------------------

module Exotic.ERL.FullCoupled.TheoremsMonolith where

open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; cong; cong₂; subst; trans)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)
open import Data.Nat using (NonZero; _∸_; _<_; _≤_; _<ᵇ_; _/_; z≤n; s≤s)
open import Data.Nat.Properties using (+-identityʳ; +-suc; ≤-antisym; ≤-refl; ≤-trans; ≤-decTotalOrder; n<1+n)
open import Data.Integer using (ℤ; +_; -_; -[1+_]; _≤?_; _≤_) renaming (_+_ to _+ℤ_; _*_ to _*ℤ_; _≤_ to _≤ℤ_)
import Data.Integer.Properties as IntegerProperties
open import Level using (0ℓ)
open import Data.List.Base using (List; []; _∷_; _++_; map; length)
open import Data.List.Sort as Sort
open import Relation.Binary.Bundles using (DecTotalOrder)
open import Relation.Binary.Construct.On as On
import Relation.Binary.Construct.Flip.EqAndOrd as Flip
open import Data.Product.Relation.Binary.Lex.NonStrict as Lex
open import Data.Nat.DivMod using (m%n<n; m<n⇒m%n≡m)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Empty using (⊥)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Nullary using (¬_)
open import Exotic.ERL.FullCoupled.CanonicalLearnerMonolith as C
open import Exotic.ERL.FullCoupled.GRUStatisticalInjectivity public
open import Exotic.ERL.FullCoupled.ZPFStatisticalRepresentation
open import Exotic.ERL.FullCoupled.FourLawClosureWitnesses public
open import Exotic.ERL.FullCoupled.EGraphSemanticTransport public
open import Exotic.ERL.FullCoupled.RepositorySemanticEGraphClosure public

record CanonicalAQLoopTheorem : Set₁ where
  constructor canonicalAQLoopTheorem
  field
    policyComposition :
      ∀ K s →
      C.canonicalPolicy K s ≡
      C.sparsemaxPolicy
        (C.actionSpaceK K)
        (C.lcbScore
          (C.lcbKernel K)
          (C.lcbCounts s)
          (C.critic (C.watkins s)))
        (C.valuesCount (C.lcbCounts s))
    sharedWatkinsSignal :
      ∀ K s →
      C.canonicalSignal K s ≡
      C.canonicalWatkinsTarget K s
    gruSignalCoupling :
      ∀ K s →
      C.canonicalGRUStep K s ≡
      C.gruStep (C.gru s) (C.canonicalSignal K s)
    f4SignalCoupling :
      ∀ K s →
      C.canonicalOptimizerStep K s ≡
      C.f4ThetaStep (C.optimizerKernel K) (C.optimizer s) (C.canonicalSignal K s)
    watkinsEndogenousCoupling :
      ∀ K s →
      C.canonicalWatkinsTarget K s ≡
      C.int8Add
        (C.int8Add
          (C.int8Add
            (C.canonicalReward8 K s)
            (C.canonicalQLogBias K s))
          (C.int8Mul C.canonicalDiscount8
            (C.maxCriticValue8 (C.critic (C.watkins s)))))
        (C.canonicalEndogenousFeedback K s)

open CanonicalAQLoopTheorem public

canonical-aq-loop-theorem :
  CanonicalAQLoopTheorem
canonical-aq-loop-theorem =
  canonicalAQLoopTheorem
    (λ K s → refl)
    (λ K s → refl)
    (λ K s → refl)
    (λ K s → refl)
    (λ K s → refl)
    (λ K s → refl)

canonicalTotalCountAfter :
  ∀ K n s →
  C.totalCount (C.lcbCounts (C.iterateCanonical K n s)) ≡
  C.totalCount (C.lcbCounts s) + n
canonicalTotalCountAfter = C.canonicalTotalCountAfter

canonicalAperiodic-theorem :
  ∀ K s n →
  C.iterateCanonical K (suc n) s ≢ s
canonicalAperiodic-theorem = C.canonicalAperiodic

canonicalNoNontrivialFiniteCycle-theorem :
  ∀ K s n →
  C.iterateCanonical K (suc n) s ≡ s → ⊥
canonicalNoNontrivialFiniteCycle-theorem = C.canonicalNoNontrivialFiniteCycle

record StateIsomorphism (A B : Set) : Set where
  constructor stateIsomorphism
  field
    to : A → B
    from : B → A
    from-to : ∀ a → from (to a) ≡ a
    to-from : ∀ b → to (from b) ≡ b

open StateIsomorphism public

iterateIsomorphism :
  ∀ {A : Set} → (A → A) → Nat → A → A
iterateIsomorphism f zero a = a
iterateIsomorphism f (suc n) a = iterateIsomorphism f n (f a)

record StepConjugacyWitness
  (A B : Set)
  (sourceStep : A → A)
  (targetStep : B → B) : Set₁ where
  constructor stepConjugacyWitness
  field
    isomorphism : StateIsomorphism A B
    stepCommutes :
      ∀ a →
      to isomorphism (sourceStep a) ≡
      targetStep (to isomorphism a)

open StepConjugacyWitness public

stepConjugacy-iterate :
  ∀ {A B : Set}
  {sourceStep : A → A}
  {targetStep : B → B}
  (W : StepConjugacyWitness A B sourceStep targetStep)
  (n : Nat)
  (a : A) →
  to (isomorphism W) (iterateIsomorphism sourceStep n a) ≡
  iterateIsomorphism targetStep n (to (isomorphism W) a)
stepConjugacy-iterate W zero a =
  refl
stepConjugacy-iterate W (suc n) a =
  trans
    (stepConjugacy-iterate W n (sourceStep a))
    (cong
      (iterateIsomorphism targetStep n)
      (stepCommutes W a))

iteratePredicateTransport :
  ∀ {B : Set}
  (step : B → B)
  (Property : B → Set) →
  (∀ b → Property b → Property (step b)) →
  ∀ n b →
  Property b →
  Property (iterateIsomorphism step n b)
iteratePredicateTransport step Property preserved zero b proof =
  proof
iteratePredicateTransport step Property preserved (suc n) b proof =
  iteratePredicateTransport
    step
    Property
    preserved
    n
    (step b)
    (preserved b proof)

stepConjugacy-property-transport :
  ∀ {A B : Set}
  {sourceStep : A → A}
  {targetStep : B → B}
  (W : StepConjugacyWitness A B sourceStep targetStep)
  (P : A → Set)
  (Q : B → Set)
  (bridge : ∀ a → P a → Q (to (isomorphism W) a))
  (preserved : ∀ b → Q b → Q (targetStep b)) →
  ∀ n a →
  P a →
  Q (iterateIsomorphism targetStep n (to (isomorphism W) a))
stepConjugacy-property-transport W P Q bridge preserved n a proof =
  iteratePredicateTransport
    targetStep
    Q
    preserved
    n
    (to (isomorphism W) a)
    (bridge a proof)

canonical-connected-composition-theorem :
  CanonicalConnectedCompositionTheorem
canonical-connected-composition-theorem =
  canonicalConnectedCompositionTheorem
    canonical-aq-loop-theorem
    canonicalTotalCountAfter
    canonicalNoNontrivialFiniteCycle-theorem

data LearnerReplacement : Set where
  normReplacement : NormPair → LearnerReplacement
  optimizerReplacement : F4IntUState → LearnerReplacement

applyLearnerReplacement :
  LearnerReplacement → FullLearnerState → FullLearnerState
applyLearnerReplacement (normReplacement n) s = replaceNorm s n
applyLearnerReplacement (optimizerReplacement o) s = replaceOptimizer s o

applyLearnerReplacements :
  List LearnerReplacement → FullLearnerState → FullLearnerState
applyLearnerReplacements [] s = s
applyLearnerReplacements (r ∷ rs) s =
  applyLearnerReplacements rs (applyLearnerReplacement r s)

canonicalPolicy-learnerReplacement-invariant :
  ∀ K s r →
  canonicalPolicy K (applyLearnerReplacement r s) ≡ canonicalPolicy K s
canonicalPolicy-learnerReplacement-invariant K s (normReplacement n) =
  canonicalPolicy-norm-invariant K s n
canonicalPolicy-learnerReplacement-invariant K s (optimizerReplacement o) =
  canonicalPolicy-optimizer-invariant K s o

canonicalPolicy-learnerReplacement-composition :
  ∀ K s rs →
  canonicalPolicy K (applyLearnerReplacements rs s) ≡ canonicalPolicy K s
canonicalPolicy-learnerReplacement-composition K s [] = refl
canonicalPolicy-learnerReplacement-composition K s (r ∷ rs) =
  trans
    (canonicalPolicy-learnerReplacement-composition
      K (applyLearnerReplacement r s) rs)
    (canonicalPolicy-learnerReplacement-invariant K s r)

canonicalFullStep-replaceNorm :
  ∀ {A : Set}
  (K : C.FullLearnerKernel A)
  (s : C.FullLearnerState A)
  (n : C.NormPair) →
  C.canonicalFullStep K (C.replaceNorm s n)
  ≡
  C.replaceNorm (C.canonicalFullStep K s) n
canonicalFullStep-replaceNorm K s n = refl

canonicalFullStep-replaceNorm-iterate :
  ∀ {A : Set}
  (K : C.FullLearnerKernel A)
  (n : Nat)
  (s : C.FullLearnerState A)
  (normValue : C.NormPair) →
  C.iterateCanonical K n (C.replaceNorm s normValue)
  ≡
  C.replaceNorm (C.iterateCanonical K n s) normValue
canonicalFullStep-replaceNorm-iterate K zero s normValue = refl
canonicalFullStep-replaceNorm-iterate K (suc n) s normValue =
  trans
    (cong
      (C.iterateCanonical K n)
      (canonicalFullStep-replaceNorm K s normValue))
    (canonicalFullStep-replaceNorm-iterate
      K
      n
      (C.canonicalFullStep K s)
      normValue)

record CanonicalLearnerReplacementClosureTheorem : Set₁ where
  constructor canonicalLearnerReplacementClosureTheorem
  field
    policyInvariant :
      ∀ (K : C.CanonicalFullLearnerKernel)
      (s : C.CanonicalFullLearnerState)
      (rs : List LearnerReplacement) →
      C.canonicalPolicy
        K
        (applyLearnerReplacements rs s)
      ≡
      C.canonicalPolicy K s

canonical-learner-replacement-closure-theorem :
  CanonicalLearnerReplacementClosureTheorem
canonical-learner-replacement-closure-theorem =
  canonicalLearnerReplacementClosureTheorem
    canonicalPolicy-learnerReplacement-composition

canonicalNormPair-afterFullStep-iterate :
  ∀ K n s →
  normPairWeightPlusOne
    (norm (iterateCanonical K n s))
  ≡
  normPairWeightPlusOne (norm s)
canonicalNormPair-afterFullStep-iterate K zero s = refl
canonicalNormPair-afterFullStep-iterate K (suc n) s =
  trans
    (canonicalNormPair-afterFullStep-iterate
      K n (canonicalFullStep K s))
    (canonicalNormPairWeightPlusOne-preservation K s)

canonicalPersistentGRU-afterFullStep-iterate :
  ∀ K n s →
  persistentGRU
    (gru (iterateCanonical K n s))
  ≡
  persistentGRU (gru s)
canonicalPersistentGRU-afterFullStep-iterate K zero s = refl
canonicalPersistentGRU-afterFullStep-iterate K (suc n) s =
  trans
    (canonicalPersistentGRU-afterFullStep-iterate
      K n (canonicalFullStep K s))
    (canonicalPersistentGRUPreservation K s)

record EqualityCompositionTheorem
  {A : Set}
  {x y z : A} : Set where
  constructor equalityCompositionTheorem
  field
    firstStep : x ≡ y
    secondStep : y ≡ z
    composedStep : x ≡ z

composeEqualityTheorem :
  ∀ {A : Set} {x y z : A} →
  x ≡ y →
  y ≡ z →
  EqualityCompositionTheorem
composeEqualityTheorem first second =
  equalityCompositionTheorem
    first
    second
    (trans first second)

record RecurrentAssociativeScanTheorem
  (State Input : Set) : Set₁ where
  constructor recurrentAssociativeScanTheorem
  field
    actionAssociative :
      ∀ (f g h : C.Endomorphism State) s →
      C.applyEndomorphism
        (C.composeEndomorphism
          (C.composeEndomorphism f g)
          h)
        s
      ≡
      C.applyEndomorphism
        (C.composeEndomorphism
          f
          (C.composeEndomorphism g h))
        s

    prefixCorrect :
      ∀ (R : C.RecurrentNetwork State Input)
        (xs : Nat → Input)
        (n : Nat)
        (s : State) →
      C.applyEndomorphism
        (C.recurrentPrefixEndomorphism R xs n)
        s
      ≡
      C.recurrentPrefixState R xs n s

    prefixSplit :
      ∀ (R : C.RecurrentNetwork State Input)
        (xs : Nat → Input)
        (m n : Nat)
        (s : State) →
      C.recurrentPrefixState R xs (m + n) s
      ≡
      C.recurrentPrefixState
        R
        (C.shiftInput xs m)
        n
        (C.recurrentPrefixState R xs m s)

canonicalGRU-recurrent-associative-scan-theorem :
  RecurrentAssociativeScanTheorem C.GRUState C.Int8
canonicalGRU-recurrent-associative-scan-theorem =
  recurrentAssociativeScanTheorem
    C.endomorphismAssociative
    C.recurrentPrefix-correct
    C.recurrentPrefix-split

prefixOp :
  ∀ {State : Set} →
  C.Endomorphism State →
  C.Endomorphism State →
  C.Endomorphism State
prefixOp f g = C.composeEndomorphism g f

prefixListEndomorphism :
  ∀ {State Input : Set} →
  C.RecurrentNetwork State Input →
  List Input →
  C.Endomorphism State
prefixListEndomorphism R [] =
  C.identityEndomorphism
prefixListEndomorphism R (x ∷ xs) =
  C.composeEndomorphism
    (prefixListEndomorphism R xs)
    (C.recurrentInputEndomorphism R x)

prefixListEndomorphism-unit :
  ∀ {State Input : Set}
  (R : C.RecurrentNetwork State Input)
  (s : State) →
  C.applyEndomorphism
    (prefixListEndomorphism R [])
    s
  ≡ s
prefixListEndomorphism-unit R s = refl

prefixListEndomorphism-append :
  ∀ {State Input : Set}
  (R : C.RecurrentNetwork State Input)
  (xs ys : List Input)
  (s : State) →
  C.applyEndomorphism
    (prefixListEndomorphism R (xs ++ ys))
    s
  ≡
  C.applyEndomorphism
    (prefixOp
      (prefixListEndomorphism R xs)
      (prefixListEndomorphism R ys))
    s
prefixListEndomorphism-append R [] ys s = refl
prefixListEndomorphism-append R (x ∷ xs) ys s =
  trans
    (prefixListEndomorphism-append
      R
      xs
      ys
      (C.applyEndomorphism
        (C.recurrentInputEndomorphism R x)
        s))
    refl

prefixOp-associative :
  ∀ {State : Set}
  (f g h : C.Endomorphism State)
  (s : State) →
  C.applyEndomorphism
    (prefixOp (prefixOp f g) h)
    s
  ≡
  C.applyEndomorphism
    (prefixOp f (prefixOp g h))
    s
prefixOp-associative f g h s =
  C.endomorphismAssociative h g f s

prefixOp-identity-left :
  ∀ {State : Set}
  (f : C.Endomorphism State) (s : State) →
  C.applyEndomorphism (prefixOp C.identityEndomorphism f) s
  ≡ C.applyEndomorphism f s
prefixOp-identity-left f s = refl

prefixOp-identity-right :
  ∀ {State : Set}
  (f : C.Endomorphism State) (s : State) →
  C.applyEndomorphism (prefixOp f C.identityEndomorphism) s
  ≡ C.applyEndomorphism f s
prefixOp-identity-right f s = refl

record RecurrentPrefixMonoidHomomorphism
  (State Input : Set) : Set₁ where
  constructor recurrentPrefixMonoidHomomorphism
  field
    unit :
      ∀ (R : C.RecurrentNetwork State Input) (s : State) →
      C.applyEndomorphism
        (prefixListEndomorphism R [])
        s
      ≡ s
    append :
      ∀ (R : C.RecurrentNetwork State Input)
        (xs ys : List Input)
        (s : State) →
      C.applyEndomorphism
        (prefixListEndomorphism R (xs ++ ys))
        s
      ≡
      C.applyEndomorphism
        (prefixOp
          (prefixListEndomorphism R xs)
          (prefixListEndomorphism R ys))
        s

canonical-recurrent-prefix-monoid-homomorphism :
  RecurrentPrefixMonoidHomomorphism C.GRUState C.Int8
canonical-recurrent-prefix-monoid-homomorphism =
  recurrentPrefixMonoidHomomorphism
    (λ R s → prefixListEndomorphism-unit R s)
    (λ R xs ys s → prefixListEndomorphism-append R xs ys s)

productEndomorphism :
  ∀ {StateA StateB : Set} →
  C.Endomorphism StateA →
  C.Endomorphism StateB →
  C.Endomorphism (StateA × StateB)
productEndomorphism f g =
  C.endomorphism
    (λ st →
      (C.applyEndomorphism f (proj₁ st) ,
       C.applyEndomorphism g (proj₂ st)))

productEndomorphism-compose :
  ∀ {StateA StateB : Set}
  (f₁ f₂ : C.Endomorphism StateA)
  (g₁ g₂ : C.Endomorphism StateB)
  (s : StateA)
  (t : StateB) →
  C.applyEndomorphism
    (productEndomorphism
      (C.composeEndomorphism f₁ f₂)
      (C.composeEndomorphism g₁ g₂))
    (s , t)
  ≡
  C.applyEndomorphism
    (C.composeEndomorphism
      (productEndomorphism f₁ g₁)
      (productEndomorphism f₂ g₂))
    (s , t)
productEndomorphism-compose f₁ f₂ g₁ g₂ s t = refl

canonicalF4RecurrentNetwork :
  C.CanonicalFullLearnerKernel →
  C.RecurrentNetwork C.F4IntUState C.Int8
canonicalF4RecurrentNetwork K =
  C.recurrentNetwork
    (λ o signal →
      C.f4ThetaStep (C.optimizerKernel K) o signal)

canonicalF4RecurrentNetwork-step-law :
  ∀ (K : C.CanonicalFullLearnerKernel)
  (o : C.F4IntUState)
  (signal : C.Int8) →
  C.runNetwork
    (canonicalF4RecurrentNetwork K)
    o
    signal
  ≡
  C.f4ThetaStep (C.optimizerKernel K) o signal
canonicalF4RecurrentNetwork-step-law K o signal = refl

canonicalF4-prefix-monoid-homomorphism :
  RecurrentPrefixMonoidHomomorphism
    C.F4IntUState
    C.Int8
canonicalF4-prefix-monoid-homomorphism =
  recurrentPrefixMonoidHomomorphism
    (λ R s → prefixListEndomorphism-unit R s)
    (λ R xs ys s → prefixListEndomorphism-append R xs ys s)

canonicalNormPairRecurrentNetwork :
  C.RecurrentNetwork C.NormPair C.Int8
canonicalNormPairRecurrentNetwork =
  C.recurrentNetwork
    (λ n _ → n)

canonicalNormPairRecurrentNetwork-step-law :
  ∀ (n : C.NormPair) (signal : C.Int8) →
  C.runNetwork
    canonicalNormPairRecurrentNetwork
    n
    signal
  ≡ n
canonicalNormPairRecurrentNetwork-step-law n signal = refl

canonicalNormPair-prefix-monoid-homomorphism :
  RecurrentPrefixMonoidHomomorphism
    C.NormPair
    C.Int8
canonicalNormPair-prefix-monoid-homomorphism =
  recurrentPrefixMonoidHomomorphism
    (λ R s → prefixListEndomorphism-unit R s)
    (λ R xs ys s → prefixListEndomorphism-append R xs ys s)

CanonicalGRUF4NormPrefixState : Set
CanonicalGRUF4NormPrefixState =
  C.GRUState × (C.F4IntUState × C.NormPair)

CanonicalGRUF4NormPrefixInput : Set
CanonicalGRUF4NormPrefixInput =
  C.Int8

canonicalGRUF4NormPrefixNetwork :
  C.CanonicalFullLearnerKernel →
  C.RecurrentNetwork
    CanonicalGRUF4NormPrefixState
    CanonicalGRUF4NormPrefixInput
canonicalGRUF4NormPrefixNetwork K =
  C.recurrentNetwork
    (λ { (g , (o , n)) signal →
      ( C.gruStep g signal
      , ( C.f4ThetaStep (C.optimizerKernel K) o signal
        , n)) })

canonicalGRUF4NormPrefix-step-law :
  ∀ (K : C.CanonicalFullLearnerKernel)
  (g : C.GRUState) (o : C.F4IntUState) (n : C.NormPair)
  (signal : C.Int8) →
  C.runNetwork (canonicalGRUF4NormPrefixNetwork K)
    (g , (o , n)) signal
  ≡
  ( C.gruStep g signal
  , ( C.f4ThetaStep (C.optimizerKernel K) o signal
    , n))
canonicalGRUF4NormPrefix-step-law K g o n signal = refl

canonicalGRUF4Norm-prefix-monoid-homomorphism :
  RecurrentPrefixMonoidHomomorphism
    CanonicalGRUF4NormPrefixState
    CanonicalGRUF4NormPrefixInput
canonicalGRUF4Norm-prefix-monoid-homomorphism =
  recurrentPrefixMonoidHomomorphism
    (λ R s → prefixListEndomorphism-unit R s)
    (λ R xs ys s → prefixListEndomorphism-append R xs ys s)

canonicalFullStep-GRUF4Norm-prefix-bridge :
  ∀ (K : C.CanonicalFullLearnerKernel)
  (s : C.CanonicalFullLearnerState) →
  C.runNetwork (canonicalGRUF4NormPrefixNetwork K)
    (C.gru s , (C.optimizer s , C.norm s))
    (C.canonicalSignal K s)
  ≡
  ( C.gru (C.canonicalFullStep K s)
  , ( C.optimizer (C.canonicalFullStep K s)
    , C.norm (C.canonicalFullStep K s)))
canonicalFullStep-GRUF4Norm-prefix-bridge K s = refl

record CanonicalGRUF4NormWatkinsPrefixCompositionTheorem : Set₁ where
  constructor canonicalGRUF4NormWatkinsPrefixCompositionTheorem
  field
    recurrentScan :
      RecurrentPrefixMonoidHomomorphism C.GRUState C.Int8
    targetCorrectness :
      ∀ (K : C.CanonicalFullLearnerKernel)
      (s : C.CanonicalFullLearnerState) →
      C.canonicalSignal K s ≡ C.canonicalWatkinsTarget K s
    gruf4NormCorrectness :
      ∀ (K : C.CanonicalFullLearnerKernel)
      (s : C.CanonicalFullLearnerState) →
      C.runNetwork (canonicalGRUF4NormPrefixNetwork K)
        (C.gru s , (C.optimizer s , C.norm s))
        (C.canonicalSignal K s)
      ≡
      ( C.gru (C.canonicalFullStep K s)
      , ( C.optimizer (C.canonicalFullStep K s)
        , C.norm (C.canonicalFullStep K s)))

canonical-gruf4-norm-watkins-prefix-composition-theorem :
  CanonicalGRUF4NormWatkinsPrefixCompositionTheorem
canonical-gruf4-norm-watkins-prefix-composition-theorem =
  canonicalGRUF4NormWatkinsPrefixCompositionTheorem
    canonical-recurrent-prefix-monoid-homomorphism
    C.canonicalSignal-watkins-target
    canonicalFullStep-GRUF4Norm-prefix-bridge

commutingIterate :
  ∀ {S : Set} →
  (S → S) → Nat → S → S
commutingIterate step zero s = s
commutingIterate step (suc n) s =
  step (commutingIterate step n s)

record CommutingSquareTheorem
  (State Feature : Set)
  (step : State → State)
  (observe : State → Feature)
  (featureStep : Feature → Feature) : Set₁ where
  constructor commutingSquareTheorem
  field
    square :
      ∀ s → observe (step s) ≡ featureStep (observe s)
    iterateSquare :
      ∀ n s →
      observe (commutingIterate step n s) ≡
      commutingIterate featureStep n (observe s)

open CommutingSquareTheorem public

freeMonoidActionHomomorphism-from-square :
  ∀ {State Feature : Set}
  {step : State → State}
  {observe : State → Feature}
  {featureStep : Feature → Feature} →
  CommutingSquareTheorem State Feature step observe featureStep →
  FreeMonoidActionHomomorphism State Feature step observe featureStep
freeMonoidActionHomomorphism-from-square squareWitness =
  freeMonoidActionHomomorphism
    (CommutingSquareTheorem.iterateSquare squareWitness)

canonicalCount-freeMonoidActionHomomorphism :
  ∀ (K : C.CanonicalFullLearnerKernel) →
  FreeMonoidActionHomomorphism
    C.CanonicalFullLearnerState
    Nat
    (C.canonicalFullStep K)
    suc
    (λ s → C.totalCount (C.lcbCounts s))
canonicalCount-freeMonoidActionHomomorphism K =
  freeMonoidActionHomomorphism-from-square
    (commutingSquareTheorem-from-square
      (λ s →
        C.canonicalTotalCountStep K s))

recurrentWordState :
  ∀ {State Input : Set} →
  C.RecurrentNetwork State Input →
  List Input →
  State →
  State
recurrentWordState R word s =
  C.applyEndomorphism
    (prefixListEndomorphism R word)
    s

recurrentPrefix-scan-lifts-conjugacy :
  ∀ {State Input : Set}
  (replace : State → State)
  (step : State → Input → State)
  (h :
    ∀ (s : State) (x : Input) →
    replace (step s x) ≡ step (replace s) x) →
  ∀ (xs : List Input) (n : Nat) (s : State) →
    replace
      (C.recurrentPrefixState
        (C.recurrentNetwork step)
        xs n s)
    ≡
    C.recurrentPrefixState
      (C.recurrentNetwork step)
      xs n
      (replace s)
recurrentPrefix-scan-lifts-conjugacy replace step h xs zero s = refl
recurrentPrefix-scan-lifts-conjugacy replace step h xs (suc n) s =
  trans
    (recurrentPrefix-scan-lifts-conjugacy
      replace
      step
      h
      xs
      n
      (step s (xs n)))
    (cong
      (λ q →
        C.recurrentPrefixState
          (C.recurrentNetwork step)
          xs n
          q)
      (h s (xs n)))

canonical-recurrent-scan-conjugacy-theorem :
  RecurrentScanConjugacyTheorem C.GRUState C.Int8
canonical-recurrent-scan-conjugacy-theorem =
  recurrentScanConjugacyTheorem
    (λ replace step h → replace)
    (λ replace step h xs n s → recurrentPrefix-scan-lifts-conjugacy replace step h xs n s)

canonicalRecurrentInput-watkinsTarget-law :
  ∀ {A} (K : C.FullLearnerKernel A) (s : C.FullLearnerState A) →
  C.canonicalGRUStep K s ≡
  C.gruStep (C.gru s) (C.canonicalWatkinsTarget K s)
canonicalRecurrentInput-watkinsTarget-law K s =
  trans
    (C.canonicalRecurrentInput-law K s)
    (cong
      (C.gruStep (C.gru s))
      (C.canonicalSignal-watkins-target K s))
record CanonicalFullLearnerConnectedScanConjugacyTheorem : Set₁ where
  constructor canonicalFullLearnerConnectedScanConjugacyTheorem
  field
    scanConjugacy :
      (replace : C.CanonicalFullLearnerState → C.CanonicalFullLearnerState)
      (K : C.CanonicalFullLearnerKernel) →
      (h :
        ∀ s →
        replace (C.canonicalFullStep K s) ≡
        C.canonicalFullStep K (replace s)) →
      ∀ n s →
        replace (C.iterateCanonical K n s) ≡
        C.iterateCanonical K n (replace s)
    connectedStep :
      ∀ (K : C.CanonicalFullLearnerKernel)
      (s : C.CanonicalFullLearnerState) →
      C.runNetwork (canonicalGRUF4NormPrefixNetwork K)
        (C.gru s , (C.optimizer s , C.norm s))
        (C.canonicalSignal K s)
      ≡
      ( C.gru (C.canonicalFullStep K s)
      , ( C.optimizer (C.canonicalFullStep K s)
        , C.norm (C.canonicalFullStep K s)))
    watkinsConnected :
      ∀ (K : C.CanonicalFullLearnerKernel)
      (s : C.CanonicalFullLearnerState) →
      C.watkins (C.canonicalFullStep K s) ≡
      C.canonicalWatkinsStep K s
    watkinsTargetCoupling :
      ∀ (K : C.CanonicalFullLearnerKernel)
      (s : C.CanonicalFullLearnerState) →
      C.canonicalSignal K s ≡ C.canonicalWatkinsTarget K s
    gruWatkinsCoupling :
      ∀ (K : C.CanonicalFullLearnerKernel)
      (s : C.CanonicalFullLearnerState) →
      C.canonicalGRUStep K s ≡
      C.gruStep
        (C.gru s)
        (C.canonicalWatkinsTarget K s)
    optimizerWatkinsCoupling :
      ∀ (K : C.CanonicalFullLearnerKernel)
      (s : C.CanonicalFullLearnerState) →
      C.canonicalOptimizerStep K s ≡
      C.f4ThetaStep
        (C.optimizerKernel K)
        (C.optimizer s)
        (C.canonicalWatkinsTarget K s)

canonicalFullLearner-iterate-conjugacy :
  ∀
  (replace : C.CanonicalFullLearnerState → C.CanonicalFullLearnerState)
  (K : C.CanonicalFullLearnerKernel)
  (h :
    ∀ s →
    replace (C.canonicalFullStep K s) ≡
    C.canonicalFullStep K (replace s)) →
  ∀ n s →
  replace (C.iterateCanonical K n s) ≡
  C.iterateCanonical K n (replace s)
canonicalFullLearner-iterate-conjugacy replace K h zero s = refl
canonicalFullLearner-iterate-conjugacy replace K h (suc n) s =
  trans
    (canonicalFullLearner-iterate-conjugacy
      replace K h n (C.canonicalFullStep K s))
    (cong
      (C.iterateCanonical K n)
      (h s))

canonical-full-learner-connected-scan-conjugacy-theorem :
  CanonicalFullLearnerConnectedScanConjugacyTheorem
canonical-full-learner-connected-scan-conjugacy-theorem =
  canonicalFullLearnerConnectedScanConjugacyTheorem
    (λ replace K h → canonicalFullLearner-iterate-conjugacy replace K h)
    canonicalFullStep-GRUF4Norm-prefix-bridge
    C.canonicalFullStep-watkins
    C.canonicalSignal-watkins-target
    canonicalRecurrentInput-watkinsTarget-law
    C.canonicalOptimizerStep-qMunchausen-L2
record S4PlusS5RecurrentScanTheorem (State Input : Set) : Set₁ where
  constructor s4PlusS5RecurrentScanTheorem
  field
    recurrentScan :
      RecurrentAssociativeScanTheorem State Input
    identityAction :
      ∀ (s : State) →
      C.applyEndomorphism
        C.identityEndomorphism s ≡ s

open S4PlusS5RecurrentScanTheorem public

canonical-S4S5-recurrent-scan-theorem :
  S4PlusS5RecurrentScanTheorem C.GRUState C.Int8
canonical-S4S5-recurrent-scan-theorem =
  s4PlusS5RecurrentScanTheorem
    canonicalGRU-recurrent-associative-scan-theorem
    (λ s → refl)

productRecurrentNetwork :
  ∀ {StateA StateB Input : Set} →
  C.RecurrentNetwork StateA Input →
  C.RecurrentNetwork StateB Input →
  C.RecurrentNetwork (StateA × StateB) Input
productRecurrentNetwork RA RB =
  C.recurrentNetwork
    (λ st x →
      (C.runNetwork RA (proj₁ st) x ,
       C.runNetwork RB (proj₂ st) x))

productRecurrentPrefix-correct :
  ∀ {StateA StateB Input : Set}
  (RA : C.RecurrentNetwork StateA Input)
  (RB : C.RecurrentNetwork StateB Input)
  (xs : Nat → Input)
  (n : Nat)
  (s : StateA)
  (t : StateB) →
  C.recurrentPrefixState
    (productRecurrentNetwork RA RB)
    xs n
    (s , t)
  ≡
  (C.recurrentPrefixState RA xs n s ,
   C.recurrentPrefixState RB xs n t)
productRecurrentPrefix-correct RA RB xs zero s t = refl
productRecurrentPrefix-correct RA RB xs (suc n) s t =
  cong₂
    (λ a b →
      (C.runNetwork RA a (xs n) ,
       C.runNetwork RB b (xs n)))
    (cong proj₁ (productRecurrentPrefix-correct RA RB xs n s t))
    (cong proj₂ (productRecurrentPrefix-correct RA RB xs n s t))

informationPreserving-symbolic-task-factorization :
  ∀ {State Feature Output : Set}
  (observe : State → Feature)
  (inverse : Feature → State)
  (leftInverse : ∀ s → inverse (observe s) ≡ s)
  (target : State → Output)
  (s : State) →
  target s ≡ target (inverse (observe s))
informationPreserving-symbolic-task-factorization
  observe inverse leftInverse target s =
  cong target (sym (leftInverse s))

informationPreserving-all-tasks-injective :
  ∀ {State Feature : Set}
  (observe : State → Feature)
  (inverse : Feature → State) →
  (∀ (target : State → State) (s : State) →
    target s ≡ target (inverse (observe s))) →
  ∀ {s t} → observe s ≡ observe t → s ≡ t
informationPreserving-all-tasks-injective
  observe inverse allTasks
  {s} {t} eq =
  trans
    (sym (allTasks (λ x → x) s))
    (trans
      (cong inverse eq)
      (allTasks (λ x → x) t))

productObservation :
  ∀ {StateA StateB FeatureA FeatureB : Set} →
  (StateA → FeatureA) →
  (StateB → FeatureB) →
  (StateA × StateB) →
  (FeatureA × FeatureB)
productObservation observeA observeB st =
  (observeA (proj₁ st) , observeB (proj₂ st))

productInverse :
  ∀ {StateA StateB FeatureA FeatureB : Set} →
  (FeatureA → StateA) →
  (FeatureB → StateB) →
  (FeatureA × FeatureB) →
  (StateA × StateB)
productInverse inverseA inverseB feature =
  (inverseA (proj₁ feature) , inverseB (proj₂ feature))

productObservation-leftInverse :
  ∀ {StateA StateB FeatureA FeatureB : Set}
  (observeA : StateA → FeatureA)
  (inverseA : FeatureA → StateA)
  (observeB : StateB → FeatureB)
  (inverseB : FeatureB → StateB)
  (leftInverseA : ∀ s → inverseA (observeA s) ≡ s)
  (leftInverseB : ∀ s → inverseB (observeB s) ≡ s)
  (s : StateA)
  (t : StateB) →
  productInverse inverseA inverseB
    (productObservation observeA observeB (s , t))
  ≡
  (s , t)
productObservation-leftInverse observeA inverseA observeB inverseB
  leftInverseA leftInverseB s t =
  cong₂ _,_ (leftInverseA s) (leftInverseB t)

informationPreserving-symbolic-task-boundary :
  ∀ {State Feature : Set}
  (observe : State → Feature)
  (inverse : Feature → State)
  (leftInverse : ∀ s → inverse (observe s) ≡ s) →
  ∀ (target : State → State) (s : State) →
  target s ≡ target (inverse (observe s))
informationPreserving-symbolic-task-boundary =
  informationPreserving-symbolic-task-factorization

record PointwiseSandwich
  {Input Value : Set}
  (_≤_ : Value → Value → Set)
  (lower actual upper : Input → Value) : Set₁ where
  constructor pointwiseSandwich
  field
    lower≤actual : ∀ x → lower x ≤ actual x
    actual≤upper : ∀ x → actual x ≤ upper x

record MinimaxBellmanShapleyOperator
  (State Value : Set)
  (_≤_ : Value → Value → Set) : Set₁ where
  constructor minimaxBellmanShapleyOperator
  field
    value : (State → Value) → Value
    monotone :
      ∀ (f g : State → Value) →
      (∀ s → f s ≤ g s) →
      value f ≤ value g

record MinimaxBellmanShapleyInclusionTheorem
  (State Value : Set)
  (_≤_ : Value → Value → Set)
  (operator : MinimaxBellmanShapleyOperator State Value _≤_)
  (lower actual upper : State → Value) : Set₁ where
  constructor minimaxBellmanShapleyInclusionTheorem
  field
    lowerBound :
      MinimaxBellmanShapleyOperator.value operator lower
      ≤
      MinimaxBellmanShapleyOperator.value operator actual
    upperBound :
      MinimaxBellmanShapleyOperator.value operator actual
      ≤
      MinimaxBellmanShapleyOperator.value operator upper

open PointwiseSandwich public
open MinimaxBellmanShapleyOperator public
open MinimaxBellmanShapleyInclusionTheorem public

canonicalBiasedWatkinsNegativeQMunchausenL2Target :
  C.CanonicalFullLearnerKernel → C.CanonicalFullLearnerState → C.Int8
canonicalBiasedWatkinsNegativeQMunchausenL2Target =
  C.canonicalWatkinsTarget

record CanonicalQMunchausenL2SharedNegationPolarityTheorem : Set₁ where
  constructor canonicalQMunchausenL2SharedNegationPolarityTheorem
  field
    qMunchausenBiasNegation :
      ∀ x →
      C.qLog2Bias8 x ≡
      C.int8Neg
        (C.int8OfNat
          ((C.munchausenScale8 * C.numerator (C.finiteQLog8 x)) /
           C.denominator (C.finiteQLog8 x)))

    l2CorrectionNegation :
      ∀ x →
      C.l2Correction x ≡ C.int8Neg x

open CanonicalQMunchausenL2SharedNegationPolarityTheorem public

canonicalWatkinsTarget-endogenous-leftInverse :
  ∀ (K : C.CanonicalFullLearnerKernel)
  (observe : C.CanonicalFullLearnerState → C.Int8)
  (inverse : C.Int8 → C.CanonicalFullLearnerState) →
  (leftInverse : ∀ t → inverse (observe t) ≡ t) →
  ∀ s →
  C.canonicalWatkinsTarget K s ≡
    C.int8Add
      (C.int8Add
        (C.int8Add
          (C.canonicalReward8 K (inverse (observe s)))
          (C.canonicalQLogBias K (inverse (observe s))))
        (C.int8Mul
          C.canonicalDiscount8
          (C.maxCriticValue8
            (C.critic
              (C.watkins
                (inverse (observe s)))))))
      (C.canonicalEndogenousFeedback K (inverse (observe s)))
canonicalWatkinsTarget-endogenous-leftInverse K observe inverse leftInverse s =
  trans
    (C.canonicalWatkinsTarget-law K s)
    (cong
      (λ t →
        C.int8Add
          (C.int8Add
            (C.int8Add
              (C.canonicalReward8 K t)
              (C.canonicalQLogBias K t))
            (C.int8Mul
              C.canonicalDiscount8
              (C.maxCriticValue8
                (C.critic (C.watkins t)))))
          (C.canonicalEndogenousFeedback K t))
      (leftInverse s))

suc-injective :
  ∀ {m n : Nat} → suc m ≡ suc n → m ≡ n
suc-injective refl = refl

natPlus-left-cancel :
  ∀ (k m n : Nat) → k + m ≡ k + n → m ≡ n
natPlus-left-cancel zero m n eq = eq
natPlus-left-cancel (suc k) m n eq =
  natPlus-left-cancel k m n (suc-injective eq)

canonicalTotalCountSuccessorWitness :
  ∀ {A : Set}
  (K : C.FullLearnerKernel A) →
  NatSuccessorProgressWitness
    (C.FullLearnerState A)
    (C.canonicalFullStep K)
    (λ s → C.totalCount (C.lcbCounts s))
canonicalTotalCountSuccessorWitness K =
  natSuccessorProgressWitness
    (C.canonicalTotalCountStep K)

canonicalOrbit-state-injective :
  ∀ K s {m n : Nat} →
  C.iterateCanonical K m s ≡ C.iterateCanonical K n s →
  m ≡ n
canonicalOrbit-state-injective K s {m} {n} eq =
  successorMeasureOrbitInjective
    (canonicalTotalCountSuccessorWitness K)
    s
    eq

canonicalInfiniteStateOrbitEmbedding :
  ∀ (K : C.CanonicalFullLearnerKernel)
  (s : C.CanonicalFullLearnerState) →
  ∀ {m n : Nat} →
  C.iterateCanonical K m s ≡ C.iterateCanonical K n s →
  m ≡ n
canonicalInfiniteStateOrbitEmbedding K s =
  canonicalOrbit-state-injective K s

record DiscreteExactUAPTheorem
  (State Feature Output : Set)
  (observe : State → Feature)
  (inverse : Feature → State) : Set₁ where
  constructor discreteExactUAPTheorem
  field
    leftInverse :
      ∀ s → inverse (observe s) ≡ s
    exactReadout :
      (target : State → Output) →
      ∀ s →
      target s ≡ target (inverse (observe s))

open DiscreteExactUAPTheorem public

record DiscreteLeftInverseWitness
  (State Feature : Set)
  (observe : State → Feature) : Set₁ where
  constructor discreteLeftInverseWitness
  field
    inverse : Feature → State
    leftInverse :
      ∀ s → inverse (observe s) ≡ s

open DiscreteLeftInverseWitness public

record DiscreteExactUniversalUAP
  (State Feature : Set)
  (observe : State → Feature) : Set₁ where
  constructor discreteExactUniversalUAP
  field
    readout :
      {Output : Set} →
      (State → Output) →
      Feature →
      Output
    exactReadout :
      {Output : Set} →
      (target : State → Output) →
      ∀ s →
      target s ≡ readout target (observe s)

open DiscreteExactUniversalUAP public

discreteLeftInverse-observe-injective :
  ∀ {State Feature : Set}
  {observe : State → Feature}
  {inverse : Feature → State} →
  (∀ s → inverse (observe s) ≡ s) →
  ∀ {s t} →
  observe s ≡ observe t →
  s ≡ t
discreteLeftInverse-observe-injective leftInverse {s} {t} eq =
  trans
    (sym (leftInverse s))
    (trans
      (cong inverse eq)
      (leftInverse t))

collision-implies-no-leftInverse-via-injectivity :
  ∀ {State Feature : Set}
  (observe : State → Feature)
  {s t : State} →
  observe s ≡ observe t →
  s ≢ t →
  ¬ (Σ (λ inverse →
      ∀ u → inverse (observe u) ≡ u))
collision-implies-no-leftInverse-via-injectivity
  observe obsEq distinct =
  λ witness →
    distinct
      (discreteLeftInverse-observe-injective
        (proj₂ witness)
        obsEq)

canonicalWatkinsTargetSignalStream :
  C.CanonicalFullLearnerKernel →
  C.CanonicalFullLearnerState →
  Nat →
  C.Int8
canonicalWatkinsTargetSignalStream K s n =
  C.canonicalWatkinsTarget K
    (C.iterateCanonical K n s)

canonicalWatkinsTarget-recurrent-prefix-correct :
  ∀ (K : C.CanonicalFullLearnerKernel)
  (s : C.CanonicalFullLearnerState)
  (n : Nat)
  (h : C.GRUState) →
  C.applyEndomorphism
    (C.recurrentPrefixEndomorphism
      C.canonicalGRURecurrentNetwork
      (canonicalWatkinsTargetSignalStream K s)
      n)
    h
  ≡
  C.recurrentPrefixState
    C.canonicalGRURecurrentNetwork
    (canonicalWatkinsTargetSignalStream K s)
    n
    h
canonicalWatkinsTarget-recurrent-prefix-correct K s n h =
  C.recurrentPrefix-correct
    C.canonicalGRURecurrentNetwork
    (canonicalWatkinsTargetSignalStream K s)
    n
    h

record ExactTwoCounterConfiguration : Set where
  constructor exactTwoCounterConfiguration
  field
    control : Nat
    counter₁ : Nat
    counter₂ : Nat

record ExactTwoCounterMachine : Set₁ where
  constructor exactTwoCounterMachine
  field
    step : ExactTwoCounterConfiguration → ExactTwoCounterConfiguration
    halting : ExactTwoCounterConfiguration → C.BoolLike

open ExactTwoCounterConfiguration ExactTwoCounterMachine public

record CanonicalExactCompositionTuringCompletenessContract : Set₁ where
  constructor canonicalExactCompositionTuringCompletenessContract
  field
    compile :
      ExactTwoCounterMachine →
      C.CanonicalFullLearnerKernel
    encode :
      (M : ExactTwoCounterMachine) →
      ExactTwoCounterConfiguration →
      C.CanonicalFullLearnerState
    decode :
      (M : ExactTwoCounterMachine) →
      C.CanonicalFullLearnerState →
      ExactTwoCounterConfiguration
    exactEncodeDecode :
      ∀ M c →
      decode M (encode M c) ≡ c
    exactStepSimulation :
      ∀ M c →
      encode M (ExactTwoCounterMachine.step M c) ≡
      C.canonicalFullStep
        (compile M)
        (encode M c)
    output :
      C.CanonicalFullLearnerState → C.BoolLike
    exactHaltingCorrespondence :
      ∀ M c →
      output (encode M c) ≡ ExactTwoCounterMachine.halting M c

exactSelfLoopMachine : ExactTwoCounterMachine
exactSelfLoopMachine =
  exactTwoCounterMachine
    (λ c → c)
    (λ _ → disabled)

canonicalExactCompositionTuringCompletenessContract-impossible :
  ¬ CanonicalExactCompositionTuringCompletenessContract
canonicalExactCompositionTuringCompletenessContract-impossible witness =
  let
    M = exactSelfLoopMachine
    c = exactTwoCounterConfiguration zero zero zero
    K =
      CanonicalExactCompositionTuringCompletenessContract.compile
        witness
        M
    s =
      CanonicalExactCompositionTuringCompletenessContract.encode
        witness
        M
        c
    exactStep =
      CanonicalExactCompositionTuringCompletenessContract.exactStepSimulation
        witness
        M
        c
  in
  C.canonicalNoFixedPoint K s (sym exactStep)

record ContinuousLeftInverseTheorem
  (State Feature : Set)
  (observe : State → Feature)
  (inverse : Feature → State)
  (Continuous : {A B : Set} → (A → B) → Set) : Set₁ where
  constructor continuousLeftInverseTheorem
  field
    observeContinuous : Continuous observe
    inverseContinuous : Continuous inverse
    leftInverse :
      ∀ s → inverse (observe s) ≡ s

open ContinuousLeftInverseTheorem public

record CanonicalEndogenousMinimaxBellmanShapleyUAPTheorem : Set₁ where
  constructor canonicalEndogenousMinimaxBellmanShapleyUAPTheorem
  field
    targetSemantics :
      CanonicalBiasedWatkinsNegativeQMunchausenL2TargetTheorem

    exactDiscreteUAP :
      ∀ {Feature Output : Set}
      (observe : C.CanonicalFullLearnerState → Feature)
      (inverse : Feature → C.CanonicalFullLearnerState) →
      (leftInverse : ∀ s → inverse (observe s) ≡ s) →
      DiscreteExactUAPTheorem
        C.CanonicalFullLearnerState
        Feature
        Output
        observe
        inverse

    inclusionClass :
      ∀ (K : C.CanonicalFullLearnerKernel)
      (_≤_ : C.Int8 → C.Int8 → Set)
      (operator :
        MinimaxBellmanShapleyOperator
          C.CanonicalFullLearnerState
          C.Int8
          _≤_)
      (lower upper : C.CanonicalFullLearnerState → C.Int8) →
      PointwiseSandwich
        _≤_
        lower
        (canonicalBiasedWatkinsNegativeQMunchausenL2Target K)
        upper →
      MinimaxBellmanShapleyInclusionTheorem
        C.CanonicalFullLearnerState
        C.Int8
        _≤_
        operator
        lower
        (canonicalBiasedWatkinsNegativeQMunchausenL2Target K)
        upper

    endogenousFactorization :
      ∀ (K : C.CanonicalFullLearnerKernel)
      (observe : C.CanonicalFullLearnerState → C.Int8)
      (inverse : C.Int8 → C.CanonicalFullLearnerState) →
      (leftInverse : ∀ t → inverse (observe t) ≡ t) →
      ∀ s →
      C.canonicalWatkinsTarget K s ≡
      C.int8Add
        (C.int8Add
          (C.int8Add
            (C.canonicalReward8 K (inverse (observe s)))
            (C.canonicalQLogBias K (inverse (observe s))))
          (C.int8Mul
            C.canonicalDiscount8
            (C.maxCriticValue8
              (C.critic (C.watkins (inverse (observe s))))))
        (C.canonicalEndogenousFeedback K (inverse (observe s))))

    targetScan :
      ∀ (K : C.CanonicalFullLearnerKernel)
      (s : C.CanonicalFullLearnerState)
      (n : Nat)
      (h : C.GRUState) →
      C.applyEndomorphism
        (C.recurrentPrefixEndomorphism
          C.canonicalGRURecurrentNetwork
          (canonicalWatkinsTargetSignalStream K s)
          n)
        h
      ≡
      C.recurrentPrefixState
        C.canonicalGRURecurrentNetwork
        (canonicalWatkinsTargetSignalStream K s)
        n
        h

    continuousReadoutTransfer :
      ∀ {Feature Output : Set}
      {observe : C.CanonicalFullLearnerState → Feature}
      {inverse : Feature → C.CanonicalFullLearnerState}
      {Continuous : {A B : Set} → (A → B) → Set} →
      ContinuousLeftInverseTheorem
        C.CanonicalFullLearnerState
        Feature
        observe
        inverse
        Continuous →
      (target : C.CanonicalFullLearnerState → Output) →
      ∀ s →
      target s ≡ target (inverse (observe s))

    ringStateInjection :
      ∀ (K : C.CanonicalFullLearnerKernel)
      (s : C.CanonicalFullLearnerState) →
      RingStateInjectivityTheorem C.CanonicalFullLearnerState

    infiniteStateOrbit :
      ∀ (K : C.CanonicalFullLearnerKernel)
      (s : C.CanonicalFullLearnerState) →
      ∀ {m n : Nat} →
      C.iterateCanonical K m s ≡ C.iterateCanonical K n s →
      m ≡ n

    denseNeighborhoodSeparation :
      ∀ (K : C.CanonicalFullLearnerKernel)
      (s : C.CanonicalFullLearnerState)
      (observe : C.CanonicalFullLearnerState → C.Int8)
      (inverse : C.Int8 → C.CanonicalFullLearnerState) →
      (∀ t → inverse (observe t) ≡ t) →
      DenseNeighborhoodSeparationTheorem
        C.CanonicalFullLearnerState
        C.Int8
        (λ n → C.iterateCanonical K n s)
        observe

canonicalDeterministicFiniteStepDivergenceInevitability :
  ∀ {A}
  (K : C.CanonicalFullLearnerKernel)
  (s : C.CanonicalFullLearnerState)
  (n : Nat) →
  C.iterateCanonical K (suc n) s ≢ s
canonicalDeterministicFiniteStepDivergenceInevitability =
  C.canonicalAperiodic

canonicalNoFiniteStepConvergenceToFixedPoint :
  ∀ {A}
  (K : C.CanonicalFullLearnerKernel)
  (s equilibrium : C.CanonicalFullLearnerState) →
  C.canonicalFullStep K equilibrium ≡ equilibrium →
  ¬ (Σ Nat (λ n → C.iterateCanonical K n s ≡ equilibrium))
canonicalNoFiniteStepConvergenceToFixedPoint K s equilibrium fixedPoint reached =
  C.canonicalNoFixedPoint K equilibrium fixedPoint

canonicalIterateComposition :
  ∀ (K : C.CanonicalFullLearnerKernel)
  (m n : Nat)
  (s : C.CanonicalFullLearnerState) →
  C.iterateCanonical K (m + n) s ≡
  C.iterateCanonical K n (C.iterateCanonical K m s)
canonicalIterateComposition K m zero s
  rewrite +-identityʳ m = refl
canonicalIterateComposition K m (suc n) s
  rewrite +-suc m n =
  cong (C.canonicalFullStep K)
    (canonicalIterateComposition K m n s)

recurrentPrefixStepWork : Nat → Nat
recurrentPrefixStepWork zero = zero
recurrentPrefixStepWork (suc n) = suc (recurrentPrefixStepWork n)

recurrentPrefixStepWork-law :
  ∀ n → recurrentPrefixStepWork n ≡ n
recurrentPrefixStepWork-law n = refl

recurrentPrefixStepWork-split :
  ∀ m n →
  recurrentPrefixStepWork (m + n) ≡
  recurrentPrefixStepWork m + recurrentPrefixStepWork n
recurrentPrefixStepWork-split m zero
  rewrite +-identityʳ m = refl
recurrentPrefixStepWork-split m (suc n)
  rewrite +-suc m n =
  cong suc (recurrentPrefixStepWork-split m n)

canonicalNatIndexedExactUniversalReadout :
  ∀ {Feature Output : Set}
  (K : C.CanonicalFullLearnerKernel)
  (s : C.CanonicalFullLearnerState)
  (observe : C.CanonicalFullLearnerState → Feature)
  (inverse : Feature → C.CanonicalFullLearnerState) →
  (leftInverse : ∀ t → inverse (observe t) ≡ t) →
  (target : C.CanonicalFullLearnerState → Output) →
  ∀ n →
  target (C.iterateCanonical K n s) ≡
  target (inverse (observe (C.iterateCanonical K n s)))
canonicalNatIndexedExactUniversalReadout
  K s observe inverse leftInverse target n =
  cong
    target
    (sym (leftInverse (C.iterateCanonical K n s)))

hardSignGate-idempotent :
  ∀ x → C.hardSignGate (C.hardSignGate x) ≡ C.hardSignGate x
hardSignGate-idempotent x with C.hardSign x
... | C.negative = refl
... | C.zeroSign = refl
... | C.positive = refl

hardSignGate-continuous-discrete :
  Continuous
    C.Int8
    C.Int8
    (discreteTopology C.Int8)
    (discreteTopology C.Int8)
    C.hardSignGate
hardSignGate-continuous-discrete =
  continuous-under-discrete-topology C.hardSignGate

record FiniteRankStabilityCertificate
  (State : Set)
  (step : State → State)
  (equilibrium : State) : Set₁ where
  constructor finiteRankStabilityCertificate
  field
    rank : State → Nat
    equilibriumFixed :
      step equilibrium ≡ equilibrium
    rankZero :
      ∀ s → rank s ≡ zero → s ≡ equilibrium
    strictDescent :
      ∀ s → s ≢ equilibrium →
      rank (step s) < rank s
    eventualExact :
      ∀ s → Σ Nat (λ n → iterateState step n s ≡ equilibrium)

open FiniteRankStabilityCertificate public

canonicalFullLearner-no-finite-rank-stability :
  ∀ {A : Set}
  (K : C.CanonicalFullLearnerKernel)
  (equilibrium : C.CanonicalFullLearnerState A) →
  ¬ FiniteRankStabilityCertificate
    (C.CanonicalFullLearnerState A)
    (C.canonicalFullStep K)
    equilibrium
canonicalFullLearner-no-finite-rank-stability K equilibrium certificate =
  C.canonicalNoFixedPoint
    K
    equilibrium
    (FiniteRankStabilityCertificate.equilibriumFixed certificate)

sumNat :
  List Nat → Nat
sumNat [] = zero
sumNat (x ∷ xs) = x + sumNat xs

bundleCost :
  ∀ {Good : Set} →
  List Good →
  (Good → Nat) →
  (Good → Nat) →
  Nat
bundleCost goods price bundle =
  sumNat (map (λ g → price g * bundle g) goods)

BudgetFeasible :
  ∀ {Good : Set} →
  List Good →
  (Good → Nat) →
  (Good → Nat) →
  (Good → Nat) →
  Set
BudgetFeasible goods price endowment bundle =
  bundleCost goods price bundle ≤
  bundleCost goods price endowment

record FiniteNonIIDWalrasianEquilibrium
  (Agent Good : Set)
  (agents : List Agent)
  (goods : List Good)
  (utility : Agent → (Good → Nat) → Nat)
  (endowment : Agent → Good → Nat) : Set₁ where
  constructor finiteNonIIDWalrasianEquilibrium
  field
    price : Good → Nat
    allocation : Agent → Good → Nat
    budgetOptimal :
      ∀ i bundle →
      BudgetFeasible
        goods
        price
        (endowment i)
        bundle →
      utility i bundle ≤
      utility i (allocation i)
    marketClearing :
      ∀ g →
      sumNat (map (λ i → allocation i g) agents) ≡
      sumNat (map (λ i → endowment i g) agents)

open FiniteNonIIDWalrasianEquilibrium public

record FiniteTUShapleyAllocationEquilibrium
  (Player : Set)
  (players : List Player) : Set₁ where
  constructor finiteTUShapleyAllocationEquilibrium
  field
    coalitionWorth : List Player → Nat
    payoff : Player → Nat
    scaledShapley : Player → Nat
    scaledValue : Nat
    scaledShapleyCorrect :
      ∀ p →
      scaledValue * payoff p ≡
      scaledShapley p
    scaledEfficiency :
      sumNat (map payoff players) ≡
      scaledValue * coalitionWorth players

open FiniteTUShapleyAllocationEquilibrium public

record CanonicalPolymorphicSparsemaxCompositionTheorem : Set₁ where
  constructor canonicalPolymorphicSparsemaxCompositionTheorem
  field
    genericPolicy :
      ∀ {A} (K : C.FullLearnerKernel A) (s : C.FullLearnerState A) →
      C.canonicalPolicy K s ≡
      C.sparsemaxPolicy
        (C.actionSpaceK K)
        (C.lcbScore (C.lcbKernel K) (C.lcbCounts s)
          (C.critic (C.watkins s)))
        (C.valuesCount (C.lcbCounts s))
    normProjectionInvariant :
      ∀ (K : C.CanonicalFullLearnerKernel)
      (s : C.CanonicalFullLearnerState) (n : C.NormPair) →
      C.canonicalPolicy K (C.replaceNorm s n) ≡ C.canonicalPolicy K s
    optimizerProjectionInvariant :
      ∀ (K : C.CanonicalFullLearnerKernel)
      (s : C.CanonicalFullLearnerState) (o : C.F4IntUState) →
      C.canonicalPolicy K (C.replaceOptimizer s o) ≡ C.canonicalPolicy K s
    hardSparseComposition :
      ∀ (K : C.CanonicalFullLearnerKernel)
      (s : C.CanonicalFullLearnerState)
      (n : C.NormPair) (o : C.F4IntUState) →
      C.HardSparse K s →
      C.HardSparse K (C.replaceNorm (C.replaceOptimizer s o) n)
    recurrentPrefixComposition :
      RecurrentPrefixMonoidHomomorphism C.GRUState C.Int8
    s4PlusS5RecurrentScan :
      S4PlusS5RecurrentScanTheorem C.GRUState C.Int8
    informationPreservingTask :
      ∀ {State Feature Output : Set}
      (observe : State → Feature) (inverse : Feature → State)
      (leftInverse : ∀ s → inverse (observe s) ≡ s)
      (target : State → Output) (s : State) →
      target s ≡ target (inverse (observe s))

open CanonicalPolymorphicSparsemaxCompositionTheorem public

canonical-polymorphic-sparsemax-egraph-theorem :
  CanonicalPolymorphicSparsemaxCompositionTheorem
canonical-polymorphic-sparsemax-egraph-theorem =
  canonicalPolymorphicSparsemaxCompositionTheorem
    (λ K s → refl)
    C.canonicalPolicy-norm-invariant
    C.canonicalPolicy-optimizer-invariant
    C.hardSparse-composition-normPair-F4-L2
    canonical-recurrent-prefix-monoid-homomorphism
    canonical-S4S5-recurrent-scan-theorem
    informationPreserving-symbolic-task-factorization

record ContinuousStationaryMarkovWalrasianData
  (State Price Allocation : Set)
  (Continuous : {A B : Set} → (A → B) → Set) : Set₁ where
  constructor continuousStationaryMarkovWalrasianData
  field
    step : State → State
    aggregate : (State → Allocation) → Allocation
    aggregateContinuous : Continuous aggregate
    invariant :
      ∀ (allocation : State → Allocation) →
      aggregate allocation
      ≡
      aggregate (λ s → allocation (step s))
    staticWalrasian :
      Price → Allocation → Set

open ContinuousStationaryMarkovWalrasianData public

componentPrefix :
  ∀ {Q Input : Set} →
  (Q → Input → Q) → List Input → Q → Q
componentPrefix step [] q = q
componentPrefix step (x ∷ xs) q =
  componentPrefix step xs (step q x)

productPrefix :
  ∀ {Q₁ Q₂ Input : Set} →
  ((Q₁ × Q₂) → Input → (Q₁ × Q₂)) →
  List Input → (Q₁ × Q₂) → (Q₁ × Q₂)
productPrefix step [] q = q
productPrefix step (x ∷ xs) q =
  productPrefix step xs (step q x)

productPrefix-componentPrefix :
  ∀ {Q₁ Q₂ Input : Set}
  (step₁ : Q₁ → Input → Q₁)
  (step₂ : Q₂ → Input → Q₂)
  (xs : List Input) (q₁ : Q₁) (q₂ : Q₂) →
  productPrefix
    (λ { (a , b) x → step₁ a x , step₂ b x })
    xs
    (q₁ , q₂)
  ≡
  (componentPrefix step₁ xs q₁ ,
   componentPrefix step₂ xs q₂)
productPrefix-componentPrefix step₁ step₂ [] q₁ q₂ = refl
productPrefix-componentPrefix step₁ step₂ (x ∷ xs) q₁ q₂ =
  productPrefix-componentPrefix
    step₁ step₂ xs (step₁ q₁ x) (step₂ q₂ x)

record DirectProductFiniteAutomatonComposition
  (Q₁ Q₂ Input : Set) : Set₁ where
  constructor directProductFiniteAutomatonComposition
  field
    step₁ : Q₁ → Input → Q₁
    step₂ : Q₂ → Input → Q₂
    productStep :
      (Q₁ × Q₂) → Input → (Q₁ × Q₂)
    productStep-def :
      ∀ q₁ q₂ x →
      productStep (q₁ , q₂) x
      ≡
      (step₁ q₁ x , step₂ q₂ x)
    prefixCorrect :
      ∀ (xs : List Input) (q₁ : Q₁) (q₂ : Q₂) →
      productPrefix productStep xs (q₁ , q₂)
      ≡
      (componentPrefix step₁ xs q₁ ,
       componentPrefix step₂ xs q₂)

directProductFiniteAutomatonComposition-theorem :
  ∀ {Q₁ Q₂ Input : Set}
  (step₁ : Q₁ → Input → Q₁)
  (step₂ : Q₂ → Input → Q₂) →
  DirectProductFiniteAutomatonComposition Q₁ Q₂ Input
directProductFiniteAutomatonComposition-theorem step₁ step₂ =
  directProductFiniteAutomatonComposition
    step₁
    step₂
    (λ { (q₁ , q₂) x → step₁ q₁ x , step₂ q₂ x })
    (λ _ _ _ → refl)
    (λ xs q₁ q₂ → productPrefix-componentPrefix step₁ step₂ xs q₁ q₂)

data TrivialContinuity : Set where
  trivialContinuity : TrivialContinuity

iterateUpdate :
  ∀ {State : Set} →
  (State → State) → Nat → State → State
iterateUpdate update zero state = state
iterateUpdate update (suc n) state =
  update (iterateUpdate update n state)

GloballyEventuallyFixed :
  ∀ {State : Set} →
  (State → State) → State → Set
GloballyEventuallyFixed update fixed =
  ∀ state → Σ Nat (λ n → iterateUpdate update n state ≡ fixed)

successor-never-globally-eventually-fixed-at-zero :
  ¬ GloballyEventuallyFixed suc 0
successor-never-globally-eventually-fixed-at-zero h =
  no-suc-zero
    (trans
      (sym (iterateUpdate-suc 1))
      (proj₂ (h 1)))
  where
    iterateUpdate-suc :
      ∀ n → iterateUpdate suc n 1 ≡ suc n
    iterateUpdate-suc zero = refl
    iterateUpdate-suc (suc n) =
      cong suc (iterateUpdate-suc n)

    no-suc-zero : ∀ {n : Nat} → suc n ≢ 0
    no-suc-zero ()

exact-injective-continuous-leftInverse-does-not-imply-update-stability :
  ¬
    (∀ {State Feature : Set}
       (observe : State → Feature)
       (inverse : Feature → State)
       (Continuous : {A B : Set} → (A → B) → Set)
       (update : State → State)
       (fixed : State) →
       ContinuousLeftInverseTheorem
         State Feature observe inverse Continuous →
       GloballyEventuallyFixed update fixed)
exact-injective-continuous-leftInverse-does-not-imply-update-stability h =
  successor-never-globally-eventually-fixed-at-zero
    (h
      (λ n → n)
      (λ n → n)
      (λ _ → TrivialContinuity)
      suc
      0
      (continuousLeftInverseTheorem
        (λ _ → trivialContinuity)
        (λ _ → trivialContinuity)
        (λ _ → refl)))

record OffPolicyFunctionApproximationStabilityBoundary : Set₁ where
  constructor offPolicyFunctionApproximationStabilityBoundary
  field
    representationVsUpdateStability :
      ¬
        (∀ {State Feature : Set}
           (observe : State → Feature)
           (inverse : Feature → State)
           (Continuous : {A B : Set} → (A → B) → Set)
           (update : State → State)
           (fixed : State) →
           ContinuousLeftInverseTheorem
             State Feature observe inverse Continuous →
           GloballyEventuallyFixed update fixed)

offPolicyFunctionApproximationStabilityBoundaryWitness :
  OffPolicyFunctionApproximationStabilityBoundary
offPolicyFunctionApproximationStabilityBoundaryWitness =
  offPolicyFunctionApproximationStabilityBoundary
    exact-injective-continuous-leftInverse-does-not-imply-update-stability

record ExactReconstructionOnImage
  (State Feature : Set)
  (observe : State → Feature)
  (inverse : Feature → State) : Set₁ where
  constructor exactReconstructionOnImage
  field
    reconstruct :
      ∀ s → inverse (observe s) ≡ s
    imageReconstructs :
      ∀ f → (Σ State (λ s → observe s ≡ f)) →
      observe (inverse f) ≡ f

open ExactReconstructionOnImage public

exactReconstructionOnImage-from-inverses :
  ∀ {State Feature : Set}
  {observe : State → Feature}
  {inverse : Feature → State} →
  (∀ s → inverse (observe s) ≡ s) →
  (∀ f → observe (inverse f) ≡ f) →
  ExactReconstructionOnImage State Feature observe inverse
exactReconstructionOnImage-from-inverses leftInverse rightInverse =
  exactReconstructionOnImage
    leftInverse
    (λ f _ → rightInverse f)

record GlobalConjugacyEquivalence
  (State Feature : Set)
  (step : State → State)
  (observe : State → Feature)
  (featureStep : Feature → Feature)
  (inverse : Feature → State) : Set₁ where
  constructor globalConjugacyEquivalence
  field
    forward :
      ∀ s → observe (step s) ≡ featureStep (observe s)
    stateReconstruction :
      ∀ s → inverse (observe s) ≡ s
    featureReconstruction :
      ∀ f → observe (inverse f) ≡ f
    stateDynamicsFromFeature :
      ∀ s → step s ≡ inverse (featureStep (observe s))
    featureDynamicsFromState :
      ∀ f → featureStep f ≡ observe (step (inverse f))

globalConjugacyEquivalence-iterate :
  ∀ {State Feature : Set}
    {step : State → State}
    {observe : State → Feature}
    {featureStep : Feature → Feature}
    {inverse : Feature → State}
    (G : GlobalConjugacyEquivalence
      State
      Feature
      step
      observe
      featureStep
      inverse)
    (n : Nat)
    (s : State) →
  observe (iterateState step n s)
  ≡
  iterateState featureStep n (observe s)
globalConjugacyEquivalence-iterate G zero s = refl
globalConjugacyEquivalence-iterate G (suc n) s =
  trans
    (field G .forward (iterateState step n s))
    (cong
      featureStep
      (globalConjugacyEquivalence-iterate G n s))

recurrentListState-append :
  ∀ {State Input : Set}
  (R : C.RecurrentNetwork State Input)
  (xs ys : List Input)
  (s : State) →
  C.recurrentListState R (xs ++ ys) s
  ≡
  C.recurrentListState R ys
    (C.recurrentListState R xs s)
recurrentListState-append R [] ys s = refl
recurrentListState-append R (x ∷ xs) ys s =
  recurrentListState-append
    R
    xs
    ys
    (C.runNetwork R s x)

canonicalTokenStep-conjugacy :
  ∀ (s : C.GRUState) (t : C.CanonicalToken) →
  C.runNetwork C.canonicalTokenRecurrentNetwork s t
  ≡
  C.runNetwork C.canonicalGRURecurrentNetwork
    s
    (C.canonicalTokenEncode t)
canonicalTokenStep-conjugacy s t = refl

canonicalTokenListState-conjugacy :
  ∀ (xs : C.CanonicalTokenSequence) (s : C.GRUState) →
  C.canonicalTokenListState xs s
  ≡
  C.recurrentListState
    C.canonicalGRURecurrentNetwork
    (C.canonicalTokenEncodeList xs)
    s
canonicalTokenListState-conjugacy [] s = refl
canonicalTokenListState-conjugacy (t ∷ ts) s =
  canonicalTokenListState-conjugacy
    ts
    (C.canonicalTokenStep s t)

canonicalToken-prefix-monoid-homomorphism :
  RecurrentPrefixMonoidHomomorphism
    C.GRUState
    C.CanonicalToken
canonicalToken-prefix-monoid-homomorphism =
  recurrentPrefixMonoidHomomorphism
    (λ R s → prefixListEndomorphism-unit R s)
    (λ R xs ys s → prefixListEndomorphism-append R xs ys s)

canonicalTokenLogitTrace-append :
  ∀ (K : C.CanonicalTokenLanguageModelKernel)
  (xs ys : C.CanonicalTokenSequence)
  (s : C.GRUState) →
  C.canonicalTokenLogitTrace K (xs ++ ys) s
  ≡
  C.canonicalTokenLogitTrace K xs s ++
  C.canonicalTokenLogitTrace K ys
    (C.canonicalTokenListState xs s)
canonicalTokenLogitTrace-append K [] ys s = refl
canonicalTokenLogitTrace-append K (t ∷ xs) ys s =
  cong
    (λ trace →
      C.logits K s ∷ trace)
    (canonicalTokenLogitTrace-append
      K
      xs
      ys
      (C.canonicalTokenStep s t))

record CanonicalGlobalTokenEncodingConjugacyTheorem : Set₁ where
  constructor canonicalGlobalTokenEncodingConjugacyTheorem
  field
    recurrentStepConjugacy :
      ∀ s t →
      C.runNetwork C.canonicalTokenRecurrentNetwork s t
      ≡
      C.runNetwork C.canonicalGRURecurrentNetwork
        s
        (C.canonicalTokenEncode t)
    recurrentListConjugacy :
      ∀ xs s →
      C.canonicalTokenListState xs s
      ≡
      C.recurrentListState
        C.canonicalGRURecurrentNetwork
        (C.canonicalTokenEncodeList xs)
        s

open CanonicalGlobalTokenEncodingConjugacyTheorem public

canonical-global-token-encoding-conjugacy :
  CanonicalGlobalTokenEncodingConjugacyTheorem
canonical-global-token-encoding-conjugacy =
  canonicalGlobalTokenEncodingConjugacyTheorem
    canonicalTokenStep-conjugacy
    canonicalTokenListState-conjugacy

record ExactFunctionIsomorphismTransportTheorem
  (S T A B : Set)
  (isoA : StateIsomorphism S A)
  (isoB : StateIsomorphism T B)
  (f : S → T) : Set₁ where
  constructor exactFunctionIsomorphismTransportTheorem
  field
    translatedFunction : A → B
    exactTransport :
      ∀ x →
      StateIsomorphism.to isoB (f x) ≡
      translatedFunction (StateIsomorphism.to isoA x)

exactRecurrentFunctionTranslation :
  ∀ {S A : Set}
    {isoA : StateIsomorphism S A}
    (step : S → S)
    (stepA : A → A)
    (conjugacy :
      ∀ x →
      StateIsomorphism.to isoA (step x) ≡
      stepA (StateIsomorphism.to isoA x)) →
  ExactRecurrentFunctionTranslationTheorem S A isoA step stepA
exactRecurrentFunctionTranslation step stepA conjugacy =
  exactRecurrentFunctionTranslationTheorem
    conjugacy
    (λ {T} {B} {isoB} f →
      exactFunctionIsomorphismTransport f)

record CanonicalExactRNNLMTheorem : Set₁ where
  constructor canonicalExactRNNLMTheorem
  field
    globalTokenConjugacy :
      CanonicalGlobalTokenEncodingConjugacyTheorem
    recurrentTrace :
      ∀ (K : C.CanonicalTokenLanguageModelKernel)
      (xs ys : C.CanonicalTokenSequence)
      (s : C.GRUState) →
      C.canonicalTokenLogitTrace K (xs ++ ys) s
      ≡
      C.canonicalTokenLogitTrace K xs s ++
      C.canonicalTokenLogitTrace K ys
        (C.canonicalTokenListState xs s)

open CanonicalExactRNNLMTheorem public

canonical-exact-rnn-lm-theorem : CanonicalExactRNNLMTheorem
canonical-exact-rnn-lm-theorem =
  canonicalExactRNNLMTheorem
    canonical-global-token-encoding-conjugacy
    canonicalTokenLogitTrace-append

record CanonicalGlobalTokenLMCompositionTheorem : Set₁ where
  constructor canonicalGlobalTokenLMCompositionTheorem
  field
    globalTokenConjugacy :
      CanonicalGlobalTokenEncodingConjugacyTheorem
    tokenPrefixMonoid :
      RecurrentPrefixMonoidHomomorphism
        C.GRUState
        C.CanonicalToken
    traceAppend :
      ∀ (K : C.CanonicalTokenLanguageModelKernel)
      (xs ys : C.CanonicalTokenSequence)
      (s : C.GRUState) →
      C.canonicalTokenLogitTrace K (xs ++ ys) s
      ≡
      C.canonicalTokenLogitTrace K xs s ++
      C.canonicalTokenLogitTrace K ys
        (C.canonicalTokenListState xs s)

open CanonicalGlobalTokenLMCompositionTheorem public

canonical-global-token-lm-composition-theorem :
  CanonicalGlobalTokenLMCompositionTheorem
canonical-global-token-lm-composition-theorem =
  canonicalGlobalTokenLMCompositionTheorem
    canonical-global-token-encoding-conjugacy
    canonicalToken-prefix-monoid-homomorphism
    canonicalTokenLogitTrace-append

record CanonicalTokenArbitraryLengthGenerationTheorem : Set₁ where
  constructor canonicalTokenArbitraryLengthGenerationTheorem
  field
    stateConjugacy :
      ∀ (xs : C.CanonicalTokenSequence) (s : C.GRUState) →
      C.canonicalTokenListState xs s
      ≡
      C.recurrentListState
        C.canonicalGRURecurrentNetwork
        (C.canonicalTokenEncodeList xs)
        s

    traceAppend :
      ∀ (K : C.CanonicalTokenLanguageModelKernel)
      (xs ys : C.CanonicalTokenSequence)
      (s : C.GRUState) →
      C.canonicalTokenLogitTrace K (xs ++ ys) s
      ≡
      C.canonicalTokenLogitTrace K xs s ++
      C.canonicalTokenLogitTrace K ys
        (C.canonicalTokenListState xs s)

    prefixMonoid :
      RecurrentPrefixMonoidHomomorphism
        C.GRUState
        C.CanonicalToken

canonical-token-arbitrary-length-generation-theorem :
  CanonicalTokenArbitraryLengthGenerationTheorem
canonical-token-arbitrary-length-generation-theorem =
  canonicalTokenArbitraryLengthGenerationTheorem
    canonicalTokenListState-conjugacy
    canonicalTokenLogitTrace-append
    canonicalToken-prefix-monoid-homomorphism

canonicalIntegerHaarCross :
  C.int8Add C.one8 (C.int8Neg C.one8) ≡ C.zero8
canonicalIntegerHaarCross = refl

canonicalIntegerHaarEnergy :
  C.int8Add C.one8 C.one8 ≡ C.int8OfNat 2
canonicalIntegerHaarEnergy = refl

record CanonicalIntegerHaarScaledOrthogonalityTheorem : Set₁ where
  constructor canonicalIntegerHaarScaledOrthogonalityTheorem
  field
    crossOrthogonality :
      C.int8Add C.one8 (C.int8Neg C.one8) ≡ C.zero8
    integerEnergy :
      C.int8Add C.one8 C.one8 ≡ C.int8OfNat 2

open CanonicalIntegerHaarScaledOrthogonalityTheorem public

canonical-integer-haar-scaled-orthogonality-theorem :
  CanonicalIntegerHaarScaledOrthogonalityTheorem
canonical-integer-haar-scaled-orthogonality-theorem =
  canonicalIntegerHaarScaledOrthogonalityTheorem
    canonicalIntegerHaarCross
    canonicalIntegerHaarEnergy

canonicalAStarZeroCost :
  (zero + zero) ≡ zero
canonicalAStarZeroCost = refl

canonicalAStarSuccessorCost :
  ∀ n → n + suc zero ≡ suc n
canonicalAStarSuccessorCost n = +-suc n zero

record CanonicalAStarCostGuidanceTheorem : Set₁ where
  constructor canonicalAStarCostGuidanceTheorem
  field
    zeroCostIdentity :
      (zero + zero) ≡ zero
    successorCostComposition :
      ∀ n → n + suc zero ≡ suc n
    exactTokenTrace :
      ∀ (K : C.CanonicalTokenLanguageModelKernel)
      (xs ys : C.CanonicalTokenSequence)
      (s : C.GRUState) →
      C.canonicalTokenLogitTrace K (xs ++ ys) s
      ≡
      C.canonicalTokenLogitTrace K xs s ++
      C.canonicalTokenLogitTrace K ys
        (C.canonicalTokenListState xs s)

open CanonicalAStarCostGuidanceTheorem public

canonical-a-star-cost-guidance-theorem :
  CanonicalAStarCostGuidanceTheorem
canonical-a-star-cost-guidance-theorem =
  canonicalAStarCostGuidanceTheorem
    canonicalAStarZeroCost
    canonicalAStarSuccessorCost
    canonicalTokenLogitTrace-append

record CanonicalEndogenousEGraphAStarTransportClosureTheorem : Set₁ where
  constructor canonicalEndogenousEGraphAStarTransportClosureTheorem
  field
    aStarGuidance :
      CanonicalAStarCostGuidanceTheorem
    representationTransport :
      GeneralizedRepresentationTransportCompositionTheorem
    endogenousTraceTransport :
      ∀ {S T A B : Set}
        {isoA : StateIsomorphism S A}
        {isoB : StateIsomorphism T B}
        (f : S → T) →
      ExactFunctionIsomorphismTransportTheorem S T A B isoA isoB f
    semanticEGraphAStarClosure :
      ∀ {Expression State : Set} →
      (A : AStarSemanticClosure Expression State) →
      ∀ {e f : Expression} →
      EGraphSemanticPath (semantics A) e f →
      interpret (semantics A) e ≡ interpret (semantics A) f

CanonicalEndogenousAStarTransportClosureTheorem :
  Set₁
CanonicalEndogenousAStarTransportClosureTheorem =
  CanonicalEndogenousEGraphAStarTransportClosureTheorem

open CanonicalEndogenousAStarTransportClosureTheorem public

record CanonicalFiniteCycleExclusionIsomorphismTheorem : Set₁ where
  constructor canonicalFiniteCycleExclusionIsomorphismTheorem
  field
    iterateConjugacy :
      ∀ {A B : Set}
        (iso : StateIsomorphism A B)
        (f : A → A)
        (g : B → B) →
        (∀ a → to iso (f a) ≡ g (to iso a)) →
        ∀ n a →
        to iso (iterateIsomorphism f n a)
        ≡
        iterateIsomorphism g n (to iso a)
    cycleTransport :
      ∀ {A B : Set}
        (iso : StateIsomorphism A B)
        (f : A → A)
        (g : B → B) →
        (∀ a → to iso (f a) ≡ g (to iso a)) →
        (∀ n a → iterateIsomorphism f (suc n) a ≢ a) →
        ∀ n a →
        iterateIsomorphism g (suc n) (to iso a) ≢ to iso a

open CanonicalFiniteCycleExclusionIsomorphismTheorem public

record CanonicalOperatorCompositionTheorem : Set₁ where
  constructor canonicalOperatorCompositionTheorem
  field
    identity :
      ∀ {S : Set} (s : S) →
      C.applyEndomorphism
        (C.identityEndomorphism {State = S}) s
      ≡ s
    composition :
      ∀ {S : Set}
        (f g : C.Endomorphism S) (s : S) →
      C.applyEndomorphism
        (C.composeEndomorphism f g) s
      ≡
      C.applyEndomorphism f
        (C.applyEndomorphism g s)
    associativity :
      ∀ {S : Set}
        (f g h : C.Endomorphism S) (s : S) →
      C.applyEndomorphism
        (C.composeEndomorphism
          (C.composeEndomorphism f g) h) s
      ≡
      C.applyEndomorphism
        (C.composeEndomorphism
          f (C.composeEndomorphism g h)) s

open CanonicalOperatorCompositionTheorem public

canonical-operator-composition-theorem :
  CanonicalOperatorCompositionTheorem
canonical-operator-composition-theorem =
  canonicalOperatorCompositionTheorem
    (λ s → refl)
    (λ f g s → refl)
    C.endomorphismAssociative

record CanonicalF4GlobalOptimizerStabilityTheorem : Set₁ where
  constructor canonicalF4GlobalOptimizerStabilityTheorem
  field
    thetaTranslation :
      ∀ {A} (K : C.FullLearnerKernel A) (s : C.FullLearnerState A) →
      C.thetaQ (C.canonicalOptimizerStep K s) ≡
      C.int8Add
        (C.int8Add (C.thetaQ (C.optimizer s)) (C.canonicalSignal K s))
        (C.l2Correction (C.globalL2 (C.optimizerKernel K)))
    stableNonThetaCoordinates :
      ∀ {A} (K : C.FullLearnerKernel A) (s : C.FullLearnerState A) →
      C.rTheta (C.canonicalOptimizerStep K s) ≡ C.zero8 ×
      C.eQ (C.canonicalOptimizerStep K s) ≡ C.eQ (C.optimizer s) ×
      C.rE (C.canonicalOptimizerStep K s) ≡ C.rE (C.optimizer s) ×
      C.rL (C.canonicalOptimizerStep K s) ≡ C.rL (C.optimizer s)
    equalInputStability :
      ∀ {A} (K : C.FullLearnerKernel A)
        (s t : C.FullLearnerState A) →
      C.optimizer s ≡ C.optimizer t →
      C.canonicalSignal K s ≡ C.canonicalSignal K t →
      C.canonicalOptimizerStep K s ≡ C.canonicalOptimizerStep K t

open CanonicalF4GlobalOptimizerStabilityTheorem public

canonical-f4-global-optimizer-stability-theorem :
  CanonicalF4GlobalOptimizerStabilityTheorem
canonical-f4-global-optimizer-stability-theorem =
  canonicalF4GlobalOptimizerStabilityTheorem
    (λ K s → C.f4ParameterInvariant
      (C.optimizerKernel K) (C.optimizer s) (C.canonicalSignal K s))
    (λ K s → refl , (refl , (refl , refl)))
    (λ K s t optimizerEq signalEq →
      cong₂
        (λ optimizer signal →
          C.f4ThetaStep (C.optimizerKernel K) optimizer signal)
        optimizerEq signalEq)

f4Orbit :
  C.F4IntUKernel → C.Int8 → Nat → C.F4IntUState → C.F4IntUState
f4Orbit K g zero s = s
f4Orbit K g (suc n) s =
  C.f4ThetaStep K (f4Orbit K g n s) g

record F4UpperBoundedTrajectory
  (K : C.F4IntUKernel)
  (g : C.Int8)
  (s : C.F4IntUState) : Set₁ where
  constructor f4UpperBoundedTrajectory
  field
    bound : Nat
    bounded :
      ∀ n →
      C.code (C.thetaQ (f4Orbit K g n s)) ≤ℤ + bound

nat-plus-one :
  ∀ n → n + suc zero ≡ suc n
nat-plus-one n =
  trans
    (+-suc n zero)
    (cong suc (+-identityʳ n))

integer-nat-plus-one :
  ∀ n → (+ n) +ℤ (+ 1) ≡ + (suc n)
integer-nat-plus-one n =
  cong +_ (nat-plus-one n)

f4-zero-L2-unit-step-code :
  ∀ s →
  C.code
    (C.thetaQ
      (C.f4ThetaStep
        (C.f4IntUKernel C.zero8)
        s
        C.one8))
  ≡
  C.code (C.thetaQ s) +ℤ (+ 1)
f4-zero-L2-unit-step-code s =
  trans
    (cong C.code
      (C.f4ParameterInvariant
        (C.f4IntUKernel C.zero8)
        s
        C.one8))
    (IntegerProperties.+-identityʳ
      (C.code (C.thetaQ s) +ℤ (+ 1)))

f4-unit-forcing-linear-growth :
  ∀ n s →
  C.code
    (C.thetaQ
      (f4Orbit
        (C.f4IntUKernel C.zero8)
        C.one8
        n
        s))
  ≡
  C.code (C.thetaQ s) +ℤ (+ n)
f4-unit-forcing-linear-growth zero s =
  sym (IntegerProperties.+-identityʳ (C.code (C.thetaQ s)))
f4-unit-forcing-linear-growth (suc n) s =
  trans
    (f4-zero-L2-unit-step-code
      (f4Orbit (C.f4IntUKernel C.zero8) C.one8 n s))
    (trans
      (cong
        (λ z → z +ℤ (+ 1))
        (f4-unit-forcing-linear-growth n s))
      (trans
        (IntegerProperties.+-assoc
          (C.code (C.thetaQ s))
          (+ n)
          (+ 1))
        (cong
          (λ z → C.code (C.thetaQ s) +ℤ z)
          (integer-nat-plus-one n))))

nat-suc-not-le :
  ∀ n → suc n ≤ n → ⊥
nat-suc-not-le zero ()
nat-suc-not-le (suc n) (s≤s h) =
  nat-suc-not-le n h

f4-unit-forcing-no-upper-bound :
  ∀ {s : C.F4IntUState} →
  C.thetaQ s ≡ C.zero8 →
  ¬ F4UpperBoundedTrajectory
      (C.f4IntUKernel C.zero8)
      C.one8
      s
f4-unit-forcing-no-upper-bound thetaZero boundedWitness =
  let
    B = F4UpperBoundedTrajectory.bound boundedWitness
    horizonBound = F4UpperBoundedTrajectory.bounded boundedWitness (suc B)
    growth =
      f4-unit-forcing-linear-growth
        (suc B)
        _
    growthFromZero :
      C.code
        (C.thetaQ
          (f4Orbit
            (C.f4IntUKernel C.zero8)
            C.one8
            (suc B)
            _))
      ≡
      + (suc B)
    growthFromZero =
      trans
        growth
        (trans
          (cong
            (λ z → z +ℤ (+ suc B))
            (cong C.code thetaZero))
          (IntegerProperties.+-identityˡ (+ suc B)))
    impossibleOrder :
      + (suc B) ≤ℤ + B
    impossibleOrder =
      subst
        (λ z → z ≤ℤ + B)
        growthFromZero
        horizonBound
  in
    nat-suc-not-le B
      (IntegerProperties.drop‿+≤+ impossibleOrder)

record CanonicalPureNonOrangeBypassCompletionTheorem : Set₁ where
  constructor canonicalPureNonOrangeBypassCompletionTheorem
  field
    recurrentPrefix :
      RecurrentPrefixMonoidHomomorphism C.GRUState C.Int8
    fullLearnerScanConjugacy :
      CanonicalFullLearnerConnectedScanConjugacyTheorem
    exactTuringBoundary :
      ¬ CanonicalExactCompositionTuringCompletenessContract
    finiteCycleIsomorphismTransport :
      CanonicalFiniteCycleExclusionIsomorphismTheorem
    operatorComposition :
      CanonicalOperatorCompositionTheorem
    f4OptimizerStability :
      CanonicalF4GlobalOptimizerStabilityTheorem
    integerHaarOrthogonality :
      CanonicalIntegerHaarScaledOrthogonalityTheorem

open CanonicalPureNonOrangeBypassCompletionTheorem public

record StationaryLimitTheorem
  (Distribution : Set)
  (P : Distribution → Distribution)
  (μ : Nat → Distribution)
  (μ∞ : Distribution)
  (Converges : (Nat → Distribution) → Distribution → Set) : Set₁ where
  constructor stationaryLimitTheorem
  field
    transitionLaw :
      ∀ n → μ (suc n) ≡ P (μ n)
    converges :
      Converges μ μ∞
    limitPreserved :
      Converges μ μ∞ → P μ∞ ≡ μ∞

canonical-persistent-excitation-requirement-theorem :
  CanonicalPersistentExcitationRequirementTheorem
canonical-persistent-excitation-requirement-theorem =
  canonicalPersistentExcitationRequirementTheorem
    tt
    tt

record ExactContractComputabilityBoundaryTheorem : Set₁ where
  constructor exactContractComputabilityBoundaryTheorem
  field
    specifiedContractImpossible :
      ¬ CanonicalExactCompositionTuringCompletenessContract
    scopeIsContractSpecific :
      ⊤

exact-contract-computability-boundary-theorem :
  ExactContractComputabilityBoundaryTheorem
exact-contract-computability-boundary-theorem =
  exactContractComputabilityBoundaryTheorem
    canonicalExactCompositionTuringCompletenessContract-impossible
    tt

record CanonicalStationarySubcompositionTheorem : Set₁ where
  constructor canonicalStationarySubcompositionTheorem
  field
    stationaryLimitContract :
      ∀ {Distribution : Set}
        (P : Distribution → Distribution)
        (μ : Nat → Distribution)
        (π : Distribution)
        (Converges : (Nat → Distribution) → Distribution → Set) →
      (∀ n → μ (suc n) ≡ P (μ n)) →
      Converges μ π →
      (Converges μ π → P π ≡ π) →
      StationaryLimitTheorem
        Distribution P μ π Converges

canonical-stationary-subcomposition-theorem :
  CanonicalStationarySubcompositionTheorem
canonical-stationary-subcomposition-theorem =
  canonicalStationarySubcompositionTheorem
    (λ P μ π Converges transitionLaw convergence limitPreserved →
      stationaryLimitTheorem
        transitionLaw
        convergence
        limitPreserved)

record DistributionalStationaryAggregateTransport
  (Distribution Economic : Set)
  (P : Distribution → Distribution)
  (μ : Nat → Distribution)
  (μ∞ : Distribution)
  (Converges : (Nat → Distribution) → Distribution → Set)
  (aggregate : Distribution → Economic)
  (economicStep : Economic → Economic) : Set₁ where
  constructor distributionalStationaryAggregateTransport
  field
    stationaryLimit :
      StationaryLimitTheorem
        Distribution
        P
        μ
        μ∞
        Converges
    aggregateStepCommutes :
      ∀ d →
      aggregate (P d) ≡
      economicStep (aggregate d)

open DistributionalStationaryAggregateTransport public

distributionalStationaryAggregate-stationary :
  ∀ {Distribution Economic : Set}
  {P : Distribution → Distribution}
  {μ : Nat → Distribution}
  {μ∞ : Distribution}
  {Converges : (Nat → Distribution) → Distribution → Set}
  {aggregate : Distribution → Economic}
  {economicStep : Economic → Economic}
  (W :
    DistributionalStationaryAggregateTransport
      Distribution
      Economic
      P
      μ
      μ∞
      Converges
      aggregate
      economicStep) →
  economicStep (aggregate μ∞) ≡ aggregate μ∞
distributionalStationaryAggregate-stationary W =
  trans
    (sym (aggregateStepCommutes W _))
    (cong
      aggregate
      (StationaryLimitTheorem.limitPreserved
        (stationaryLimit W)
        (StationaryLimitTheorem.converges (stationaryLimit W))))

record FunctionClassInclusion
  (Input Output : Set)
  (FBase FFull : (Input → Output) → Set₁) : Set₁ where
  constructor functionClassInclusion
  field
    include :
      ∀ {f : Input → Output} →
      FBase f →
      FFull f

record StrictFunctionClassSeparation
  (Input Output : Set)
  (FBase FFull : (Input → Output) → Set₁) : Set₁ where
  constructor strictFunctionClassSeparation
  field
    inclusion :
      FunctionClassInclusion Input Output FBase FFull
    witness :
      Input → Output
    witnessInFull :
      FFull witness
    witnessNotInBase :
      ¬ FBase witness

twoPow : Nat → Nat
twoPow zero = suc zero
twoPow (suc k) = twoPow k + twoPow k

nat-plus-right-mono :
  ∀ {a b c : Nat} → a ≤ b → a + c ≤ b + c
nat-plus-right-mono z≤n = z≤n
nat-plus-right-mono (s≤s p) = s≤s (nat-plus-right-mono p)

record EfficientOperatorMonoidRepresentation
  (State Input : Set) : Set₁ where
  constructor efficientOperatorMonoidRepresentation
  field
    operator :
      Input → C.Endomorphism State
    operatorAssociative :
      ∀ (f g h : C.Endomorphism State) s →
      C.applyEndomorphism
        (C.composeEndomorphism
          (C.composeEndomorphism f g)
          h)
        s
      ≡
      C.applyEndomorphism
        (C.composeEndomorphism
          f
          (C.composeEndomorphism g h))
        s
    representationSpan : Nat
    decodingSpan : Nat
    compositionSpan : Nat
    compositionWork : Nat
    scanSpan : Nat → Nat
    scanWork : Nat → Nat
    scanSpan-linear :
      ∀ h →
      scanSpan h ≤ compositionSpan + compositionSpan * h
    scanWork-linear :
      ∀ h →
      scanWork h ≤ compositionWork * h

record ParallelPrefixComplexityCertificate
  (State Input : Set) : Set₁ where
  constructor parallelPrefixComplexityCertificate
  field
    monoidRepresentation :
      EfficientOperatorMonoidRepresentation State Input
    exactScan :
      RecurrentAssociativeScanTheorem State Input
    totalSpan :
      Nat → Nat
    totalWork :
      Nat → Nat
    totalSpan-definition :
      ∀ h →
      totalSpan h ≡
        EfficientOperatorMonoidRepresentation.representationSpan
          monoidRepresentation
        + EfficientOperatorMonoidRepresentation.scanSpan
            monoidRepresentation h
        + EfficientOperatorMonoidRepresentation.decodingSpan
            monoidRepresentation
    totalWork-definition :
      ∀ h →
      totalWork h ≡
        EfficientOperatorMonoidRepresentation.scanWork
          monoidRepresentation h

record LogarithmicScanSpanCertificate
  (State Input : Set) : Set₁ where
  constructor logarithmicScanSpanCertificate
  field
    scanSpan : Nat → Nat
    coefficient : Nat
    additive : Nat
    scanSpan-bound :
      ∀ k h →
      h ≤ twoPow k →
      scanSpan h ≤ coefficient * k + additive

record LogarithmicPrefixScanComplexityTheorem
  (State Input : Set) : Set₁ where
  constructor logarithmicPrefixScanComplexityTheorem
  field
    exactScan :
      RecurrentAssociativeScanTheorem State Input
    operatorMonoid :
      EfficientOperatorMonoidRepresentation State Input
    logarithmicSpan :
      LogarithmicScanSpanCertificate State Input
    representationOverhead :
      Nat
    decodingOverhead :
      Nat
    horizonSpan :
      Nat → Nat
    horizonWork :
      Nat → Nat
    horizonSpan-definition :
      ∀ h →
      horizonSpan h ≡
        LogarithmicScanSpanCertificate.scanSpan logarithmicSpan h
        + representationOverhead
        + decodingOverhead
    horizonWork-linear :
      ∀ h →
      horizonWork h ≤
      EfficientOperatorMonoidRepresentation.compositionWork operatorMonoid * h
    exactness :
      ∀ (R : C.RecurrentNetwork State Input)
        (xs : Nat → Input)
        (h : Nat)
        (s : State) →
      C.applyEndomorphism
        (C.recurrentPrefixEndomorphism R xs h)
        s
      ≡
      C.recurrentPrefixState R xs h s
    horizonSpan-logarithmic :
      ∀ k h →
      h ≤ twoPow k →
      horizonSpan h ≤
        LogarithmicScanSpanCertificate.coefficient logarithmicSpan * k
        + LogarithmicScanSpanCertificate.additive logarithmicSpan
        + representationOverhead
        + decodingOverhead

------------------------------------------------------------------------
-- Closed MARL law composition.
--
-- These are the three exact learner-facing laws used by the current
-- coupled learner: recurrent-prefix composition, the F4 optimizer step,
-- and NormPair step invariance.  They compose with the endogenous Watkins
-- target in one closed theorem package.  This is the unconditional
-- learner-side theorem; it does not claim the separate physics Law I/II/III
-- interface is already proved.
------------------------------------------------------------------------

record CanonicalMARLLawCompositionTheorem : Set₁ where
  constructor canonicalMARLLawCompositionTheorem
  field
    recurrentPrefixComposition :
      RecurrentPrefixMonoidHomomorphism C.GRUState C.Int8
    f4StepLaw :
      ∀ (K : C.CanonicalFullLearnerKernel)
      (o : C.F4IntUState)
      (signal : C.Int8) →
      C.runNetwork
        (canonicalF4RecurrentNetwork K)
        o
        signal
      ≡
      C.f4ThetaStep (C.optimizerKernel K) o signal
    normPairStepLaw :
      ∀ (n : C.NormPair) (signal : C.Int8) →
      C.runNetwork
        canonicalNormPairRecurrentNetwork
        n
        signal
      ≡ n
    watkinsSignalLaw :
      ∀ (K : C.CanonicalFullLearnerKernel)
      (s : C.CanonicalFullLearnerState) →
      C.canonicalSignal K s ≡
      C.canonicalWatkinsTarget K s
    fullComposition :
      CanonicalGRUF4NormWatkinsPrefixCompositionTheorem

canonical-marl-law-composition-theorem :
  CanonicalMARLLawCompositionTheorem
canonical-marl-law-composition-theorem =
  canonicalMARLLawCompositionTheorem
    canonical-recurrent-prefix-monoid-homomorphism
    canonicalF4RecurrentNetwork-step-law
    canonicalNormPairRecurrentNetwork-step-law
    C.canonicalSignal-watkins-target
    canonical-gruf4-norm-watkins-prefix-composition-theorem

------------------------------------------------------------------------
-- Carrier-polymorphic continuous Hodge-Maxwell representation.
--
-- The physical content is explicit in the certificate: d F = 0 and
-- d(star F) = j, closure under the supplied solution step, exact
-- encode/decode inverse laws, recurrent-step conjugacy, and continuity.
-- This is an exact representation schema.  It does not assert existence
-- of such a certificate for the current learner without those witnesses.
------------------------------------------------------------------------

record ContinuousHodgeMaxwellExactRepresentationData
  (GRU : Set)
  {Continuous : {A B : Set} → (A → B) → Set} : Set₁ where
  constructor continuousHodgeMaxwellExactRepresentationData
  field
    Form2 : Set
    FormStar : Set
    Form3 : Set
    d : Form2 → Form3
    star : Form2 → FormStar
    dStar : FormStar → Form3
    zero3 : Form3

    Solution : Set
    fieldF : Solution → Form2
    fieldJ : Solution → Form3

    maxwellEquation :
      ∀ s →
      (d (fieldF s) ≡ zero3) ×
      (dStar (star (fieldF s)) ≡ fieldJ s)

    step : Solution → Solution
    gruStep : GRU → GRU
    encode : Solution → GRU
    decode : GRU → Solution

    decodeEncode :
      ∀ s → decode (encode s) ≡ s

    encodeDecode :
      ∀ g → encode (decode g) ≡ g

    maxwellClosed :
      ∀ s →
      maxwellEquation (step s)

    conjugacy :
      ∀ s →
      encode (step s) ≡ gruStep (encode s)

    continuousD : Continuous d
    continuousStar : Continuous star
    continuousDStar : Continuous dStar
    continuousFieldF : Continuous fieldF
    continuousFieldJ : Continuous fieldJ
    continuousStep : Continuous step
    continuousGRUStep : Continuous gruStep
    continuousEncode : Continuous encode
    continuousDecode : Continuous decode

open ContinuousHodgeMaxwellExactRepresentationData public

continuousHodgeMaxwell-state-isomorphism :
  ∀ {GRU : Set}
  {Continuous : {A B : Set} → (A → B) → Set}
  (D : ContinuousHodgeMaxwellExactRepresentationData GRU) →
  StateIsomorphism (Solution D) GRU
continuousHodgeMaxwell-state-isomorphism D =
  stateIsomorphism
    (encode D)
    (decode D)
    (decodeEncode D)
    (encodeDecode D)

continuousHodgeMaxwell-global-encode-injective :
  ∀ {GRU : Set}
  {Continuous : {A B : Set} → (A → B) → Set}
  (D : ContinuousHodgeMaxwellExactRepresentationData GRU) →
  ∀ {x y} →
  encode D x ≡ encode D y →
  x ≡ y
continuousHodgeMaxwell-global-encode-injective D {x} {y} eq =
  trans
    (sym (decodeEncode D x))
    (trans
      (cong (decode D) eq)
      (decodeEncode D y))

record ConnectedContinuousHodgeMaxwellGRURepresentationTheorem
  (GRU : Set)
  {Continuous : {A B : Set} → (A → B) → Set} : Set₁ where
  constructor connectedContinuousHodgeMaxwellGRURepresentationTheorem
  field
    semantics :
      ContinuousHodgeMaxwellExactRepresentationData GRU

    globalStateIsomorphism :
      StateIsomorphism
        (Solution semantics)
        GRU

    exactGRUStepRepresentation :
      ∀ s →
      to globalStateIsomorphism (step semantics s)
      ≡
      gruStep semantics
        (to globalStateIsomorphism s)

    exactFieldEquations :
      ∀ s →
      maxwellEquation semantics s

    globalEncodeInjective :
      ∀ {x y} →
      encode semantics x ≡ encode semantics y →
      x ≡ y

connected-continuous-hodge-maxwell-gru-representation-theorem :
  ∀ {GRU : Set}
  {Continuous : {A B : Set} → (A → B) → Set}
  (D : ContinuousHodgeMaxwellExactRepresentationData GRU) →
  ConnectedContinuousHodgeMaxwellGRURepresentationTheorem GRU
connected-continuous-hodge-maxwell-gru-representation-theorem D =
  connectedContinuousHodgeMaxwellGRURepresentationTheorem
    D
    (continuousHodgeMaxwell-state-isomorphism D)
    (λ s → conjugacy D s)
    (λ s → maxwellEquation D s)
    (continuousHodgeMaxwell-global-encode-injective D)

------------------------------------------------------------------------
-- Exact Hodge-Maxwell/full-learner bridge.
--
-- The learner side is the closed MARL law composition above.  The
-- cross-domain step is deliberately proof-relevant: a solution-state
-- encoder/decoder and exact step conjugacy are required.  The theorem then
-- derives the corresponding encoded learner-step conjugacy by equality
-- transport.  No equilibrium, convergence, or physical existence theorem
-- is smuggled into this bridge.
------------------------------------------------------------------------

record CanonicalLearnerHodgeMaxwellCompositionTheorem
  {Continuous : {A B : Set} → (A → B) → Set} : Set₁ where
  constructor canonicalLearnerHodgeMaxwellCompositionTheorem
  field
    learnerSemantics :
      CanonicalMARLLawCompositionTheorem
    hodgeRepresentation :
      ConnectedContinuousHodgeMaxwellGRURepresentationTheorem
        C.CanonicalFullLearnerState

    learnerToSolution :
      C.CanonicalFullLearnerState →
      Solution (semantics hodgeRepresentation)

    solutionToLearner :
      Solution (semantics hodgeRepresentation) →
      C.CanonicalFullLearnerState

    learnerSolutionLeftInverse :
      ∀ s →
      solutionToLearner (learnerToSolution s) ≡ s

    learnerSolutionRightInverse :
      ∀ q →
      learnerToSolution (solutionToLearner q) ≡ q

    learnerStepConjugacy :
      ∀ (K : C.CanonicalFullLearnerKernel)
      (s : C.CanonicalFullLearnerState) →
      learnerToSolution
        (C.canonicalFullStep K s)
      ≡
      step
        (semantics hodgeRepresentation)
        (learnerToSolution s)

open CanonicalLearnerHodgeMaxwellCompositionTheorem public

canonical-learner-hodge-maxwell-step-conjugacy :
  ∀ {Continuous : {A B : Set} → (A → B) → Set}
  (W :
    CanonicalLearnerHodgeMaxwellCompositionTheorem
      {Continuous = Continuous}) →
  ∀ (K : C.CanonicalFullLearnerKernel)
  (s : C.CanonicalFullLearnerState) →
  encode
    (semantics (hodgeRepresentation W))
    (learnerToSolution W s)
  ≡
  gruStep
    (semantics (hodgeRepresentation W))
    (encode
      (semantics (hodgeRepresentation W))
      (learnerToSolution W s))
canonical-learner-hodge-maxwell-step-conjugacy
  W K s =
  trans
    (cong
      (encode (semantics (hodgeRepresentation W)))
      (sym (learnerStepConjugacy W K s)))
    (conjugacy
      (semantics (hodgeRepresentation W))
      (learnerToSolution W s))

canonical-physics-to-learner-transition-witness :
  ∀ {Continuous : {A B : Set} → (A → B) → Set}
  (W :
    CanonicalLearnerHodgeMaxwellCompositionTheorem
      {Continuous = Continuous})
  (K : C.CanonicalFullLearnerKernel) →
  PhysicsToLearnerTransitionWitness
    C.CanonicalFullLearnerState
    (Solution (semantics (hodgeRepresentation W)))
    (C.canonicalFullStep K)
    (step (semantics (hodgeRepresentation W)))
canonical-physics-to-learner-transition-witness W K =
  physicsToLearnerTransitionWitness
    (learnerToSolution W)
    (solutionToLearner W)
    (learnerSolutionLeftInverse W)
    (learnerStepConjugacy W K)

------------------------------------------------------------------------
-- nLab-guided semantic closure for the Maxwell four-law seam.
--
-- Sources:
--   Noether theorem / conserved current:
--     https://ncatlab.org/nlab/show/Noether%27s%2Btheorem
--     https://ncatlab.org/nlab/show/conserved%2Bcurrent
--   Maxwell differential-form equations / Hodge-Maxwell theorem:
--     https://ncatlab.org/nlab/show/Maxwell%27s%2Bequations
--     https://ncatlab.org/nlab/show/Hodge-Maxwell%2Btheorem
--   Action / Euler-Lagrange critical locus:
--     https://ncatlab.org/nlab/show/action%2Bfunctional
--     https://ncatlab.org/nlab/show/Euler-Lagrange%2Bequation
--
-- The repository does not expose a differential-form calculus or a
-- variational bicomplex. Therefore the external theorems are represented
-- by theorem-output interfaces rather than fabricated Agda axioms:
--
--   Noether output:
--     an on-shell conserved current for the physical step;
--   Euler-Lagrange output:
--     a variational/action semantics whose Euler-Lagrange shell contains
--     the Maxwell shell and whose critical-locus predicate is stationary.
--
-- The concrete Hodge-Maxwell representation still supplies the learner ↔
-- solution inverse and one-step conjugacy. The only semantic frontier
-- entering the four-law contract is therefore this single typed closure
-- record.
------------------------------------------------------------------------

record NLabNoetherConservationTheorem
  (PhysicalState Current : Set)
  (PhysicalStep : PhysicalState → PhysicalState)
  (MaxwellShell : PhysicalState → Set) : Set₁ where
  constructor nLabNoetherConservationTheorem
  field
    current :
      PhysicalState → Current
    conservedOnShell :
      ∀ p →
      MaxwellShell p →
      current (PhysicalStep p) ≡ current p

open NLabNoetherConservationTheorem public

record NLabEulerLagrangeMaxwellTheorem
  (PhysicalState Variation Action : Set)
  (Admissible : Variation → Set)
  (Stationary : PhysicalState → Set)
  (MaxwellShell : PhysicalState → Set) : Set₁ where
  constructor nLabEulerLagrangeMaxwellTheorem
  field
    variation :
      PhysicalState → Variation
    action :
      PhysicalState → Action
    admissibleVariation :
      ∀ p →
      Admissible (variation p)
    eulerLagrangeShell :
      PhysicalState → Set
    maxwellImpliesEulerLagrange :
      ∀ p →
      MaxwellShell p →
      eulerLagrangeShell p
    eulerLagrangeImpliesMaxwell :
      ∀ p →
      eulerLagrangeShell p →
      MaxwellShell p
    eulerLagrangeImpliesStationary :
      ∀ p →
      eulerLagrangeShell p →
      Stationary p

open NLabEulerLagrangeMaxwellTheorem public

nLabMaxwellEulerLagrangeShell-equivalence :
  ∀ {PhysicalState Variation Action : Set}
  {Admissible : Variation → Set}
  {Stationary : PhysicalState → Set}
  {MaxwellShell : PhysicalState → Set}
  (S :
    NLabEulerLagrangeMaxwellTheorem
      PhysicalState
      Variation
      Action
      Admissible
      Stationary
      MaxwellShell)
  (p : PhysicalState) →
  (MaxwellShell p → eulerLagrangeShell S p)
  ×
  (eulerLagrangeShell S p → MaxwellShell p)
nLabMaxwellEulerLagrangeShell-equivalence S p =
  ( maxwellImpliesEulerLagrange S p
  , eulerLagrangeImpliesMaxwell S p )

MaxwellSolution :
  ∀ {GRU : Set}
  {Continuous : {A B : Set} → (A → B) → Set}
  (D :
    ContinuousHodgeMaxwellExactRepresentationData
      GRU) →
  Set
MaxwellSolution D = Solution D

MaxwellShell :
  ∀ {GRU : Set}
  {Continuous : {A B : Set} → (A → B) → Set}
  (D :
    ContinuousHodgeMaxwellExactRepresentationData
      GRU) →
  MaxwellSolution D → Set
MaxwellShell D p = maxwellEquation D p

lawIFromNLabNoether :
  ∀ {LearnerState PhysicalState Current : Set}
  {PhysicalStep : PhysicalState → PhysicalState}
  {MaxwellShell : PhysicalState → Set}
  (S :
    NLabNoetherConservationTheorem
      PhysicalState
      Current
      PhysicalStep
      MaxwellShell)
  (shell : ∀ p → MaxwellShell p)
  (encodeD : LearnerState → PhysicalState)
  (decodeD : PhysicalState → LearnerState)
  (decodeEncodeD :
    ∀ s → decodeD (encodeD s) ≡ s) →
  LawIPhysicsWitness
    LearnerState
    PhysicalState
    Current
lawIFromNLabNoether
  S
  shell
  encodeD
  decodeD
  decodeEncodeD =
  lawIPhysicsWitness
    encodeD
    decodeD
    decodeEncodeD
    (λ p → PhysicalStep p)
    (current S)
    (λ p → conservedOnShell S p (shell p))

lawIIIFromNLabEulerLagrange :
  ∀ {LearnerState PhysicalState Variation Action : Set}
  {Admissible : Variation → Set}
  {Stationary : PhysicalState → Set}
  {MaxwellShell : PhysicalState → Set}
  (S :
    NLabEulerLagrangeMaxwellTheorem
      PhysicalState
      Variation
      Action
      Admissible
      Stationary
      MaxwellShell)
  (shell : ∀ p → MaxwellShell p)
  (encodeD : LearnerState → PhysicalState)
  (decodeD : PhysicalState → LearnerState)
  (decodeEncodeD :
    ∀ s → decodeD (encodeD s) ≡ s) →
  LawIIIVariationalWitness
    LearnerState
    PhysicalState
    Variation
    Action
    Admissible
    Stationary
lawIIIFromNLabEulerLagrange
  S
  shell
  encodeD
  decodeD
  decodeEncodeD =
  lawIIIVariationalWitness
    encodeD
    decodeD
    decodeEncodeD
    (variation S)
    (action S)
    (admissibleVariation S)
    (λ p →
      eulerLagrangeImpliesStationary
        S
        p
        (maxwellImpliesEulerLagrange S p (shell p)))

record NLabMaxwellSemanticClosure
  {Continuous : {A B : Set} → (A → B) → Set}
  (W :
    CanonicalLearnerHodgeMaxwellCompositionTheorem
      {Continuous = Continuous})
  (Current Variation Action : Set)
  (Admissible : Variation → Set)
  (Stationary :
    MaxwellSolution
      (semantics (hodgeRepresentation W)) → Set) : Set₁ where
  constructor nLabMaxwellSemanticClosure
  field
    noether :
      NLabNoetherConservationTheorem
        (MaxwellSolution
          (semantics (hodgeRepresentation W)))
        Current
        (step (semantics (hodgeRepresentation W)))
        (MaxwellShell
          (semantics (hodgeRepresentation W)))

    variational :
      NLabEulerLagrangeMaxwellTheorem
        (MaxwellSolution
          (semantics (hodgeRepresentation W)))
        Variation
        Action
        Admissible
        Stationary
        (MaxwellShell
          (semantics (hodgeRepresentation W)))

open NLabMaxwellSemanticClosure public

nLabMaxwellFourLawOneStep :
  ∀ {Continuous : {A B : Set} → (A → B) → Set}
  (W :
    CanonicalLearnerHodgeMaxwellCompositionTheorem
      {Continuous = Continuous})
  (K : C.CanonicalFullLearnerKernel)
  {Current Variation Action : Set}
  {Admissible : Variation → Set}
  {Stationary :
    MaxwellSolution
      (semantics (hodgeRepresentation W)) → Set} →
  NLabMaxwellSemanticClosure
    W
    Current
    Variation
    Action
    Admissible
    Stationary →
  FourLawOneStepWitnessContract
    C.CanonicalFullLearnerState
    (MaxwellSolution
      (semantics (hodgeRepresentation W)))
    Current
    Variation
    Action
    Admissible
    Stationary
    (C.canonicalFullStep K)
    (step (semantics (hodgeRepresentation W)))
nLabMaxwellFourLawOneStep
  W
  K
  S =
  fourLawOneStepWitnessContract
    (lawIFromNLabNoether
      (noether S)
      (λ p →
        maxwellEquation
          (semantics (hodgeRepresentation W))
          p)
      (learnerToSolution W)
      (solutionToLearner W)
      (learnerSolutionLeftInverse W))
    (lawIIIFromNLabEulerLagrange
      (variational S)
      (λ p →
        maxwellEquation
          (semantics (hodgeRepresentation W))
          p)
      (learnerToSolution W)
      (solutionToLearner W)
      (learnerSolutionLeftInverse W))
    (canonical-physics-to-learner-transition-witness W K)

------------------------------------------------------------------------
-- A semantically closed four-law model is the single proof-relevant
-- downstream boundary.  Once this package is inhabited, callers do not
-- repeat the Noether, variational, shell, inverse, or transition premises.
--
-- This does not manufacture an inhabitant: the repository's generic
-- impossibility boundary rules out a constructor that could populate these
-- fields for arbitrary predicates.  The package therefore concentrates the
-- unavoidable physical semantics into one explicit object while keeping all
-- later transport theorems premise-free.
------------------------------------------------------------------------

record NLabMaxwellFourLawSemanticallyClosed
  {Continuous : {A B : Set} → (A → B) → Set}
  (W :
    CanonicalLearnerHodgeMaxwellCompositionTheorem
      {Continuous = Continuous})
  (Current Variation Action : Set)
  (Admissible : Variation → Set)
  (Stationary :
    MaxwellSolution
      (semantics (hodgeRepresentation W)) → Set) : Set₁ where
  constructor nLabMaxwellFourLawSemanticallyClosed
  field
    kernel : C.CanonicalFullLearnerKernel
    semanticClosure :
      NLabMaxwellSemanticClosure
        W
        Current
        Variation
        Action
        Admissible
        Stationary

nLabMaxwellFourLawSemanticallyClosed-from-semantic :
  ∀ {Continuous : {A B : Set} → (A → B) → Set}
  (W :
    CanonicalLearnerHodgeMaxwellCompositionTheorem
      {Continuous = Continuous})
  (K : C.CanonicalFullLearnerKernel)
  {Current Variation Action : Set}
  {Admissible : Variation → Set}
  {Stationary :
    MaxwellSolution
      (semantics (hodgeRepresentation W)) → Set}
  (S :
    NLabMaxwellSemanticClosure
      W
      Current
      Variation
      Action
      Admissible
      Stationary) →
  NLabMaxwellFourLawSemanticallyClosed
    W
    Current
    Variation
    Action
    Admissible
    Stationary
nLabMaxwellFourLawSemanticallyClosed-from-semantic
  W
  K
  S =
  nLabMaxwellFourLawSemanticallyClosed
    K
    S

open NLabMaxwellFourLawSemanticallyClosed public

nLabMaxwellFourLawOneStepClosed :
  ∀ {Continuous : {A B : Set} → (A → B) → Set}
  {W :
    CanonicalLearnerHodgeMaxwellCompositionTheorem
      {Continuous = Continuous}}
  {Current Variation Action : Set}
  {Admissible : Variation → Set}
  {Stationary :
    MaxwellSolution
      (semantics (hodgeRepresentation W)) → Set}
  (B :
    NLabMaxwellFourLawSemanticallyClosed
      W
      Current
      Variation
      Action
      Admissible
      Stationary) →
  FourLawOneStepWitnessContract
    C.CanonicalFullLearnerState
    (MaxwellSolution
      (semantics (hodgeRepresentation W)))
    Current
    Variation
    Action
    Admissible
    Stationary
    (C.canonicalFullStep (kernel B))
    (step (semantics (hodgeRepresentation W)))
nLabMaxwellFourLawOneStepClosed B =
  nLabMaxwellFourLawOneStep
    W
    (kernel B)
    (semanticClosure B)

------------------------------------------------------------------------
-- Once the nLab semantic square is inhabited, autonomous-time transport
-- is already closed by the existing one-step conjugacy kernel.
------------------------------------------------------------------------

nLabMaxwellIterateConjugacy :
  ∀ {Continuous : {A B : Set} → (A → B) → Set}
  (W :
    CanonicalLearnerHodgeMaxwellCompositionTheorem
      {Continuous = Continuous})
  (K : C.CanonicalFullLearnerKernel) →
  ∀ n s →
  learnerToSolution W
    (iterateStep
      (C.canonicalFullStep K)
      n
      s)
  ≡
  iterateStep
    (step (semantics (hodgeRepresentation W)))
    n
    (learnerToSolution W s)
nLabMaxwellIterateConjugacy
  W
  K
  n
  s =
  iterateConjugacy
    (learnerToSolution W)
    (λ s →
      learnerStepConjugacy W K s)
    n
    s

nLabMaxwellIterateConjugacyClosed :
  ∀ {Continuous : {A B : Set} → (A → B) → Set}
  {W :
    CanonicalLearnerHodgeMaxwellCompositionTheorem
      {Continuous = Continuous}}
  {Current Variation Action : Set}
  {Admissible : Variation → Set}
  {Stationary :
    MaxwellSolution
      (semantics (hodgeRepresentation W)) → Set}
  (B :
    NLabMaxwellFourLawSemanticallyClosed
      W
      Current
      Variation
      Action
      Admissible
      Stationary) →
  ∀ n s →
  learnerToSolution W
    (iterateStep
      (C.canonicalFullStep (kernel B))
      n
      s)
  ≡
  iterateStep
    (step (semantics (hodgeRepresentation W)))
    n
    (learnerToSolution W s)
nLabMaxwellIterateConjugacyClosed B =
  nLabMaxwellIterateConjugacy
    W
    (kernel B)
    n
    s

------------------------------------------------------------------------
-- Single-file algebraic consistency package.
--
-- The statistical Law-IV representation and the nLab-guided four-law
-- witness are already proved independently.  This package composes those
-- existing proofs in this monolith: GRU injectivity, the closed four-law
-- witness, one-step physics/learner transport, and exact iterate transport.
-- It adds no physical inhabitant and no new axiom; an instance still requires
-- the explicit semantic closure B above.
------------------------------------------------------------------------

record NLabMaxwellFourLawGRUAlgebraicConsistencyTheorem
  {Continuous : {A B : Set} → (A → B) → Set}
  {W :
    CanonicalLearnerHodgeMaxwellCompositionTheorem
      {Continuous = Continuous}}
  {Current Variation Action : Set}
  {Admissible : Variation → Set}
  {Stationary :
    MaxwellSolution
      (semantics (hodgeRepresentation W)) → Set}
  (B :
    NLabMaxwellFourLawSemanticallyClosed
      W
      Current
      Variation
      Action
      Admissible
      Stationary) : Set₁ where
  constructor nLabMaxwellFourLawGRUAlgebraicConsistencyTheorem
  field
    statisticalRepresentation :
      CanonicalGRUStatisticalInjectivityTheorem
    statisticalInjective :
      ∀ {s t : C.GRUState} →
      canonicalGRUStatisticalEncode s ≡
      canonicalGRUStatisticalEncode t →
      s ≡ t
    statisticalStep :
      ∀ (s : C.GRUState) (x : C.Int8) →
      canonicalGRUStatisticalEncode (C.gruStep s x)
      ≡
      (C.gruStep s x ,
       (λ _ → C.hiddenState (C.gruStep s x)))
    fourLaw :
      FourLawOneStepWitnessContract
        C.CanonicalFullLearnerState
        (MaxwellSolution
          (semantics (hodgeRepresentation W)))
        Current
        Variation
        Action
        Admissible
        Stationary
        (C.canonicalFullStep (kernel B))
        (step (semantics (hodgeRepresentation W)))
    learnerSemantics :
      CanonicalMARLLawCompositionTheorem
    representation :
      ConnectedContinuousHodgeMaxwellGRURepresentationTheorem
        C.CanonicalFullLearnerState
    iterateTransport :
      ∀ n s →
      learnerToSolution W
        (iterateStep
          (C.canonicalFullStep (kernel B))
          n
          s)
      ≡
      iterateStep
        (step (semantics (hodgeRepresentation W)))
        n
        (learnerToSolution W s)

nLabMaxwellFourLawGRUAlgebraicConsistencyTheorem-from-closed :
  ∀ {Continuous : {A B : Set} → (A → B) → Set}
  {W :
    CanonicalLearnerHodgeMaxwellCompositionTheorem
      {Continuous = Continuous}}
  {Current Variation Action : Set}
  {Admissible : Variation → Set}
  {Stationary :
    MaxwellSolution
      (semantics (hodgeRepresentation W)) → Set}
  (B :
    NLabMaxwellFourLawSemanticallyClosed
      W
      Current
      Variation
      Action
      Admissible
      Stationary) →
  NLabMaxwellFourLawGRUAlgebraicConsistencyTheorem B
nLabMaxwellFourLawGRUAlgebraicConsistencyTheorem-from-closed B =
  nLabMaxwellFourLawGRUAlgebraicConsistencyTheorem
    canonical-gru-statistical-injectivity-theorem
    canonicalGRUStatisticalEncodeInjective
    canonicalGRUStatisticalStepConsequence
    (nLabMaxwellFourLawOneStepClosed B)
    (learnerSemantics W)
    (hodgeRepresentation W)
    (nLabMaxwellIterateConjugacyClosed B)


------------------------------------------------------------------------
-- Repository-wide semantic e-graph/A* closure.
--
-- Every surviving Agda module can be placed in an indexed semantic family.
-- The closure is unconditional at that semantic layer: any supplied sound
-- interpretation and any sound e-graph path produce exact equality.
-- A* costs remain search metadata, never proof evidence.
------------------------------------------------------------------------

canonical-repository-wide-agda-egraph-astar-closure :
  ∀ {Module : Set}
  (F : AgdaSemanticModuleFamily Module)
  (m : Module)
  {e f : Expression F m} →
  EGraphSemanticPath
    (semantics (closure F m))
    e
    f →
  interpret (semantics (closure F m)) e
  ≡
  interpret (semantics (closure F m)) f
canonical-repository-wide-agda-egraph-astar-closure =
  repositoryAgdaAStarSemanticClosure

canonical-unconditional-agda-egraph-astar-closure :
  UnconditionalAgdaEGraphAStarClosure
canonical-unconditional-agda-egraph-astar-closure =
  unconditional-agda-egraph-astar-closure


------------------------------------------------------------------------

f4-add-right-nonnegative :
  ∀ (n m : Nat) → n ≤ n + m
f4-add-right-nonnegative n zero = ≤-refl
f4-add-right-nonnegative n (suc m) =
  s≤s (f4-add-right-nonnegative n m)

record MegaGeneralizedWalrasianEquilibrium
  (State Price Allocation : Set) : Set₁ where
  constructor megaGeneralizedWalrasianEquilibrium
  field
    aggregate : (State → Allocation) → Allocation
    equilibrium : Price → Allocation → Set
    characterization : Price → Allocation → Set
    characterizationBridge :
      ∀ {p a} →
      characterization p a →
      equilibrium p a

open MegaGeneralizedWalrasianEquilibrium public

record GeneralizedWalrasianData
  (Agent Commodity Price Allocation : Set) : Set₁ where
  constructor generalizedWalrasianData
  field
    consumption : Agent → Set
    preference : Agent → Allocation → Allocation → Set
    budget : Price → Agent → Allocation → Set
    feasible : Allocation → Set
    marketClearing : Price → Allocation → Set
    equilibrium : Price → Allocation → Set
    characterization : Price → Allocation → Set
    characterizationFromEquilibrium :
      ∀ {p a} →
      equilibrium p a →
      characterization p a

open GeneralizedWalrasianData public

FiniteNonIIDPreference :
  ∀ {Agent Good : Set}
  (utility : Agent → (Good → Nat) → Nat) →
  Agent → (Agent → Good → Nat) → (Agent → Good → Nat) → Set
FiniteNonIIDPreference utility i x y =
  utility i (x i) ≤ utility i (y i)

record FiniteNonIIDGeneralizedEquilibrium
  (Agent Good : Set)
  (agents : List Agent)
  (goods : List Good)
  (utility : Agent → (Good → Nat) → Nat)
  (endowment : Agent → Good → Nat)
  (price : Good → Nat)
  (allocation : Agent → Good → Nat) : Set₁ where
  constructor finiteNonIIDGeneralizedEquilibrium
  field
    budgetOptimal :
      ∀ i bundle →
      BudgetFeasible
        goods
        price
        (endowment i)
        bundle →
      utility i bundle ≤
      utility i (allocation i)
    marketClearing :
      ∀ g →
      sumNat (map (λ i → allocation i g) agents) ≡
      sumNat (map (λ i → endowment i g) agents)

megaParetoOptimal :
  ∀ {Agent Allocation : Set}
  {weakPreference strictPreference :
    Agent → Allocation → Allocation → Set}
  (feasible : Allocation → Set) →
  Allocation → Set₁
megaParetoOptimal
  feasible
  a =
  feasible a ×
  (∀ {b : Allocation} →
   feasible b →
   MegaParetoImprovement
     Agent
     Allocation
     weakPreference
     strictPreference
     b
     a →
   ⊥)

record MegaFirstWelfareTheoremConditions
  (Agent Price Allocation : Set)
  (weakPreference strictPreference :
    Agent → Allocation → Allocation → Set)
  (feasible : Allocation → Set)
  (budget : Price → Agent → Allocation → Set)
  (equilibrium : Price → Allocation → Set)
  (p : Price)
  (a : Allocation) : Set₁ where
  constructor megaFirstWelfareTheoremConditions
  field
    equilibriumWitness :
      equilibrium p a
    feasibleWitness :
      feasible a
    noStrictAffordableAlternative :
      ∀ i b →
      budget p i b →
      ¬ strictPreference i b a
    paretoImprovementAffordability :
      ∀ {b : Allocation} →
      feasible b →
      (improvement :
        MegaParetoImprovement
          Agent
          Allocation
          weakPreference
          strictPreference
          b
          a) →
      budget p
        (proj₁ (strictlyBetter improvement))
        b

open MegaFirstWelfareTheoremConditions public

megaNatNoStrictBack :
  ∀ {n : Nat} →
  suc n ≤ n →
  ⊥
megaNatNoStrictBack {zero} ()
megaNatNoStrictBack {suc n} (s≤s h) =
  megaNatNoStrictBack h

megaNatStrictCostContradiction :
  ∀ {m n : Nat} →
  n ≤ m →
  m < n →
  ⊥
megaNatStrictCostContradiction hle hlt =
  megaNatNoStrictBack (≤-trans hlt hle)

megaNoStrictAffordableAlternative-from-demand-cost :
  ∀ {Agent Price Allocation : Set}
  {weakPreference strictPreference :
    Agent → Allocation → Allocation → Set}
  {feasible : Allocation → Set}
  {budget : Price → Agent → Allocation → Set}
  {equilibrium : Price → Allocation → Set}
  {cost : Price → Agent → Allocation → Nat}
  {p : Price}
  {a : Allocation} →
  MegaDemandCostKernel
    Agent
    Price
    Allocation
    weakPreference
    strictPreference
    feasible
    budget
    equilibrium
    cost
    p
    a →
  ∀ i b →
  budget p i b →
  ¬ strictPreference i b a
megaNoStrictAffordableAlternative-from-demand-cost kernel i b affordable =
  λ strictlyPreferred →
    megaNatStrictCostContradiction
      (budgetCostBound kernel i b affordable)
      (strictlyPreferredCostly kernel i b strictlyPreferred)

FiniteNonIIDStrictPreference :
  ∀ {Agent Good : Set}
  (utility : Agent → (Good → Nat) → Nat) →
  Agent → (Agent → Good → Nat) → (Agent → Good → Nat) → Set
FiniteNonIIDStrictPreference utility i x y =
  utility i (y i) < utility i (x i)

record FiniteNonIIDDemandCostClosure
  (Agent Good : Set)
  (agents : List Agent)
  (goods : List Good)
  (utility : Agent → (Good → Nat) → Nat)
  (endowment : Agent → Good → Nat)
  (price : Good → Nat)
  (allocation : Agent → Good → Nat) : Set₁ where
  constructor finiteNonIIDDemandCostClosure
  field
    equilibriumWitness :
      FiniteNonIIDGeneralizedEquilibrium
        Agent
        Good
        agents
        goods
        utility
        endowment
        price
        allocation

    preferredCostly :
      ∀ i x y →
      utility i (x i) ≤ utility i (y i) →
      bundleCost goods price (y i) ≤
      bundleCost goods price (x i)

    strictlyPreferredCostly :
      ∀ i x y →
      utility i (y i) < utility i (x i) →
      bundleCost goods price (y i) <
      bundleCost goods price (x i)

    paretoImprovementAffordability :
      ∀ {b : Agent → Good → Nat} →
      (improvement :
        MegaParetoImprovement
          Agent
          (Agent → Good → Nat)
          (FiniteNonIIDPreference utility)
          (FiniteNonIIDStrictPreference utility)
          b
          allocation) →
      BudgetFeasible
        goods
        price
        (endowment
          (proj₁ (strictlyBetter improvement)))
        b

finiteNonIIDBudgetCostBound :
  ∀ {Agent Good : Set}
  {goods : List Good}
  {price : Good → Nat}
  {endowment : Agent → Good → Nat}
  {i : Agent}
  {bundle : Good → Nat} →
  BudgetFeasible goods price (endowment i) bundle →
  bundleCost goods price bundle ≤
  bundleCost goods price (endowment i)
finiteNonIIDBudgetCostBound affordable = affordable

finiteNonIIDDemandCostKernel :
  ∀ {Agent Good : Set}
  {agents : List Agent}
  {goods : List Good}
  {utility : Agent → (Good → Nat) → Nat}
  {endowment : Agent → Good → Nat}
  {price : Good → Nat}
  {allocation : Agent → Good → Nat} →
  FiniteNonIIDDemandCostClosure
    Agent
    Good
    agents
    goods
    utility
    endowment
    price
    allocation →
  MegaDemandCostKernel
    Agent
    (Good → Nat)
    (Agent → Good → Nat)
    (FiniteNonIIDPreference utility)
    (FiniteNonIIDStrictPreference utility)
    (λ a →
      ∀ g →
      sumNat (map (λ i → a i g) agents) ≡
      sumNat (map (λ i → endowment i g) agents))
    (λ p i bundle → BudgetFeasible goods p (endowment i) bundle)
    (λ p a →
      FiniteNonIIDGeneralizedEquilibrium
        Agent
        Good
        agents
        goods
        utility
        endowment
        p
        a)
    (λ p i bundle → bundleCost goods p (bundle i))
    price
    allocation
finiteNonIIDDemandCostKernel closure =
  megaDemandCostKernel
    (equilibriumWitness closure)
    (marketClearing (equilibriumWitness closure))
    (λ i b preferred →
      preferredCostly closure i b allocation preferred)
    (λ i b strictlyPreferred →
      strictlyPreferredCostly closure i b allocation strictlyPreferred)
    (λ i b affordable →
      finiteNonIIDBudgetCostBound affordable)
    (λ {b} _ improvement →
      paretoImprovementAffordability closure improvement)

record MegaSecondWelfareTheoremBoundaryCounterexample : Set₁ where
  constructor megaSecondWelfareTheoremBoundaryCounterexample
  field
    Price : Set
    Allocation : Set
    paretoOptimal : Allocation → Set₁
    equilibrium : Price → Allocation → Set
    allocationWitness : Allocation
    paretoWitness :
      paretoOptimal allocationWitness
    noSupportingPrice :
      ¬ Σ Price (λ p → equilibrium p allocationWitness)

open MegaSecondWelfareTheoremBoundaryCounterexample public

megaSecondWelfareTheorem-boundary-counterexample :
  MegaSecondWelfareTheoremBoundaryCounterexample
megaSecondWelfareTheorem-boundary-counterexample =
  megaSecondWelfareTheoremBoundaryCounterexample
    ⊥
    ⊤
    (λ _ → ⊤)
    (λ _ _ → ⊥)
    tt
    tt
    (λ { (_ , e) → e })

record MegaNoStrictAffordableAlternativeBoundary
  (Agent Price Allocation : Set)
  (strictPreference :
    Agent → Allocation → Allocation → Set)
  (budget : Price → Agent → Allocation → Set)
  (p : Price)
  (a : Allocation) : Set₁ where
  constructor megaNoStrictAffordableAlternativeBoundary
  field
    demandOptimality :
      ∀ i b →
      budget p i b →
      ¬ strictPreference i b a

megaNoStrictAffordableAlternative-is-demand-optimality :
  ∀ {Agent Price Allocation : Set}
  {strictPreference :
    Agent → Allocation → Allocation → Set}
  {budget : Price → Agent → Allocation → Set}
  {p : Price} {a : Allocation} →
  MegaNoStrictAffordableAlternativeBoundary
    Agent Price Allocation strictPreference budget p a →
  (∀ i b →
    budget p i b →
    ¬ strictPreference i b a)
megaNoStrictAffordableAlternative-is-demand-optimality boundary =
  demandOptimality boundary

GeneralizedWalrasianEquilibrium :
  Set → Set → Set → Set₁
GeneralizedWalrasianEquilibrium =
  MegaGeneralizedWalrasianEquilibrium

generalizedWalrasianEquilibrium :
  ∀ {State Price Allocation : Set} →
  (encode : State → Price) →
  (equilibrium : Price → Allocation → Set) →
  (feasibility : Price → Allocation → Set) →
  (characterize :
    ∀ {p a} →
    equilibrium p a →
    feasibility p a) →
  GeneralizedWalrasianEquilibrium State Price Allocation
generalizedWalrasianEquilibrium =
  megaGeneralizedWalrasianEquilibrium

ProductionSet : Set → Set
ProductionSet ProductionPlan = ProductionPlan → Set

record CompetitiveProductionEconomy
  (Agent Firm Commodity Price Consumption ProductionPlan : Set) : Set₁ where
  constructor competitiveProductionEconomy
  field
    endowment : Agent → Consumption
    preference : Agent → Consumption → Consumption → Set
    consumptionFeasible : Agent → Consumption → Set
    productionSet : Firm → ProductionPlan → Set
    ownershipShare : Agent → Firm → Set
    profitMaximization :
      Firm → Price → ProductionPlan → Set
    resourceBalance :
      Commodity → Set

record CompetitiveWalrasianEquilibriumWithProduction
  (Agent Firm Commodity Price Consumption ProductionPlan : Set)
  (E : CompetitiveProductionEconomy
    Agent Firm Commodity Price Consumption ProductionPlan) : Set₁ where
  constructor competitiveWalrasianEquilibriumWithProduction
  field
    price : Price
    consumption : Agent → Consumption
    production : Firm → ProductionPlan
    consumerOptimality :
      ∀ i →
      CompetitiveProductionEconomy.preference E i
        (consumption i)
        (consumption i)
    productionFeasibility :
      ∀ j →
      CompetitiveProductionEconomy.productionSet E
        j
        (production j)
    productionOptimality :
      ∀ j →
      CompetitiveProductionEconomy.profitMaximization E
        j
        price
        (production j)
    consumptionFeasibility :
      ∀ i →
      CompetitiveProductionEconomy.consumptionFeasible E
        i
        (consumption i)
    marketClearing :
      ∀ c →
      CompetitiveProductionEconomy.resourceBalance E c

record ProductionFeasibilityWitness
  (Firm ProductionPlan : Set)
  (feasible : Firm → ProductionPlan → Set)
  (production : Firm → ProductionPlan) : Set₁ where
  constructor productionFeasibilityWitness
  field
    witness :
      ∀ j →
      feasible j (production j)

record FirmProfitOptimalityWitness
  (Firm Price ProductionPlan : Set)
  (optimal : Firm → Price → ProductionPlan → Set)
  (price : Price)
  (production : Firm → ProductionPlan) : Set₁ where
  constructor firmProfitOptimalityWitness
  field
    witness :
      ∀ j →
      optimal j price (production j)

record ConsumerOptimalityWitness
  (Agent Consumption : Set)
  (optimal : Agent → Consumption → Set)
  (consumption : Agent → Consumption) : Set₁ where
  constructor consumerOptimalityWitness
  field
    witness :
      ∀ i →
      optimal i (consumption i)

record ConsumptionFeasibilityWitness
  (Agent Consumption : Set)
  (feasible : Agent → Consumption → Set)
  (consumption : Agent → Consumption) : Set₁ where
  constructor consumptionFeasibilityWitness
  field
    witness :
      ∀ i →
      feasible i (consumption i)

record AggregateFeasibilityWitness
  (Allocation : Set)
  (feasible : Allocation → Set)
  (allocation : Allocation) : Set₁ where
  constructor aggregateFeasibilityWitness
  field
    witness :
      feasible allocation

record MarketClearingWitness
  (Price Allocation : Set)
  (marketClearing : Price → Allocation → Set)
  (price : Price)
  (allocation : Allocation) : Set₁ where
  constructor marketClearingWitness
  field
    witness :
      marketClearing price allocation

record SupportingPriceWitness
  (Price Allocation : Set)
  (supports : Price → Allocation → Set)
  (price : Price)
  (allocation : Allocation) : Set₁ where
  constructor supportingPriceWitness
  field
    witness :
      supports price allocation

applyNormPairReplacements :
  ∀ {A : Set} →
  List C.NormPair →
  C.FullLearnerState A →
  C.FullLearnerState A
applyNormPairReplacements [] s = s
applyNormPairReplacements (n ∷ ns) s =
  applyNormPairReplacements ns (C.replaceNorm s n)

normPairReplacementRelation :
  ∀ {A : Set} →
  C.FullLearnerState A →
  C.FullLearnerState A →
  Set
normPairReplacementRelation s t =
  Σ C.NormPair (λ n → C.replaceNorm s n ≡ t)

applyNormPairReplacements-collapse :
  ∀ {A : Set}
  (s : C.FullLearnerState A)
  (ns : List C.NormPair) →
  Σ C.NormPair
    (λ n → C.replaceNorm s n
      ≡ applyNormPairReplacements ns s)
applyNormPairReplacements-collapse s [] =
  C.norm s , refl
applyNormPairReplacements-collapse s (n ∷ ns)
  with applyNormPairReplacements-collapse
    (C.replaceNorm s n)
    ns
... | m , eq = m , eq

normPairReplacementRelation-generated :
  ∀ {A : Set}
  (s t : C.FullLearnerState A) →
  (Σ (List C.NormPair)
    (λ ns →
      applyNormPairReplacements ns s ≡ t)) →
  normPairReplacementRelation s t
normPairReplacementRelation-generated s t (ns , eq)
  with applyNormPairReplacements-collapse s ns
... | n , collapse =
  n , trans collapse eq

normPairReplacementRelation-refl :
  ∀ {A : Set}
  (s : C.FullLearnerState A) →
  normPairReplacementRelation s s
normPairReplacementRelation-refl s =
  C.norm s , refl

normPairReplacementRelation-sym :
  ∀ {A : Set}
  {s t : C.FullLearnerState A} →
  normPairReplacementRelation s t →
  normPairReplacementRelation t s
normPairReplacementRelation-sym (n , eq) =
  C.norm _ ,
  trans
    (sym
      (cong
        (λ x → C.replaceNorm x (C.norm _))
        eq))
    refl

normPairReplacementRelation-trans :
  ∀ {A : Set}
  {s t u : C.FullLearnerState A} →
  normPairReplacementRelation s t →
  normPairReplacementRelation t u →
  normPairReplacementRelation s u
normPairReplacementRelation-trans
  (n , st)
  (m , tu) =
  m ,
  trans
    (cong
      (λ x → C.replaceNorm x m)
      st)
    tu

canonicalPolicy-factors-through-NormPair :
  ∀ {A : Set}
  (K : C.FullLearnerKernel A)
  {s t : C.FullLearnerState A} →
  normPairReplacementRelation s t →
  C.canonicalPolicy K t ≡ C.canonicalPolicy K s
canonicalPolicy-factors-through-NormPair
  K
  (n , eq) =
  trans
    (sym (cong (C.canonicalPolicy K) eq))
    (C.canonicalPolicy-norm-invariant _ _ n)

canonicalNormPairQuotient-step-compatible :
  ∀ {A : Set}
  (K : C.FullLearnerKernel A)
  {s t : C.FullLearnerState A} →
  normPairReplacementRelation s t →
  normPairReplacementRelation
    (C.canonicalFullStep K s)
    (C.canonicalFullStep K t)
canonicalNormPairQuotient-step-compatible
  K
  (n , eq) =
  n ,
  trans
    (sym (canonicalFullStep-replaceNorm K _ n))
    (cong (C.canonicalFullStep K) eq)

canonicalNormPairQuotient-iterate-compatible :
  ∀ {A : Set}
  (K : C.FullLearnerKernel A)
  (n : Nat)
  {s t : C.FullLearnerState A} →
  normPairReplacementRelation s t →
  normPairReplacementRelation
    (C.iterateCanonical K n s)
    (C.iterateCanonical K n t)
canonicalNormPairQuotient-iterate-compatible
  K
  zero
  relation =
  relation
canonicalNormPairQuotient-iterate-compatible
  K
  (suc n)
  relation =
  canonicalNormPairQuotient-iterate-compatible
    K
    n
    (canonicalNormPairQuotient-step-compatible K relation)

record FactorTransitionWitness
  (State Factor : Set)
  (step : State → State)
  (observe : State → Factor) : Set₁ where
  constructor factorTransitionWitness
  field
    factorStep : Factor → Factor
    observe-step :
      ∀ s →
      observe (step s) ≡
      factorStep (observe s)

open FactorTransitionWitness public

factorTransitionAfterIterate :
  ∀ {State Factor : Set}
  {step : State → State}
  {observe : State → Factor}
  (W :
    FactorTransitionWitness
      State
      Factor
      step
      observe)
  (n : Nat)
  (s : State) →
  observe (iterateIsomorphism step n s) ≡
  iterateIsomorphism (factorStep W) n (observe s)
factorTransitionAfterIterate W zero s =
  refl
factorTransitionAfterIterate W (suc n) s =
  trans
    (factorTransitionAfterIterate W n (step s))
    (cong
      (iterateIsomorphism (factorStep W) n)
      (observe-step W s))

record RelationFactorTransitionWitness
  (State Factor : Set)
  (step : State → State)
  (related : State → State → Set)
  (observe : State → Factor) : Set₁ where
  constructor relationFactorTransitionWitness
  field
    transition :
      FactorTransitionWitness
        State
        Factor
        step
        observe
    observeRespects :
      ∀ {s t} →
      related s t →
      observe s ≡ observe t
    relationStepPreserved :
      ∀ {s t} →
      related s t →
      related
        (step s)
        (step t)

canonicalPolicyFactorTransition :
  ∀ {A : Set}
  (K : C.FullLearnerKernel A)
  (factorStep : Nat → Nat)
  (factorStepCommutes :
    ∀ s →
    C.canonicalPolicy K (C.canonicalFullStep K s) ≡
    factorStep (C.canonicalPolicy K s)) →
  RelationFactorTransitionWitness
    (C.FullLearnerState A)
    Nat
    (C.canonicalFullStep K)
    normPairReplacementRelation
    (C.canonicalPolicy K)
canonicalPolicyFactorTransition
  K
  factorStep
  factorStepCommutes =
  relationFactorTransitionWitness
    (factorTransitionWitness
      factorStep
      factorStepCommutes)
    (canonicalPolicy-factors-through-NormPair K)
    (canonicalNormPairQuotient-step-compatible K)

record CanonicalNormPairQuotientFactorTransitionTheorem : Set₁ where
  constructor canonicalNormPairQuotientFactorTransitionTheorem
  field
    generatedOrbit :
      ∀ {A : Set}
      (s t : C.FullLearnerState A) →
      (Σ (List C.NormPair)
        (λ ns →
          applyNormPairReplacements ns s ≡ t)) →
      normPairReplacementRelation s t

    quotientReflexive :
      ∀ {A : Set}
      (s : C.FullLearnerState A) →
      normPairReplacementRelation s s

    quotientSymmetric :
      ∀ {A : Set}
      {s t : C.FullLearnerState A} →
      normPairReplacementRelation s t →
      normPairReplacementRelation t s

    quotientTransitive :
      ∀ {A : Set}
      {s t u : C.FullLearnerState A} →
      normPairReplacementRelation s t →
      normPairReplacementRelation t u →
      normPairReplacementRelation s u

    policyFactors :
      ∀ {A : Set}
      (K : C.FullLearnerKernel A)
      {s t : C.FullLearnerState A} →
      normPairReplacementRelation s t →
      C.canonicalPolicy K t ≡ C.canonicalPolicy K s

    transitionCompatible :
      ∀ {A : Set}
      (K : C.FullLearnerKernel A)
      {s t : C.FullLearnerState A} →
      normPairReplacementRelation s t →
      normPairReplacementRelation
        (C.canonicalFullStep K s)
        (C.canonicalFullStep K t)

    iterateCompatible :
      ∀ {A : Set}
      (K : C.FullLearnerKernel A)
      (n : Nat)
      {s t : C.FullLearnerState A} →
      normPairReplacementRelation s t →
      normPairReplacementRelation
        (C.iterateCanonical K n s)
        (C.iterateCanonical K n t)

canonical-normPair-quotient-factor-transition-theorem :
  CanonicalNormPairQuotientFactorTransitionTheorem
canonical-normPair-quotient-factor-transition-theorem =
  canonicalNormPairQuotientFactorTransitionTheorem
    normPairReplacementRelation-generated
    normPairReplacementRelation-refl
    normPairReplacementRelation-sym
    normPairReplacementRelation-trans
    canonicalPolicy-factors-through-NormPair
    canonicalNormPairQuotient-step-compatible
    canonicalNormPairQuotient-iterate-compatible

record CanonicalF4NormPairUnconditionalFactorStabilityTheorem : Set₁ where
  constructor canonicalF4NormPairUnconditionalFactorStabilityTheorem
  field
    f4Stability :
      CanonicalF4GlobalOptimizerStabilityTheorem

    normPairFactorTransition :
      CanonicalNormPairQuotientFactorTransitionTheorem

    policyFactorization :
      ∀ {A : Set}
        (K : C.FullLearnerKernel A)
        {s t : C.FullLearnerState A} →
        normPairReplacementRelation s t →
        C.canonicalPolicy K t ≡ C.canonicalPolicy K s

    transitionFactorization :
      ∀ {A : Set}
        (K : C.FullLearnerKernel A)
        {s t : C.FullLearnerState A} →
        normPairReplacementRelation s t →
        normPairReplacementRelation
          (C.canonicalFullStep K s)
          (C.canonicalFullStep K t)

    iterateFactorization :
      ∀ {A : Set}
        (K : C.FullLearnerKernel A)
        (n : Nat)
        {s t : C.FullLearnerState A} →
        normPairReplacementRelation s t →
        normPairReplacementRelation
          (C.iterateCanonical K n s)
          (C.iterateCanonical K n t)

canonical-f4-normPair-unconditional-factor-stability-theorem :
  CanonicalF4NormPairUnconditionalFactorStabilityTheorem
canonical-f4-normPair-unconditional-factor-stability-theorem =
  canonicalF4NormPairUnconditionalFactorStabilityTheorem
    canonical-f4-global-optimizer-stability-theorem
    canonical-normPair-quotient-factor-transition-theorem
    canonicalPolicy-factors-through-NormPair
    canonicalNormPairQuotient-step-compatible
    canonicalNormPairQuotient-iterate-compatible

record CanonicalF4NormPairIterateFactorStabilityTheorem : Set₁ where
  constructor canonicalF4NormPairIterateFactorStabilityTheorem
  field
    oneStepStability :
      CanonicalF4NormPairUnconditionalFactorStabilityTheorem

    normPairWeightPlusOneIterate :
      ∀ {A : Set}
      (K : C.FullLearnerKernel A)
      (n : Nat)
      (s : C.FullLearnerState A) →
      C.normPairWeightPlusOne
        (C.norm (C.iterateCanonical K n s))
      ≡
      C.normPairWeightPlusOne (C.norm s)

    persistentGRUIterate :
      ∀ {A : Set}
      (K : C.FullLearnerKernel A)
      (n : Nat)
      (s : C.FullLearnerState A) →
      C.persistentGRU
        (C.gru (C.iterateCanonical K n s))
      ≡
      C.persistentGRU (C.gru s)

    quotientIterateFactorization :
      ∀ {A : Set}
      (K : C.FullLearnerKernel A)
      (n : Nat)
      {s t : C.FullLearnerState A} →
      normPairReplacementRelation s t →
      normPairReplacementRelation
        (C.iterateCanonical K n s)
        (C.iterateCanonical K n t)

canonical-f4-normPair-iterate-factor-stability-theorem :
  CanonicalF4NormPairIterateFactorStabilityTheorem
canonical-f4-normPair-iterate-factor-stability-theorem =
  canonicalF4NormPairIterateFactorStabilityTheorem
    canonical-f4-normPair-unconditional-factor-stability-theorem
    canonicalNormPair-afterFullStep-iterate
    canonicalPersistentGRU-afterFullStep-iterate
    canonicalNormPairQuotient-iterate-compatible

record RecursiveRadnerData
  (State Agent Commodity Asset Price Allocation Portfolio : Set)
  (priceProcess : State → Price)
  (allocationProcess : State → Agent → Allocation)
  (portfolioProcess : State → Agent → Portfolio) : Set₁ where
  constructor recursiveRadnerData
  field
    transition : State → State
    feasible : State → Agent → Allocation → Portfolio → Set
    optimal : State → Agent → Allocation → Portfolio → Set
    commodityMarketClearing : State → Set
    assetMarketClearing : State → Set
    priceRecursion : State → Price → Set
    allocationRecursion : State → Agent → Allocation → Set
    portfolioRecursion : State → Agent → Portfolio → Set

record RecursiveRadnerEquilibrium
  (State Agent Commodity Asset Price Allocation Portfolio : Set)
  (priceProcess : State → Price)
  (allocationProcess : State → Agent → Allocation)
  (portfolioProcess : State → Agent → Portfolio)
  (D :
    RecursiveRadnerData
      State Agent Commodity Asset Price Allocation Portfolio
      priceProcess
      allocationProcess
      portfolioProcess) : Set₁ where
  constructor recursiveRadnerEquilibrium
  field
    feasibility :
      ∀ s i →
      RecursiveRadnerData.feasible D
        s i
        (allocationProcess s i)
        (portfolioProcess s i)

    optimality :
      ∀ s i →
      RecursiveRadnerData.optimal D
        s i
        (allocationProcess s i)
        (portfolioProcess s i)

    commodityClearing :
      ∀ s →
      RecursiveRadnerData.commodityMarketClearing D s

    assetClearing :
      ∀ s →
      RecursiveRadnerData.assetMarketClearing D s

    priceRecursionWitness :
      ∀ s →
      RecursiveRadnerData.priceRecursion D
        s
        (priceProcess s)

    allocationRecursionWitness :
      ∀ s i →
      RecursiveRadnerData.allocationRecursion D
        s i
        (allocationProcess s i)

    portfolioRecursionWitness :
      ∀ s i →
      RecursiveRadnerData.portfolioRecursion D
        s i
        (portfolioProcess s i)

record RecursiveRadnerExistence
  (State Agent Commodity Asset Price Allocation Portfolio : Set) : Set₁ where
  constructor recursiveRadnerExistence
  field
    priceProcess : State → Price
    allocationProcess : State → Agent → Allocation
    portfolioProcess : State → Agent → Portfolio

    data :
      RecursiveRadnerData
        State Agent Commodity Asset Price Allocation Portfolio
        priceProcess
        allocationProcess
        portfolioProcess

    equilibrium :
      RecursiveRadnerEquilibrium
        State Agent Commodity Asset Price Allocation Portfolio
        priceProcess
        allocationProcess
        portfolioProcess
        data

RecursiveRadnerPrice :
  ∀ {State Price : Set} →
  Set
RecursiveRadnerPrice {State} {Price} =
  State → Price

RecursiveRadnerAllocation :
  ∀ {State Agent Allocation Portfolio : Set} →
  Set
RecursiveRadnerAllocation {State} {Agent} {Allocation} {Portfolio} =
  (State → Agent → Allocation)
  ×
  (State → Agent → Portfolio)

recursiveRadner-generalized :
  ∀ {State Agent Commodity Asset Price Allocation Portfolio : Set} →
  MegaGeneralizedWalrasianEquilibrium
    State
    RecursiveRadnerPrice
    (RecursiveRadnerAllocation
      {State = State}
      {Agent = Agent}
      {Allocation = Allocation}
      {Portfolio = Portfolio})
recursiveRadner-generalized =
  megaGeneralizedWalrasianEquilibrium
    (λ x → x)
    (λ pricePair allocationPair →
      Σ (RecursiveRadnerData
          State
          Agent
          Commodity
          Asset
          Price
          Allocation
          Portfolio
          (proj₁ allocationPair)
          (proj₂ allocationPair))
        (λ D →
          RecursiveRadnerEquilibrium
            State
            Agent
            Commodity
            Asset
            Price
            Allocation
            Portfolio
            (proj₁ allocationPair)
            (proj₂ allocationPair)
            D))
    (λ pricePair allocationPair →
      Σ (RecursiveRadnerData
          State
          Agent
          Commodity
          Asset
          Price
          Allocation
          Portfolio
          (proj₁ allocationPair)
          (proj₂ allocationPair))
        (λ D →
          RecursiveRadnerEquilibrium
            State
            Agent
            Commodity
            Asset
            Price
            Allocation
            Portfolio
            (proj₁ allocationPair)
            (proj₂ allocationPair)
            D))
    (λ {pricePair} {allocationPair} h → h)

megaNoEquilibriumGeneralizedWalrasian :
  MegaGeneralizedWalrasianEquilibrium ⊤ ⊤ ⊤
megaNoEquilibriumGeneralizedWalrasian =
  megaGeneralizedWalrasianEquilibrium
    (λ _ → tt)
    (λ _ _ → ⊥)
    (λ _ _ → ⊥)
    (λ ())

megaNoEquilibriumWitness :
  ¬ Σ ⊤
    (λ p → Σ ⊤
      (λ a →
        equilibrium
          megaNoEquilibriumGeneralizedWalrasian
          p
          a))
megaNoEquilibriumWitness
  (p , a , witness) =
  witness

noUnconditionalMegaGeneralizedWalrasianExistence :
  ¬
    (∀ {State Price Allocation : Set}
      (D : MegaGeneralizedWalrasianEquilibrium
        State Price Allocation) →
      Σ Price
        (λ p →
          Σ Allocation
            (λ a → equilibrium D p a)))
noUnconditionalMegaGeneralizedWalrasianExistence
  theorem =
  megaNoEquilibriumWitness
    (theorem megaNoEquilibriumGeneralizedWalrasian)

megaNoEquilibriumWalrasianSquare :
  MegaWalrasianGlobalSquareConjugacy
    ⊤
    ⊤
    ⊤
    (λ _ → tt)
    (λ _ → tt)
    (λ x → x)
    (λ x → x)
    (λ x → x)
    (λ x → x)
megaNoEquilibriumWalrasianSquare =
  megaWalrasianGlobalSquareConjugacy
    (λ _ → refl)
    (λ _ → refl)
    (λ _ → refl)

megaNoEquilibriumF4NormPairEconomicWitness :
  ¬
    Σ ⊤
      (λ p →
        Σ ⊤
          (λ a →
            equilibrium
              megaNoEquilibriumGeneralizedWalrasian
              p
              a))
megaNoEquilibriumF4NormPairEconomicWitness
  (p , a , witness) =
  witness

noUnconditionalMegaWalrasianExistenceAfterF4NormPairFactorStability :
  ¬
    (∀ {State Price Allocation : Set}
      (D : MegaGeneralizedWalrasianEquilibrium
        State
        Price
        Allocation) →
      Σ Price
        (λ p →
          Σ Allocation
            (λ a →
              equilibrium D p a)))
noUnconditionalMegaWalrasianExistenceAfterF4NormPairFactorStability
  theorem =
  megaNoEquilibriumWitness
    (theorem megaNoEquilibriumGeneralizedWalrasian)


------------------------------------------------------------------------
-- Generic strict-progress and carrier-polymorphic frontier core.
-- Kept in this monolith so there is one authoritative theorem source.
------------------------------------------------------------------------

iterateStep :
  ∀ {State : Set} →
  (State → State) →
  Nat →
  State →
  State
iterateStep step zero s = s
iterateStep step (suc n) s = step (iterateStep step n s)

record StrictProgressWitness
  (State Measure : Set)
  (step : State → State)
  (_<_ : Measure → Measure → Set) : Set₁ where
  constructor strictProgressWitness
  field
    measure : State → Measure
    stepProgress :
      ∀ s →
      measure s < measure (step s)
    transitive :
      ∀ {a b c} →
      a < b →
      b < c →
      a < c
    irreflexive :
      ∀ a → ¬ (a < a)

record StrictProgressRelation
  (Measure : Set)
  (_<_ : Measure → Measure → Set) : Set₁ where
  constructor strictProgressRelation
  field
    isTransitive :
      ∀ {a b c} →
      a < b →
      b < c →
      a < c
    isIrreflexive :
      ∀ a → ¬ (a < a)

strictProgressRelation-from-witness :
  ∀ {State Measure : Set}
  {step : State → State}
  {_<_ : Measure → Measure → Set}
  (W : StrictProgressWitness State Measure step _<_) →
  StrictProgressRelation Measure _<_
strictProgressRelation-from-witness W =
  strictProgressRelation
    (transitive W)
    (irreflexive W)

strictProgressWitness-from-relation :
  ∀ {State Measure : Set}
  {step : State → State}
  {_<_ : Measure → Measure → Set}
  (R : StrictProgressRelation Measure _<_)
  (measure : State → Measure)
  (stepProgress :
    ∀ s → measure s < measure (step s)) →
  StrictProgressWitness State Measure step _<_
strictProgressWitness-from-relation R measure stepProgress =
  strictProgressWitness
    measure
    stepProgress
    (StrictProgressRelation.isTransitive R)
    (StrictProgressRelation.isIrreflexive R)

open StrictProgressWitness public

strictProgressAfterIterate :
  ∀ {State Measure : Set}
  {step : State → State}
  {_<_ : Measure → Measure → Set}
  (W : StrictProgressWitness State Measure step _<_)
  (n : Nat)
  (s : State) →
  measure W s <
  measure W (iterateStep step (suc n) s)
strictProgressAfterIterate W zero s =
  stepProgress W s
strictProgressAfterIterate W (suc n) s =
  transitive W
    (stepProgress W s)
    (strictProgressAfterIterate W n (step s))

noPositiveFiniteCycleFromStrictProgress :
  ∀ {State Measure : Set}
  {step : State → State}
  {_<_ : Measure → Measure → Set}
  (W : StrictProgressWitness State Measure step _<_)
  (n : Nat)
  (s : State) →
  iterateStep step (suc n) s ≡ s →
  ⊥
noPositiveFiniteCycleFromStrictProgress W n s eq =
  irreflexive W
    (measure W s)
    (subst
      (λ t → measure W s < measure W t)
      eq
      (strictProgressAfterIterate W n s))


record NatSuccessorProgressWitness
  (State : Set)
  (step : State → State)
  (measure : State → Nat) : Set₁ where
  constructor natSuccessorProgressWitness
  field
    successor :
      ∀ s →
      measure (step s) ≡ suc (measure s)

open NatSuccessorProgressWitness public

sucInjective :
  ∀ {m n : Nat} → suc m ≡ suc n → m ≡ n
sucInjective refl = refl

natPlusLeftCancel :
  ∀ (k m n : Nat) → k + m ≡ k + n → m ≡ n
natPlusLeftCancel zero m n eq = eq
natPlusLeftCancel (suc k) m n eq =
  natPlusLeftCancel k m n (sucInjective eq)

successorMeasureAfterIterate :
  ∀ {State : Set}
  {step : State → State}
  {measure : State → Nat}
  (W : NatSuccessorProgressWitness State step measure)
  (n : Nat)
  (s : State) →
  measure (iterateStep step n s) ≡ measure s + n
successorMeasureAfterIterate W zero s =
  sym (+-identityʳ (measure W s))
successorMeasureAfterIterate W (suc n) s =
  trans
    (successor W (iterateStep (step W) n s))
    (trans
      (cong suc (successorMeasureAfterIterate W n s))
      (sym (+-suc (measure W s) n)))

successorMeasureOrbitInjective :
  ∀ {State : Set}
  {step : State → State}
  {measure : State → Nat}
  (W : NatSuccessorProgressWitness State step measure)
  (s : State)
  {m n : Nat} →
  iterateStep step m s ≡ iterateStep step n s →
  m ≡ n
successorMeasureOrbitInjective W s {m} {n} eq =
  natPlusLeftCancel
    (measure W s)
    m
    n
    (trans
      (sym (successorMeasureAfterIterate W m s))
      (trans
        (cong (measure W) eq)
        (successorMeasureAfterIterate W n s)))

natSucProgress : ∀ n → n < suc n
natSucProgress zero = s≤s z≤n
natSucProgress (suc n) = s≤s (natSucProgress n)

canonicalTotalCountStepProgress :
  ∀ {A : Set}
  (K : C.FullLearnerKernel A)
  (s : C.FullLearnerState A) →
  C.totalCount (C.lcbCounts s) <
  C.totalCount (C.lcbCounts (C.canonicalFullStep K s))
canonicalTotalCountStepProgress K s =
  subst
    (λ t → C.totalCount (C.lcbCounts s) < t)
    (C.canonicalTotalCountStep K s)
    (natSucProgress (C.totalCount (C.lcbCounts s)))

canonicalTotalCountStrictProgress :
  ∀ {A : Set}
  (K : C.FullLearnerKernel A) →
  StrictProgressWitness
    (C.FullLearnerState A)
    Nat
    (C.canonicalFullStep K)
    _<_
canonicalTotalCountStrictProgress K =
  strictProgressWitness
    (λ s → C.totalCount (C.lcbCounts s))
    (λ s → canonicalTotalCountStepProgress K s)
    <-trans
    <-irrefl

canonicalNoPositiveCycleFromTotalCount :
  ∀ {A : Set}
  (K : C.FullLearnerKernel A)
  (n : Nat)
  (s : C.FullLearnerState A) →
  iterateStep (C.canonicalFullStep K) (suc n) s ≡ s →
  ⊥
canonicalNoPositiveCycleFromTotalCount K n s =
  noPositiveFiniteCycleFromStrictProgress
    (canonicalTotalCountStrictProgress K)
    n
    s


------------------------------------------------------------------------
-- 2026-09-26 theorem-improvement closure layer.
--
-- These interfaces deliberately remain in the theorem monolith and use
-- only the imports already present above. Each bridge is proof-relevant:
-- no graph edge, semantic label, convergence claim, or economic claim is
-- promoted without an explicit inhabitant.
------------------------------------------------------------------------

record MonolithStrictProgressClosure
  (State Measure : Set)
  (step : State → State)
  (_<_ : Measure → Measure → Set) : Set₁ where
  constructor monolithStrictProgressClosure
  field
    witness :
      StrictProgressWitness State Measure step _<_
    noPositiveCycle :
      ∀ n s →
      iterateStep step (suc n) s ≡ s →
      ⊥

open MonolithStrictProgressClosure public

monolithStrictProgressClosure-from-witness :
  ∀ {State Measure : Set}
  {step : State → State}
  {_<_ : Measure → Measure → Set}
  (W : StrictProgressWitness State Measure step _<_) →
  MonolithStrictProgressClosure State Measure step _<_
monolithStrictProgressClosure-from-witness W =
  monolithStrictProgressClosure
    W
    (λ n s →
      noPositiveFiniteCycleFromStrictProgress W n s)

canonicalTotalCountStrictProgress-closure :
  ∀ {A : Set}
  (K : C.FullLearnerKernel A) →
  MonolithStrictProgressClosure
    (C.FullLearnerState A)
    Nat
    (C.canonicalFullStep K)
    _<_
canonicalTotalCountStrictProgress-closure K =
  monolithStrictProgressClosure-from-witness
    (canonicalTotalCountStrictProgress K)

record MonolithFactorTransitionClosure
  (State Factor : Set)
  (step : State → State)
  (related : State → State → Set)
  (observe : State → Factor) : Set₁ where
  constructor monolithFactorTransitionClosure
  field
    factorStep : Factor → Factor
    factorStepCommutes :
      ∀ s →
      observe (step s) ≡ factorStep (observe s)
    observeRespects :
      ∀ {s t} →
      related s t →
      observe s ≡ observe t
    relationStepPreserved :
      ∀ {s t} →
      related s t →
      related (step s) (step t)

monolithFactorTransition-to-relationWitness :
  ∀ {State Factor : Set}
  {step : State → State}
  {related : State → State → Set}
  {observe : State → Factor}
  (W : MonolithFactorTransitionClosure
    State
    Factor
    step
    related
    observe) →
  RelationFactorTransitionWitness
    State
    Factor
    step
    related
    observe
monolithFactorTransition-to-relationWitness W =
  relationFactorTransitionWitness
    (factorTransitionWitness
      (factorStep W)
      (factorStepCommutes W))
    (observeRespects W)
    (relationStepPreserved W)

canonicalNormPairFactorTransitionClosure :
  ∀ {A : Set}
  (K : C.FullLearnerKernel A)
  (factorStep : Nat → Nat)
  (factorStepCommutes :
    ∀ s →
    C.canonicalPolicy K (C.canonicalFullStep K s) ≡
    factorStep (C.canonicalPolicy K s)) →
  MonolithFactorTransitionClosure
    (C.FullLearnerState A)
    Nat
    (C.canonicalFullStep K)
    normPairReplacementRelation
    (C.canonicalPolicy K)
canonicalNormPairFactorTransitionClosure
  K
  factorStep
  factorStepCommutes =
  monolithFactorTransitionClosure
    factorStep
    factorStepCommutes
    (canonicalPolicy-factors-through-NormPair K)
    (canonicalNormPairQuotient-step-compatible K)

record MonolithCommutingSquareTransport
  (A B : Set)
  (sourceStep : A → A)
  (targetStep : B → B) : Set₁ where
  constructor monolithCommutingSquareTransport
  field
    square :
      StepConjugacyWitness A B sourceStep targetStep

monolithCommutingSquare-iterate :
  ∀ {A B : Set}
  {sourceStep : A → A}
  {targetStep : B → B}
  (W : MonolithCommutingSquareTransport
    A B
    sourceStep
    targetStep)
  (n : Nat)
  (a : A) →
  to (isomorphism (square W))
    (iterateIsomorphism sourceStep n a)
  ≡
  iterateIsomorphism targetStep n
    (to (isomorphism (square W)) a)
monolithCommutingSquare-iterate W =
  stepConjugacy-iterate (square W)

monolithCommutingSquare-property :
  ∀ {A B : Set}
  {sourceStep : A → A}
  {targetStep : B → B}
  (W : MonolithCommutingSquareTransport
    A B
    sourceStep
    targetStep)
  (P : A → Set)
  (Q : B → Set)
  (bridge :
    ∀ a →
    P a →
    Q (to (isomorphism (square W)) a))
  (preserved :
    ∀ b →
    Q b →
    Q (targetStep b)) →
  ∀ n a →
  P a →
  Q
    (iterateIsomorphism targetStep n
      (to (isomorphism (square W)) a))
monolithCommutingSquare-property W P Q bridge preserved =
  stepConjugacy-property-transport
    (square W)
    P
    Q
    bridge
    preserved

record MonolithProductionSideAssumptionBundle
  (Agent Firm Price Consumption ProductionPlan Allocation : Set)
  (consumer : Agent → Consumption)
  (production : Firm → ProductionPlan)
  (price : Price)
  (allocation : Allocation)
  (consumerOptimal : Agent → Consumption → Set)
  (productionFeasible : Firm → ProductionPlan → Set)
  (firmOptimal : Firm → Price → ProductionPlan → Set)
  (consumptionFeasible : Agent → Consumption → Set)
  (aggregateFeasible : Allocation → Set)
  (marketClearing : Price → Allocation → Set)
  (supportingPrice : Price → Allocation → Set) : Set₁ where
  constructor monolithProductionSideAssumptionBundle
  field
    consumerOptimality :
      ∀ i →
      consumerOptimal i (consumer i)
    productionFeasibility :
      ∀ j →
      productionFeasible j (production j)
    firmProfitOptimality :
      ∀ j →
      firmOptimal j price (production j)
    consumptionFeasibility :
      ∀ i →
      consumptionFeasible i (consumer i)
    aggregateFeasibility :
      aggregateFeasible allocation
    marketClearingWitness :
      marketClearing price allocation
    supportingPriceWitness :
      supportingPrice price allocation

open MonolithProductionSideAssumptionBundle public

record MonolithStationaryLawBridge
  (Distribution Economic : Set)
  (P : Distribution → Distribution)
  (μ : Nat → Distribution)
  (μ∞ : Distribution)
  (Converges : (Nat → Distribution) → Distribution → Set)
  (aggregate : Distribution → Economic)
  (economicStep : Economic → Economic) : Set₁ where
  constructor monolithStationaryLawBridge
  field
    distributionalLimit :
      StationaryLimitTheorem
        Distribution
        P
        μ
        μ∞
        Converges
    aggregateCommutes :
      ∀ d →
      aggregate (P d) ≡ economicStep (aggregate d)

monolithStationaryLawBridge-stationary :
  ∀ {Distribution Economic : Set}
  {P : Distribution → Distribution}
  {μ : Nat → Distribution}
  {μ∞ : Distribution}
  {Converges : (Nat → Distribution) → Distribution → Set}
  {aggregate : Distribution → Economic}
  {economicStep : Economic → Economic}
  (W :
    MonolithStationaryLawBridge
      Distribution
      Economic
      P
      μ
      μ∞
      Converges
      aggregate
      economicStep) →
  economicStep (aggregate μ∞) ≡ aggregate μ∞
monolithStationaryLawBridge-stationary W =
  distributionalStationaryAggregate-stationary
    (distributionalStationaryAggregateTransport
      (distributionalLimit W)
      (aggregateCommutes W))

record MonolithEGraphProofCertificate
  (Node Edge Assumption : Set) : Set₁ where
  constructor monolithEGraphProofCertificate
  field
    source : Edge → Node
    target : Edge → Node
    semanticAssumption : Edge → Assumption
    proofWitness : Edge → Set
    proofSound :
      ∀ e →
      proofWitness e
    assumptionToProof :
      ∀ e →
      semanticAssumption e → proofWitness e

record MonolithEGraphClosureCertificate
  (Node Edge Assumption : Set) : Set₁ where
  constructor monolithEGraphClosureCertificate
  field
    certificate :
      MonolithEGraphProofCertificate
        Node
        Edge
        Assumption
    closedEdge :
      Edge → Set

monolithEGraphClosureCertificate-from-proof :
  ∀ {Node Edge Assumption : Set}
  (W :
    MonolithEGraphProofCertificate
      Node
      Edge
      Assumption) →
  MonolithEGraphClosureCertificate
    Node
    Edge
    Assumption
monolithEGraphClosureCertificate-from-proof W =
  monolithEGraphClosureCertificate
    W
    (λ e → proofWitness W e)


------------------------------------------------------------------------
-- Unconditional finite-candidate price kernel.
--
-- This is deliberately weaker than a Walrasian existence theorem:
-- for any finite candidate-price list and an explicit decision procedure
-- for the supporting relation at the chosen allocation, the kernel
-- unconditionally returns either a supporting-price witness or a complete
-- rejection certificate for the supplied candidate list.
--
-- No new imports are required. The result does not claim that a supporting
-- price exists outside the supplied finite candidate set.
------------------------------------------------------------------------

data FiniteCandidateDecision (P : Set) : Set where
  acceptCandidate : P → FiniteCandidateDecision P
  rejectCandidate : (P → ⊥) → FiniteCandidateDecision P

FiniteCandidatePriceResult :
  (Price Allocation : Set) →
  (supports : Price → Allocation → Set) →
  Allocation →
  Set₁
FiniteCandidatePriceResult Price Allocation supports allocation =
  (Σ Price (λ p → supports p allocation))
  ⊎
  List (Σ Price (λ p → supports p allocation → ⊥))

finiteCandidatePriceSearch :
  ∀ {Price Allocation : Set}
  (supports : Price → Allocation → Set)
  (allocation : Allocation)
  (decide : ∀ p → FiniteCandidateDecision (supports p allocation))
  (candidates : List Price) →
  FiniteCandidatePriceResult Price Allocation supports allocation
finiteCandidatePriceSearch supports allocation decide [] =
  inj₂ []
finiteCandidatePriceSearch supports allocation decide (p ∷ ps) with decide p
... | acceptCandidate witness =
  inj₁ (p , witness)
... | rejectCandidate refute with
  finiteCandidatePriceSearch supports allocation decide ps
...   | inj₁ witness =
  inj₁ witness
...   | inj₂ rejected =
  inj₂ ((p , refute) ∷ rejected)

finiteCandidatePriceSearch-complete :
  ∀ {Price Allocation : Set}
  (supports : Price → Allocation → Set)
  (allocation : Allocation)
  (decide : ∀ p → FiniteCandidateDecision (supports p allocation))
  (candidates : List Price) →
  FiniteCandidatePriceResult Price Allocation supports allocation
finiteCandidatePriceSearch-complete =
  finiteCandidatePriceSearch


------------------------------------------------------------------------
-- Unconditional tragedy-of-the-commons non-derivability.
--
-- This is an interface-level impossibility boundary. It deliberately
-- separates local optimality from the aggregate preservation predicate
-- for a shared resource. The counterexample shows that local optimality
-- plus a common-resource carrier does not unconditionally derive
-- preservation of that resource.
------------------------------------------------------------------------

record CommonsPreservationDerivation
  (World Agent Resource : Set)
  (sharedResource : World → Resource)
  (localOptimal : World → Agent → Set)
  (preserves : World → Set) : Set₁ where
  constructor commonsPreservationDerivation
  field
    derive :
      ∀ w →
      (∀ a → localOptimal w a) →
      preserves w

open CommonsPreservationDerivation public

record CommonsNonDerivabilityCounterexample : Set₁ where
  constructor commonsNonDerivabilityCounterexample
  field
    World : Set
    Agent : Set
    Resource : Set
    sharedResource : World → Resource
    localOptimal : World → Agent → Set
    preserves : World → Set
    commonsWorld : World
    commonResource :
      sharedResource commonsWorld
    allLocallyOptimal :
      ∀ a → localOptimal commonsWorld a
    notPreserved :
      ¬ preserves commonsWorld

open CommonsNonDerivabilityCounterexample public

noUnconditionalCommonsPreservation :
  ∀ (C : CommonsNonDerivabilityCounterexample) →
  ¬ CommonsPreservationDerivation
      (World C)
      (Agent C)
      (Resource C)
      (sharedResource C)
      (localOptimal C)
      (preserves C)
noUnconditionalCommonsPreservation C D =
  notPreserved C
    (derive D
      (commonsWorld C)
      (allLocallyOptimal C))

twoAgentCommonsCounterexample :
  CommonsNonDerivabilityCounterexample
twoAgentCommonsCounterexample =
  commonsNonDerivabilityCounterexample
    (⊤)
    (⊤ ⊎ ⊤)
    (⊤ ⊎ ⊤)
    (λ _ → inj₁ tt)
    (λ _ _ → ⊤)
    (λ _ → ⊥)
    tt
    tt
    (λ _ → tt)
    (λ ())

noUnconditionalCommonsPreservation-twoAgent :
  ¬ CommonsPreservationDerivation
      (World twoAgentCommonsCounterexample)
      (Agent twoAgentCommonsCounterexample)
      (Resource twoAgentCommonsCounterexample)
      (sharedResource twoAgentCommonsCounterexample)
      (localOptimal twoAgentCommonsCounterexample)
      (preserves twoAgentCommonsCounterexample)
noUnconditionalCommonsPreservation-twoAgent =
  noUnconditionalCommonsPreservation
    twoAgentCommonsCounterexample

------------------------------------------------------------------------
-- Stronger semantic reading of the boundary:
--
-- market clearing is not itself a commons-preservation theorem.
-- Any positive bridge must expose an aggregate resource constraint,
-- internalized externality, quota/property-right mechanism, dynamic
-- regeneration law, or another explicit coupling assumption.
------------------------------------------------------------------------
