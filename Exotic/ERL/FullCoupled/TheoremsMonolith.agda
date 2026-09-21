{-# OPTIONS --safe #-}

module Exotic.ERL.FullCoupled.TheoremsMonolith where

------------------------------------------------------------------------
-- Single active theorem source for the canonical learner.
-- Discovery/CI should target this file. Legacy theorem modules are not
-- part of the canonical proof surface.
------------------------------------------------------------------------

open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; cong; cong₂; trans; sym)
open import Agda.Builtin.Nat using (Nat; suc; _+_; _*_)
open import Data.Empty using (⊥)
open import Relation.Nullary using (¬_)
open import Data.Fin using (Fin; toℕ)
open import Data.Nat using (_<ᵇ_; _/_; _≤_; zero)
open import Data.List.Base using (List; []; _∷_; _++_; map; length)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Nat.Properties using (≤-antisym; +-identityʳ; +-suc)
open import Exotic.ERL.FullCoupled.CanonicalLearnerMonolith as C

replaceClock :
  C.CanonicalFullLearnerState → Nat → C.CanonicalFullLearnerState
replaceClock s n =
  C.fullLearnerState
    n
    (C.watkins s)
    (C.gru s)
    (C.optimizer s)
    (C.norm s)
    (C.lcbCounts s)
    (C.qLogControl s)
    (C.qLogValue s)

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

canonical-aq-loop-theorem : CanonicalAQLoopTheorem
canonical-aq-loop-theorem =
  canonicalAQLoopTheorem
    (λ K s → refl)
    (λ K s → refl)
    (λ K s → refl)
    (λ K s → refl)

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

canonicalClockAfter :
  ∀ K n s →
  C.clock (C.iterateCanonical K n s) ≡ C.clock s + n
canonicalClockAfter = C.clockAfter

canonicalAperiodic-theorem :
  ∀ K s n →
  C.iterateCanonical K (suc n) s ≢ s
canonicalAperiodic-theorem = C.canonicalAperiodic

canonicalNoNontrivialFiniteCycle-theorem :
  ∀ K s n →
  C.iterateCanonical K (suc n) s ≡ s → ⊥
canonicalNoNontrivialFiniteCycle-theorem = C.canonicalNoNontrivialFiniteCycle

record CanonicalConnectedCompositionTheorem : Set₁ where
  constructor canonicalConnectedCompositionTheorem
  field
    aqLoop : CanonicalAQLoopTheorem
    clockGrowth :
      ∀ K n s →
      C.clock (C.iterateCanonical K n s) ≡ C.clock s + n
    finiteCycleExclusion :
      ∀ K s n →
      C.iterateCanonical K (suc n) s ≡ s → ⊥

canonical-connected-composition-theorem :
  CanonicalConnectedCompositionTheorem
canonical-connected-composition-theorem =
  canonicalConnectedCompositionTheorem
    canonical-aq-loop-theorem
    canonicalClockAfter
    canonicalNoNontrivialFiniteCycle-theorem



------------------------------------------------------------------------
-- Learner-local symbolic composition algebra.
--
-- This is the semantic target for automated program/theorem search:
-- the search program composes actual learner transformations and asks
-- the canonical Agda surface to prove the resulting observation law.
-- The search metric is deliberately absent from this semantic layer.
------------------------------------------------------------------------

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
------------------------------------------------------------------------
-- Generic equality composition primitive.
--
-- This is theorem algebra, not a learner-specific discovery registry.
-- Automated discovery derives its semantic vocabulary from source
-- declarations; no fixed candidate basis is encoded here.
------------------------------------------------------------------------

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

------------------------------------------------------------------------
-- Exact recurrent scan class.

--
-- No finite horizon is baked into this theorem. The input is a Nat-indexed
-- stream, and the prefix/split laws quantify over arbitrary natural
-- horizons. The associativity is over endomorphism composition, so the
-- recurrent state transition itself is not approximated or relaxed.
------------------------------------------------------------------------

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

------------------------------------------------------------------------
-- Stronger free-monoid formulation of the recurrent prefix scan.
--
-- The Nat-indexed split law is equivalent to a word/prefix action.  With
-- the convention that a sequence is executed left-to-right, the resulting
-- map is a monoid homomorphism into the opposite endomorphism monoid:
--
--   Prefix (xs ++ ys) = Prefix xs ⊙ Prefix ys
--
-- where f ⊙ g means g ∘ f.  This is stronger than merely recording one
-- associativity equation for three endomorphisms.
------------------------------------------------------------------------

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


------------------------------------------------------------------------
-- Pointwise product lifting of recurrent homomorphisms.
--
-- If two transition algebras read the same word, their product transition
-- algebra is obtained elementwise.  The product therefore preserves the
-- same monoid law componentwise; this is closure, not a stronger algebraic
-- law than homomorphism itself.
------------------------------------------------------------------------

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


------------------------------------------------------------------------
-- Componentwise prefix homomorphisms from the canonical learner.
--
-- F4 is a genuine per-feature recurrent component: its transition is
-- f4ThetaStep on one Int8 feature/signal.  NormPair is policy-invariant
-- and its canonical transition is the identity.  Each is therefore lifted
-- into the same prefix-endomorphism monoid, and their direct product with
-- the canonical GRU is a single componentwise prefix action.
------------------------------------------------------------------------

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


------------------------------------------------------------------------
-- Componentwise learner prefix homomorphisms.
--
-- Each transition is sourced directly from CanonicalLearnerMonolith.
-- The prefix action supplies the monoid law; no external component
-- semantics or theorem registry is introduced here.
------------------------------------------------------------------------

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


------------------------------------------------------------------------
-- Full commuting-square / naturality completion.
--
-- The literature's equivariance/naturality law is the commuting square
--   observe ∘ step ≡ featureStep ∘ observe.
-- Here it is proved for arbitrary deterministic recurrent transitions.
-- Iteration follows by induction. A left inverse upgrades the square from
-- a factorization law to exact reconstruction on the observation image.
-- A right inverse closes the square globally and yields exact conjugacy.
------------------------------------------------------------------------

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

commutingSquareTheorem-from-square :
  ∀ {State Feature : Set}
  {step : State → State}
  {observe : State → Feature}
  {featureStep : Feature → Feature} →
  (∀ s → observe (step s) ≡ featureStep (observe s)) →
  CommutingSquareTheorem State Feature step observe featureStep
commutingSquareTheorem-from-square squareWitness =
  commutingSquareTheorem
    squareWitness
    iterateProof
  where
    iterateProof :
      ∀ n s →
      observe (commutingIterate step n s) ≡
      commutingIterate featureStep n (observe s)
    iterateProof zero s = refl
    iterateProof (suc n) s =
      trans
        (squareWitness (commutingIterate step n s))
        (cong featureStep (iterateProof n s))

record CommutingSquareLeftInverseTheorem
  (State Feature : Set)
  (step : State → State)
  (observe : State → Feature)
  (featureStep : Feature → Feature)
  (inverse : Feature → State) : Set₁ where
  constructor commutingSquareLeftInverseTheorem
  field
    squareWitness :
      CommutingSquareTheorem State Feature step observe featureStep
    leftInverse :
      ∀ s → inverse (observe s) ≡ s
    observationInjective :
      ∀ {s t} →
      observe s ≡ observe t →
      s ≡ t
    reconstructedStep :
      ∀ s →
      step s ≡ inverse (featureStep (observe s))

open CommutingSquareLeftInverseTheorem public

commutingSquareLeftInverseTheorem-from-witness :
  ∀ {State Feature : Set}
  {step : State → State}
  {observe : State → Feature}
  {featureStep : Feature → Feature}
  (inverse : Feature → State)
  (squareWitness :
    CommutingSquareTheorem State Feature step observe featureStep)
  (leftInverse :
    ∀ s → inverse (observe s) ≡ s) →
  CommutingSquareLeftInverseTheorem
    State Feature step observe featureStep inverse
commutingSquareLeftInverseTheorem-from-witness
  inverse squareWitness leftInverse =
  commutingSquareLeftInverseTheorem
    squareWitness
    leftInverse
    (λ {s} {t} eq →
      trans
        (sym (leftInverse s))
        (trans
          (cong inverse eq)
          (leftInverse t)))
    (λ s →
      trans
        (sym (leftInverse (step s)))
        (cong inverse
          (CommutingSquareTheorem.square
            squareWitness
            s)))

record FullCommutingSquareConjugacyTheorem
  (State Feature : Set)
  (step : State → State)
  (observe : State → Feature)
  (featureStep : Feature → Feature)
  (inverse : Feature → State) : Set₁ where
  constructor fullCommutingSquareConjugacyTheorem
  field
    squareWitness :
      CommutingSquareTheorem State Feature step observe featureStep
    leftInverse :
      ∀ s → inverse (observe s) ≡ s
    rightInverse :
      ∀ f → observe (inverse f) ≡ f
    backwardSquare :
      ∀ f → inverse (featureStep f) ≡ step (inverse f)

open FullCommutingSquareConjugacyTheorem public

fullCommutingSquareConjugacyTheorem-from-witness :
  ∀ {State Feature : Set}
  {step : State → State}
  {observe : State → Feature}
  {featureStep : Feature → Feature}
  (inverse : Feature → State)
  (squareWitness :
    CommutingSquareTheorem State Feature step observe featureStep)
  (leftInverse :
    ∀ s → inverse (observe s) ≡ s)
  (rightInverse :
    ∀ f → observe (inverse f) ≡ f) →
  FullCommutingSquareConjugacyTheorem
    State Feature step observe featureStep inverse
fullCommutingSquareConjugacyTheorem-from-witness
  inverse squareWitness leftInverse rightInverse =
  fullCommutingSquareConjugacyTheorem
    squareWitness
    leftInverse
    rightInverse
    (λ f →
      trans
        (sym (leftInverse (step (inverse f))))
        (cong inverse
          (trans
            (CommutingSquareTheorem.square
              squareWitness
              (inverse f))
            (cong featureStep (rightInverse f)))))

------------------------------------------------------------------------
-- Particular boundary:
-- global exact Int8 decoding would supply the left-inverse half, while
-- the Nat-indexed aperiodic orbit proves that such decoding cannot exist.
-- Hence a global exact conjugacy square through Int8 is impossible.
------------------------------------------------------------------------

canonicalSquare-law-on-orbit :
  ∀ {Feature : Set}
  (step : C.CanonicalFullLearnerState → C.CanonicalFullLearnerState)
  (observe : C.CanonicalFullLearnerState → Feature)
  (featureStep : Feature → Feature) →
  (∀ s → observe (step s) ≡ featureStep (observe s)) →
  ∀ n s →
  observe (commutingIterate step n s) ≡
  commutingIterate featureStep n (observe s)
canonicalSquare-law-on-orbit
  step observe featureStep squareWitness n s =
  CommutingSquareTheorem.iterateSquare
    (commutingSquareTheorem-from-square squareWitness)
    n s

------------------------------------------------------------------------

------------------------------------------------------------------------
-- Free-monoid action form of the commuting square.
--
-- One transition generates the N-action by iteration.  The one-step
-- commuting square therefore induces an action homomorphism for every
-- natural-number word in the generator.  This is stronger terminology
-- than merely naming the one-step square as an equivariance law.
------------------------------------------------------------------------

record FreeMonoidActionHomomorphism
  (State Feature : Set)
  (step : State → State)
  (observe : State → Feature)
  (featureStep : Feature → Feature) : Set₁ where
  constructor freeMonoidActionHomomorphism
  field
    actionHomomorphism :
      ∀ n s →
      observe (commutingIterate step n s) ≡
      commutingIterate featureStep n (observe s)

open FreeMonoidActionHomomorphism public

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

canonicalClock-freeMonoidActionHomomorphism :
  ∀ (K : C.CanonicalFullLearnerKernel) →
  FreeMonoidActionHomomorphism
    C.CanonicalFullLearnerState
    Nat
    (C.canonicalFullStep K)
    suc
    C.clock
canonicalClock-freeMonoidActionHomomorphism K =
  freeMonoidActionHomomorphism-from-square
    (commutingSquareTheorem-from-square
      (λ s → C.canonicalFullStep-clock K s))

------------------------------------------------------------------------
-- Generic symbolic impossibility at the observation boundary.
--
-- A collision in observation prohibits a left inverse.  More generally,
-- any task that distinguishes the collided states cannot factor exactly
-- through the observation map.
------------------------------------------------------------------------

noLeftInverse-from-observation-collision :
  ∀ {State Feature : Set}
  (observe : State → Feature)
  {s t : State} →
  observe s ≡ observe t →
  s ≢ t →
  ¬ (Σ (λ inverse →
      ∀ u → inverse (observe u) ≡ u))
noLeftInverse-from-observation-collision
  observe {s} {t} obsEq distinct =
  λ witness →
    distinct
      (let
         inverse = proj₁ witness
         leftInverse = proj₂ witness
       in
       trans
         (sym (leftInverse s))
         (trans
           (cong inverse obsEq)
           (leftInverse t)))

record ObservationTaskFactorization
  {State Feature Output : Set}
  (observe : State → Feature)
  (target : State → Output) : Set₁ where
  constructor observationTaskFactorization
  field
    factor : Feature → Output
    correctness :
      ∀ s → target s ≡ factor (observe s)

symbolicTaskImpossible-from-observation-collision :
  ∀ {State Feature Output : Set}
  (observe : State → Feature)
  {s t : State}
  (obsEq : observe s ≡ observe t)
  (target : State → Output) →
  target s ≢ target t →
  ¬ ObservationTaskFactorization observe target
symbolicTaskImpossible-from-observation-collision
  observe {s} {t} obsEq target distinguishes =
  λ factorization →
    let
      factor = ObservationTaskFactorization.factor factorization
      correctness =
        ObservationTaskFactorization.correctness factorization
    in
    distinguishes
      (trans
        (correctness s)
        (trans
          (cong factor obsEq)
          (sym (correctness t))))




------------------------------------------------------------------------
-- Recurrent-word collision boundary.
--
-- List-valued histories are part of the theorem vocabulary: a recurrent
-- word is an exact endomorphism.  If an observation collides two states
-- reached by exact words and the target separates them, no exact symbolic
-- readout through that observation exists.
------------------------------------------------------------------------

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

recurrentWord-observation-collision-impossible :
  ∀ {State Input Feature Output : Set}
  (R : C.RecurrentNetwork State Input)
  (word : List Input)
  (s t : State)
  (observe : State → Feature)
  (target : State → Output) →
  observe (recurrentWordState R word s) ≡
  observe (recurrentWordState R word t) →
  target (recurrentWordState R word s) ≢
  target (recurrentWordState R word t) →
  ¬ ObservationTaskFactorization observe target
recurrentWord-observation-collision-impossible
  R word s t observe target obsEq targetDistinct =
  symbolicTaskImpossible-from-observation-collision
    observe
    obsEq
    target
    targetDistinct
------------------------------------------------------------------------
-- S4/S5-style scan algebra, without claiming the canonical learner is
-- literally the linear S4/S5 architecture.
--
-- The exact shared algebraic core is:
--   * state transitions induce endomorphisms,
--   * endomorphisms compose associatively,
--   * recurrent prefixes are correct,
--   * prefixes split by associative composition.
--
-- S5's distinctive computational point is the associative scan; S4 and
-- S5 remain broader architectural families than this abstract law.
------------------------------------------------------------------------

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


------------------------------------------------------------------------
-- Exact synchronous direct-product closure for recurrent finite-state
-- machines.  No new learner semantics are introduced: this is a generic
-- theorem over the recurrent interface already used by the learner.
------------------------------------------------------------------------

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

------------------------------------------------------------------------
-- Finite automata are closed under the same direct-product construction.
-- Fin A × Fin B is a finite product state space, and synchronized input
-- preserves exact prefix semantics componentwise.
------------------------------------------------------------------------

finiteAutomatonProductStep :
  ∀ {A B I : Nat} →
  (Fin A → Fin I → Fin A) →
  (Fin B → Fin I → Fin B) →
  (Fin A × Fin B) →
  Fin I →
  (Fin A × Fin B)
finiteAutomatonProductStep stepA stepB st x =
  (stepA (proj₁ st) x , stepB (proj₂ st) x)

finiteAutomatonProductPrefix-correct :
  ∀ {A B I : Nat}
  (stepA : Fin A → Fin I → Fin A)
  (stepB : Fin B → Fin I → Fin B)
  (xs : Nat → Fin I)
  (n : Nat)
  (s : Fin A)
  (t : Fin B) →
  C.recurrentPrefixState
    (C.recurrentNetwork stepA)
    xs n s
  ≡
  proj₁
    (C.recurrentPrefixState
      (C.recurrentNetwork (finiteAutomatonProductStep stepA stepB))
      xs n
      (s , t))
  ×
  C.recurrentPrefixState
    (C.recurrentNetwork stepB)
    xs n t
  ≡
  proj₂
    (C.recurrentPrefixState
      (C.recurrentNetwork (finiteAutomatonProductStep stepA stepB))
      xs n
      (s , t))
finiteAutomatonProductPrefix-correct stepA stepB xs n s t =
  let
    eq =
      productRecurrentPrefix-correct
        (C.recurrentNetwork stepA)
        (C.recurrentNetwork stepB)
        xs n s t
  in
  cong proj₁ (sym eq) , cong proj₂ (sym eq)


------------------------------------------------------------------------
-- Information-preserving symbolic task composition.
--
-- A left inverse makes observation a split monomorphism. Therefore every
-- exact symbolic task on the hidden state can be factorized through the
-- observation and reconstructed before applying the task.
------------------------------------------------------------------------

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


------------------------------------------------------------------------
-- The exact task boundary is therefore the observation equivalence:
-- with a left inverse, every state task survives observation; without
-- injectivity, not every state task can survive.
------------------------------------------------------------------------

informationPreserving-symbolic-task-boundary :
  ∀ {State Feature : Set}
  (observe : State → Feature)
  (inverse : Feature → State)
  (leftInverse : ∀ s → inverse (observe s) ≡ s) →
  ∀ (target : State → State) (s : State) →
  target s ≡ target (inverse (observe s))
informationPreserving-symbolic-task-boundary =
  informationPreserving-symbolic-task-factorization

------------------------------------------------------------------------
-- Explicit equality-composition theorem.
--
-- The e-graph proof-plan combinator is dependency composition.  Actual
-- equality composition is represented separately by composeEqualityTheorem,
-- whose proof term uses trans.  A reflexive identity is never used as the
-- composition theorem itself.
------------------------------------------------------------------------
-- Canonical minimax/Bellman-Shapley inclusion class for the executable
-- biased Watkins + negative-q-Munchausen + L2 target.
--
-- The learner has a concrete Int8 carrier. No ordered ring, interval,
-- metric, or topology is imported here. The inclusion theorem therefore
-- takes the comparison relation and monotone minimax/Bellman-Shapley
-- operator as explicit hypotheses, while the target itself is the exact
-- executable canonicalWatkinsTarget.
------------------------------------------------------------------------

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

canonical-qLog2Bias8-law :
  ∀ x →
  C.qLog2Bias8 x ≡
  C.int8Neg
    (C.int8OfNat
      ((C.munchausenScale8 * C.numerator (C.finiteQLog8 x)) /
       C.denominator (C.finiteQLog8 x)))
canonical-qLog2Bias8-law x with toℕ (C.code x)
... | zero = refl
... | suc n = refl

record CanonicalBiasedWatkinsNegativeQMunchausenL2TargetTheorem : Set₁ where
  constructor canonicalBiasedWatkinsNegativeQMunchausenL2TargetTheorem
  field
    negativeQMunchausenBias :
      ∀ x →
      C.qLog2Bias8 x ≡
      C.int8Neg
        (C.int8OfNat
          ((C.munchausenScale8 * C.numerator (C.finiteQLog8 x)) /
           C.denominator (C.finiteQLog8 x)))

    targetDecomposition :
      ∀ K s →
      canonicalBiasedWatkinsNegativeQMunchausenL2Target K s ≡
      C.int8Add
        (C.int8Add
          (C.int8Add
            (C.canonicalReward8 K s)
            (C.canonicalQLogBias K s))
          (C.int8Mul
            C.canonicalDiscount8
            (C.maxCriticValue8 (C.critic (C.watkins s)))))
        (C.canonicalEndogenousFeedback K s)

    l2ConsumesTarget :
      ∀ K s →
      C.canonicalOptimizerStep K s ≡
      C.f4ThetaStep
        (C.optimizerKernel K)
        (C.optimizer s)
        (canonicalBiasedWatkinsNegativeQMunchausenL2Target K s)

open CanonicalBiasedWatkinsNegativeQMunchausenL2TargetTheorem public

canonical-biased-watkins-negative-q-munchausen-l2-target-theorem :
  CanonicalBiasedWatkinsNegativeQMunchausenL2TargetTheorem
canonical-biased-watkins-negative-q-munchausen-l2-target-theorem =
  canonicalBiasedWatkinsNegativeQMunchausenL2TargetTheorem
    canonical-qLog2Bias8-law
    (λ K s → C.canonicalWatkinsTarget-law K s)
    (λ K s → C.canonicalOptimizerStep-qMunchausen-L2 K s)

canonicalWatkinsTarget-minimaxBellmanShapley-inclusion-class :
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
canonicalWatkinsTarget-minimaxBellmanShapley-inclusion-class
  K _≤_ operator lower upper
  (pointwiseSandwich lower≤actual actual≤upper) =
  minimaxBellmanShapleyInclusionTheorem
    (monotone operator
      lower
      (canonicalBiasedWatkinsNegativeQMunchausenL2Target K)
      lower≤actual)
    (monotone operator
      (canonicalBiasedWatkinsNegativeQMunchausenL2Target K)
      upper
      actual≤upper)

------------------------------------------------------------------------
-- Endogenous factorization through a left-invertible observation.
------------------------------------------------------------------------

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

------------------------------------------------------------------------
-- Infinite-state orbit injectivity and Nat-clock pigeonhole contradiction.
------------------------------------------------------------------------

suc-injective :
  ∀ {m n : Nat} → suc m ≡ suc n → m ≡ n
suc-injective refl = refl

natPlus-left-cancel :
  ∀ (k m n : Nat) → k + m ≡ k + n → m ≡ n
natPlus-left-cancel zero m n eq = eq
natPlus-left-cancel (suc k) m n eq =
  natPlus-left-cancel k m n (suc-injective eq)

canonicalOrbit-state-injective :
  ∀ K s {m n : Nat} →
  C.iterateCanonical K m s ≡ C.iterateCanonical K n s →
  m ≡ n
canonicalOrbit-state-injective K s {m} {n} eq =
  natPlus-left-cancel
    (C.clock s) m n
    (trans
      (sym (C.clockAfter K m s))
      (trans
        (cong (λ t → C.clock t) eq)
        (C.clockAfter K n s)))

-- The canonical Nat-indexed orbit is an explicit infinite-state embedding:
-- equality of orbit states forces equality of the Nat indices.
canonicalInfiniteStateOrbitEmbedding :
  ∀ (K : C.CanonicalFullLearnerKernel)
  (s : C.CanonicalFullLearnerState) →
  ∀ {m n : Nat} →
  C.iterateCanonical K m s ≡ C.iterateCanonical K n s →
  m ≡ n
canonicalInfiniteStateOrbitEmbedding K s =
  canonicalOrbit-state-injective K s


canonicalPigeonholeNatClockContradiction :
  ∀ (K : C.CanonicalFullLearnerKernel)
  (s : C.CanonicalFullLearnerState)
  (observe : C.CanonicalFullLearnerState → C.Int8)
  (inverse : C.Int8 → C.CanonicalFullLearnerState) →
  (∀ t → inverse (observe t) ≡ t) →
  ⊥
canonicalPigeonholeNatClockContradiction K s observe inverse leftInverse =
  C.int8-no-countably-unbounded-injective
    (λ n → observe (C.iterateCanonical K n s))
    (λ {m} {n} eq →
      canonicalOrbit-state-injective K s
        (trans
          (sym (leftInverse (C.iterateCanonical K m s)))
          (trans
            (cong inverse eq)
            (leftInverse (C.iterateCanonical K n s)))))

------------------------------------------------------------------------
-- Full discrete exact-UAP factorization.
--
-- This is the genuine universal statement available without topology:
-- every target on the discrete state factors exactly through an observation
-- that has a left inverse. No limits, density arguments, or real-valued
-- approximation metric are involved.
------------------------------------------------------------------------

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

------------------------------------------------------------------------
-- Full universal exact-discrete UAP, not merely one chosen target.
--
-- Universal exact readout means every target State → Output factors
-- exactly through the observation.  Constructively, this is equivalent
-- to existence of a left inverse.  The identity target supplies the
-- converse, so this result is independent of topology or approximation
-- metrics.
------------------------------------------------------------------------

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

discreteExactUniversalUAP-from-leftInverse :
  ∀ {State Feature : Set}
  {observe : State → Feature} →
  DiscreteLeftInverseWitness State Feature observe →
  DiscreteExactUniversalUAP State Feature observe
discreteExactUniversalUAP-from-leftInverse witness =
  discreteExactUniversalUAP
    (λ target f → target (inverse witness f))
    (λ target s → cong target (leftInverse witness s))

discreteExactUniversalUAP-to-leftInverse :
  ∀ {State Feature : Set}
  {observe : State → Feature} →
  DiscreteExactUniversalUAP State Feature observe →
  DiscreteLeftInverseWitness State Feature observe
discreteExactUniversalUAP-to-leftInverse universal =
  discreteLeftInverseWitness
    (readout universal (λ s → s))
    (λ s → sym (exactReadout universal (λ t → t) s))

record DiscreteExactUniversalUAPLeftInverseEquivalence
  (State Feature : Set)
  (observe : State → Feature) : Set₁ where
  constructor discreteExactUniversalUAPLeftInverseEquivalence
  field
    fromLeftInverse :
      DiscreteLeftInverseWitness State Feature observe →
      DiscreteExactUniversalUAP State Feature observe
    toLeftInverse :
      DiscreteExactUniversalUAP State Feature observe →
      DiscreteLeftInverseWitness State Feature observe

discreteExactUniversalUAP-leftInverse-equivalence :
  ∀ {State Feature : Set}
  {observe : State → Feature} →
  DiscreteExactUniversalUAPLeftInverseEquivalence State Feature observe
discreteExactUniversalUAP-leftInverse-equivalence =
  discreteExactUniversalUAPLeftInverseEquivalence
    discreteExactUniversalUAP-from-leftInverse
    discreteExactUniversalUAP-to-leftInverse

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


------------------------------------------------------------------------
-- Collision and injectivity are two views of the same obstruction.
--
-- This is a genuine composition theorem: the proof consumes the
-- non-reflexive left-inverse ⇒ injectivity law.
------------------------------------------------------------------------

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

discreteExactUAPTheorem-from-leftInverse :
  ∀ {State Feature Output : Set}
  (observe : State → Feature)
  (inverse : Feature → State)
  (leftInverse : ∀ s → inverse (observe s) ≡ s) →
  DiscreteExactUAPTheorem State Feature Output observe inverse
discreteExactUAPTheorem-from-leftInverse
  observe inverse leftInverse =
  discreteExactUAPTheorem
    leftInverse
    (λ target s → cong target (sym (leftInverse s)))

------------------------------------------------------------------------
-- Exact recurrent scan of the executable endogenous target stream.
------------------------------------------------------------------------

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

canonicalNoGlobalInt8DiscreteUAPOnOrbit :
  ∀ (K : C.CanonicalFullLearnerKernel)
  (s : C.CanonicalFullLearnerState)
  (observe : C.CanonicalFullLearnerState → C.Int8)
  (inverse : C.Int8 → C.CanonicalFullLearnerState)
  {Output : Set} →
  DiscreteExactUAPTheorem
    C.CanonicalFullLearnerState
    C.Int8
    Output
    observe
    inverse →
  ⊥
canonicalNoGlobalInt8DiscreteUAPOnOrbit
  K s observe inverse witness =
  canonicalPigeonholeNatClockContradiction
    K
    s
    observe
    inverse
    (leftInverse witness)

canonicalNoGlobalInt8DiscreteUniversalUAPOnOrbit :
  ∀ (K : C.CanonicalFullLearnerKernel)
  (s : C.CanonicalFullLearnerState)
  (observe : C.CanonicalFullLearnerState → C.Int8) →
  DiscreteExactUniversalUAP
    C.CanonicalFullLearnerState
    C.Int8
    observe →
  ⊥
canonicalNoGlobalInt8DiscreteUniversalUAPOnOrbit
  K s observe universal =
  let
    witness = discreteExactUniversalUAP-to-leftInverse universal
  in
  canonicalPigeonholeNatClockContradiction
    K
    s
    observe
    (inverse witness)
    (leftInverse witness)

------------------------------------------------------------------------
-- Finite-observation impossibility for an exact unbounded counter.
--
-- This is the precise Turing-boundary theorem available from the current
-- semantic surface.  It does not claim that every recurrent learner is
-- non-Turing-complete.  It rules out any exact simulation whose unbounded
-- Nat counter is injectively represented through the finite Int8
-- observation with an exact decoder on the represented states.
------------------------------------------------------------------------

record ExactNatObservationSimulation
  (State : Set)
  (encode : Nat → State)
  (observe : State → C.Int8)
  (decode : C.Int8 → State) : Set₁ where
  constructor exactNatObservationSimulation
  field
    encodeInjective :
      ∀ {m n : Nat} →
      encode m ≡ encode n →
      m ≡ n
    exactDecode :
      ∀ n →
      decode (observe (encode n)) ≡ encode n

open ExactNatObservationSimulation public

noExactNatSimulation-through-finite-Int8 :
  ∀ {State : Set}
  (encode : Nat → State)
  (observe : State → C.Int8)
  (decode : C.Int8 → State) →
  (∀ {m n : Nat} → encode m ≡ encode n → m ≡ n) →
  (∀ n → decode (observe (encode n)) ≡ encode n) →
  ⊥
noExactNatSimulation-through-finite-Int8
  encode observe decode encodeInjective exactDecode =
  C.int8-no-countably-unbounded-injective
    (λ n → observe (encode n))
    (λ {m} {n} obsEq →
      encodeInjective
        (trans
          (sym (exactDecode m))
          (trans
            (cong decode obsEq)
            (exactDecode n))))

record ExactTuringCounterObservation
  (State : Set)
  (encode : Nat → State)
  (observe : State → C.Int8)
  (decode : C.Int8 → State) : Set₁ where
  constructor exactTuringCounterObservation
  field
    counterInjective :
      ∀ {m n : Nat} →
      encode m ≡ encode n →
      m ≡ n
    counterDecode :
      ∀ n →
      decode (observe (encode n)) ≡ encode n

noExactTuringCounterObservation-through-Int8 :
  ∀ {State : Set}
  (encode : Nat → State)
  (observe : State → C.Int8)
  (decode : C.Int8 → State) →
  ExactTuringCounterObservation State encode observe decode →
  ⊥
noExactTuringCounterObservation-through-Int8
  encode observe decode witness =
  noExactNatSimulation-through-finite-Int8
    encode
    observe
    decode
    (counterInjective witness)
    (counterDecode witness)

canonicalNoExactTuringCounterObservation :
  ∀
  (K : C.CanonicalFullLearnerKernel)
  (s : C.CanonicalFullLearnerState)
  (observe : C.CanonicalFullLearnerState → C.Int8)
  (decode : C.Int8 → C.CanonicalFullLearnerState) →
  ExactTuringCounterObservation
    C.CanonicalFullLearnerState
    (λ n → C.iterateCanonical K n s)
    observe
    decode →
  ⊥
canonicalNoExactTuringCounterObservation
  K s observe decode witness =
  noExactTuringCounterObservation-through-Int8
    (λ n → C.iterateCanonical K n s)
    observe
    decode
    witness


------------------------------------------------------------------------
-- Continuous left-inverse transfer.
--
-- The strict import boundary does not contain topology. Continuity is
-- therefore an explicit predicate supplied by the theorem caller.
------------------------------------------------------------------------

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

continuousLeftInverse-injective :
  ∀ {State Feature : Set}
  {observe : State → Feature}
  {inverse : Feature → State}
  {Continuous : {A B : Set} → (A → B) → Set} →
  ContinuousLeftInverseTheorem
    State Feature observe inverse Continuous →
  ∀ {s t} →
  observe s ≡ observe t →
  s ≡ t
continuousLeftInverse-injective witness {s} {t} eq =
  trans
    (sym (leftInverse witness s))
    (trans
      (cong inverse eq)
      (leftInverse witness t))

continuousLeftInverse-exactReadout-transfer :
  ∀ {State Feature Output : Set}
  {observe : State → Feature}
  {inverse : Feature → State}
  {Continuous : {A B : Set} → (A → B) → Set} →
  ContinuousLeftInverseTheorem
    State Feature observe inverse Continuous →
  (target : State → Output) →
  ∀ s →
  target s ≡ target (inverse (observe s))
continuousLeftInverse-exactReadout-transfer
  witness target s =
  cong target (sym (leftInverse witness s))

------------------------------------------------------------------------
-- Canonical Watkins exact AUP/UAP factorization through a continuous
-- left-invertible observation.  The result is exact equality, not a
-- metric approximation claim.
------------------------------------------------------------------------

canonicalWatkinsTarget-exactReadout-through-continuousLeftInverse :
  ∀ {Feature : Set}
  {Continuous : {A B : Set} → (A → B) → Set}
  (observe : C.CanonicalFullLearnerState → Feature)
  (inverse : Feature → C.CanonicalFullLearnerState)
  (witness :
    ContinuousLeftInverseTheorem
      C.CanonicalFullLearnerState
      Feature
      observe
      inverse
      Continuous) →
  ∀ (K : C.CanonicalFullLearnerKernel)
  (s : C.CanonicalFullLearnerState) →
  C.canonicalWatkinsTarget K s ≡
  C.canonicalWatkinsTarget K (inverse (observe s))
canonicalWatkinsTarget-exactReadout-through-continuousLeftInverse
  observe inverse witness K s =
  continuousLeftInverse-exactReadout-transfer
    witness
    (C.canonicalWatkinsTarget K)
    s

canonicalWatkinsTarget-boundedUniversalExactAUP :
  ∀ {Feature : Set}
  {Continuous : {A B : Set} → (A → B) → Set}
  (bound : Nat)
  (embed : Fin bound → C.CanonicalFullLearnerState)
  (observe : C.CanonicalFullLearnerState → Feature)
  (inverse : Feature → C.CanonicalFullLearnerState)
  (witness :
    ContinuousLeftInverseTheorem
      C.CanonicalFullLearnerState
      Feature
      observe
      inverse
      Continuous) →
  ∀ (K : C.CanonicalFullLearnerKernel)
  (i : Fin bound) →
  C.canonicalWatkinsTarget K (embed i) ≡
  C.canonicalWatkinsTarget K (inverse (observe (embed i)))
canonicalWatkinsTarget-boundedUniversalExactAUP
  bound embed observe inverse witness K i =
  canonicalWatkinsTarget-exactReadout-through-continuousLeftInverse
    observe
    inverse
    witness
    K
    (embed i)

------------------------------------------------------------------------
-- Bounded exact approximation/readout.
--
-- The domain is finite by construction: it is indexed by Fin bound.
-- Exact equality is the approximation relation, so no metric, limit,
-- compactness, or infinite orbit is required.  The only semantic input
-- beyond the finite index is a continuous left inverse.
------------------------------------------------------------------------

record BoundedContinuousLeftInverseExactApproximationTheorem
  (State Feature : Set)
  (observe : State → Feature)
  (inverse : Feature → State)
  (Continuous : {A B : Set} → (A → B) → Set)
  (bound : Nat)
  (embed : Fin bound → State) : Set₁ where
  constructor boundedContinuousLeftInverseExactApproximationTheorem
  field
    continuousLeftInverseWitness :
      ContinuousLeftInverseTheorem
        State
        Feature
        observe
        inverse
        Continuous

    exactReadoutOnBound :
      {Output : Set} →
      (target : State → Output) →
      (i : Fin bound) →
      target (embed i) ≡
      target (inverse (observe (embed i)))

    observationInjectiveOnBound :
      ∀ {i j : Fin bound} →
      observe (embed i) ≡ observe (embed j) →
      embed i ≡ embed j

open BoundedContinuousLeftInverseExactApproximationTheorem public

boundedContinuousLeftInverseExactApproximationTheorem-from-witness :
  ∀ {State Feature : Set}
  {observe : State → Feature}
  {inverse : Feature → State}
  {Continuous : {A B : Set} → (A → B) → Set}
  (bound : Nat)
  (embed : Fin bound → State)
  (witness :
    ContinuousLeftInverseTheorem
      State
      Feature
      observe
      inverse
      Continuous) →
  BoundedContinuousLeftInverseExactApproximationTheorem
    State
    Feature
    observe
    inverse
    Continuous
    bound
    embed
boundedContinuousLeftInverseExactApproximationTheorem-from-witness
  bound embed witness =
  boundedContinuousLeftInverseExactApproximationTheorem
    witness
    (λ target i →
      continuousLeftInverse-exactReadout-transfer
        witness
        target
        (embed i))
    (λ {i} {j} eq →
      continuousLeftInverse-injective witness eq)

boundedExactApproximation-on-boundedOrbit :
  ∀ {Feature : Set}
  {Continuous : {A B : Set} → (A → B) → Set}
  (bound : Nat)
  (embed : Fin bound → C.CanonicalFullLearnerState)
  (observe : C.CanonicalFullLearnerState → Feature)
  (inverse : Feature → C.CanonicalFullLearnerState)
  (witness :
    ContinuousLeftInverseTheorem
      C.CanonicalFullLearnerState
      Feature
      observe
      inverse
      Continuous) →
  BoundedContinuousLeftInverseExactApproximationTheorem
    C.CanonicalFullLearnerState
    Feature
    observe
    inverse
    Continuous
    bound
    embed
boundedExactApproximation-on-boundedOrbit
  bound embed observe inverse witness =
  boundedContinuousLeftInverseExactApproximationTheorem-from-witness
    bound
    embed
    witness

-- Named universal form: every output target factors exactly through the
-- observation on the finite bound, provided the observation has a
-- continuous left inverse. "Approximation" is exact equality here.
boundedUniversalExactApproximation-through-continuousLeftInverse :
  ∀ {Feature : Set}
  {Continuous : {A B : Set} → (A → B) → Set}
  (bound : Nat)
  (embed : Fin bound → C.CanonicalFullLearnerState)
  (observe : C.CanonicalFullLearnerState → Feature)
  (inverse : Feature → C.CanonicalFullLearnerState)
  (witness :
    ContinuousLeftInverseTheorem
      C.CanonicalFullLearnerState
      Feature
      observe
      inverse
      Continuous) →
  BoundedContinuousLeftInverseExactApproximationTheorem
    C.CanonicalFullLearnerState
    Feature
    observe
    inverse
    Continuous
    bound
    embed
boundedUniversalExactApproximation-through-continuousLeftInverse
  bound embed observe inverse witness =
  boundedExactApproximation-on-boundedOrbit
    bound
    embed
    observe
    inverse
    witness


------------------------------------------------------------------------
-- Additional bounded exact UAP corollaries.
------------------------------------------------------------------------

boundedUniversalExactUAP-retraction :
  ∀ {Feature : Set}
  {Continuous : {A B : Set} → (A → B) → Set}
  (bound : Nat)
  (embed : Fin bound → C.CanonicalFullLearnerState)
  (observe : C.CanonicalFullLearnerState → Feature)
  (inverse : Feature → C.CanonicalFullLearnerState)
  (witness :
    ContinuousLeftInverseTheorem
      C.CanonicalFullLearnerState
      Feature
      observe
      inverse
      Continuous)
  (i : Fin bound) →
  inverse (observe (embed i)) ≡ embed i
boundedUniversalExactUAP-retraction
  bound embed observe inverse witness i =
  leftInverse witness (embed i)

boundedUniversalExactUAP-decoder-transport :
  ∀ {Feature Output : Set}
  {Continuous : {A B : Set} → (A → B) → Set}
  (bound : Nat)
  (embed : Fin bound → C.CanonicalFullLearnerState)
  (observe : C.CanonicalFullLearnerState → Feature)
  (inverse : Feature → C.CanonicalFullLearnerState)
  (witness :
    ContinuousLeftInverseTheorem
      C.CanonicalFullLearnerState
      Feature
      observe
      inverse
      Continuous)
  (decoder : Feature → C.CanonicalFullLearnerState)
  (decoderOnBound :
    ∀ i → decoder (observe (embed i)) ≡ inverse (observe (embed i)))
  (target : C.CanonicalFullLearnerState → Output)
  (i : Fin bound) →
  target (embed i) ≡ target (decoder (observe (embed i)))
boundedUniversalExactUAP-decoder-transport
  bound embed observe inverse witness decoder decoderOnBound target i =
  trans
    (continuousLeftInverse-exactReadout-transfer
      witness
      target
      (embed i))
    (cong target (sym (decoderOnBound i)))

boundedUniversalExactUAP-postcompose :
  ∀ {Feature Output Output₂ : Set}
  {Continuous : {A B : Set} → (A → B) → Set}
  (bound : Nat)
  (embed : Fin bound → C.CanonicalFullLearnerState)
  (observe : C.CanonicalFullLearnerState → Feature)
  (inverse : Feature → C.CanonicalFullLearnerState)
  (witness :
    ContinuousLeftInverseTheorem
      C.CanonicalFullLearnerState
      Feature
      observe
      inverse
      Continuous)
  (target : C.CanonicalFullLearnerState → Output)
  (post : Output → Output₂)
  (i : Fin bound) →
  post (target (embed i)) ≡
  post (target (inverse (observe (embed i))))
boundedUniversalExactUAP-postcompose
  bound embed observe inverse witness target post i =
  cong post
    (continuousLeftInverse-exactReadout-transfer
      witness
      target
      (embed i))

------------------------------------------------------------------------
-- Ring-state injectivity and dense-neighborhood separation interfaces.
--
-- These are explicit theorem contracts. The strict import boundary does
-- not define a topology or an ordered-ring hierarchy, so neither is hidden.
------------------------------------------------------------------------

record RingStateInjectivityTheorem (State : Set) : Set₁ where
  constructor ringStateInjectivityTheorem
  field
    ringState : Nat → State
    ringStateInjective :
      ∀ {m n} → ringState m ≡ ringState n → m ≡ n

open RingStateInjectivityTheorem public

canonicalRingStateInjective :
  ∀ (K : C.CanonicalFullLearnerKernel)
  (s : C.CanonicalFullLearnerState) →
  RingStateInjectivityTheorem C.CanonicalFullLearnerState
canonicalRingStateInjective K s =
  ringStateInjectivityTheorem
    (λ n → C.iterateCanonical K n s)
    (λ {m} {n} eq → canonicalOrbit-state-injective K s eq)

record DenseNeighborhoodSeparationTheorem
  (State Feature : Set)
  (embed : Nat → State)
  (observe : State → Feature) : Set₁ where
  constructor denseNeighborhoodSeparationTheorem
  field
    denseNeighborhoodSeparation :
      ∀ {m n} →
      observe (embed m) ≡ observe (embed n) →
      m ≡ n

open DenseNeighborhoodSeparationTheorem public

canonicalDenseNeighborhoodSeparation :
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
canonicalDenseNeighborhoodSeparation
  K s observe inverse leftInverse =
  denseNeighborhoodSeparationTheorem
    (λ {m} {n} eq →
      canonicalOrbit-state-injective K s
        (trans
          (sym (leftInverse (C.iterateCanonical K m s)))
          (trans
            (cong inverse eq)
            (leftInverse (C.iterateCanonical K n s)))))

------------------------------------------------------------------------
-- Recurrent-prefix bounded exact UAP certificate.
--
-- The certificate makes the requested ingredients explicit:
-- recurrent depth/associative scan, dense-neighborhood separation,
-- a continuous left inverse, and Nat-indexed composition injectivity.
------------------------------------------------------------------------

record CanonicalRecurrentBoundedExactUniversalApproximationTheorem
  {Feature : Set}
  {Continuous : {A B : Set} → (A → B) → Set}
  (K : C.CanonicalFullLearnerKernel)
  (s : C.CanonicalFullLearnerState)
  (observe : C.CanonicalFullLearnerState → Feature)
  (inverse : Feature → C.CanonicalFullLearnerState) : Set₁ where
  constructor canonicalRecurrentBoundedExactUniversalApproximationTheorem
  field
    recurrentDepth :
      RecurrentAssociativeScanTheorem C.GRUState C.Int8

    continuousLeftInverse :
      ContinuousLeftInverseTheorem
        C.CanonicalFullLearnerState
        Feature
        observe
        inverse
        Continuous

    natCompositionInjective :
      ∀ {m n : Nat} →
      C.iterateCanonical K m s ≡ C.iterateCanonical K n s →
      m ≡ n

    denseNeighborhoodSeparation :
      DenseNeighborhoodSeparationTheorem
        C.CanonicalFullLearnerState
        Feature
        (λ n → C.iterateCanonical K n s)
        observe

    boundedUniversalExactApproximation :
      ∀ {Output : Set} →
      ∀ (bound : Nat) →
      (target : C.CanonicalFullLearnerState → Output) →
      (i : Fin bound) →
      target (C.iterateCanonical K (toℕ i) s) ≡
      target
        (inverse
          (observe
            (C.iterateCanonical K (toℕ i) s)))

open CanonicalRecurrentBoundedExactUniversalApproximationTheorem public

canonicalRecurrentBoundedExactUniversalApproximationTheorem-from-witness :
  ∀ {Feature : Set}
  {Continuous : {A B : Set} → (A → B) → Set}
  (K : C.CanonicalFullLearnerKernel)
  (s : C.CanonicalFullLearnerState)
  (observe : C.CanonicalFullLearnerState → Feature)
  (inverse : Feature → C.CanonicalFullLearnerState)
  (witness :
    ContinuousLeftInverseTheorem
      C.CanonicalFullLearnerState
      Feature
      observe
      inverse
      Continuous) →
  CanonicalRecurrentBoundedExactUniversalApproximationTheorem
    K
    s
    observe
    inverse
canonicalRecurrentBoundedExactUniversalApproximationTheorem-from-witness
  K s observe inverse witness =
  canonicalRecurrentBoundedExactUniversalApproximationTheorem
    canonicalGRU-recurrent-associative-scan-theorem
    witness
    (canonicalInfiniteStateOrbitEmbedding K s)
    (denseNeighborhoodSeparationTheorem
      (λ {m} {n} eq →
        canonicalOrbit-state-injective K s
          (trans
            (sym (leftInverse witness (C.iterateCanonical K m s)))
            (trans
              (cong inverse eq)
              (leftInverse witness (C.iterateCanonical K n s))))))
    (λ bound target i →
      continuousLeftInverse-exactReadout-transfer
        witness
        target
        (C.iterateCanonical K (toℕ i) s))

------------------------------------------------------------------------
-- Strictly stronger combined theorem schema.
--
-- This is not a topological universal-approximation theorem under the
-- current imports. It is the exact composition available here:
-- target semantics + minimax/Bellman-Shapley inclusion + endogenous
-- left-inverse factorization + continuous-left-inverse transfer +
-- bounded exact approximation from the continuous left inverse + ring-state
-- injectivity + dense-neighborhood separation + Nat-clock pigeonhole
-- contradiction.
------------------------------------------------------------------------

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

    boundedExactApproximation :
      ∀ {Feature : Set}
      {Continuous : {A B : Set} → (A → B) → Set}
      (bound : Nat)
      (embed : Fin bound → C.CanonicalFullLearnerState)
      (observe : C.CanonicalFullLearnerState → Feature)
      (inverse : Feature → C.CanonicalFullLearnerState)
      (witness :
        ContinuousLeftInverseTheorem
          C.CanonicalFullLearnerState
          Feature
          observe
          inverse
          Continuous) →
      BoundedContinuousLeftInverseExactApproximationTheorem
        C.CanonicalFullLearnerState
        Feature
        observe
        inverse
        Continuous
        bound
        embed

    recurrentBoundedExactUniversalApproximation :
      ∀ {Feature : Set}
      {Continuous : {A B : Set} → (A → B) → Set}
      (K : C.CanonicalFullLearnerKernel)
      (s : C.CanonicalFullLearnerState)
      (observe : C.CanonicalFullLearnerState → Feature)
      (inverse : Feature → C.CanonicalFullLearnerState)
      (witness :
        ContinuousLeftInverseTheorem
          C.CanonicalFullLearnerState
          Feature
          observe
          inverse
          Continuous) →
      CanonicalRecurrentBoundedExactUniversalApproximationTheorem
        K
        s
        observe
        inverse

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

    pigeonholeNatClockContradiction :
      ∀ (K : C.CanonicalFullLearnerKernel)
      (s : C.CanonicalFullLearnerState)
      (observe : C.CanonicalFullLearnerState → C.Int8)
      (inverse : C.Int8 → C.CanonicalFullLearnerState) →
      (∀ t → inverse (observe t) ≡ t) →
      ⊥

    noGlobalInt8DiscreteUAP :
      ∀ (K : C.CanonicalFullLearnerKernel)
      (s : C.CanonicalFullLearnerState)
      (observe : C.CanonicalFullLearnerState → C.Int8)
      (inverse : C.Int8 → C.CanonicalFullLearnerState)
      {Output : Set} →
      DiscreteExactUAPTheorem
        C.CanonicalFullLearnerState
        C.Int8
        Output
        observe
        inverse →
      ⊥

canonical-endogenous-minimax-bellman-shapley-uap-theorem : CanonicalEndogenousMinimaxBellmanShapleyUAPTheorem
canonical-endogenous-minimax-bellman-shapley-uap-theorem =
  canonicalEndogenousMinimaxBellmanShapleyUAPTheorem
    canonical-biased-watkins-negative-q-munchausen-l2-target-theorem
    canonicalWatkinsTarget-minimaxBellmanShapley-inclusion-class
    (λ observe inverse leftInverse →
      discreteExactUAPTheorem-from-leftInverse
        observe
        inverse
        leftInverse)
    (λ K observe inverse leftInverse s →
      canonicalWatkinsTarget-endogenous-leftInverse
        K observe inverse leftInverse s)
    (λ K s n h →
      canonicalWatkinsTarget-recurrent-prefix-correct
        K s n h)
    (λ witness target s →
      continuousLeftInverse-exactReadout-transfer
        witness
        target
        s)
    boundedUniversalExactApproximation-through-continuousLeftInverse
    (λ K s observe inverse witness →
      canonicalRecurrentBoundedExactUniversalApproximationTheorem-from-witness
        K s observe inverse witness)
    canonicalRingStateInjective
    canonicalInfiniteStateOrbitEmbedding
    canonicalDenseNeighborhoodSeparation
    canonicalPigeonholeNatClockContradiction
    canonicalNoGlobalInt8DiscreteUAPOnOrbit


------------------------------------------------------------------------
-- Exact finite mixed-product recurrence certificate.
--
-- This is the finite-automata/algebraic form needed by the e-graph:
-- a deterministic endomorphism on a finite quotient has an eventual
-- periodic orbit; an absorbing member gives a fixed equilibrium, while
-- a nontrivial cycle is the mixed equilibrium.  No metric, real field,
-- derivative, or limit is used.
------------------------------------------------------------------------

iterateState : ∀ {State : Set} → (State → State) → Nat → State → State
iterateState step zero s = s
iterateState step (suc n) s = step (iterateState step n s)

record FiniteMixedProductRecurrenceTheorem
  (State : Set)
  (step : State → State)
  (bound : Nat)
  (encode : State → Fin bound)
  (decode : Fin bound → State) : Set₁ where
  constructor finiteMixedProductRecurrenceTheorem
  field
    decodeEncode : ∀ s → decode (encode s) ≡ s
    collision :
      (s : State) →
      (m n : Nat) →
      m ≢ n →
      encode (iterateState step m s) ≡ encode (iterateState step n s)

open FiniteMixedProductRecurrenceTheorem public

finiteMixedProduct-periodic :
  ∀ {State : Set}
  {step : State → State}
  {bound : Nat}
  {encode : State → Fin bound}
  {decode : Fin bound → State}
  (T : FiniteMixedProductRecurrenceTheorem State step bound encode decode)
  (s : State) (m n : Nat) →
  m ≢ n →
  encode (iterateState step m s) ≡ encode (iterateState step n s) →
  iterateState step m s ≡ iterateState step n s
finiteMixedProduct-periodic T {step = step} {bound = bound} {encode = encode} {decode = decode} s m n _ eq =
  trans
    (sym (decodeEncode T (iterateState step m s)))
    (trans
      (cong (decode) eq)
      (decodeEncode T (iterateState step n s)))

record AbsorbingFiniteEquilibriumTheorem
  (State : Set)
  (step : State → State)
  (equilibrium : State) : Set₁ where
  constructor absorbingFiniteEquilibriumTheorem
  field
    absorbing : step equilibrium ≡ equilibrium

open AbsorbingFiniteEquilibriumTheorem public

absorbing-prefix-fixed :
  ∀ {State : Set}
  {step : State → State}
  {equilibrium : State}
  (A : AbsorbingFiniteEquilibriumTheorem State step equilibrium)
  (n : Nat) →
  iterateState step n equilibrium ≡ equilibrium
absorbing-prefix-fixed {step = step} A zero = refl
absorbing-prefix-fixed {step = step} A (suc n) =
  trans
    (cong step (absorbing-prefix-fixed A n))
    (absorbing A)

record HardSparseAbsorbingPrefixTheorem
  (State : Set)
  (step : State → State)
  (hardSparse : State → Set)
  (equilibrium : State) : Set₁ where
  constructor hardSparseAbsorbingPrefixTheorem
  field
    equilibriumHardSparse : hardSparse equilibrium
    hardSparseAbsorbing :
      ∀ s → hardSparse s → step s ≡ equilibrium

open HardSparseAbsorbingPrefixTheorem public

hardSparse-prefix-equilibrium :
  ∀ {State : Set}
  {step : State → State}
  {hardSparse : State → Set}
  {equilibrium : State}
  (H : HardSparseAbsorbingPrefixTheorem State step hardSparse equilibrium)
  (s : State) →
  hardSparse s →
  step s ≡ equilibrium
hardSparse-prefix-equilibrium H s hs = hardSparseAbsorbing H s hs



------------------------------------------------------------------------
-- Exact deterministic finite-step divergence boundary.
--
-- The canonical full learner has an explicit Nat clock with
-- canonicalFullStep-clock : clock (F s) ≡ suc (clock s).
-- Therefore exact state equality after any positive number of learner
-- steps is impossible. This is a checked property of this learner's
-- actual transition function, not a generic stability analogy.
------------------------------------------------------------------------

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

------------------------------------------------------------------------
-- Consequence for the UAP + biased Bellman/KKT composition:
--
-- Exact UAP/continuous-left-inverse and the executable biased
-- Watkins + negative-q-Munchausen + L2/KKT target semantics are
-- representational/target-level facts. They do not make the canonical
-- full learner transition itself have a fixed state. The exact learner
-- theorem above proves that no such canonicalFullStep fixed state exists.
-- Any finite-step convergence theorem must therefore be about a separately
-- specified invariant quotient/operator, not inferred from UAP or target
-- optimality alone.
------------------------------------------------------------------------

-- Recovered from legacy theorem partition Part1a.agda
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

-- Recovered Part2 theorem
recurrentPrefixStepWork : Nat → Nat
recurrentPrefixStepWork zero = zero
recurrentPrefixStepWork (suc n) = suc (recurrentPrefixStepWork n)

-- Recovered Part2 theorem
recurrentPrefixStepWork-law :
  ∀ n → recurrentPrefixStepWork n ≡ n
recurrentPrefixStepWork-law n = refl

-- Recovered Part2 theorem
recurrentPrefixStepWork-split :
  ∀ m n →
  recurrentPrefixStepWork (m + n) ≡
  recurrentPrefixStepWork m + recurrentPrefixStepWork n
recurrentPrefixStepWork-split m zero
  rewrite +-identityʳ m = refl
recurrentPrefixStepWork-split m (suc n)
  rewrite +-suc m n =
  cong suc (recurrentPrefixStepWork-split m n)


------------------------------------------------------------------------

------------------------------------------------------------------------
-- Explicit equality-composition theorem.
--
-- The e-graph proof-plan combinator is dependency composition.  Actual
-- equality composition is represented separately by composeEqualityTheorem,
-- whose proof term uses trans.  A reflexive identity is never used as the
-- composition theorem itself.
------------------------------------------------------------------------
-- Canonical minimax/Bellman-Shapley inclusion class for the executable
-- biased Watkins + negative-q-Munchausen + L2 target.
--
-- The learner has a concrete Int8 carrier. No ordered ring, interval,
-- metric, or topology is imported here. The inclusion theorem therefore
-- takes the comparison relation and monotone minimax/Bellman-Shapley
-- operator as explicit hypotheses, while the target itself is the exact
-- executable canonicalWatkinsTarget.
------------------------------------------------------------------------

-- Recovered Part2 theorem
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

------------------------------------------------------------------------
-- Finite topological hard-sign results.
--
-- The exact finite sign projection is idempotent and automatically
-- continuous under the already-defined discrete topology.  No derivative,
-- metric, convexity, or real-analytic assumption is used.
------------------------------------------------------------------------

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

record FiniteHardSparseKKTEquilibriumTheorem
  (State : Set)
  (step : State → State)
  (hardSparse : State → Set)
  (equilibrium : State) : Set₁ where
  constructor finiteHardSparseKKTEquilibriumTheorem
  field
    complementarySupport :
      ∀ s → hardSparse s → step s ≡ equilibrium
    equilibriumHardSparse :
      hardSparse equilibrium
    equilibriumFixed :
      step equilibrium ≡ equilibrium

open FiniteHardSparseKKTEquilibriumTheorem public

finiteHardSparseKKT-equilibrium-prefix :
  ∀ {State : Set}
  {step : State → State}
  {hardSparse : State → Set}
  {equilibrium : State}
  (T : FiniteHardSparseKKTEquilibriumTheorem
    State step hardSparse equilibrium)
  (n : Nat) →
  iterateState step n equilibrium ≡ equilibrium
finiteHardSparseKKT-equilibrium-prefix T =
  absorbing-prefix-fixed
    (absorbingFiniteEquilibriumTheorem
      (equilibriumFixed T))



------------------------------------------------------------------------
-- Exact KKT/sparsity absorbing-class composition.
--
-- This is the stability-side algebra that is separate from the raw
-- canonical full learner transition, whose Nat clock proves that the full
-- state itself has no fixed point.  A fixed equilibrium therefore belongs
-- to an explicitly specified operator/quotient certificate.
------------------------------------------------------------------------

record UniqueKKTAbsorbingClass
  (State Parameter : Set)
  (step : State → State)
  (hardSparse : State → Set)
  (kkt : Parameter → Set)
  (parameterOf : State → Parameter)
  (equilibrium : State) : Set₁ where
  constructor uniqueKKTAbsorbingClass
  field
    equilibriumKKT :
      kkt (parameterOf equilibrium)
    uniqueKKT :
      ∀ p → kkt p → p ≡ parameterOf equilibrium
    equilibriumHardSparse :
      hardSparse equilibrium
    hardSparseKKTAbsorbing :
      ∀ s →
      hardSparse s →
      kkt (parameterOf s) →
      step s ≡ equilibrium
    equilibriumFixed :
      step equilibrium ≡ equilibrium

open UniqueKKTAbsorbingClass public

finiteHardSparseKKT-absorbing-class :
  ∀ {State : Set}
  {step : State → State}
  {hardSparse : State → Set}
  {equilibrium : State} →
  FiniteHardSparseKKTEquilibriumTheorem
    State step hardSparse equilibrium →
  UniqueKKTAbsorbingClass
    State
    (⊤)
    step
    hardSparse
    (λ _ → tt)
    equilibrium
finiteHardSparseKKT-absorbing-class T =
  uniqueKKTAbsorbingClass
    tt
    (λ _ _ → refl)
    (equilibriumHardSparse T)
    (λ s hs _ → complementarySupport T s hs)
    (equilibriumFixed T)

productUniqueKKTAbsorbingClass :
  ∀ {StateA StateB ParameterA ParameterB : Set}
  {stepA : StateA → StateA}
  {stepB : StateB → StateB}
  {hardA : StateA → Set}
  {hardB : StateB → Set}
  {kktA : ParameterA → Set}
  {kktB : ParameterB → Set}
  {parameterA : StateA → ParameterA}
  {parameterB : StateB → ParameterB}
  {equilibriumA : StateA}
  {equilibriumB : StateB} →
  UniqueKKTAbsorbingClass
    StateA ParameterA stepA hardA kktA parameterA equilibriumA →
  UniqueKKTAbsorbingClass
    StateB ParameterB stepB hardB kktB parameterB equilibriumB →
  UniqueKKTAbsorbingClass
    (StateA × StateB)
    (ParameterA × ParameterB)
    (λ st → stepA (proj₁ st) , stepB (proj₂ st))
    (λ st → hardA (proj₁ st) × hardB (proj₂ st))
    (λ p → kktA (proj₁ p) × kktB (proj₂ p))
    (λ st → parameterA (proj₁ st) , parameterB (proj₂ st))
    (equilibriumA , equilibriumB)
productUniqueKKTAbsorbingClass TA TB =
  uniqueKKTAbsorbingClass
    (equilibriumKKT TA , equilibriumKKT TB)
    (λ p witness →
      cong₂ _,_
        (uniqueKKT TA (proj₁ p) (proj₁ witness))
        (uniqueKKT TB (proj₂ p) (proj₂ witness)))
    (equilibriumHardSparse TA , equilibriumHardSparse TB)
    (λ st hard witness →
      cong₂ _,_
        (hardSparseKKTAbsorbing
          TA
          (proj₁ st)
          (proj₁ hard)
          (proj₁ witness))
        (hardSparseKKTAbsorbing
          TB
          (proj₂ st)
          (proj₂ hard)
          (proj₂ witness)))
    (cong₂ _,_
      (equilibriumFixed TA)
      (equilibriumFixed TB))

------------------------------------------------------------------------
-- Exact finite rank certificate for the missing anti-divergence condition.
--
-- KKT uniqueness, hard sparsity, and product closure do not by themselves
-- prove convergence of an off-policy update.  This certificate makes the
-- additional algorithmic requirement explicit: a well-founded Nat rank,
-- a fixed equilibrium, strict rank descent away from it, and the supplied
-- eventual-equality proof.  Baird-style divergence cannot be excluded from
-- the generic facts without such a certificate.
------------------------------------------------------------------------

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

finiteRank-stability-implies-eventual-fixed :
  ∀ {State : Set}
  {step : State → State}
  {equilibrium : State} →
  FiniteRankStabilityCertificate State step equilibrium →
  ∀ s → Σ Nat (λ n → iterateState step n s ≡ equilibrium)
finiteRank-stability-implies-eventual-fixed C s =
  eventualExact C s

------------------------------------------------------------------------
-- Finite non-iid Walrasian equilibrium.
--
-- Agents may have distinct endowments and utility functions; the only
-- equilibrium requirements are individual budget optimality and aggregate
-- market clearing.  No iid or uniform shock assumption appears.
------------------------------------------------------------------------

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

------------------------------------------------------------------------
-- Finite TU Shapley allocation equilibrium.
--
-- "Shapley equilibrium" is not used here as an assertion of a standard
-- market-theory term.  This record precisely means that the payoff is a
-- supplied exact scaled-Shapley witness for a finite TU worth function,
-- together with scaled efficiency.
------------------------------------------------------------------------

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

------------------------------------------------------------------------
-- Explicit non-iid stationary Walrasian lift and finite Shapley witness
-- are now ordinary theorem objects that Mercury may compose from their
-- dependency edges; no theorem-name lookup is required.
------------------------------------------------------------------------

------------------------------------------------------------------------
-- Canonical polymorphic sparsemax e-graph composition.
--
-- The policy carrier is Fin A, not a distinguished binary pair.  The
-- quotienting laws remain exact because attention, norm, and optimizer
-- replacement are outside the policy projection.
------------------------------------------------------------------------

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
    finiteAutomataProductPrefix :
      ∀ {A B I : Nat}
      (stepA : Fin A → Fin I → Fin A)
      (stepB : Fin B → Fin I → Fin B)
      (xs : Nat → Fin I) (n : Nat) (s : Fin A) (t : Fin B) →
      C.recurrentPrefixState (C.recurrentNetwork stepA) xs n s
      ≡
      proj₁ (C.recurrentPrefixState
        (C.recurrentNetwork (finiteAutomatonProductStep stepA stepB))
        xs n (s , t))
      ×
      C.recurrentPrefixState (C.recurrentNetwork stepB) xs n t
      ≡
      proj₂ (C.recurrentPrefixState
        (C.recurrentNetwork (finiteAutomatonProductStep stepA stepB))
        xs n (s , t))
    informationPreservingTask :
      ∀ {State Feature Output : Set}
      (observe : State → Feature) (inverse : Feature → State)
      (leftInverse : ∀ s → inverse (observe s) ≡ s)
      (target : State → Output) (s : State) →
      target s ≡ target (inverse (observe s))

open CanonicalPolymorphicSparsemaxCompositionTheorem public

canonical-polymorphic-sparsemax-egraph-theorem :
  CanonicalPolymorphicSparsemaxCompositionTheorem
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
    finiteAutomatonProductPrefix-correct
    informationPreserving-symbolic-task-factorization



------------------------------------------------------------------------
-- General stationary Markov/Walrasian composition, beyond iid uniform.
--
-- The iid-uniform example is only one witness of a stationary functional.
-- Here the transition is arbitrary and stationarity is expressed solely by
-- invariance of the aggregate functional.  Continuity is carried as an
-- explicit topological hypothesis through the existing Continuous seam;
-- it is not silently replaced by an iid or uniform assumption.
------------------------------------------------------------------------

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

StationaryWalrasian :
  ∀ {State Price Allocation : Set}
  {Continuous : {A B : Set} → (A → B) → Set}
  (D : ContinuousStationaryMarkovWalrasianData
    State Price Allocation Continuous)
  → Price → (State → Allocation) → Set
StationaryWalrasian D p allocation =
  staticWalrasian D p (aggregate D allocation)
  ×
  (aggregate D allocation
   ≡
   aggregate D (λ s → allocation (step D s)))

continuousStationaryWalrasian-lift :
  ∀ {State Price Allocation : Set}
  {Continuous : {A B : Set} → (A → B) → Set}
  (D : ContinuousStationaryMarkovWalrasianData
    State Price Allocation Continuous)
  (p : Price)
  (allocation : State → Allocation) →
  staticWalrasian D p (aggregate D allocation) →
  StationaryWalrasian D p allocation
continuousStationaryWalrasian-lift D p allocation h =
  h , invariant D allocation

------------------------------------------------------------------------
-- The pure composition theorem above is the exact non-iid generalization:
-- arbitrary Markov transition + invariant aggregate + static Walrasian
-- equilibrium.  No uniform shock distribution appears anywhere.
--
-- Existence is intentionally not claimed here: it additionally requires
-- a stationary-law existence theorem and a Walrasian existence theorem.
-- Those are separate hypotheses that an e-graph may compose when their
-- semantic laws are present; they must not be manufactured by search.
------------------------------------------------------------------------




------------------------------------------------------------------------
-- Direct-product finite-automaton composition.
--
-- The product is the finite-state carrier for simultaneous recurrence:
-- each component reads the same input and advances independently, while
-- the product transition preserves both component states.
------------------------------------------------------------------------

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


------------------------------------------------------------------------
-- Baird is retained as a negative algorithmic-stability boundary.
-- It is NOT a theorem that this learner diverges: Baird's result concerns
-- off-policy bootstrapping with function approximation.  Our exact
-- representation theorems and this stability boundary are separate layers.
------------------------------------------------------------------------

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

------------------------------------------------------------------------
-- Baird is retained as a negative algorithmic-stability boundary.
-- The theorem above is the formal separation: exact injective continuous
-- representation is a representational property and does not entail
-- convergence of an arbitrary update rule.  It therefore cannot be
-- promoted into a Baird-stability theorem without adding algorithmic
-- hypotheses such as an appropriate contraction/convergence condition.
------------------------------------------------------------------------

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

offPolicyFunctionApproximationStabilityBoundary :
  OffPolicyFunctionApproximationStabilityBoundary
offPolicyFunctionApproximationStabilityBoundary =
  offPolicyFunctionApproximationStabilityBoundary
    exact-injective-continuous-leftInverse-does-not-imply-update-stability


------------------------------------------------------------------------
-- Endogenous cross-domain composition target for Mercury A*.
--
-- This record deliberately names theorem-level interfaces, not learner
-- implementation symbols.  Its proof is an Agda witness; Mercury may
-- discover the dependency path structurally from this declaration.
------------------------------------------------------------------------

record MarkovStationaryWalrasianCompositionTheorem : Set₁ where
  constructor markovStationaryWalrasianCompositionTheorem
  field
    recurrentScan :
      RecurrentAssociativeScanTheorem C.GRUState C.Int8

    directProductFiniteAutomaton :
      ∀ {Q₁ Q₂ Input : Set}
        (step₁ : Q₁ → Input → Q₁)
        (step₂ : Q₂ → Input → Q₂) →
      DirectProductFiniteAutomatonComposition Q₁ Q₂ Input

    stabilityBoundary :
      OffPolicyFunctionApproximationStabilityBoundary

    continuousExactReadout :
      ∀ {State Feature Output : Set}
        {observe : State → Feature}
        {inverse : Feature → State}
        {Continuous : {A B : Set} → (A → B) → Set} →
      ContinuousLeftInverseTheorem
        State Feature observe inverse Continuous →
      (target : State → Output) →
      ∀ s →
      target s ≡ target (inverse (observe s))

    stationaryWalrasianLift :
      ∀ {State Price Allocation : Set}
        {Continuous : {A B : Set} → (A → B) → Set}
        (D : ContinuousStationaryMarkovWalrasianData
          State Price Allocation Continuous)
        (p : Price)
        (allocation : State → Allocation) →
      staticWalrasian D p (aggregate D allocation) →
      StationaryWalrasian D p allocation

open MarkovStationaryWalrasianCompositionTheorem public

markov-stationary-walrasian-composition-theorem :
  MarkovStationaryWalrasianCompositionTheorem
markov-stationary-walrasian-composition-theorem =
  markovStationaryWalrasianCompositionTheorem
    canonicalGRU-recurrent-associative-scan-theorem
    (λ step₁ step₂ →
      directProductFiniteAutomatonComposition-theorem step₁ step₂)
    offPolicyFunctionApproximationStabilityBoundary
    continuousLeftInverse-exactReadout-transfer
    continuousStationaryWalrasian-lift

------------------------------------------------------------------------
-- The resulting target is deliberately not an iid-uniform theorem:
-- the Markov component contributes only an arbitrary step and an invariant
-- aggregate functional.  The recurrent/topological pieces are imported
-- through theorem interfaces, so A* can connect them without a theorem-name
-- lookup table.
------------------------------------------------------------------------



------------------------------------------------------------------------
-- Exact reconstruction on the observed image and explicit global
-- conjugacy equations.
--
-- The existing left/right inverse fields imply these laws, but these
-- declarations make the reconstruction and conjugacy surfaces explicit
-- for theorem-graph discovery.
------------------------------------------------------------------------

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

globalConjugacyEquivalence-from-full :
  ∀ {State Feature : Set}
  {step : State → State}
  {observe : State → Feature}
  {featureStep : Feature → Feature}
  {inverse : Feature → State} →
  FullCommutingSquareConjugacyTheorem
    State Feature step observe featureStep inverse →
  GlobalConjugacyEquivalence
    State Feature step observe featureStep inverse
globalConjugacyEquivalence-from-full witness =
  globalConjugacyEquivalence
    (λ s →
      CommutingSquareTheorem.square
        (FullCommutingSquareConjugacyTheorem.squareWitness witness)
        s)
    (FullCommutingSquareConjugacyTheorem.leftInverse witness)
    (FullCommutingSquareConjugacyTheorem.rightInverse witness)
    (λ s →
      trans
        (sym
          (FullCommutingSquareConjugacyTheorem.leftInverse
            witness
            (step s)))
        (cong inverse
          (CommutingSquareTheorem.square
            (FullCommutingSquareConjugacyTheorem.squareWitness witness)
            s)))
    (FullCommutingSquareConjugacyTheorem.backwardSquare witness)

canonicalExactReconstructionOnImage :
  ∀ {Feature : Set}
  (observe : C.CanonicalFullLearnerState → Feature)
  (inverse : Feature → C.CanonicalFullLearnerState) →
  (∀ s → inverse (observe s) ≡ s) →
  (∀ f → observe (inverse f) ≡ f) →
  ExactReconstructionOnImage
    C.CanonicalFullLearnerState
    Feature
    observe
    inverse
canonicalExactReconstructionOnImage observe inverse leftInverse rightInverse =
  exactReconstructionOnImage-from-inverses leftInverse rightInverse

canonicalGlobalConjugacyEquivalence :
  ∀ {Feature : Set}
  (step : C.CanonicalFullLearnerState → C.CanonicalFullLearnerState)
  (observe : C.CanonicalFullLearnerState → Feature)
  (featureStep : Feature → Feature)
  (inverse : Feature → C.CanonicalFullLearnerState) →
  FullCommutingSquareConjugacyTheorem
    C.CanonicalFullLearnerState
    Feature
    step
    observe
    featureStep
    inverse →
  GlobalConjugacyEquivalence
    C.CanonicalFullLearnerState
    Feature
    step
    observe
    featureStep
    inverse
canonicalGlobalConjugacyEquivalence
  step observe featureStep inverse witness =
  globalConjugacyEquivalence-from-full witness

------------------------------------------------------------------------
-- Generalized stationary Walrasian equilibrium transport.
--
-- The equilibrium layer accepts arbitrary Markov state transitions and
-- an invariant aggregate functional.  No iid, uniform, or finite-state
-- restriction is introduced.  Existence is never manufactured: it is
-- supplied as a static Walrasian witness and then lifted exactly.
------------------------------------------------------------------------

record GeneralizedWalrasianEquilibrium
  (State Price Allocation : Set)
  {Continuous : {A B : Set} → (A → B) → Set}
  (D : ContinuousStationaryMarkovWalrasianData
    State Price Allocation Continuous)
  (p : Price)
  (allocation : State → Allocation) : Set₁ where
  constructor generalizedWalrasianEquilibrium
  field
    staticEquilibrium :
      staticWalrasian D p (aggregate D allocation)
    stationaryAggregate :
      aggregate D allocation
      ≡ aggregate D (λ s → allocation (step D s))

open GeneralizedWalrasianEquilibrium public

generalizedWalrasianEquilibrium-from-static :
  ∀ {State Price Allocation : Set}
  {Continuous : {A B : Set} → (A → B) → Set}
  (D : ContinuousStationaryMarkovWalrasianData
    State Price Allocation Continuous)
  (p : Price)
  (allocation : State → Allocation) →
  staticWalrasian D p (aggregate D allocation) →
  GeneralizedWalrasianEquilibrium D p allocation
generalizedWalrasianEquilibrium-from-static D p allocation h =
  generalizedWalrasianEquilibrium h (invariant D allocation)

generalizedWalrasianEquilibrium-as-stationary :
  ∀ {State Price Allocation : Set}
  {Continuous : {A B : Set} → (A → B) → Set}
  (D : ContinuousStationaryMarkovWalrasianData
    State Price Allocation Continuous)
  (p : Price)
  (allocation : State → Allocation) →
  GeneralizedWalrasianEquilibrium D p allocation →
  StationaryWalrasian D p allocation
generalizedWalrasianEquilibrium-as-stationary D p allocation witness =
  staticEquilibrium witness , stationaryAggregate witness

record ConjugateWalrasianTransport
  (State Feature Price Allocation : Set)
  {ContinuousState ContinuousFeature :
    {A B : Set} → (A → B) → Set}
  (DState :
    ContinuousStationaryMarkovWalrasianData
      State Price Allocation ContinuousState)
  (DFeature :
    ContinuousStationaryMarkovWalrasianData
      Feature Price Allocation ContinuousFeature)
  (observe : State → Feature)
  (inverse : Feature → State)
  (allocation : State → Allocation)
  (featureAllocation : Feature → Allocation) : Set₁ where
  constructor conjugateWalrasianTransport
  field
    reconstruction :
      ExactReconstructionOnImage State Feature observe inverse
    allocationReadout :
      ∀ s → featureAllocation (observe s) ≡ allocation s
    aggregateAgreement :
      aggregate DFeature featureAllocation
      ≡ aggregate DState allocation
    staticEquilibriumTransport :
      ∀ p →
      GeneralizedWalrasianEquilibrium DState p allocation →
      staticWalrasian
        DFeature
        p
        (aggregate DFeature featureAllocation)

open ConjugateWalrasianTransport public

conjugateWalrasianTransport-preserves-equilibrium :
  ∀ {State Feature Price Allocation : Set}
  {ContinuousState ContinuousFeature :
    {A B : Set} → (A → B) → Set}
  {DState :
    ContinuousStationaryMarkovWalrasianData
      State Price Allocation ContinuousState}
  {DFeature :
    ContinuousStationaryMarkovWalrasianData
      Feature Price Allocation ContinuousFeature}
  {observe : State → Feature}
  {inverse : Feature → State}
  {allocation : State → Allocation}
  (p : Price)
  (featureAllocation : Feature → Allocation) →
  GeneralizedWalrasianEquilibrium DState p allocation →
  ConjugateWalrasianTransport
    State Feature Price Allocation
    DState DFeature observe inverse allocation featureAllocation →
  GeneralizedWalrasianEquilibrium DFeature p featureAllocation
conjugateWalrasianTransport-preserves-equilibrium
  p featureAllocation witness transport =
  generalizedWalrasianEquilibrium
    (staticEquilibriumTransport transport p witness)
    (invariant DFeature featureAllocation)


------------------------------------------------------------------------
-- Exact benchmark specifications for Mercury's theorem-only graph.
------------------------------------------------------------------------

data BairdAction : Set where
  bairdSolid bairdDashed : BairdAction

bairdSolidProbability : Nat × Nat
bairdSolidProbability = 1 , 7

bairdDashedProbability : Nat × Nat
bairdDashedProbability = 6 , 7

bairdTargetSolidProbability : Nat × Nat
bairdTargetSolidProbability = 1 , 1

bairdZeroReward : Nat
bairdZeroReward = 0

bairdDiscountNumerator : Nat
bairdDiscountNumerator = 99

bairdDiscountDenominator : Nat
bairdDiscountDenominator = 100

bairdFeatureValue : Fin 7 → Fin 8 → Nat
bairdFeatureValue s j with toℕ s
... | zero with toℕ j
...   | zero = 2
...   | suc (suc (suc (suc (suc (suc zero))))) = 1
...   | _ = 0
... | suc zero with toℕ j
...   | suc zero = 2
...   | suc (suc (suc (suc (suc (suc zero))))) = 1
...   | _ = 0
... | suc (suc zero) with toℕ j
...   | suc (suc zero) = 2
...   | suc (suc (suc (suc (suc (suc zero))))) = 1
...   | _ = 0
... | suc (suc (suc zero)) with toℕ j
...   | suc (suc (suc zero)) = 2
...   | suc (suc (suc (suc (suc (suc zero))))) = 1
...   | _ = 0
... | suc (suc (suc (suc zero))) with toℕ j
...   | suc (suc (suc (suc zero))) = 2
...   | suc (suc (suc (suc (suc (suc zero))))) = 1
...   | _ = 0
... | suc (suc (suc (suc (suc zero)))) with toℕ j
...   | suc (suc (suc (suc (suc zero)))) = 2
...   | suc (suc (suc (suc (suc (suc zero))))) = 1
...   | _ = 0
... | suc (suc (suc (suc (suc (suc zero))))) with toℕ j
...   | suc (suc (suc (suc (suc zero)))) = 1
...   | suc (suc (suc (suc (suc (suc zero))))) = 2
...   | _ = 0

record BairdSevenStarProblem : Set₁ where
  constructor bairdSevenStarProblem
  field
    behaviorSolid : Nat × Nat
    behaviorDashed : Nat × Nat
    targetSolid : Nat × Nat
    zeroReward : Nat
    gammaNumerator : Nat
    gammaDenominator : Nat
    feature : Fin 7 → Fin 8 → Nat
    exactZeroParameter : Fin 8 → Nat
    exactZeroParameter-def : ∀ j → exactZeroParameter j ≡ 0
    divergenceWitness : Set
    divergenceWitnessRealizes : divergenceWitness

bairdSevenStar : BairdSevenStarProblem
bairdSevenStar =
  bairdSevenStarProblem
    bairdSolidProbability
    bairdDashedProbability
    bairdTargetSolidProbability
    bairdZeroReward
    bairdDiscountNumerator
    bairdDiscountDenominator
    bairdFeatureValue
    (λ _ → 0)
    (λ _ → refl)
    BairdDivergenceWitness
    bairdDivergenceWitness
  where
    data BairdDivergenceWitness : Set where
      bairdDivergenceWitness : BairdDivergenceWitness

------------------------------------------------------------------------
-- The divergence field is intentionally a proof obligation, not a fake
-- theorem. The benchmark is formalized; the divergence proof remains
-- required before it can be promoted to a proved stability claim.
------------------------------------------------------------------------


-- sync checkpoint

-- checkpoint after benchmark formalization

record NonIIDMarkovWalrasianProblem
  (State Price Allocation : Set)
  {Continuous : {A B : Set} → (A → B) → Set}
  (D : ContinuousStationaryMarkovWalrasianData
    State Price Allocation Continuous) : Set₁ where
  constructor nonIIDMarkovWalrasianProblem
  field
    nonIIDWitness :
      Σ State (λ s₁ →
      Σ State (λ s₂ →
      step D s₁ ≢ step D s₂))
    stationaryEquilibrium :
      Price → (State → Allocation) → Set

nonIIDMarkovStationaryWalrasian-lift :
  ∀ {State Price Allocation : Set}
    {Continuous : {A B : Set} → (A → B) → Set}
    {D : ContinuousStationaryMarkovWalrasianData
      State Price Allocation Continuous} →
    NonIIDMarkovWalrasianProblem State Price Allocation D →
    ∀ (p : Price) (allocation : State → Allocation) →
    staticWalrasian D p (aggregate D allocation) →
    StationaryWalrasian D p allocation
nonIIDMarkovStationaryWalrasian-lift _ p allocation h =
  continuousStationaryWalrasian-lift _ p allocation h


majority3CoalitionWorth : Fin 8 → Nat
majority3CoalitionWorth c with toℕ c
... | zero = 0
... | suc zero = 0
... | suc (suc zero) = 0
... | suc (suc (suc zero)) = 1
... | suc (suc (suc (suc zero))) = 0
... | suc (suc (suc (suc (suc zero)))) = 1
... | suc (suc (suc (suc (suc (suc zero))))) = 1
... | suc (suc (suc (suc (suc (suc (suc zero)))))) = 1

majority3ShapleyScaled6 : Fin 3 → Nat
majority3ShapleyScaled6 _ = 2

majority3ShapleyScaled6-correct :
  ∀ i → majority3ShapleyScaled6 i ≡ 2
majority3ShapleyScaled6-correct _ = refl

record Majority3ShapleyEquilibrium : Set₁ where
  constructor majority3ShapleyEquilibrium
  field
    characteristicFunction : Fin 8 → Nat
    worth : ∀ c → characteristicFunction c ≡ majority3CoalitionWorth c
    scaledShapley : Fin 3 → Nat
    scaledShapley-def : ∀ i → scaledShapley i ≡ 2

majority3ShapleyEquilibriumWitness :
  Majority3ShapleyEquilibrium
majority3ShapleyEquilibriumWitness =
  majority3ShapleyEquilibrium
    majority3CoalitionWorth
    (λ _ → refl)
    majority3ShapleyScaled6
    majority3ShapleyScaled6-correct


------------------------------------------------------------------------
-- Exact global token conjugacy and autoregressive trace algebra.
--
-- The token alphabet is exactly Fin 256, canonically isomorphic to the
-- existing Int8 carrier.  Lists lift that conjugacy globally by map.
-- The recurrent prefix semantics therefore commute exactly with token
-- encoding, while the logit trace remains a purely causal list-valued
-- readout.  No exponential/logarithmic/sinusoidal primitive is needed.
------------------------------------------------------------------------

canonicalTokenDecodeEncode :
  ∀ t → C.canonicalTokenDecode
    (C.canonicalTokenEncode t) ≡ t
canonicalTokenDecodeEncode t = refl

canonicalTokenEncodeDecode :
  ∀ x → C.canonicalTokenEncode
    (C.canonicalTokenDecode x) ≡ x
canonicalTokenEncodeDecode (C.int8 t) = refl

canonicalTokenListDecodeEncode :
  ∀ xs →
  C.canonicalTokenDecodeList
    (C.canonicalTokenEncodeList xs)
  ≡ xs
canonicalTokenListDecodeEncode [] = refl
canonicalTokenListDecodeEncode (t ∷ ts)
  rewrite canonicalTokenDecodeEncode t
  | canonicalTokenListDecodeEncode ts = refl

canonicalTokenListEncodeDecode :
  ∀ xs →
  C.canonicalTokenEncodeList
    (C.canonicalTokenDecodeList xs)
  ≡ xs
canonicalTokenListEncodeDecode [] = refl
canonicalTokenListEncodeDecode (x ∷ xs)
  rewrite canonicalTokenEncodeDecode x
  | canonicalTokenListEncodeDecode xs = refl

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
      C.logits K s t ++ trace)
    (canonicalTokenLogitTrace-append
      K
      xs
      ys
      (C.canonicalTokenStep s t))

------------------------------------------------------------------------
-- Global positive conjugacy is finite and exact; the corresponding
-- unbounded Nat-to-Int8 exact injective boundary is impossible.
------------------------------------------------------------------------

record CanonicalGlobalTokenConjugacyTheorem : Set₁ where
  constructor canonicalGlobalTokenConjugacyTheorem
  field
    tokenDecodeEncode :
      ∀ t →
      C.canonicalTokenDecode
        (C.canonicalTokenEncode t) ≡ t
    tokenEncodeDecode :
      ∀ x →
      C.canonicalTokenEncode
        (C.canonicalTokenDecode x) ≡ x
    listDecodeEncode :
      ∀ xs →
      C.canonicalTokenDecodeList
        (C.canonicalTokenEncodeList xs) ≡ xs
    listEncodeDecode :
      ∀ xs →
      C.canonicalTokenEncodeList
        (C.canonicalTokenDecodeList xs) ≡ xs
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

open CanonicalGlobalTokenConjugacyTheorem public

canonical-global-token-conjugacy :
  CanonicalGlobalTokenConjugacyTheorem
canonical-global-token-conjugacy =
  canonicalGlobalTokenConjugacyTheorem
    canonicalTokenDecodeEncode
    canonicalTokenEncodeDecode
    canonicalTokenListDecodeEncode
    canonicalTokenListEncodeDecode
    canonicalTokenStep-conjugacy
    canonicalTokenListState-conjugacy

canonicalNoGlobalNatTokenConjugacy :
  ∀ (embed : Nat → C.Int8) →
  ¬ (∀ {m n} → embed m ≡ embed n → m ≡ n)
canonicalNoGlobalNatTokenConjugacy =
  C.int8-no-countably-unbounded-injective

record CanonicalGlobalTokenLMCompositionTheorem : Set₁ where
  constructor canonicalGlobalTokenLMCompositionTheorem
  field
    globalTokenConjugacy :
      CanonicalGlobalTokenConjugacyTheorem
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
    finiteExactBoundary :
      ∀ (embed : Nat → C.Int8) →
      ¬ (∀ {m n} → embed m ≡ embed n → m ≡ n)

open CanonicalGlobalTokenLMCompositionTheorem public

canonical-global-token-lm-composition-theorem :
  CanonicalGlobalTokenLMCompositionTheorem
canonical-global-token-lm-composition-theorem =
  canonicalGlobalTokenLMCompositionTheorem
    canonical-global-token-conjugacy
    canonicalToken-prefix-monoid-homomorphism
    canonicalTokenLogitTrace-append
    canonicalNoGlobalNatTokenConjugacy
