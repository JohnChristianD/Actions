{-# OPTIONS --safe #-}

module Exotic.ERL.FullCoupled.TheoremsMonolith where

------------------------------------------------------------------------
-- Single active theorem source for the architecture and all emergence proofs.
-- The learner is the only intentionally separated Agda module and is
-- imported below. Economic, Arrow-Debreu, KKT, welfare, and other proof
-- surfaces belong in this monolith rather than in parallel theorem modules.
-- Discovery/CI should target this file.
------------------------------------------------------------------------

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

------------------------------------------------------------------------
-- Isomorphism/conjugacy laws for deterministic state evolution.
-- A state isomorphism preserves iteration traces and transports finite-cycle
-- exclusion to the isomorphic state representation.
------------------------------------------------------------------------

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

-- NormPair is not only policy-invariant: it is dynamically inert under the
-- canonical transition. Replacing the norm before a step is definitionally
-- the same as taking the step first and replacing the preserved norm after it.
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


------------------------------------------------------------------------
-- Exact Turing-completeness contract for the canonical composition.
--
-- This is tied to the actual CanonicalFullLearnerState,
-- CanonicalFullLearnerKernel, canonicalFullStep, and exact Int8 semantics.
-- It does not quantify over a substitute RNN or an arbitrary-precision
-- surrogate.  An inhabitant requires a genuine universal two-counter
-- simulation with exact state equality and a halting/output correspondence.
-- The declaration itself does not assert that such an inhabitant exists.
------------------------------------------------------------------------

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

------------------------------------------------------------------------
-- Exact obstruction for the proposed universal contract.
--
-- The exact canonical full transition has no fixed points because its
-- Nat clock increments on every step. Therefore the contract above cannot
-- hold for the self-looping two-counter machine: exact state equality would
-- force a fixed point of canonicalFullStep. This is tied to the actual
-- CanonicalFullLearnerState and exact Int8-based component semantics; it
-- does not replace them with a different-precision or input-augmented model.
------------------------------------------------------------------------

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

------------------------------------------------------------------------
-- Exact stabilization can feed the existing convergence-witness interface.
-- The convergence relation is an explicit premise; rank alone does not
-- manufacture topology.
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
-- The policy carrier is a generic learner action carrier, not a distinguished binary pair.
-- quotienting laws remain exact because norm and optimizer replacement
-- are outside the policy projection.
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



------------------------------------------------------------------------
-- The finite automaton product was a separate finite-carrier branch and is
-- deliberately not part of the canonical sparsemax composition.  The
-- surviving composition is carrier-polymorphic: NormPair/F4 replacement
-- invariance, exact recurrent scan, and exact readout transport.
------------------------------------------------------------------------

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

offPolicyFunctionApproximationStabilityBoundaryWitness :
  OffPolicyFunctionApproximationStabilityBoundary
offPolicyFunctionApproximationStabilityBoundaryWitness =
  offPolicyFunctionApproximationStabilityBoundary
    exact-injective-continuous-leftInverse-does-not-imply-update-stability


------------------------------------------------------------------------
-- Endogenous cross-domain composition target for Mercury A*.
--
-- This record deliberately names theorem-level interfaces, not learner
-- implementation symbols.  Its proof is an Agda witness; Mercury may
-- discover the dependency path structurally from this declaration.
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


------------------------------------------------------------------------
-- Exact transport through arbitrary representation isomorphisms.
--
-- The transport law is carrier-polymorphic.  Finite carriers are merely
-- one possible specialization and no longer define the canonical theorem.
------------------------------------------------------------------------

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

------------------------------------------------------------------------
-- Exact POMDP-model transport seam.
--
-- This is deliberately a transport theorem, not a probabilistic
-- convergence theorem.  Distribution semantics remain explicit, while
-- state/action/observation carriers are arbitrary Sets.
------------------------------------------------------------------------

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

------------------------------------------------------------------------
-- Global positive conjugacy is finite and exact; the corresponding
-- unbounded Nat-to-Int8 exact injective boundary is impossible.
------------------------------------------------------------------------

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

------------------------------------------------------------------------
-- Exact integer Haar kernel and A* cost algebra surfaces.
--
-- The 2-point Haar kernel is represented in the canonical Int8 ring.
-- Its two defining scalar identities are kept exact at the proof seam;
-- the normalized real-valued Haar matrix would require 1/sqrt(2), so
-- this theorem intentionally certifies the integer, scaled kernel.
------------------------------------------------------------------------

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

------------------------------------------------------------------------
-- A* cost algebra seam. Mercury owns the cost-guided graph search;
-- Agda certifies the exact Nat cost identities used by that search.
------------------------------------------------------------------------

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


------------------------------------------------------------------------
-- Emergent endogenous A* transport closure.
--
-- The A* cost algebra is kernel-checked by Agda.  The exact token trace
-- makes the cost-guided path endogenous to the canonical recurrent learner.
-- Representation transport is carrier-polymorphic and uses no finite carrier.
-- dependency.
------------------------------------------------------------------------

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

------------------------------------------------------------------------
-- Exact global optimizer stability on the unbounded integer carrier.
------------------------------------------------------------------------

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

------------------------------------------------------------------------
-- F4 infinite-horizon forcing ray.
--
-- The canonical F4 coordinate is exact integer algebra.  With zero global
-- L2 correction and unit signal at every step, the theta coordinate grows
-- exactly linearly with horizon.  This is a formal counterexample to any
-- unconditional upper-bound / sure-boundedness claim for the current F4
-- semantics.  NormPair is not involved in this calculation.
------------------------------------------------------------------------

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

------------------------------------------------------------------------
-- The linear-growth theorem is the exact reason the earlier coercivity /
-- boundedness fields must not be promoted to unconditional facts.  There is
-- also no analytic coercivity notion in the current F4 record: no objective,
-- norm, or real-valued level-set relation is part of F4IntUKernel.  The
-- correct closure is therefore a negative theorem plus a separately stated
-- analytic bridge if a genuine coercivity theorem is desired later.
------------------------------------------------------------------------

------------------------------------------------------------------------
-- Fully connected F4/NormPair stability composition.
--
-- "Sure stability" here means the exact deterministic stability certificate
-- already proved by the F4 theorem: theta translation, preservation of the
-- non-theta coordinates, and equal-input step stability.  It is not a
-- probabilistic convergence claim.  Frank-Wolfe/rounding regret and the
-- Markov stationary/Walrasian interface remain explicit downstream fields.
------------------------------------------------------------------------

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

------------------------------------------------------------------------
-- The exact Turing boundary is contract-specific. It does not state
-- that every function class is non-universal; it states that the exact
-- contract named by this repository is impossible.
------------------------------------------------------------------------

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


------------------------------------------------------------------------
-- Stationary convergence without a Lyapunov premise.
--
-- For a finite observed Markov chain, the stationary/convergence seam is
-- carried by the transition kernel plus recurrence/aperiodicity assumptions.
-- This is deliberately independent of the monotone-energy contract above.
------------------------------------------------------------------------

------------------------------------------------------------------------
-- 2026-09-22 graph-search requirement/subcomposition completion.
------------------------------------------------------------------------

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


------------------------------------------------------------------------
-- Minimal exact finite probability semantics.
--
-- No analytic probability import is required here. A finite distribution
-- is represented by non-negative Nat weights with a positive denominator
-- and an exact normalization certificate. Each coordinate therefore denotes
-- the rational mass weight/denominator without introducing a second
-- arithmetic tower into the canonical theorem surface.
------------------------------------------------------------------------
-- New endogenous composition: probabilistic POMDP semantics plus exact
-- belief-state transport preserve the endogenous observation boundary.
------------------------------------------------------------------------

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

maxwellStateIsomorphism :
  ∀ {Carrier State : Set} →
  MaxwellExactConjugacyData Carrier State →
  StateIsomorphism State Carrier
maxwellStateIsomorphism D =
  stateIsomorphism
    (encode D)
    (decode D)
    (decodeEncode D)
    (encodeDecode D)

record ConnectedMaxwellTsallisExactConjugacyTheorem
  (Carrier State : Set) : Set₁ where
  constructor connectedMaxwellTsallisExactConjugacyTheorem
  field
    semantics :
      MaxwellExactConjugacyData Carrier State

    translatedStep :
      ∀ x →
      decode semantics (encodedStep semantics (encode semantics x))
      ≡
      step semantics x

    exactMaxwellConjugacy :
      ∀ x →
      encode semantics (step semantics x)
      ≡
      encodedStep semantics (encode semantics x)

open ConnectedMaxwellTsallisExactConjugacyTheorem public

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

record ConnectedCarrierAgnosticHodgeMaxwellGRUF4WatkinsExactPrefixHorizonRegretConjugacyEGraphCompositionTheorem
  (GRU : Set)
  {Continuous : {A B : Set} → (A → B) → Set} : Set₁ where
  constructor connectedCarrierAgnosticHodgeMaxwellGRUF4WatkinsExactPrefixHorizonRegretConjugacyEGraphCompositionTheorem
  field
    carrierComposition :
      ConnectedCarrierAgnosticHodgeMaxwellGRUF4WatkinsEGraphCompositionTheorem
        GRU

    exactStepComposition :
      ConnectedCarrierAgnosticHodgeMaxwellGRUF4WatkinsExactStepCompositionTheorem
        GRU

    exactEndpoint :
      ConnectedContinuousHodgeMaxwellGRUF4WatkinsExactPrefixHorizonRegretConjugacyEGraphCompositionTheorem
        GRU

    globalInjectivityComposition :
      ConnectedHodgeMaxwellGRUF4WatkinsGlobalEncodeInjectivityCompositionTheorem
        GRU

open ConnectedCarrierAgnosticHodgeMaxwellGRUF4WatkinsExactPrefixHorizonRegretConjugacyEGraphCompositionTheorem public

record HodgeMaxwellMiddleDegreeInvolutionTransportTheorem
  (GRU : Set)
  {Feature : Set}
  {Continuous : {A B : Set} → (A → B) → Set}
  (representation :
    ConnectedContinuousHodgeMaxwellGRURepresentationTheorem GRU)
  (observe :
    Solution (semantics representation) → Feature)
  (inverse :
    Feature → Solution (semantics representation))
  (embed :
    Nat → Solution (semantics representation))
  (star :
    Solution (semantics representation) →
    Solution (semantics representation))
  (starGRU : GRU → GRU)
  (observeGRU : GRU → Feature) : Set₁ where
  constructor hodgeMaxwellMiddleDegreeInvolutionTransportTheorem
  field
    observation :
      ContinuousLeftInverseTheorem
        (Solution (semantics representation))
        Feature
        observe
        inverse
        Continuous

    neighborhoodSeparation :
      DenseNeighborhoodSeparationTheorem
        (Solution (semantics representation))
        Feature
        embed
        observe

    observeFactorization :
      ∀ s →
      observe s ≡
      observeGRU
        (to
          (globalStateIsomorphism representation)
          s)

    starConjugacy :
      ∀ s →
      to
        (globalStateIsomorphism representation)
        (star s)
      ≡
      starGRU
        (to
          (globalStateIsomorphism representation)
          s)

    gruInvolution :
      ∀ g →
      starGRU (starGRU g) ≡ g

open HodgeMaxwellMiddleDegreeInvolutionTransportTheorem public

record ConnectedHodgeMaxwellTsallisDivergenceCompositionTheorem
  (GRU : Set)
  {Continuous : {A B : Set} → (A → B) → Set} : Set₁ where
  constructor connectedHodgeMaxwellTsallisDivergenceCompositionTheorem
  field
    hodgeMaxwell :
      ConnectedContinuousHodgeMaxwellGRURepresentationTheorem GRU

    tsallis :
      ConnectedMaxwellTsallisExactConjugacyTheorem
        GRU
        (Solution (semantics hodgeMaxwell))

open ConnectedHodgeMaxwellTsallisDivergenceCompositionTheorem public

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

------------------------------------------------------------------------
-- Architecture/emergence boundary.
--
-- This monolith owns the economic architecture and every theorem that
-- establishes an emergent consequence. CanonicalLearnerMonolith is the
-- only separated learner implementation and is imported at the top of this
-- file. Do not create parallel economic proof modules for e-graph nodes.
------------------------------------------------------------------------

------------------------------------------------------------------------
-- Singular generalized Walrasian data.
--
-- One economic relation is exposed to the connected GRU/Hodge-Maxwell/
-- Tsallis/POMDP composition. Walrasian, Arrow-Debreu, and KKT are not
-- separate semantic nodes: any desired characterization is represented
-- by the single generalized characterization predicate and its bridge.
-- No finite-dimensional, continuity, differentiability, convexity,
-- monotonicity, or free-disposal assumption is built into the carrier.
------------------------------------------------------------------------

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

------------------------------------------------------------------------
-- Concrete economic closure on the canonical generalized surface.
--
-- The finite non-iid witness above is not a second equilibrium ontology.
-- It is interpreted directly as GeneralizedWalrasianData, with its
-- individual budget-optimality and aggregate resource-balance witnesses
-- supplying the generalized equilibrium predicate.
------------------------------------------------------------------------

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

------------------------------------------------------------------------
-- Logical boundary for the first-welfare demand condition.
--
-- noStrictAffordableAlternative is a revealed demand-optimality
-- condition. It is neither monotonicity nor local nonsatiation, and
-- monotonicity + local nonsatiation do not imply it without the
-- equilibrium/demand-maximization and budget structure that connect
-- preferences to affordability.
--
-- Whole-allocation preferences are a separate generalization of the
-- preference domain: they allow an agent's ranking to depend on the
-- entire allocation. Heterogeneity means different agents may carry
-- different preference relations. Heterogeneity therefore enlarges
-- the profile space, while whole-allocation dependence enlarges the
-- argument domain; neither is an algebraic strengthening of
-- monotonicity/LNS.
------------------------------------------------------------------------

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


------------------------------------------------------------------------
-- Generalized Second Welfare theorem.
--
-- The theorem is stated against MegaGeneralizedWalrasianEquilibrium rather
-- than a separate Arrow-Debreu/KKT surface.  The supporting-price step is
-- the economic separation input; once it supplies a price and the
-- generalized characterization, the existing characterization bridge
-- proves the actual equilibrium witness.  Heterogeneous agents and
-- whole-allocation/interdependent preferences remain inside the generalized
-- equilibrium relation rather than being erased into a scalar demand model.
------------------------------------------------------------------------

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

------------------------------------------------------------------------
-- Unconditional F4/NormPair factor stability.
--
-- This theorem composes only closed proof terms: exact F4 optimizer
-- stability and exact NormPair quotient/factor compatibility.  It makes
-- no convergence, boundedness, economic, or external certificate claim.
------------------------------------------------------------------------

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

------------------------------------------------------------------------

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

------------------------------------------------------------------------
-- Recursive Radner as an instance of the singular generalized Walrasian
-- ontology.
--
-- The generalized equilibrium carrier stores the full state-contingent
-- price/allocation/portfolio processes.  The equilibrium predicate carries
-- the Radner feasibility, optimality, commodity clearing, asset clearing,
-- and recursive-law witnesses.  This avoids introducing a second
-- equilibrium ontology into the monolith.
------------------------------------------------------------------------

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


------------------------------------------------------------------------
-- F4 coercivity/boundedness frontier composed with NormPair stability
-- and economic injectivity.
--
-- Important semantic boundary: the canonical F4 theorem proves exact
-- Z-valued step stability. It does not currently prove an analytic
-- coercivity theorem or a raw global thetaQ boundedness theorem. Those
-- are therefore explicit proof premises here rather than renamed
-- consequences of F4 stability.
------------------------------------------------------------------------

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

------------------------------------------------------------------------
-- Strict unconditional economic impossibility.
--
-- Even after the closed F4/NormPair factor-stability theorem is available,
-- the generalized Walrasian contract itself does not imply existence.
-- The singleton countermodel has an empty equilibrium predicate.
------------------------------------------------------------------------

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
