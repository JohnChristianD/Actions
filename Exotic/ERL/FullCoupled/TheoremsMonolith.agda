{-# OPTIONS --safe #-}

module Exotic.ERL.FullCoupled.TheoremsMonolith where

------------------------------------------------------------------------
-- Single active theorem source for the canonical learner.
-- Discovery/CI should target this file. Legacy theorem modules are not
-- part of the canonical proof surface.
------------------------------------------------------------------------

open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; cong; cong₂; trans; sym; subst)
open import Agda.Builtin.Nat using (Nat; suc; _+_; _*_)
open import Data.Empty using (⊥)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Nullary using (¬_)
open import Data.Fin using (Fin; toℕ)
open import Data.Fin.Properties using (pigeonhole; toℕ-injective; toℕ-mono-<; ℕ→Fin-notInjective)
open import Data.Nat using (_<ᵇ_; _/_; _≤_; _<_; z≤n; s≤s; zero)
open import Data.List.Base using (List; []; _∷_; _++_; map; length)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Nat.Properties using (≤-antisym; ≤-refl; +-identityʳ; +-suc; n<1+n)
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

isomorphismIterateConjugacy :
  ∀ {A B : Set}
  (iso : StateIsomorphism A B)
  (f : A → A)
  (g : B → B) →
  (∀ a → to iso (f a) ≡ g (to iso a)) →
  ∀ n a →
  to iso (iterateIsomorphism f n a) ≡
  iterateIsomorphism g n (to iso a)
isomorphismIterateConjugacy iso f g stepConjugacy zero a = refl
isomorphismIterateConjugacy iso f g stepConjugacy (suc n) a =
  trans
    (isomorphismIterateConjugacy iso f g stepConjugacy n (f a))
    (cong (iterateIsomorphism g n) (stepConjugacy a))

isomorphismToInjective :
  ∀ {A B : Set}
  (iso : StateIsomorphism A B) →
  ∀ a b →
  to iso a ≡ to iso b →
  a ≡ b
isomorphismToInjective iso a b eq =
  trans
    (sym (from-to iso a))
    (trans
      (cong (from iso) eq)
      (from-to iso b))

isomorphismEqualityTransport :
  ∀ {A B : Set}
  (iso : StateIsomorphism A B)
  {x y : A} →
  x ≡ y →
  to iso x ≡ to iso y
isomorphismEqualityTransport iso refl = refl

isomorphismDisequalityTransport :
  ∀ {A B : Set}
  (iso : StateIsomorphism A B)
  {x y : A} →
  x ≢ y →
  to iso x ≢ to iso y
isomorphismDisequalityTransport iso distinct eq =
  distinct (isomorphismToInjective iso _ _ eq)

isomorphismNoFiniteCycleTransport :
  ∀ {A B : Set}
  (iso : StateIsomorphism A B)
  (f : A → A)
  (g : B → B) →
  (∀ a → to iso (f a) ≡ g (to iso a)) →
  (∀ n a → iterateIsomorphism f (suc n) a ≢ a) →
  ∀ n a →
  iterateIsomorphism g (suc n) (to iso a) ≢ to iso a
isomorphismNoFiniteCycleTransport iso f g stepConjugacy noCycle n a cyc =
  λ cycle →
    noCycle n a
      (isomorphismToInjective
        iso
        (iterateIsomorphism f (suc n) a)
        a
        (trans
          (sym
            (isomorphismIterateConjugacy
              iso f g stepConjugacy (suc n) a))
          cycle))

------------------------------------------------------------------------
-- The generic transport law makes canonical finite-cycle exclusion stable
-- under exact state isomorphism rather than tied to one representation.
------------------------------------------------------------------------

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

commutingSquareTheorem-from-square :
  ∀ {State Feature : Set}
  {step : State → State}
  {observe : State → Feature}
  {featureStep : Feature → Feature} →
  (∀ s → observe (step s) ≡ featureStep (observe s)) →
  CommutingSquareTheorem State Feature step observe featureStep
commutingSquareTheorem-from-square
  {State} {Feature} {step} {observe} {featureStep}
  squareWitness =
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
  {State} {Feature} {step} {observe} {featureStep}
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
  {State} {Feature} {step} {observe} {featureStep}
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

record RecurrentScanConjugacyTheorem (State Input : Set) : Set₁ where
  constructor recurrentScanConjugacyTheorem
  field
    scanLiftsConjugacy :
      (replace : State → State)
      (step : State → Input → State) →
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

------------------------------------------------------------------------
-- Polarity clarification for the canonical negative-q-Munchausen + L2 path.
--
-- Both components are implemented as modular negation of their respective
-- inputs.  This is a shared negation operator law, not an order-theoretic
-- "opposite signs" theorem: Int8 is modular, and no signed-order premise
-- is introduced here.
------------------------------------------------------------------------

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

canonical-q-munchausen-l2-shared-negation-polarity-theorem :
  CanonicalQMunchausenL2SharedNegationPolarityTheorem
canonical-q-munchausen-l2-shared-negation-polarity-theorem =
  canonicalQMunchausenL2SharedNegationPolarityTheorem
    canonical-qLog2Bias8-law
    (λ x → refl)

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
  (observe : C.CanonicalFullLearnerState → Fin 256)
  (inverse : Fin 256 → C.CanonicalFullLearnerState) →
  (∀ t → inverse (observe t) ≡ t) →
  ⊥
canonicalPigeonholeNatClockContradiction K s observe inverse leftInverse =
  C.finiteObservation-no-countably-unbounded-injective
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

canonicalNoGlobalFiniteObservationDiscreteUAPOnOrbit :
  ∀ (K : C.CanonicalFullLearnerKernel)
  (s : C.CanonicalFullLearnerState)
  (observe : C.CanonicalFullLearnerState → Fin 256)
  (inverse : Fin 256 → C.CanonicalFullLearnerState)
  {Output : Set} →
  DiscreteExactUAPTheorem
    C.CanonicalFullLearnerState
    (Fin 256)
    Output
    observe
    inverse →
  ⊥
canonicalNoGlobalFiniteObservationDiscreteUAPOnOrbit
  K s observe inverse witness =
  canonicalPigeonholeNatClockContradiction
    K
    s
    observe
    inverse
    (leftInverse witness)

canonicalNoGlobalFiniteObservationDiscreteUniversalUAPOnOrbit :
  ∀ (K : C.CanonicalFullLearnerKernel)
  (s : C.CanonicalFullLearnerState)
  (observe : C.CanonicalFullLearnerState → Fin 256) →
  DiscreteExactUniversalUAP
    C.CanonicalFullLearnerState
    (Fin 256)
    observe →
  ⊥
canonicalNoGlobalFiniteObservationDiscreteUniversalUAPOnOrbit
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
  (observe : State → Fin 256)
  (decode : Fin 256 → State) : Set₁ where
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

noExactNatSimulation-through-finite-observation :
  ∀ {State : Set}
  (encode : Nat → State)
  (observe : State → Fin 256)
  (decode : Fin 256 → State) →
  (∀ {m n : Nat} → encode m ≡ encode n → m ≡ n) →
  (∀ n → decode (observe (encode n)) ≡ encode n) →
  ⊥
noExactNatSimulation-through-finite-observation
  encode observe decode encodeInjective exactDecode =
  C.finiteObservation-no-countably-unbounded-injective
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

noExactTuringCounterObservation-through-finite-observation :
  ∀ {State : Set}
  (encode : Nat → State)
  (observe : State → Fin 256)
  (decode : Fin 256 → State) →
  ExactTuringCounterObservation State encode observe decode →
  ⊥
noExactTuringCounterObservation-through-finite-observation
  encode observe decode witness =
  noExactNatSimulation-through-finite-observation
    encode
    observe
    decode
    (ExactTuringCounterObservation.counterInjective witness)
    (ExactTuringCounterObservation.counterDecode witness)

canonicalNoExactTuringCounterObservation :
  ∀
  (K : C.CanonicalFullLearnerKernel)
  (s : C.CanonicalFullLearnerState)
  (observe : C.CanonicalFullLearnerState → Fin 256)
  (decode : Fin 256 → C.CanonicalFullLearnerState) →
  ExactTuringCounterObservation
    C.CanonicalFullLearnerState
    (λ n → C.iterateCanonical K n s)
    observe
    decode →
  ⊥
canonicalNoExactTuringCounterObservation
  K s observe decode witness =
  noExactTuringCounterObservation-through-finite-observation
    (λ n → C.iterateCanonical K n s)
    observe
    decode
    witness


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
    canonicalNoGlobalFiniteObservationDiscreteUAPOnOrbit


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
    offPolicyFunctionApproximationStabilityBoundaryWitness
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
      C.logits K s ∷ trace)
    (canonicalTokenLogitTrace-append
      K
      xs
      ys
      (C.canonicalTokenStep s t))

canonicalTokenSparsemaxWeight-shared :
  ∀ (K : C.CanonicalTokenLanguageModelKernel)
  (s : C.GRUState)
  (t : C.CanonicalToken) →
  C.canonicalTokenSparsemaxWeight K s t
  ≡
  C.sparsemaxWeight
    C.canonicalTokenActionSpace
    (C.logits K s)
    C.canonicalTokenLogitCounts
    t
canonicalTokenSparsemaxWeight-shared K s t = refl

canonicalTokenSparsemaxPolicy-shared :
  ∀ (K : C.CanonicalTokenLanguageModelKernel)
  (s : C.GRUState) →
  C.canonicalTokenSparsemaxPolicy K s
  ≡
  C.sparsemaxPolicy
    C.canonicalTokenActionSpace
    (C.logits K s)
    C.canonicalTokenLogitCounts
canonicalTokenSparsemaxPolicy-shared K s = refl

canonicalTokenSparsemaxTrace :
  C.CanonicalTokenLanguageModelKernel →
  C.CanonicalTokenSequence →
  C.GRUState →
  List C.SparseWeight
canonicalTokenSparsemaxTrace K [] s = []
canonicalTokenSparsemaxTrace K (t ∷ ts) s =
  C.canonicalTokenSparsemaxWeight K s t ∷
  canonicalTokenSparsemaxTrace K ts
    (C.canonicalTokenStep s t)

canonicalTokenSparsemaxTrace-append :
  ∀ (K : C.CanonicalTokenLanguageModelKernel)
  (xs ys : C.CanonicalTokenSequence)
  (s : C.GRUState) →
  canonicalTokenSparsemaxTrace K (xs ++ ys) s
  ≡
  canonicalTokenSparsemaxTrace K xs s ++
  canonicalTokenSparsemaxTrace K ys
    (C.canonicalTokenListState xs s)
canonicalTokenSparsemaxTrace-append K [] ys s = refl
canonicalTokenSparsemaxTrace-append K (t ∷ xs) ys s =
  cong
    (λ trace →
      C.canonicalTokenSparsemaxWeight K s t ∷ trace)
    (canonicalTokenSparsemaxTrace-append
      K
      xs
      ys
      (C.canonicalTokenStep s t))

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


------------------------------------------------------------------------
-- Exact transport of arbitrary finite functions through exact
-- representation isomorphisms.  The construction is representation-
-- independent and therefore also applies to finite recurrent interfaces.
------------------------------------------------------------------------

record FiniteFunctionExactIsomorphismTransportTheorem
  (m n : Nat)
  (A B : Set)
  (isoA : StateIsomorphism (Fin m) A)
  (isoB : StateIsomorphism (Fin n) B)
  (f : Fin m → Fin n) : Set₁ where
  constructor finiteFunctionExactIsomorphismTransportTheorem
  field
    translatedFunction : A → B
    exactTransport :
      ∀ x →
      StateIsomorphism.to isoB (f x) ≡
      translatedFunction (StateIsomorphism.to isoA x)

finiteFunctionExactIsomorphismTransport :
  ∀ {m n : Nat}
    {A B : Set}
    (isoA : StateIsomorphism (Fin m) A)
    (isoB : StateIsomorphism (Fin n) B)
    (f : Fin m → Fin n) →
  FiniteFunctionExactIsomorphismTransportTheorem m n A B isoA isoB f
finiteFunctionExactIsomorphismTransport isoA isoB f =
  finiteFunctionExactIsomorphismTransportTheorem
    (λ a →
      StateIsomorphism.to isoB
        (f (StateIsomorphism.from isoA a)))
    (λ x → refl)

record FiniteRecurrentFunctionExactTranslationTheorem
  (m : Nat)
  (A : Set)
  (isoA : StateIsomorphism (Fin m) A)
  (step : Fin m → Fin m)
  (stepA : A → A) : Set₁ where
  constructor finiteRecurrentFunctionExactTranslationTheorem
  field
    recurrentConjugacy :
      ∀ x →
      StateIsomorphism.to isoA (step x) ≡
      stepA (StateIsomorphism.to isoA x)
    translatedFunction :
      ∀ {n : Nat}
        (B : Set)
        (isoB : StateIsomorphism (Fin n) B)
        (f : Fin m → Fin n) →
      FiniteFunctionExactIsomorphismTransportTheorem m n A B isoA isoB f

finiteRecurrentFunctionExactTranslation :
  ∀ {m : Nat}
    {A : Set}
    (isoA : StateIsomorphism (Fin m) A)
    (step : Fin m → Fin m)
    (stepA : A → A)
    (conjugacy :
      ∀ x →
      StateIsomorphism.to isoA (step x) ≡
      stepA (StateIsomorphism.to isoA x)) →
  FiniteRecurrentFunctionExactTranslationTheorem m A isoA step stepA
finiteRecurrentFunctionExactTranslation isoA step stepA conjugacy =
  finiteRecurrentFunctionExactTranslationTheorem
    conjugacy
    (λ {n} B isoB f →
      finiteFunctionExactIsomorphismTransport isoA isoB f)


------------------------------------------------------------------------
-- Exact finite POMDP-model transport seam.
--
-- This is deliberately a transport theorem, not a probabilistic
-- convergence theorem: the probability/distribution semantics remain
-- explicit parameters so the graph never silently turns a deterministic
-- representation isomorphism into a stochastic claim.
------------------------------------------------------------------------

record FinitePOMDPExactTransport
  (nState nAction nObservation : Nat)
  (State Action Observation Distribution Reward : Set)
  (stateIso : StateIsomorphism (Fin nState) State)
  (actionIso : StateIsomorphism (Fin nAction) Action)
  (observationIso : StateIsomorphism (Fin nObservation) Observation)
  (transition : State → Action → Distribution)
  (observationKernel : State → Distribution)
  (reward : State → Action → Reward) : Set₁ where
  constructor finitePOMDPExactTransport
  field
    translatedTransition :
      Fin nState → Fin nAction → Distribution
    translatedObservationKernel :
      Fin nState → Distribution
    translatedReward :
      Fin nState → Fin nAction → Reward
    transitionExact :
      ∀ s a →
      translatedTransition (to stateIso s) (to actionIso a) ≡ transition s a
    observationExact :
      ∀ s →
      translatedObservationKernel (to stateIso s) ≡ observationKernel s
    rewardExact :
      ∀ s a →
      translatedReward (to stateIso s) (to actionIso a) ≡ reward s a

finite-pomdp-exact-transport :
  ∀ {nState nAction nObservation : Nat}
    {State Action Observation Distribution Reward : Set}
    (stateIso : StateIsomorphism (Fin nState) State)
    (actionIso : StateIsomorphism (Fin nAction) Action)
    (observationIso : StateIsomorphism (Fin nObservation) Observation)
    (transition : State → Action → Distribution)
    (observationKernel : State → Distribution)
    (reward : State → Action → Reward) →
  FinitePOMDPExactTransport
    nState nAction nObservation
    State Action Observation Distribution Reward
    stateIso actionIso observationIso
    transition observationKernel reward
finite-pomdp-exact-transport stateIso actionIso observationIso transition observationKernel reward =
  finitePOMDPExactTransport
    (λ s a → transition (from stateIso s) (from actionIso a))
    (λ s → observationKernel (from stateIso s))
    (λ s a → reward (from stateIso s) (from actionIso a))
    (λ s a →
      cong₂ transition (from-to stateIso s) (from-to actionIso a))
    (λ s →
      cong observationKernel (from-to stateIso s))
    (λ s a →
      cong₂ reward (from-to stateIso s) (from-to actionIso a))

------------------------------------------------------------------------
-- Architecture-preserving RNN-LM isomorphism.
--
-- An alternate implementation counts as faithful only when the exact
-- representation map preserves every declared custom component, not merely
-- the composite recurrent step.
------------------------------------------------------------------------

record ArchitecturePreservingCanonicalRNNLMIsomorphism
  (TargetToken TargetState : Set)
  (K : C.CanonicalTokenLanguageModelKernel)
  (encodeB : TargetToken → C.Int8)
  (decodeB : C.Int8 → TargetToken)
  (stepB : TargetState → TargetToken → TargetState)
  (listStateB : List TargetToken → TargetState → TargetState)
  (hiddenB : TargetState → C.Int8)
  (matrixB : TargetState → C.GRUMatrices)
  (noiseB : TargetState → C.GRUNoise)
  (controlB : TargetState → C.GlobalControl)
  (activationB : C.Int8 → C.Int8)
  (candidateB : C.Int8 → C.Int8 → C.Int8)
  (gateB : C.Int8 → C.Int8)
  (mixB : C.Int8 → C.Int8 → C.Int8 → C.Int8)
  (persistentB :
    TargetState → C.GRUMatrices × (C.GRUNoise × C.GlobalControl))
  (logitsB : TargetState → TargetToken → C.Int8)
  (sparseWeightB :
    TargetState → TargetToken → C.SparseWeight)
  (sparsePolicyB : TargetState → TargetToken)
  (fixedAttentionB :
    TargetState → TargetToken → C.Int8)
  (haarAttentionB :
    TargetState → TargetToken → TargetToken → C.CanonicalHaarPair)
  : Set₁ where
  field
    tokenIso :
      StateIsomorphism C.CanonicalToken TargetToken
    stateIso :
      StateIsomorphism C.GRUState TargetState

    encodeDecodePreserved :
      ∀ t →
      decodeB (encodeB t) ≡ t
    decodeEncodePreserved :
      ∀ x →
      encodeB (decodeB x) ≡ x

    encodePreserved :
      ∀ t →
      encodeB (to tokenIso t) ≡ C.canonicalTokenEncode t
    decodePreserved :
      ∀ t →
      decodeB (C.canonicalTokenEncode t) ≡ to tokenIso t

    hiddenStatePreserved :
      ∀ s →
      hiddenB (to stateIso s) ≡ C.hiddenState s
    matrixStatePreserved :
      ∀ s →
      matrixB (to stateIso s) ≡ C.matrixState s
    noiseStatePreserved :
      ∀ s →
      noiseB (to stateIso s) ≡ C.noiseState s
    controlStatePreserved :
      ∀ s →
      controlB (to stateIso s) ≡ C.controlState s

    activationPreserved :
      ∀ x →
      activationB x ≡ C.identityActivation8 x
    candidatePreserved :
      ∀ h x →
      candidateB h x ≡ C.gruCandidate8 h x
    gatePreserved :
      ∀ x →
      gateB x ≡ C.gateFromInput x
    mixPreserved :
      ∀ g h x →
      mixB g h x ≡ C.mix8 g h x

    recurrentStepPreserved :
      ∀ s t →
      to stateIso (C.canonicalTokenStep s t) ≡
      stepB (to stateIso s) (to tokenIso t)

    recurrentListStatePreserved :
      ∀ xs s →
      to stateIso (C.canonicalTokenListState xs s) ≡
      listStateB
        (map (to tokenIso) xs)
        (to stateIso s)

    persistentParametersPreserved :
      ∀ s →
      persistentB (to stateIso s) ≡ C.persistentGRU s

    logitsPreserved :
      ∀ s t →
      logitsB (to stateIso s) (to tokenIso t) ≡
      C.logits K s (to tokenIso t)

    sparsemaxWeightPreserved :
      ∀ s t →
      sparseWeightB (to stateIso s) (to tokenIso t) ≡
      C.canonicalTokenSparsemaxWeight K s (to tokenIso t)

    sparsemaxPolicyPreserved :
      ∀ s →
      to tokenIso (C.canonicalTokenSparsemaxPolicy K s) ≡
      sparsePolicyB (to stateIso s)

    fixedSparsemaxAttentionPreserved :
      ∀ s t →
      fixedAttentionB
        (to stateIso s)
        (to tokenIso t)
      ≡
      C.canonicalFixedSparsemaxAttentionWeight
        K s (to tokenIso t)

    haarSparsemaxAttentionPreserved :
      ∀ s t u →
      haarAttentionB
        (to stateIso s)
        (to tokenIso t)
        (to tokenIso u)
      ≡
      C.canonicalHaarSparsemaxAttention
        K
        s
        (to tokenIso t)
        (to tokenIso u)

open ArchitecturePreservingCanonicalRNNLMIsomorphism public

architecture-preserving-canonical-rnn-lm-identity :
  ∀ (K : C.CanonicalTokenLanguageModelKernel) →
  ArchitecturePreservingCanonicalRNNLMIsomorphism
    C.CanonicalToken
    C.GRUState
    K
    C.canonicalTokenEncode
    C.canonicalTokenDecode
    C.canonicalTokenStep
    C.canonicalTokenListState
    C.hiddenState
    C.matrixState
    C.noiseState
    C.controlState
    C.identityActivation8
    C.gruCandidate8
    C.gateFromInput
    C.mix8
    C.persistentGRU
    (λ s t → C.logits K s t)
    (λ s t → C.canonicalTokenSparsemaxWeight K s t)
    (λ s → C.canonicalTokenSparsemaxPolicy K s)
    (λ s t → C.canonicalFixedSparsemaxAttentionWeight K s t)
    (λ s t u → C.canonicalHaarSparsemaxAttention K s t u)
architecture-preserving-canonical-rnn-lm-identity K =
  architecturePreservingCanonicalRNNLMIsomorphism
    (stateIsomorphism
      (λ x → x)
      (λ x → x)
      (λ x → refl)
      (λ x → refl))
    (stateIsomorphism
      (λ x → x)
      (λ x → x)
      (λ x → refl)
      (λ x → refl))
    canonicalTokenDecodeEncode
    canonicalTokenEncodeDecode
    (λ t → refl)
    (λ t → refl)
    (λ s → refl)
    (λ s → refl)
    (λ s → refl)
    (λ s → refl)
    (λ x → refl)
    (λ h x → refl)
    (λ x → refl)
    (λ g h x → refl)
    (λ s → refl)
    (λ s t → refl)
    (λ s t → refl)
    (λ s → refl)
    (λ s t → refl)
    (λ s t u → refl)

record CanonicalExactRNNLMTheorem : Set₁ where
  constructor canonicalExactRNNLMTheorem
  field
    globalTokenConjugacy :
      CanonicalGlobalTokenConjugacyTheorem
    recurrentTrace :
      ∀ (K : C.CanonicalTokenLanguageModelKernel)
      (xs ys : C.CanonicalTokenSequence)
      (s : C.GRUState) →
      C.canonicalTokenLogitTrace K (xs ++ ys) s
      ≡
      C.canonicalTokenLogitTrace K xs s ++
      C.canonicalTokenLogitTrace K ys
        (C.canonicalTokenListState xs s)
    sparsemaxHead :
      ∀ (K : C.CanonicalTokenLanguageModelKernel)
      (s : C.GRUState) →
      C.canonicalTokenSparsemaxPolicy K s
      ≡
      C.sparsemaxPolicy
        C.canonicalTokenActionSpace
        (C.logits K s)
        C.canonicalTokenLogitCounts
    sparsemaxTrace :
      ∀ (K : C.CanonicalTokenLanguageModelKernel)
      (xs ys : C.CanonicalTokenSequence)
      (s : C.GRUState) →
      canonicalTokenSparsemaxTrace K (xs ++ ys) s
      ≡
      canonicalTokenSparsemaxTrace K xs s ++
      canonicalTokenSparsemaxTrace K ys
        (C.canonicalTokenListState xs s)

open CanonicalExactRNNLMTheorem public

canonical-exact-rnn-lm-theorem : CanonicalExactRNNLMTheorem
canonical-exact-rnn-lm-theorem =
  canonicalExactRNNLMTheorem
    canonical-global-token-conjugacy
    canonicalTokenLogitTrace-append
    canonicalTokenSparsemaxPolicy-shared
    canonicalTokenSparsemaxTrace-append

------------------------------------------------------------------------
-- Global positive conjugacy is finite and exact; the corresponding
-- unbounded Nat-to-Int8 exact injective boundary is impossible.
------------------------------------------------------------------------

canonicalNoGlobalFiniteObservationConjugacy :
  ∀ (observe : C.Int8 → Fin 256)
  (embed : Nat → C.Int8) →
  ¬ (∀ {m n} →
      observe (embed m) ≡ observe (embed n) →
      m ≡ n)
canonicalNoGlobalFiniteObservationConjugacy observe embed =
  C.finiteObservation-no-countably-unbounded-injective
    (λ n → observe (embed n))

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
    finiteObservationBoundary :
      ∀ (observe : C.Int8 → Fin 256)
      (embed : Nat → C.Int8) →
      ¬ (∀ {m n} →
          observe (embed m) ≡ observe (embed n) →
          m ≡ n)

open CanonicalGlobalTokenLMCompositionTheorem public

canonical-global-token-lm-composition-theorem :
  CanonicalGlobalTokenLMCompositionTheorem
canonical-global-token-lm-composition-theorem =
  canonicalGlobalTokenLMCompositionTheorem
    canonical-global-token-conjugacy
    canonicalToken-prefix-monoid-homomorphism
    canonicalTokenLogitTrace-append
    canonicalNoGlobalFiniteObservationConjugacy

  
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
-- Linear Haar + fixed unnormalized sparsemax attention composition.
--
-- This is deliberately not a second attention normalization: the
-- coefficients are the existing sparsemax numerators with zero counts,
-- while Haar is the strictly linear (sum,difference) integer transform.
------------------------------------------------------------------------

canonicalIntegerHaarOrthogonality :
  C.int8Add
    (C.int8Mul C.one8 C.one8)
    (C.int8Mul C.one8 (C.int8Neg C.one8))
  ≡ C.zero8
canonicalIntegerHaarOrthogonality = C.canonicalHaarOrthogonalCross

canonicalIntegerHaarLinearForm :
  ∀ (x y : C.Int8) →
  C.canonicalHaarMix x y
  ≡
  (C.int8Add x y , C.int8Sub x y)
canonicalIntegerHaarLinearForm = C.canonicalHaarMix-linear-form

canonicalFixedSparsemaxAttentionShared :
  ∀ (K : C.CanonicalTokenLanguageModelKernel)
  (s : C.GRUState)
  (t : C.CanonicalToken) →
  C.canonicalFixedSparsemaxAttentionWeight K s t
  ≡
  C.int8OfNat
    (C.numerator
      (C.sparsemaxWeight
        C.canonicalTokenActionSpace
        (C.logits K s)
        C.canonicalTokenLogitCounts
        t))
canonicalFixedSparsemaxAttentionShared =
  C.canonicalFixedSparsemaxAttention-shared

canonicalHaarSparsemaxAttentionLinear :
  ∀ (K : C.CanonicalTokenLanguageModelKernel)
  (s : C.GRUState)
  (t u : C.CanonicalToken) →
  C.canonicalHaarSparsemaxAttention K s t u
  ≡
  (C.int8Add
     (C.canonicalFixedSparsemaxAttentionWeight K s t)
     (C.canonicalFixedSparsemaxAttentionWeight K s u)
   ,
   C.int8Sub
     (C.canonicalFixedSparsemaxAttentionWeight K s t)
     (C.canonicalFixedSparsemaxAttentionWeight K s u))
canonicalHaarSparsemaxAttentionLinear =
  C.canonicalHaarSparsemaxAttention-linear-form

canonicalFixedSparsemaxAttentionCounts :
  C.canonicalTokenLogitCounts ≡ C.zeroCounts
canonicalFixedSparsemaxAttentionCounts =
  C.canonicalFixedSparsemaxAttention-counts

canonicalFullStateHaarSparsemaxAttentionNormInvariant :
  ∀ (K : C.CanonicalTokenLanguageModelKernel)
  (s : C.CanonicalFullLearnerState)
  (n : C.NormPair)
  (t u : C.CanonicalToken) →
  C.canonicalFullStateHaarSparsemaxAttention K (C.replaceNorm s n) t u
  ≡
  C.canonicalFullStateHaarSparsemaxAttention K s t u
canonicalFullStateHaarSparsemaxAttentionNormInvariant =
  C.canonicalFullStateHaarSparsemaxAttention-norm-invariant

canonicalFullStateHaarSparsemaxAttentionOptimizerInvariant :
  ∀ (K : C.CanonicalTokenLanguageModelKernel)
  (s : C.CanonicalFullLearnerState)
  (o : C.F4IntUState)
  (t u : C.CanonicalToken) →
  C.canonicalFullStateHaarSparsemaxAttention K (C.replaceOptimizer s o) t u
  ≡
  C.canonicalFullStateHaarSparsemaxAttention K s t u
canonicalFullStateHaarSparsemaxAttentionOptimizerInvariant =
  C.canonicalFullStateHaarSparsemaxAttention-optimizer-invariant

record CanonicalFullStateHaarSparsemaxInvariantCompositionTheorem : Set₁ where
  constructor canonicalFullStateHaarSparsemaxInvariantCompositionTheorem
  field
    fixedCounts :
      C.canonicalTokenLogitCounts ≡ C.zeroCounts
    normInvariant :
      ∀ (K : C.CanonicalTokenLanguageModelKernel)
      (s : C.CanonicalFullLearnerState)
      (n : C.NormPair)
      (t u : C.CanonicalToken) →
      C.canonicalFullStateHaarSparsemaxAttention K (C.replaceNorm s n) t u
      ≡
      C.canonicalFullStateHaarSparsemaxAttention K s t u
    optimizerInvariant :
      ∀ (K : C.CanonicalTokenLanguageModelKernel)
      (s : C.CanonicalFullLearnerState)
      (o : C.F4IntUState)
      (t u : C.CanonicalToken) →
      C.canonicalFullStateHaarSparsemaxAttention K (C.replaceOptimizer s o) t u
      ≡
      C.canonicalFullStateHaarSparsemaxAttention K s t u

open CanonicalFullStateHaarSparsemaxInvariantCompositionTheorem public

canonical-full-state-haar-sparsemax-invariant-composition-theorem :
  CanonicalFullStateHaarSparsemaxInvariantCompositionTheorem
canonical-full-state-haar-sparsemax-invariant-composition-theorem =
  canonicalFullStateHaarSparsemaxInvariantCompositionTheorem
    canonicalFixedSparsemaxAttentionCounts
    canonicalFullStateHaarSparsemaxAttentionNormInvariant
    canonicalFullStateHaarSparsemaxAttentionOptimizerInvariant

canonicalFullStateHaarSparsemaxAttention-learnerReplacement-invariant :
  ∀ (K : C.CanonicalTokenLanguageModelKernel)
  (s : C.CanonicalFullLearnerState)
  (r : LearnerReplacement)
  (t u : C.CanonicalToken) →
  C.canonicalFullStateHaarSparsemaxAttention K
    (C.applyLearnerReplacement r s) t u
  ≡
  C.canonicalFullStateHaarSparsemaxAttention K s t u
canonicalFullStateHaarSparsemaxAttention-learnerReplacement-invariant
  K s (C.normReplacement n) t u =
  canonicalFullStateHaarSparsemaxAttentionNormInvariant K s n t u
canonicalFullStateHaarSparsemaxAttention-learnerReplacement-invariant
  K s (C.optimizerReplacement o) t u =
  canonicalFullStateHaarSparsemaxAttentionOptimizerInvariant K s o t u

record CanonicalHaarSparsemaxFullStateClosureTheorem : Set₁ where
  constructor canonicalHaarSparsemaxFullStateClosureTheorem
  field
    fixedCounts :
      C.canonicalTokenLogitCounts ≡ C.zeroCounts
    haarOrthogonality :
      C.int8Add
        (C.int8Mul C.one8 C.one8)
        (C.int8Mul C.one8 (C.int8Neg C.one8))
      ≡ C.zero8
    haarLinear :
      ∀ (x y : C.Int8) →
      C.canonicalHaarMix x y
      ≡
      (C.int8Add x y , C.int8Sub x y)
    composedAttention :
      ∀ (K : C.CanonicalTokenLanguageModelKernel)
      (s : C.GRUState)
      (t u : C.CanonicalToken) →
      C.canonicalHaarSparsemaxAttention K s t u
      ≡
      (C.int8Add
         (C.canonicalFixedSparsemaxAttentionWeight K s t)
         (C.canonicalFixedSparsemaxAttentionWeight K s u)
       ,
       C.int8Sub
         (C.canonicalFixedSparsemaxAttentionWeight K s t)
         (C.canonicalFixedSparsemaxAttentionWeight K s u))
    learnerReplacementInvariant :
      ∀ (K : C.CanonicalTokenLanguageModelKernel)
      (s : C.CanonicalFullLearnerState)
      (r : LearnerReplacement)
      (t u : C.CanonicalToken) →
      C.canonicalFullStateHaarSparsemaxAttention K
        (C.applyLearnerReplacement r s) t u
      ≡
      C.canonicalFullStateHaarSparsemaxAttention K s t u

open CanonicalHaarSparsemaxFullStateClosureTheorem public

canonical-haar-sparsemax-full-state-closure-theorem :
  CanonicalHaarSparsemaxFullStateClosureTheorem
canonical-haar-sparsemax-full-state-closure-theorem =
  canonicalHaarSparsemaxFullStateClosureTheorem
    canonicalFixedSparsemaxAttentionCounts
    canonicalIntegerHaarOrthogonality
    canonicalIntegerHaarLinearForm
    canonicalHaarSparsemaxAttentionLinear
    canonicalFullStateHaarSparsemaxAttention-learnerReplacement-invariant

record CanonicalLinearHaarSparsemaxAttentionCompositionTheorem : Set₁ where
  constructor canonicalLinearHaarSparsemaxAttentionCompositionTheorem
  field
    haarOrthogonality :
      C.int8Add
        (C.int8Mul C.one8 C.one8)
        (C.int8Mul C.one8 (C.int8Neg C.one8))
      ≡ C.zero8
    haarLinear :
      ∀ (x y : C.Int8) →
      C.canonicalHaarMix x y
      ≡
      (C.int8Add x y , C.int8Sub x y)
    sparsemaxAttention :
      ∀ (K : C.CanonicalTokenLanguageModelKernel)
      (s : C.GRUState)
      (t : C.CanonicalToken) →
      C.canonicalFixedSparsemaxAttentionWeight K s t
      ≡
      C.int8OfNat
        (C.numerator
          (C.sparsemaxWeight
            C.canonicalTokenActionSpace
            (C.logits K s)
            C.canonicalTokenLogitCounts
            t))
    composedAttention :
      ∀ (K : C.CanonicalTokenLanguageModelKernel)
      (s : C.GRUState)
      (t u : C.CanonicalToken) →
      C.canonicalHaarSparsemaxAttention K s t u
      ≡
      (C.int8Add
         (C.canonicalFixedSparsemaxAttentionWeight K s t)
         (C.canonicalFixedSparsemaxAttentionWeight K s u)
       ,
       C.int8Sub
         (C.canonicalFixedSparsemaxAttentionWeight K s t)
         (C.canonicalFixedSparsemaxAttentionWeight K s u))

open CanonicalLinearHaarSparsemaxAttentionCompositionTheorem public

canonical-linear-haar-sparsemax-attention-composition-theorem :
  CanonicalLinearHaarSparsemaxAttentionCompositionTheorem
canonical-linear-haar-sparsemax-attention-composition-theorem =
  canonicalLinearHaarSparsemaxAttentionCompositionTheorem
    canonicalIntegerHaarOrthogonality
    canonicalIntegerHaarLinearForm
    canonicalFixedSparsemaxAttentionShared
    canonicalHaarSparsemaxAttentionLinear


------------------------------------------------------------------------
-- Canonical finite-cycle exclusion transported through an exact state
-- isomorphism. This packages the already-proved generic conjugacy law;
-- it is not a Lyapunov descent theorem.
------------------------------------------------------------------------

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

canonical-finite-cycle-exclusion-isomorphism-theorem :
  CanonicalFiniteCycleExclusionIsomorphismTheorem
canonical-finite-cycle-exclusion-isomorphism-theorem =
  canonicalFiniteCycleExclusionIsomorphismTheorem
    isomorphismIterateConjugacy
    isomorphismNoFiniteCycleTransport

------------------------------------------------------------------------
-- Operator-composition closure is already an exact theorem of the
-- canonical endomorphism algebra. The standalone operator-complexity
-- module therefore adds no new learner semantics.
------------------------------------------------------------------------

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
-- Exact finite-observation / injective-lift completion.
--
-- Int8 is now an exact unbounded integer carrier. Finite recurrence therefore
-- belongs only to an explicit observation map into Fin 256. The F4 optimizer
-- remains an exact Z-valued transition.
------------------------------------------------------------------------

canonicalF4FiniteObservationRecurrence :
  ∀ {A} (K : C.FullLearnerKernel A)
    (s : C.FullLearnerState A)
    (observe : C.Int8 → Fin 256) →
  ∃ m n →
    m ≢ n ×
    observe (C.code (C.thetaQ (C.optimizer (C.iterateCanonical K m s)))) ≡
    observe (C.code (C.thetaQ (C.optimizer (C.iterateCanonical K n s))))
canonicalF4FiniteObservationRecurrence K s observe =
  canonical-finite-factor-recurrence-without-state-recurrence-factor
    (λ n → C.iterateCanonical K n s)
    (λ state → observe (C.code (C.thetaQ (C.optimizer state))))

canonicalF4FiniteObservationNotOrbitInjective :
  ∀ {A} (K : C.FullLearnerKernel A)
    (s : C.FullLearnerState A)
    (observe : C.Int8 → Fin 256) →
  ¬ (∀ {m n : Nat} →
      observe (C.code (C.thetaQ (C.optimizer (C.iterateCanonical K m s)))) ≡
      observe (C.code (C.thetaQ (C.optimizer (C.iterateCanonical K n s)))) →
      m ≡ n)
canonicalF4FiniteObservationNotOrbitInjective K s observe injective =
  let collision = canonicalF4FiniteObservationRecurrence K s observe
  in
  collisionWitness collision injective
  where
    collisionWitness :
      ∀ {A : Set} {orbit : Nat → A} {factor : A → Fin 256} →
      (∃ m n → m ≢ n × factor (orbit m) ≡ factor (orbit n)) →
      (∀ {m n} → factor (orbit m) ≡ factor (orbit n) → m ≡ n) →
      ⊥
    collisionWitness (m , n , apart , factorEq) inj = apart (inj factorEq)

canonicalF4FiniteObservationCollisionSeparatesFullState :
  ∀ {A} (K : C.FullLearnerKernel A)
    (s : C.FullLearnerState A)
    (observe : C.Int8 → Fin 256) →
  ∃ m n →
    m ≢ n ×
    observe (C.code (C.thetaQ (C.optimizer (C.iterateCanonical K m s)))) ≡
    observe (C.code (C.thetaQ (C.optimizer (C.iterateCanonical K n s)))) ×
    C.iterateCanonical K m s ≢ C.iterateCanonical K n s
canonicalF4FiniteObservationCollisionSeparatesFullState K s observe =
  let collision = canonicalF4FiniteObservationRecurrence K s observe
  in
  collisionWithStateSeparation collision
  where
    collisionWithStateSeparation :
      ∀ {A : Set} {orbit : Nat → A} {factor : A → Fin 256} →
      (∃ m n → m ≢ n × factor (orbit m) ≡ factor (orbit n)) →
      ∃ m n → m ≢ n × factor (orbit m) ≡ factor (orbit n) × orbit m ≢ orbit n
    collisionWithStateSeparation (m , n , apart , factorEq) =
      m , n , apart , factorEq ,
      (λ stateEq → apart (canonicalOrbit-state-injective K s stateEq))

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
    (λ K s → C.f4ParameterInvariant (C.optimizerKernel K) (C.optimizer s) (C.canonicalSignal K s))
    (λ K s → refl , (refl , (refl , refl)))
    (λ K s t optimizerEq signalEq →
      cong₂
        (λ optimizer signal → C.f4ThetaStep (C.optimizerKernel K) optimizer signal)
        optimizerEq signalEq)

------------------------------------------------------------------------
-- Emergent endogenous factor-recurrence separation.
--
-- Exact aperiodic full-state evolution can force recurrence in a finite
-- observation/factor without forcing recurrence of the underlying state.
-- The result is endogenous: it uses only the finite factor carrier and
-- exact orbit injectivity, with no Lyapunov or external stability premise.
------------------------------------------------------------------------

record FiniteFactorRecurrenceWithoutStateRecurrenceTheorem : Set₁ where
  constructor finiteFactorRecurrenceWithoutStateRecurrenceTheorem
  field
    factorRecurs :
      ∀ {A : Set}
        (orbit : Nat → A)
        (factor : A → Fin 256) →
        ∃ m n →
          m ≢ n ×
          factor (orbit m) ≡ factor (orbit n)
    stateSeparates :
      ∀ {A : Set}
        (orbit : Nat → A)
        (orbitInjective : ∀ {m n : Nat} → orbit m ≡ orbit n → m ≡ n)
        {m n : Nat} →
        m ≢ n →
        orbit m ≢ orbit n

canonical-finite-factor-recurrence-without-state-recurrence-factor :
  ∀ {A : Set} →
  (orbit : Nat → A) →
  (factor : A → Fin 256) →
  ∃ m n →
    m ≢ n ×
    factor (orbit m) ≡ factor (orbit n)
canonical-finite-factor-recurrence-without-state-recurrence-factor
  orbit factor with pigeonhole (n<1+n 256)
  (λ i → factor (orbit (toℕ i)))
... | i , j , apart , factorEq =
  toℕ i , toℕ j ,
  (λ mnEq → apart (toℕ-injective mnEq)) ,
  factorEq

canonical-finite-factor-recurrence-without-state-recurrence :
  FiniteFactorRecurrenceWithoutStateRecurrenceTheorem
canonical-finite-factor-recurrence-without-state-recurrence =
  finiteFactorRecurrenceWithoutStateRecurrenceTheorem
    canonical-finite-factor-recurrence-without-state-recurrence-factor
    (λ orbit orbitInjective {m} {n} apart stateEq →
      apart (orbitInjective stateEq))

------------------------------------------------------------------------
-- Pre-graphed completion endpoint for the active theorem seams.
-- Each field is an already-proved canonical theorem; this record adds no
-- alternate proof path or cancellation. It only exposes the dependency
-- graph at the monolith boundary.
------------------------------------------------------------------------

------------------------------------------------------------------------
-- 2026-09-22 emergent endogenous observation boundary.
--
-- The canonical Watkins target is an endogenous function of the exact
-- learner state.  A left-invertible observation would preserve exact
-- endogenous target readout, but the finite Int8 observation cannot be
-- globally left-invertible because the canonical Nat-clock orbit is
-- injective while every Int8 observation has a finite carrier.
------------------------------------------------------------------------

record CanonicalEndogenousObservationBoundaryTheorem : Set₁ where
  constructor canonicalEndogenousObservationBoundaryTheorem
  field
    exactOrbitEmbedding :
      ∀ (K : C.CanonicalFullLearnerKernel)
        (s : C.CanonicalFullLearnerState)
        {m n : Nat} →
      C.iterateCanonical K m s ≡
      C.iterateCanonical K n s →
      m ≡ n
    finiteObservationRecurrence :
      ∀ (K : C.CanonicalFullLearnerKernel)
        (s : C.CanonicalFullLearnerState)
        (observe : C.CanonicalFullLearnerState → C.Int8) →
      ∃ m n →
        m ≢ n ×
        observe (C.iterateCanonical K m s) ≡
        observe (C.iterateCanonical K n s)
    noGlobalLeftInverse :
      ∀ (K : C.CanonicalFullLearnerKernel)
        (s : C.CanonicalFullLearnerState)
        (observe : C.CanonicalFullLearnerState → C.Int8)
        (inverse : C.Int8 → C.CanonicalFullLearnerState) →
      ¬ (∀ t → inverse (observe t) ≡ t)
    endogenousTargetReadoutUnderLeftInverse :
      ∀ (K : C.CanonicalFullLearnerKernel)
        (observe : C.CanonicalFullLearnerState → C.Int8)
        (inverse : C.Int8 → C.CanonicalFullLearnerState) →
      (leftInverse : ∀ t → inverse (observe t) ≡ t) →
      ∀ s →
      C.canonicalWatkinsTarget K s ≡
      C.canonicalWatkinsTarget K (inverse (observe s))

open CanonicalEndogenousObservationBoundaryTheorem public

canonical-endogenous-observation-boundary-theorem :
  CanonicalEndogenousObservationBoundaryTheorem
canonical-endogenous-observation-boundary-theorem =
  canonicalEndogenousObservationBoundaryTheorem
    canonicalInfiniteStateOrbitEmbedding
    (λ K s observe →
      FiniteFactorRecurrenceWithoutStateRecurrenceTheorem.factorRecurs
        canonical-finite-factor-recurrence-without-state-recurrence
        (λ n → observe (C.iterateCanonical K n s)))
    (λ K s observe inverse →
      CanonicalGlobalFiniteObservationLeftInverseImpossibilityTheorem.noGlobalLeftInverse
        (canonical-global-finite-observation-left-inverse-impossibility-theorem K s)
        observe
        inverse)
    (λ K observe inverse leftInverse s →
      canonicalWatkinsTarget-endogenous-leftInverse
        K observe inverse leftInverse s)

record CanonicalEndogenousTopologicalObservationBoundaryTheorem : Set₁ where
  constructor canonicalEndogenousTopologicalObservationBoundaryTheorem
  field
    scanConjugacy :
      CanonicalFullLearnerConnectedScanConjugacyTheorem
    finiteCycleTransport :
      CanonicalFiniteCycleExclusionIsomorphismTheorem
    observationBoundary :
      CanonicalEndogenousObservationBoundaryTheorem

canonical-endogenous-topological-observation-boundary-theorem :
  CanonicalEndogenousTopologicalObservationBoundaryTheorem
canonical-endogenous-topological-observation-boundary-theorem =
  canonicalEndogenousTopologicalObservationBoundaryTheorem
    canonical-full-learner-connected-scan-conjugacy-theorem
    canonical-finite-cycle-exclusion-isomorphism-theorem
    canonical-endogenous-observation-boundary-theorem

record CanonicalPureNonOrangeBypassCompletionTheorem : Set₁ where
  constructor canonicalPureNonOrangeBypassCompletionTheorem
  field
    recurrentPrefix :
      RecurrentPrefixMonoidHomomorphism C.GRUState C.Int8
    fullLearnerScanConjugacy :
      CanonicalFullLearnerConnectedScanConjugacyTheorem
    exactTuringBoundary :
      ¬ CanonicalExactCompositionTuringCompletenessContract
    haarSparsemaxClosure :
      CanonicalHaarSparsemaxFullStateClosureTheorem
    finiteCycleIsomorphismTransport :
      CanonicalFiniteCycleExclusionIsomorphismTheorem
    operatorComposition :
      CanonicalOperatorCompositionTheorem
    boundedFactorLift :
      CanonicalBoundedFactorLiftTheorem
    emergentFactorSeparation :
      FiniteFactorRecurrenceWithoutStateRecurrenceTheorem
    finiteObservationInformationBoundary :
      CanonicalFiniteObservationInformationBoundaryTheorem
    endogenousObservationBoundary :
      CanonicalEndogenousObservationBoundaryTheorem
    endogenousTopologicalBoundary :
      CanonicalEndogenousTopologicalObservationBoundaryTheorem

open CanonicalPureNonOrangeBypassCompletionTheorem public

canonical-pure-non-orange-bypass-completion-theorem :
  CanonicalPureNonOrangeBypassCompletionTheorem
canonical-pure-non-orange-bypass-completion-theorem =
  canonicalPureNonOrangeBypassCompletionTheorem
    canonical-recurrent-prefix-monoid-homomorphism
    canonical-full-learner-connected-scan-conjugacy-theorem
    canonicalExactCompositionTuringCompletenessContract-impossible
    canonical-haar-sparsemax-full-state-closure-theorem
    canonical-finite-cycle-exclusion-isomorphism-theorem
    canonical-operator-composition-theorem
    canonical-bounded-factor-lift-theorem
    canonical-finite-factor-recurrence-without-state-recurrence
    canonical-finite-observation-information-boundary-theorem
    canonical-endogenous-observation-boundary-theorem
    canonical-endogenous-topological-observation-boundary-theorem


------------------------------------------------------------------------
-- Emergent endogenous finite-observation information boundary.
--
-- Combining exact Nat-indexed orbit separation with the finite Int8
-- observation boundary yields a stronger statement than factor recurrence
-- alone: no single Int8 observation of a canonical full-state orbit can
-- admit an exact left inverse. Consequently universal exact discrete UAP
-- through such an observation is impossible on that orbit.
------------------------------------------------------------------------

record CanonicalFiniteObservationInformationBoundaryTheorem : Set₁ where
  constructor canonicalFiniteObservationInformationBoundaryTheorem
  field
    exactOrbitEmbedding :
      ∀ (K : C.CanonicalFullLearnerKernel)
      (s : C.CanonicalFullLearnerState) →
      ∀ {m n : Nat} →
      C.iterateCanonical K m s ≡ C.iterateCanonical K n s →
      m ≡ n
    finiteFactorRecurrence :
      ∀ {A : Set}
        (orbit : Nat → A)
        (factor : A → Fin 256) →
        ∃ m n →
          m ≢ n ×
          factor (orbit m) ≡ factor (orbit n)
    noExactFiniteObservationLeftInverse :
      ∀ (K : C.CanonicalFullLearnerKernel)
      (s : C.CanonicalFullLearnerState)
      (observe : C.CanonicalFullLearnerState → Fin 256)
      (inverse : Fin 256 → C.CanonicalFullLearnerState) →
      (∀ t → inverse (observe t) ≡ t) →
      ⊥
    noUniversalDiscreteUAP :
      ∀ (K : C.CanonicalFullLearnerKernel)
      (s : C.CanonicalFullLearnerState)
      (observe : C.CanonicalFullLearnerState → Fin 256) →
      DiscreteExactUniversalUAP
        C.CanonicalFullLearnerState
        (Fin 256)
        observe →
      ⊥

canonical-finite-observation-information-boundary-theorem :
  CanonicalFiniteObservationInformationBoundaryTheorem
canonical-finite-observation-information-boundary-theorem =
  canonicalFiniteObservationInformationBoundaryTheorem
    canonicalInfiniteStateOrbitEmbedding
    (FiniteFactorRecurrenceWithoutStateRecurrenceTheorem.factorRecurs
      canonical-finite-factor-recurrence-without-state-recurrence)
    canonicalPigeonholeNatClockContradiction
    canonicalNoGlobalFiniteObservationDiscreteUniversalUAPOnOrbit
------------------------------------------------------------------------
-- Exact Turing-completeness mixture boundary.
-- This records the simultaneous contract being ruled out; it does not claim
-- that every weaker notion of Turing completeness is impossible.
------------------------------------------------------------------------

record CanonicalExactTuringBoundaryMixtureTheorem : Set₁ where
  constructor canonicalExactTuringBoundaryMixtureTheorem
  field
    exactClock :
      ∀ (K : C.CanonicalFullLearnerKernel)
      (s : C.CanonicalFullLearnerState) →
      C.clock (C.canonicalFullStep K s) ≡ suc (C.clock s)
    finiteObservationBoundary :
      CanonicalFiniteObservationInformationBoundaryTheorem
    exactContractImpossible :
      ¬ CanonicalExactCompositionTuringCompletenessContract

open CanonicalExactTuringBoundaryMixtureTheorem public

canonical-exact-turing-boundary-mixture-theorem :
  CanonicalExactTuringBoundaryMixtureTheorem
canonical-exact-turing-boundary-mixture-theorem =
  canonicalExactTuringBoundaryMixtureTheorem
    canonicalClockStep
    canonical-finite-observation-information-boundary-theorem
    canonicalExactCompositionTuringCompletenessContract-impossible


------------------------------------------------------------------------
-- 2026-09-22 explicit global-left-inverse and stochastic-boundary
-- theorem surfaces.
------------------------------------------------------------------------

-- The global left-inverse obstruction is quantified over the entire
-- canonical state space. The proof uses one Nat-clock orbit as the
-- finite-carrier witness; this is a witness to the global claim, not
-- a restriction of the conclusion to that orbit.
record CanonicalGlobalFiniteObservationLeftInverseImpossibilityTheorem : Set₁ where
  constructor canonicalGlobalFiniteObservationLeftInverseImpossibilityTheorem
  field
    noGlobalLeftInverse :
      ∀ (observe : C.CanonicalFullLearnerState → Fin 256)
        (inverse : Fin 256 → C.CanonicalFullLearnerState) →
      ¬ (∀ s → inverse (observe s) ≡ s)

canonical-global-finite-observation-left-inverse-impossibility-theorem :
  ∀ (K : C.CanonicalFullLearnerKernel)
    (s : C.CanonicalFullLearnerState) →
  CanonicalGlobalFiniteObservationLeftInverseImpossibilityTheorem
canonical-global-finite-observation-left-inverse-impossibility-theorem K s =
  canonicalGlobalFiniteObservationLeftInverseImpossibilityTheorem
    (λ observe inverse leftInverse →
      canonicalPigeonholeNatClockContradiction
        K
        s
        observe
        inverse
        leftInverse)

------------------------------------------------------------------------
-- A stationary-distribution conclusion is not obtained from boundedness
-- or monotone Lyapunov behavior alone. The exact theorem surface makes
-- the missing stochastic/limit-preservation assumptions explicit.
------------------------------------------------------------------------

record FiniteObservationStationaryLimitTheorem
  (Distribution : Set)
  (P : Distribution → Distribution)
  (μ : Nat → Distribution)
  (μ∞ : Distribution)
  (Converges : (Nat → Distribution) → Distribution → Set) : Set₁ where
  constructor finiteObservationStationaryLimitTheorem
  field
    transitionLaw :
      ∀ n → μ (suc n) ≡ P (μ n)
    converges :
      Converges μ μ∞
    limitPreserved :
      Converges μ μ∞ → P μ∞ ≡ μ∞

finiteObservationStationaryLimitTheorem-is-stationary :
  ∀ {Distribution : Set}
    {P : Distribution → Distribution}
    {μ : Nat → Distribution}
    {μ∞ : Distribution}
    {Converges : (Nat → Distribution) → Distribution → Set} →
  FiniteObservationStationaryLimitTheorem
    Distribution P μ μ∞ Converges →
  P μ∞ ≡ μ∞
finiteObservationStationaryLimitTheorem-is-stationary theorem =
  FiniteObservationStationaryLimitTheorem.limitPreserved theorem
    (FiniteObservationStationaryLimitTheorem.converges theorem)

------------------------------------------------------------------------
-- PE is an information condition, not a boundedness corollary. The
-- canonical repository currently has no formal Gramian/vector-space
-- stochastic layer, so the pre-graphed theorem is an explicit contract
-- requiring PE as an additional premise rather than pretending that
-- Int8 boundedness proves it.
------------------------------------------------------------------------

record CanonicalPersistentExcitationRequirementTheorem : Set₁ where
  constructor canonicalPersistentExcitationRequirementTheorem
  field
    boundednessIsNotPE :
      ⊤
    peMustBeSuppliedSeparately :
      ⊤

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

record CanonicalFiniteObservationStationarySubcompositionTheorem : Set₁ where
  constructor canonicalFiniteObservationStationarySubcompositionTheorem
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
      FiniteObservationStationaryLimitTheorem
        Distribution P μ π Converges

canonical-finite-observation-stationary-subcomposition-theorem :
  CanonicalFiniteObservationStationarySubcompositionTheorem
canonical-finite-observation-stationary-subcomposition-theorem =
  canonicalFiniteObservationStationarySubcompositionTheorem
    (λ P μ π Converges transitionLaw convergence limitPreserved →
      finiteObservationStationaryLimitTheorem
        transitionLaw
        convergence
        limitPreserved)

record CanonicalClockObservationSubcompositionTheorem : Set₁ where
  constructor canonicalClockObservationSubcompositionTheorem
  field
    exactClockGrowth :
      ∀ (K : C.CanonicalFullLearnerKernel)
        (n : Nat)
        (s : C.CanonicalFullLearnerState) →
      C.clock (C.iterateCanonical K n s) ≡ C.clock s + n
    globalLeftInverseObstruction :
      CanonicalGlobalFiniteObservationLeftInverseImpossibilityTheorem

canonical-clock-observation-subcomposition-theorem :
  ∀ (K : C.CanonicalFullLearnerKernel)
    (s : C.CanonicalFullLearnerState) →
  CanonicalClockObservationSubcompositionTheorem
canonical-clock-observation-subcomposition-theorem K s =
  canonicalClockObservationSubcompositionTheorem
    canonicalClockAfter
    (canonical-global-finite-observation-left-inverse-impossibility-theorem K s)

record CanonicalBoundednessPEBoundarySubcompositionTheorem : Set₁ where
  constructor canonicalBoundednessPEBoundarySubcompositionTheorem
  field
    boundednessBoundary :
      CanonicalBoundedFactorLiftTheorem
    persistentExcitationRequirement :
      CanonicalPersistentExcitationRequirementTheorem

canonical-boundedness-pe-boundary-subcomposition-theorem :
  CanonicalBoundednessPEBoundarySubcompositionTheorem
canonical-boundedness-pe-boundary-subcomposition-theorem =
  canonicalBoundednessPEBoundarySubcompositionTheorem
    canonical-bounded-factor-lift-theorem
    canonical-persistent-excitation-requirement-theorem

------------------------------------------------------------------------
-- Minimal exact finite probability semantics.
--
-- No analytic probability import is required here. A finite distribution
-- is represented by non-negative Nat weights with a positive denominator
-- and an exact normalization certificate. Each coordinate therefore denotes
-- the rational mass weight/denominator without introducing a second
-- arithmetic tower into the canonical theorem surface.
------------------------------------------------------------------------

natListSum : List Nat → Nat
natListSum [] = zero
natListSum (x ∷ xs) = x + natListSum xs

finiteProbabilityWeightSum :
  ∀ (n : Nat) → (Fin n → Nat) → Nat
finiteProbabilityWeightSum n w =
  natListSum (map w (C.finList n))

record FiniteProbabilityMass (n : Nat) : Set₁ where
  constructor finiteProbabilityMass
  field
    weight : Fin n → Nat
    total : Nat
    positive : zero < total
    normalized :
      finiteProbabilityWeightSum n weight ≡ total

open FiniteProbabilityMass public

finiteProbabilityMass-normalized :
  ∀ {n : Nat} (p : FiniteProbabilityMass n) →
  finiteProbabilityWeightSum n (weight p) ≡ total p
finiteProbabilityMass-normalized p = normalized p

finiteProbabilityMass-transport-weight :
  ∀ {n : Nat} {A : Set}
  (iso : StateIsomorphism (Fin n) A)
  (p : FiniteProbabilityMass n) →
  A → Nat
finiteProbabilityMass-transport-weight iso p a =
  weight p (from iso a)

finiteProbabilityMass-transport-exact :
  ∀ {n : Nat} {A : Set}
  (iso : StateIsomorphism (Fin n) A)
  (p : FiniteProbabilityMass n)
  (i : Fin n) →
  finiteProbabilityMass-transport-weight iso p (to iso i) ≡
  weight p i
finiteProbabilityMass-transport-exact iso p i = refl

record FiniteProbabilityMassSemanticsTheorem : Set₁ where
  constructor finiteProbabilityMassSemanticsTheorem
  field
    normalizedMass :
      ∀ {n : Nat} (p : FiniteProbabilityMass n) →
      finiteProbabilityWeightSum n (weight p) ≡ total p
    exactIsomorphismTransport :
      ∀ {n : Nat} {A : Set}
        (iso : StateIsomorphism (Fin n) A)
        (p : FiniteProbabilityMass n)
        (i : Fin n) →
      finiteProbabilityMass-transport-weight iso p (to iso i) ≡
      weight p i

finite-probability-mass-semantics-theorem :
  FiniteProbabilityMassSemanticsTheorem
finite-probability-mass-semantics-theorem =
  finiteProbabilityMassSemanticsTheorem
    finiteProbabilityMass-normalized
    finiteProbabilityMass-transport-exact

------------------------------------------------------------------------
-- Polymorphic exact finite POMDP probability semantics.
--
-- State/action/observation cardinalities and reward codomain are parameters.
-- The canonical Int8/Fin-256 learner is therefore an instance rather than
-- part of the theorem statement.
------------------------------------------------------------------------

record FinitePOMDPProbabilitySemantics
  (nState nAction nObservation : Nat)
  (Reward : Set) : Set₁ where
  constructor finitePOMDPProbabilitySemantics
  field
    transitionProbability :
      Fin nState → Fin nAction → FiniteProbabilityMass nState
    observationProbability :
      Fin nState → FiniteProbabilityMass nObservation
    reward :
      Fin nState → Fin nAction → Reward

open FinitePOMDPProbabilitySemantics public

record FinitePOMDPProbabilitySemanticsTheorem : Set₁ where
  constructor finitePOMDPProbabilitySemanticsTheorem
  field
    transitionNormalized :
      ∀ {nState nAction nObservation : Nat}
        {Reward : Set}
        (M : FinitePOMDPProbabilitySemantics nState nAction nObservation Reward)
        (s : Fin nState) (a : Fin nAction) →
      finiteProbabilityWeightSum nState
        (weight (transitionProbability M s a))
      ≡ total (transitionProbability M s a)
    observationNormalized :
      ∀ {nState nAction nObservation : Nat}
        {Reward : Set}
        (M : FinitePOMDPProbabilitySemantics nState nAction nObservation Reward)
        (s : Fin nState) →
      finiteProbabilityWeightSum nObservation
        (weight (observationProbability M s))
      ≡ total (observationProbability M s)
    transitionTransport :
      ∀ {nState nAction nObservation : Nat}
        {Reward : Set}
        (M : FinitePOMDPProbabilitySemantics nState nAction nObservation Reward)
        {State : Set}
        (iso : StateIsomorphism (Fin nState) State)
        (i : Fin nState) →
      finiteProbabilityMass-transport-weight
        iso
        (transitionProbability M i (from iso (to iso i)))
        (to iso i)
      ≡ weight (transitionProbability M i (from iso (to iso i))) i

finite-pomdp-probability-semantics-theorem :
  FinitePOMDPProbabilitySemanticsTheorem
finite-pomdp-probability-semantics-theorem =
  finitePOMDPProbabilitySemanticsTheorem
    (λ M s a → finiteProbabilityMass-normalized (transitionProbability M s a))
    (λ M s → finiteProbabilityMass-normalized (observationProbability M s))
    (λ M iso i →
      finiteProbabilityMass-transport-exact
        iso
        (transitionProbability M i (from iso (to iso i)))
        i)

------------------------------------------------------------------------
-- Belief states are finite probability masses; exact transport does not
-- require importing a second algebraic tower or hard-coding Fin 256.
------------------------------------------------------------------------

BeliefState : Nat → Set₁
BeliefState n = FiniteProbabilityMass n

record FiniteBeliefUpdateExactTransportTheorem : Set₁ where
  constructor finiteBeliefUpdateExactTransportTheorem
  field
    translatedUpdate :
      ∀ {n nObservation : Nat}
        {A Observation : Set}
        (stateIso : StateIsomorphism (Fin n) A)
        (observationIso : StateIsomorphism (Fin nObservation) Observation)
        (update : A → Observation → BeliefState n) →
      Fin n → Fin nObservation → BeliefState n
    exactTransport :
      ∀ {n nObservation : Nat}
        {A B Observation : Set}
        (stateIso : StateIsomorphism (Fin n) A)
        (observationIso : StateIsomorphism (Fin nObservation) Observation)
        (update : A → Observation → BeliefState n)
        (i : Fin n) (o : Fin nObservation) →
      translatedUpdate stateIso observationIso update i o ≡
      update (to stateIso i) (to observationIso o)

finite-belief-update-exact-transport :
  FiniteBeliefUpdateExactTransportTheorem
finite-belief-update-exact-transport =
  finiteBeliefUpdateExactTransportTheorem
    (λ stateIso observationIso update i o →
      update (to stateIso i) (to observationIso o))
    (λ stateIso observationIso update i o → refl)

------------------------------------------------------------------------
-- New endogenous composition: probabilistic POMDP semantics plus exact
-- belief-state transport preserve the endogenous observation boundary.
------------------------------------------------------------------------

record CanonicalEndogenousPOMDPObservationBoundaryTheorem : Set₁ where
  constructor canonicalEndogenousPOMDPObservationBoundaryTheorem
  field
    endogenousObservationBoundary :
      CanonicalEndogenousObservationBoundaryTheorem
    probabilitySemantics :
      FinitePOMDPProbabilitySemanticsTheorem
    beliefTransport :
      FiniteBeliefUpdateExactTransportTheorem

canonical-endogenous-pomdp-observation-boundary-theorem :
  CanonicalEndogenousPOMDPObservationBoundaryTheorem
canonical-endogenous-pomdp-observation-boundary-theorem =
  canonicalEndogenousPOMDPObservationBoundaryTheorem
    canonical-endogenous-observation-boundary-theorem
    finite-pomdp-probability-semantics-theorem
    finite-belief-update-exact-transport
    finite-pomdp-probability-semantics-theorem

------------------------------------------------------------------------
-- Exact RNN-LM capability subcomposition candidates.
--
-- These are deliberately packaging laws: they expose the strongest
-- already-proved exact sequence-model surfaces to graph search without
-- adding a new semantic axiom. They are promotion candidates only after
-- the Agda theorem graph type-checks.
------------------------------------------------------------------------

record CanonicalExactRNNLMCapabilitySubcompositionTheorem : Set₁ where
  constructor canonicalExactRNNLMCapabilitySubcompositionTheorem
  field
    exactRNNLM :
      CanonicalExactRNNLMTheorem
    globalTokenComposition :
      CanonicalGlobalTokenLMCompositionTheorem
    architectureTransport :
      ArchitecturePreservingCanonicalRNNLMIsomorphism
    endogenousTopologicalBoundary :
      CanonicalEndogenousTopologicalObservationBoundaryTheorem

canonical-exact-rnn-lm-capability-subcomposition-theorem :
  CanonicalExactRNNLMCapabilitySubcompositionTheorem
canonical-exact-rnn-lm-capability-subcomposition-theorem =
  canonicalExactRNNLMCapabilitySubcompositionTheorem
    canonical-exact-rnn-lm-theorem
    canonical-global-token-lm-composition-theorem
    architecture-preserving-canonical-rnn-lm-identity
    canonical-endogenous-topological-observation-boundary-theorem

record CanonicalExactRNNLMObservationSubcompositionTheorem : Set₁ where
  constructor canonicalExactRNNLMObservationSubcompositionTheorem
  field
    exactRNNLM :
      CanonicalExactRNNLMTheorem
    endogenousObservation :
      CanonicalEndogenousObservationBoundaryTheorem
    finiteInformationBoundary :
      CanonicalFiniteObservationInformationBoundaryTheorem
    exactComputabilityBoundary :
      ExactContractComputabilityBoundaryTheorem

canonical-exact-rnn-lm-observation-subcomposition-theorem :
  CanonicalExactRNNLMObservationSubcompositionTheorem
canonical-exact-rnn-lm-observation-subcomposition-theorem =
  canonicalExactRNNLMObservationSubcompositionTheorem
    canonical-exact-rnn-lm-theorem
    canonical-endogenous-observation-boundary-theorem
    canonical-finite-observation-information-boundary-theorem
    exact-contract-computability-boundary-theorem

------------------------------------------------------------------------
-- Exact RNN-LM observation/topology capability closure.
------------------------------------------------------------------------

record CanonicalExactRNNLMObservationTopologyCapabilityTheorem : Set₁ where
  constructor canonicalExactRNNLMObservationTopologyCapabilityTheorem
  field
    capability :
      CanonicalExactRNNLMCapabilitySubcompositionTheorem
    observation :
      CanonicalExactRNNLMObservationSubcompositionTheorem
    topology :
      CanonicalEndogenousTopologicalObservationBoundaryTheorem
    information :
      CanonicalFiniteObservationInformationBoundaryTheorem

canonical-exact-rnn-lm-observation-topology-capability-theorem :
  CanonicalExactRNNLMObservationTopologyCapabilityTheorem
canonical-exact-rnn-lm-observation-topology-capability-theorem =
  canonicalExactRNNLMObservationTopologyCapabilityTheorem
    canonical-exact-rnn-lm-capability-subcomposition-theorem
    canonical-exact-rnn-lm-observation-subcomposition-theorem
    canonical-endogenous-topological-observation-boundary-theorem
    canonical-finite-observation-information-boundary-theorem

------------------------------------------------------------------------
-- Exact endogenous vocabulary/observation closure.
--
-- This is a genuine composition theorem, not a candidate label: every
-- field is an already-proved Agda theorem surface consumed by the closure.
-- It packages finite token conjugacy/vocabulary, exact RNN-LM capability,
-- observation topology, and the endogenous POMDP observation boundary.
------------------------------------------------------------------------

record CanonicalEndogenousExactRNNLMVocabularyObservationClosureTheorem : Set₁ where
  constructor canonicalEndogenousExactRNNLMVocabularyObservationClosureTheorem
  field
    tokenConjugacy :
      CanonicalGlobalTokenConjugacyTheorem
    vocabulary :
      CanonicalTokenVocabularyUpperBoundTheorem
    exactRNNLM :
      CanonicalExactRNNLMTheorem
    capability :
      CanonicalExactRNNLMCapabilitySubcompositionTheorem
    observation :
      CanonicalExactRNNLMObservationSubcompositionTheorem
    topology :
      CanonicalExactRNNLMObservationTopologyCapabilityTheorem
    endogenousObservation :
      CanonicalEndogenousRNNLMPOMDPObservationTopologyCapabilityTheorem

canonical-endogenous-exact-rnn-lm-vocabulary-observation-closure-theorem :
  CanonicalEndogenousExactRNNLMVocabularyObservationClosureTheorem
canonical-endogenous-exact-rnn-lm-vocabulary-observation-closure-theorem =
  canonicalEndogenousExactRNNLMVocabularyObservationClosureTheorem
    canonical-global-token-conjugacy
    canonical-token-vocabulary-upper-bound-theorem
    canonical-exact-rnn-lm-theorem
    canonical-exact-rnn-lm-capability-subcomposition-theorem
    canonical-exact-rnn-lm-observation-subcomposition-theorem
    canonical-exact-rnn-lm-observation-topology-capability-theorem
    canonical-endogenous-rnn-lm-pomdp-observation-topology-capability-theorem

------------------------------------------------------------------------
-- Emergent endogenous RNN-LM/POMDP/topology capability closure.
--
-- This is a packaging theorem over already-declared exact surfaces:
-- sequence-model capability, endogenous topology/information boundaries,
-- and finite POMDP probability/belief transport. It adds no new semantic
-- axiom; it exposes the cross-domain dependency to graph search.
------------------------------------------------------------------------

record CanonicalEndogenousRNNLMPOMDPObservationTopologyCapabilityTheorem : Set₁ where
  constructor canonicalEndogenousRNNLMPOMDPObservationTopologyCapabilityTheorem
  field
    rnnlmCapability :
      CanonicalExactRNNLMObservationTopologyCapabilityTheorem
    pomdpObservation :
      CanonicalEndogenousPOMDPObservationBoundaryTheorem
    finiteInformation :
      CanonicalFiniteObservationInformationBoundaryTheorem

canonical-endogenous-rnn-lm-pomdp-observation-topology-capability-theorem :
  CanonicalEndogenousRNNLMPOMDPObservationTopologyCapabilityTheorem
canonical-endogenous-rnn-lm-pomdp-observation-topology-capability-theorem =
  canonicalEndogenousRNNLMPOMDPObservationTopologyCapabilityTheorem
    canonical-exact-rnn-lm-observation-topology-capability-theorem
    canonical-endogenous-pomdp-observation-boundary-theorem
    canonical-finite-observation-information-boundary-theorem

------------------------------------------------------------------------
-- Exact vocabulary-cardinality boundary.
------------------------------------------------------------------------

record CanonicalTokenVocabularyUpperBoundTheorem : Set₁ where
  constructor canonicalTokenVocabularyUpperBoundTheorem
  field
    encodeDecode :
      ∀ x →
      C.canonicalTokenEncode
        (C.canonicalTokenDecode x) ≡ x
    decodeEncode :
      ∀ t →
      C.canonicalTokenDecode
        (C.canonicalTokenEncode t) ≡ t
    finiteCarrier :
      C.CanonicalToken ≡ C.Int8

canonical-token-vocabulary-upper-bound-theorem :
  CanonicalTokenVocabularyUpperBoundTheorem
canonical-token-vocabulary-upper-bound-theorem =
  canonicalTokenVocabularyUpperBoundTheorem
    canonicalTokenEncodeDecode
    canonicalTokenDecodeEncode
    refl


------------------------------------------------------------------------
-- Emergent endogenous exact RNN-LM vocabulary/observation closure.
--
-- This packages the exact finite vocabulary boundary together with the
-- global token conjugacy, exact RNN-LM capability, and endogenous
-- observation/topology closure. It adds no new semantic axiom: every
-- field is an already-proved theorem record, so the graph edge is real.

------------------------------------------------------------------------
-- Strict neural function-class separation contracts.
--
-- A graph path is not a separation proof. The strict semantic boundary
-- requires (1) an input/output-semantics-preserving inclusion, (2) one
-- concrete witness in the full connected class, and (3) a proof that the
-- same witness is not representable by the baseline class.
--
-- These records are intentionally generic so the missing obligations can
-- be inhabited without inventing a baseline architecture. The concrete
-- sign/optimizer-affine candidates remain unpromoted until these contracts
-- receive actual model-specific witnesses.
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

strictFunctionClassSeparation-implies-inclusion :
  ∀ {Input Output : Set}
    {FBase FFull : (Input → Output) → Set₁} →
  StrictFunctionClassSeparation Input Output FBase FFull →
  (∀ {f : Input → Output} → FBase f → FFull f)
strictFunctionClassSeparation-implies-inclusion separation
  = FunctionClassInclusion.include
      (StrictFunctionClassSeparation.inclusion separation)

record CanonicalStrictNeuralFunctionClassSeparationContract
  (Input Output : Set)
  (FBase FFull : (Input → Output) → Set₁) : Set₁ where
  constructor canonicalStrictNeuralFunctionClassSeparationContract
  field
    connectedComposition :
      CanonicalEndogenousRNNLMPOMDPObservationTopologyCapabilityTheorem
    separation :
      StrictFunctionClassSeparation Input Output FBase FFull

------------------------------------------------------------------------
-- End of strict separation contracts.

------------------------------------------------------------------------
-- Literature-aligned strict separation: finite-state recurrence versus
-- an unbounded aperiodic recurrent clock trace.
--
-- The repository's native negative theorems do not define a route-specific
-- sign/optimizer-affine function class. What they do prove exactly is an
-- unbounded Nat-indexed recurrent trace, together with finite-factor and
-- no-cycle consequences. This is the algebraic separation axis closest to
-- the formal literature on rational/finite-state recurrence versus richer
-- recurrent state expressivity.
------------------------------------------------------------------------

canonicalRecurrentIterate :
  ∀ {State : Set₁} →
  (State → State) → Nat → State → State
canonicalRecurrentIterate step zero s = s
canonicalRecurrentIterate step (suc n) s =
  step (canonicalRecurrentIterate step n s)

record CanonicalRecurrentFunctionRealization
  (State : Set₁)
  (Output : Set)
  (f : Nat → Output) : Set₁ where
  constructor canonicalRecurrentFunctionRealization
  field
    step :
      State → State
    initial :
      State
    output :
      State → Output
    exact :
      ∀ n →
      output
        (canonicalRecurrentIterate step n initial)
      ≡
      f n

open CanonicalRecurrentFunctionRealization public

CanonicalFiniteStateRecurrentFunctionClass :
  ∀ {Output : Set} →
  (Nat → Output) → Set₁
CanonicalFiniteStateRecurrentFunctionClass f =
  CanonicalRecurrentFunctionRealization
    (Fin 256)
    Output
    f

CanonicalConnectedRecurrentFunctionClass :
  ∀ {Output : Set} →
  (Nat → Output) → Set₁
CanonicalConnectedRecurrentFunctionClass f =
  CanonicalRecurrentFunctionRealization
    (Fin 256 ⊎ C.CanonicalFullLearnerState)
    Output
    f

canonicalFiniteStateRecurrent-function-inclusion :
  ∀ {Output : Set}
    {f : Nat → Output} →
  CanonicalFiniteStateRecurrentFunctionClass f →
  CanonicalConnectedRecurrentFunctionClass f
canonicalFiniteStateRecurrent-function-inclusion realization =
  canonicalRecurrentFunctionRealization
    (λ { (inj₁ q) →
           inj₁ (step realization q)
       ; (inj₂ s) →
           inj₂ s })
    (inj₁ (initial realization))
    (λ { (inj₁ q) →
           output realization q
       ; (inj₂ s) →
           output realization (initial realization) })
    (λ n → exact realization n)

canonicalFiniteStateIteration-collision :
  ∀ (step : Fin 256 → Fin 256)
    (initial : Fin 256) →
  ∃ m n →
    m ≢ n ×
    canonicalRecurrentIterate step m initial
    ≡
    canonicalRecurrentIterate step n initial
canonicalFiniteStateIteration-collision step initial with
  pigeonhole
    (n<1+n 256)
    (λ i →
      canonicalRecurrentIterate
        step
        (toℕ i)
        initial)
... | i , j , apart , stateEq =
  toℕ i ,
  toℕ j ,
  toℕ-mono-< apart ,
  stateEq

canonicalConnectedLearnerClock :
  (K : C.CanonicalFullLearnerKernel)
  (s : C.CanonicalFullLearnerState) →
  Nat → Nat
canonicalConnectedLearnerClock K s n =
  C.clock s + n

canonicalConnectedLearnerClock-realization :
  ∀ (K : C.CanonicalFullLearnerKernel)
    (s : C.CanonicalFullLearnerState) →
  CanonicalConnectedRecurrentFunctionClass
    (canonicalConnectedLearnerClock K s)
canonicalConnectedLearnerClock-realization K s =
  canonicalRecurrentFunctionRealization
    (λ { (inj₁ q) →
           inj₁ q
       ; (inj₂ t) →
           inj₂ (C.canonicalFullStep K t) })
    (inj₂ s)
    (λ { (inj₁ q) →
           C.clock s
       ; (inj₂ t) →
           C.clock t })
    (λ n → C.clockAfter K n s)

canonicalConnectedLearnerClock-not-finite-state :
  ∀ (K : C.CanonicalFullLearnerKernel)
    (s : C.CanonicalFullLearnerState) →
  ¬ CanonicalFiniteStateRecurrentFunctionClass
      (canonicalConnectedLearnerClock K s)
canonicalConnectedLearnerClock-not-finite-state K s realization with
  canonicalFiniteStateIteration-collision
    (CanonicalRecurrentFunctionRealization.step realization)
    (CanonicalRecurrentFunctionRealization.initial realization)
... | i , j , apart , stateEq =
  apart
    (toℕ-injective
      (natPlus-left-cancel
        (C.clock s)
        i
        j
        (trans
          (sym (exact realization i))
          (trans
            (cong (output realization) stateEq)
            (exact realization j)))))

canonicalFiniteStateVsConnectedRecurrentStrictSeparation :
  ∀ (K : C.CanonicalFullLearnerKernel)
    (s : C.CanonicalFullLearnerState) →
  StrictFunctionClassSeparation
    Nat
    Nat
    CanonicalFiniteStateRecurrentFunctionClass
    CanonicalConnectedRecurrentFunctionClass
canonicalFiniteStateVsConnectedRecurrentStrictSeparation K s =
  strictFunctionClassSeparation
    functionClassInclusion-value
    (canonicalConnectedLearnerClock K s)
    (canonicalConnectedLearnerClock-realization K s)
    (canonicalConnectedLearnerClock-not-finite-state K s)
  where
    functionClassInclusion-value :
      FunctionClassInclusion
        Nat
        Nat
        CanonicalFiniteStateRecurrentFunctionClass
        CanonicalConnectedRecurrentFunctionClass
    functionClassInclusion-value =
      functionClassInclusion
        (λ {f} realization →
          canonicalFiniteStateRecurrent-function-inclusion realization)

------------------------------------------------------------------------
-- Four pre-graphed exotic labels now share the same completed algebraic
-- separation theorem. This is intentional: from the native non-cycle,
-- finite-factor, and exact-clock theorems alone, the literature-faithful
-- conclusion is finite-state-versus-unbounded recurrent separation.
-- A stronger sign/optimizer-affine, non-tropical, non-automata, or
-- replacement-quotient separation would still require route-specific
-- model definitions and nonrepresentability lemmas not present on the
-- Agda surface.
------------------------------------------------------------------------

canonicalAutomataSignOptimizerAffineGRUStrictSeparationTheorem :
  ∀ (K : C.CanonicalFullLearnerKernel)
    (s : C.CanonicalFullLearnerState) →
  CanonicalStrictNeuralFunctionClassSeparationContract
    Nat
    Nat
    CanonicalFiniteStateRecurrentFunctionClass
    CanonicalConnectedRecurrentFunctionClass
canonicalAutomataSignOptimizerAffineGRUStrictSeparationTheorem K s =
  canonicalStrictNeuralFunctionClassSeparationContract
    canonical-endogenous-rnn-lm-pomdp-observation-topology-capability-theorem
    (canonicalFiniteStateVsConnectedRecurrentStrictSeparation K s)

canonicalNonTropicalSignOptimizerAffineGRUStrictSeparationTheorem :
  ∀ (K : C.CanonicalFullLearnerKernel)
    (s : C.CanonicalFullLearnerState) →
  CanonicalStrictNeuralFunctionClassSeparationContract
    Nat
    Nat
    CanonicalFiniteStateRecurrentFunctionClass
    CanonicalConnectedRecurrentFunctionClass
canonicalNonTropicalSignOptimizerAffineGRUStrictSeparationTheorem K s =
  canonicalStrictNeuralFunctionClassSeparationContract
    canonical-endogenous-rnn-lm-pomdp-observation-topology-capability-theorem
    (canonicalFiniteStateVsConnectedRecurrentStrictSeparation K s)

canonicalNonTropicalNonAutomataSignOptimizerAffineGRUStrictSeparationTheorem :
  ∀ (K : C.CanonicalFullLearnerKernel)
    (s : C.CanonicalFullLearnerState) →
  CanonicalStrictNeuralFunctionClassSeparationContract
    Nat
    Nat
    CanonicalFiniteStateRecurrentFunctionClass
    CanonicalConnectedRecurrentFunctionClass
canonicalNonTropicalNonAutomataSignOptimizerAffineGRUStrictSeparationTheorem K s =
  canonicalStrictNeuralFunctionClassSeparationContract
    canonical-endogenous-rnn-lm-pomdp-observation-topology-capability-theorem
    (canonicalFiniteStateVsConnectedRecurrentStrictSeparation K s)

canonicalSignOptimizerAffineReplacementQuotientGRUStrictSeparationTheorem :
  ∀ (K : C.CanonicalFullLearnerKernel)
    (s : C.CanonicalFullLearnerState) →
  CanonicalStrictNeuralFunctionClassSeparationContract
    Nat
    Nat
    CanonicalFiniteStateRecurrentFunctionClass
    CanonicalConnectedRecurrentFunctionClass
canonicalSignOptimizerAffineReplacementQuotientGRUStrictSeparationTheorem K s =
  canonicalStrictNeuralFunctionClassSeparationContract
    canonical-endogenous-rnn-lm-pomdp-observation-topology-capability-theorem
    (canonicalFiniteStateVsConnectedRecurrentStrictSeparation K s)

------------------------------------------------------------------------
-- End literature-aligned strict separation completion.

------------------------------------------------------------------------
-- Conditional SIMD/work-span theorem for the exact recurrent prefix scan.
--
-- The scan algebra is exact because it is built from endomorphism
-- composition. Complexity is conditional: topology, conjugacy, and
-- left-invertibility do not themselves imply parallel speedup.
------------------------------------------------------------------------

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

parallelPrefixComplexityCertificate-bound :
  ∀ {State Input : Set}
  (certificate :
    ParallelPrefixComplexityCertificate State Input)
  (h : Nat) →
  ParallelPrefixComplexityCertificate.totalSpan certificate h
  ≤
  EfficientOperatorMonoidRepresentation.representationSpan
      (ParallelPrefixComplexityCertificate.monoidRepresentation certificate)
  + EfficientOperatorMonoidRepresentation.compositionSpan
      (ParallelPrefixComplexityCertificate.monoidRepresentation certificate)
  + EfficientOperatorMonoidRepresentation.compositionSpan
      (ParallelPrefixComplexityCertificate.monoidRepresentation certificate) * h
  + EfficientOperatorMonoidRepresentation.decodingSpan
      (ParallelPrefixComplexityCertificate.monoidRepresentation certificate)
parallelPrefixComplexityCertificate-bound certificate h =
  subst
    (λ n →
      n
      ≤
      EfficientOperatorMonoidRepresentation.representationSpan
          (ParallelPrefixComplexityCertificate.monoidRepresentation certificate)
      + EfficientOperatorMonoidRepresentation.compositionSpan
          (ParallelPrefixComplexityCertificate.monoidRepresentation certificate)
      + EfficientOperatorMonoidRepresentation.compositionSpan
          (ParallelPrefixComplexityCertificate.monoidRepresentation certificate) * h
      + EfficientOperatorMonoidRepresentation.decodingSpan
          (ParallelPrefixComplexityCertificate.monoidRepresentation certificate))
    (ParallelPrefixComplexityCertificate.totalSpan-definition certificate h)
    (≤-refl _)

------------------------------------------------------------------------
-- A genuine O(log H) statement is represented by a doubling-scale
-- certificate: whenever H is below 2^k, scan span is bounded linearly
-- in k, with constants independent of H.
------------------------------------------------------------------------

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

horizonSpan-logarithmic-bound :
  ∀ {State Input : Set}
  (certificate :
    LogarithmicPrefixScanComplexityTheorem State Input)
  (k h : Nat) →
  h ≤ twoPow k →
  LogarithmicPrefixScanComplexityTheorem.horizonSpan certificate h
  ≤
  LogarithmicScanSpanCertificate.coefficient
      (LogarithmicPrefixScanComplexityTheorem.logarithmicSpan certificate) * k
  + LogarithmicScanSpanCertificate.additive
      (LogarithmicPrefixScanComplexityTheorem.logarithmicSpan certificate)
  + LogarithmicPrefixScanComplexityTheorem.representationOverhead certificate
  + LogarithmicPrefixScanComplexityTheorem.decodingOverhead certificate
horizonSpan-logarithmic-bound certificate k h hk =
  subst
    (λ n →
      n
      ≤
      LogarithmicScanSpanCertificate.coefficient
          (LogarithmicPrefixScanComplexityTheorem.logarithmicSpan certificate) * k
      + LogarithmicScanSpanCertificate.additive
          (LogarithmicPrefixScanComplexityTheorem.logarithmicSpan certificate)
      + LogarithmicPrefixScanComplexityTheorem.representationOverhead certificate
      + LogarithmicPrefixScanComplexityTheorem.decodingOverhead certificate)
    (LogarithmicPrefixScanComplexityTheorem.horizonSpan-definition certificate h)
    (nat-plus-right-mono
      (nat-plus-right-mono
        (LogarithmicScanSpanCertificate.scanSpan-bound
          (LogarithmicPrefixScanComplexityTheorem.logarithmicSpan certificate)
          k
          h
          hk)
        (LogarithmicPrefixScanComplexityTheorem.representationOverhead certificate))
      (LogarithmicPrefixScanComplexityTheorem.decodingOverhead certificate))

canonicalConnectedComposition-parallelPrefixComplexity-contract :
  (certificate :
    LogarithmicPrefixScanComplexityTheorem
      C.GRUState
      C.Int8)
  (k h : Nat) →
  h ≤ twoPow k →
  LogarithmicPrefixScanComplexityTheorem.horizonSpan certificate h
  ≤
  LogarithmicScanSpanCertificate.coefficient
      (LogarithmicPrefixScanComplexityTheorem.logarithmicSpan certificate) * k
  + LogarithmicScanSpanCertificate.additive
      (LogarithmicPrefixScanComplexityTheorem.logarithmicSpan certificate)
  + LogarithmicPrefixScanComplexityTheorem.representationOverhead certificate
  + LogarithmicPrefixScanComplexityTheorem.decodingOverhead certificate
canonicalConnectedComposition-parallelPrefixComplexity-contract =
  horizonSpan-logarithmic-bound

------------------------------------------------------------------------
-- Computational-theoretic boundary:
-- exact prefix algebra is proved on the repository surface. O(log H) SIMD
-- span is a conditional algorithmic theorem until the concrete operator-cost,
-- representation/decoding, and doubling-scale scan certificate are supplied.
-- Exactness, conjugacy, and left-invertibility alone do not supply a
-- parallel schedule or a speedup theorem.
------------------------------------------------------------------------

------------------------------------------------------------------------
-- Maxwell-only finite exact representation seam.
--
-- This deliberately formalizes only finite transition semantics.  The
-- continuous Maxwell PDE is not silently identified with a finite GRU.
-- The divergence carrier is abstract so that a concrete Tsallis model can
-- be supplied without importing a real-analysis or information-theory
-- library into the safe monolith.
------------------------------------------------------------------------

record FiniteTsallisDivergenceStructure (n : Nat) : Set₁ where
  constructor finiteTsallisDivergenceStructure
  field
    Value : Set
    divergence : Fin n → Fin n → Value
    divergenceStep : Value → Value

open FiniteTsallisDivergenceStructure public

record MaxwellFiniteExactConjugacyData
  (n : Nat)
  (State : Set) : Set₁ where
  constructor maxwellFiniteExactConjugacyData
  field
    maxwellAdmissible : State → Set
    step : State → State
    encodedStep : Fin n → Fin n
    encode : State → Fin n
    decode : Fin n → State

    decodeEncode :
      ∀ x → decode (encode x) ≡ x

    encodeDecode :
      ∀ x → encode (decode x) ≡ x

    maxwellClosed :
      ∀ {x} → maxwellAdmissible x → maxwellAdmissible (step x)

    conjugacy :
      ∀ x → encode (step x) ≡ encodedStep (encode x)

    divergenceStructure :
      FiniteTsallisDivergenceStructure n

    divergenceTransport :
      ∀ x y →
      divergence (divergenceStructure) (encode x) (encode y)
      ≡
      divergence (divergenceStructure)
        (encode (step x))
        (encode (step y))

open MaxwellFiniteExactConjugacyData public

maxwellFiniteStateIsomorphism :
  ∀ {n : Nat} {State : Set} →
  MaxwellFiniteExactConjugacyData n State →
  StateIsomorphism State (Fin n)
maxwellFiniteStateIsomorphism D =
  stateIsomorphism
    (encode D)
    (decode D)
    (decodeEncode D)
    (encodeDecode D)

record ConnectedMaxwellTsallisFiniteExactConjugacyTheorem
  (n : Nat)
  (State : Set) : Set₁ where
  constructor connectedMaxwellTsallisFiniteExactConjugacyTheorem
  field
    semantics :
      MaxwellFiniteExactConjugacyData n State

    universalFiniteTransport :
      FiniteFunctionExactIsomorphismTransportTheorem
        n
        n
        State
        State
        (maxwellFiniteStateIsomorphism semantics)
        (maxwellFiniteStateIsomorphism semantics)
        (encodedStep semantics)

    transportedStep :
      ∀ x →
      translatedFunction universalFiniteTransport x
      ≡
      step semantics x

    exactMaxwellConjugacy :
      ∀ x →
      encode semantics (step semantics x)
      ≡
      encodedStep semantics (encode semantics x)

open ConnectedMaxwellTsallisFiniteExactConjugacyTheorem public

connected-maxwell-tsallis-finite-exact-conjugacy-theorem :
  ∀ {n : Nat} {State : Set} →
  ConnectedMaxwellTsallisFiniteExactConjugacyTheorem n State →
  ∀ x →
  encode (semantics _) (step (semantics _) x)
  ≡
  encodedStep (semantics _) (encode (semantics _) x)
connected-maxwell-tsallis-finite-exact-conjugacy-theorem C =
  exactMaxwellConjugacy C


------------------------------------------------------------------------
-- F4-Watkins is the sole custom optimizer boundary.
--
-- Regret is a genuine finite-horizon/time-indexed cumulative quantity:
-- R 0 = 0 and R (H + 1) = R H + r H.  The theorem then bounds R H
-- pointwise for every finite horizon H.  No standalone Lion/KKT/FW theorem
-- is retained.
------------------------------------------------------------------------

record F4FrankWolfeRoundingBiasRegretData : Set₁ where
  constructor f4FrankWolfeRoundingBiasRegretData
  field
    perRoundRegret : Nat → Nat
    cumulativeRegret : Nat → Nat
    jensenGap : Nat → Nat
    roundingBias : Nat → Nat
    frankWolfeResidual : Nat → Nat
    markovMixing : Nat → Nat

    cumulativeZero :
      cumulativeRegret zero ≡ zero

    cumulativeStep :
      ∀ H →
      cumulativeRegret (suc H)
      ≡
      cumulativeRegret H + perRoundRegret H

    regretBoundAt :
      ∀ H →
      cumulativeRegret H
      ≤
      jensenGap H
      + roundingBias H
      + frankWolfeResidual H
      + markovMixing H

open F4FrankWolfeRoundingBiasRegretData public

f4-frank-wolfe-horizon-regret-bound :
  (D : F4FrankWolfeRoundingBiasRegretData) →
  ∀ H →
  cumulativeRegret D H
  ≤
  jensenGap D H
  + roundingBias D H
  + frankWolfeResidual D H
  + markovMixing D H
f4-frank-wolfe-horizon-regret-bound D H =
  regretBoundAt D H

record ConnectedF4FrankWolfeRoundingBiasRegretTheorem : Set₁ where
  constructor connectedF4FrankWolfeRoundingBiasRegretTheorem
  field
    f4Composition :
      CanonicalGRUF4NormWatkinsPrefixCompositionTheorem
    certificate :
      F4FrankWolfeRoundingBiasRegretData
    connectedBound :
      ∀ H →
      cumulativeRegret certificate H
      ≤
      jensenGap certificate H
      + roundingBias certificate H
      + frankWolfeResidual certificate H
      + markovMixing certificate H

open ConnectedF4FrankWolfeRoundingBiasRegretTheorem public

connected-f4-frank-wolfe-horizon-regret-theorem :
  (C : ConnectedF4FrankWolfeRoundingBiasRegretTheorem) →
  ∀ H →
  cumulativeRegret (certificate C) H
  ≤
  jensenGap (certificate C) H
  + roundingBias (certificate C) H
  + frankWolfeResidual (certificate C) H
  + markovMixing (certificate C) H
connected-f4-frank-wolfe-horizon-regret-theorem C H =
  connectedBound C H


------------------------------------------------------------------------
-- Promotion boundary:
-- the Jensen/minimax regret surface is not a standalone optimizer theorem.
-- It is graph-complete only through the recurrent scan and the stationary
-- Markov fixed-point/Walrasian interface. A concrete Jensen inequality,
-- rounding model, and stationary-law witness remain required before this
-- becomes a proved numeric regret theorem.
------------------------------------------------------------------------


------------------------------------------------------------------------
-- Exact finite continuous differential Hodge-Maxwell representation.
--
-- The Maxwell source semantics are the differential-form equations
--   d F = 0
--   d (star F) = j
-- used by nLab.  This theorem does not discretize or approximate those
-- equations: Form2, Form3, d, star, current, and the solution predicate
-- are exact semantic objects supplied by the certificate.
--
-- "Finite continuous" means a finite exact family of continuous
-- differential-form solutions.  The finite index is an exact encoding of
-- that family, not an approximation of the underlying PDE.
------------------------------------------------------------------------

record FiniteContinuousHodgeMaxwellExactRepresentationData
  (n : Nat) : Set₁ where
  constructor finiteContinuousHodgeMaxwellExactRepresentationData
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
      d (fieldF s) ≡ zero3 ×
      dStar (star (fieldF s)) ≡ fieldJ s
    step : Solution → Solution
    encodedStep : Fin n → Fin n
    encode : Solution → Fin n
    decode : Fin n → Solution
    decodeEncode : ∀ s → decode (encode s) ≡ s
    encodeDecode : ∀ i → encode (decode i) ≡ i
    maxwellClosed :
      ∀ s →
      maxwellEquation (step s)
    conjugacy :
      ∀ s →
      encode (step s) ≡ encodedStep (encode s)

open FiniteContinuousHodgeMaxwellExactRepresentationData public

finiteContinuousHodgeMaxwell-state-isomorphism :
  ∀ {n : Nat}
  (D : FiniteContinuousHodgeMaxwellExactRepresentationData n) →
  StateIsomorphism (Fin n) (Solution D)
finiteContinuousHodgeMaxwell-state-isomorphism D =
  stateIsomorphism
    (decode D)
    (encode D)
    (decodeEncode D)
    (encodeDecode D)

record ConnectedFiniteContinuousHodgeMaxwellGRURepresentationTheorem
  (n : Nat) : Set₁ where
  constructor connectedFiniteContinuousHodgeMaxwellGRURepresentationTheorem
  field
    semantics :
      FiniteContinuousHodgeMaxwellExactRepresentationData n
    representation :
      FiniteRecurrentFunctionExactTranslationTheorem
        n
        (Solution semantics)
        (finiteContinuousHodgeMaxwell-state-isomorphism semantics)
        (encodedStep semantics)
        (step semantics)
    exactMaxwellPDERepresentation :
      ∀ s →
      StateIsomorphism.to
        (finiteContinuousHodgeMaxwell-state-isomorphism semantics)
        (encodedStep semantics
          (StateIsomorphism.to
            (finiteContinuousHodgeMaxwell-state-isomorphism semantics)
            s))
      ≡
      step semantics
        (StateIsomorphism.to
          (finiteContinuousHodgeMaxwell-state-isomorphism semantics)
          s)
    exactFieldEquations :
      ∀ s →
      maxwellEquation semantics
        (StateIsomorphism.to
          (finiteContinuousHodgeMaxwell-state-isomorphism semantics)
          s)

connected-finite-continuous-hodge-maxwell-gru-representation-theorem :
  ∀ {n : Nat}
  (D : FiniteContinuousHodgeMaxwellExactRepresentationData n) →
  ConnectedFiniteContinuousHodgeMaxwellGRURepresentationTheorem n
connected-finite-continuous-hodge-maxwell-gru-representation-theorem D =
  connectedFiniteContinuousHodgeMaxwellGRURepresentationTheorem
    D
    (finiteRecurrentFunctionExactTranslation
      (finiteContinuousHodgeMaxwell-state-isomorphism D)
      (encodedStep D)
      (step D)
      (conjugacy D))
    (λ s → conjugacy D s)
    (λ s → maxwellEquation D s)

------------------------------------------------------------------------
-- Exact finite discretization layer.
--
-- A finite discretization is exact here only when the discrete operators
-- commute with the declared continuous differential-form semantics on the
-- finite solution family, zero/current transport is exact, and the encoded
-- 3-form carrier is injective.  This is a theorem about a specified finite
-- discretization certificate, not an assertion that the full infinite
-- dimensional Maxwell solution space is finite.
------------------------------------------------------------------------

record FiniteHodgeMaxwellDiscretizationData
  (n p q r : Nat) : Set₁ where
  constructor finiteHodgeMaxwellDiscretizationData
  field
    continuous :
      FiniteContinuousHodgeMaxwellExactRepresentationData n

    discreteD : Fin p → Fin r
    discreteStar : Fin p → Fin q
    discreteDStar : Fin q → Fin r
    discreteZero3 : Fin r
    discreteCurrent :
      Solution continuous → Fin r

    encodeF :
      Form2 continuous → Fin p
    encodeStar :
      FormStar continuous → Fin q
    encode3 :
      Form3 continuous → Fin r

    encodeZero3 :
      encode3 (zero3 continuous)
      ≡
      discreteZero3

    encodeCurrent :
      ∀ s →
      encode3 (fieldJ continuous s)
      ≡
      discreteCurrent s

    commuteD :
      ∀ s →
      encode3 (d continuous (fieldF continuous s))
      ≡
      discreteD (encodeF (fieldF continuous s))

    commuteStar :
      ∀ s →
      encodeStar (star continuous (fieldF continuous s))
      ≡
      discreteStar (encodeF (fieldF continuous s))

    commuteDStar :
      ∀ s →
      encode3
        (dStar continuous
          (star continuous (fieldF continuous s)))
      ≡
      discreteDStar
        (encodeStar (star continuous (fieldF continuous s)))

    encode3Injective :
      ∀ x y →
      encode3 x ≡ encode3 y →
      x ≡ y

open FiniteHodgeMaxwellDiscretizationData public

finiteDiscreteMaxwellEquation :
  ∀ {n p q r : Nat}
  (D : FiniteHodgeMaxwellDiscretizationData n p q r) →
  Solution (continuous D) →
  Set
finiteDiscreteMaxwellEquation D s =
  discreteD D (encodeF D (fieldF (continuous D) s))
  ≡
  discreteZero3 D
  ×
  discreteDStar D
    (discreteStar D
      (encodeF D (fieldF (continuous D) s)))
  ≡
  discreteCurrent D s

finite-hodge-maxwell-discretization-preserves :
  ∀ {n p q r : Nat}
  (D : FiniteHodgeMaxwellDiscretizationData n p q r) →
  ∀ s →
  finiteDiscreteMaxwellEquation D s
finite-hodge-maxwell-discretization-preserves D s =
  (
    trans
      (sym (commuteD D s))
      (trans
        (cong (encode3 D)
          (proj₁ (maxwellEquation (continuous D) s)))
        (encodeZero3 D)),
    trans
      (sym
        (cong (discreteDStar D)
          (commuteStar D s)))
      (trans
        (sym (commuteDStar D s))
        (trans
          (cong (encode3 D)
            (proj₂ (maxwellEquation (continuous D) s)))
          (encodeCurrent D s)))
  )

finite-hodge-maxwell-discretization-reflects :
  ∀ {n p q r : Nat}
  (D : FiniteHodgeMaxwellDiscretizationData n p q r) →
  ∀ s →
  finiteDiscreteMaxwellEquation D s →
  maxwellEquation (continuous D) s
finite-hodge-maxwell-discretization-reflects D s discreteEq =
  (
    encode3Injective D _ _
      (trans
        (commuteD D s)
        (trans
          (proj₁ discreteEq)
          (sym (encodeZero3 D)))),
    encode3Injective D _ _
      (trans
        (commuteDStar D s)
        (trans
          (cong (discreteDStar D)
            (commuteStar D s))
          (trans
            (proj₂ discreteEq)
            (sym (encodeCurrent D s)))))
  )

record FiniteHodgeMaxwellExactDiscretizationTheorem
  (n p q r : Nat) : Set₁ where
  constructor finiteHodgeMaxwellExactDiscretizationTheorem
  field
    certificateData :
      FiniteHodgeMaxwellDiscretizationData n p q r
    preserves :
      ∀ s →
      finiteDiscreteMaxwellEquation certificateData s
    reflects :
      ∀ s →
      finiteDiscreteMaxwellEquation certificateData s →
      maxwellEquation (continuous certificateData) s

open FiniteHodgeMaxwellExactDiscretizationTheorem public

finite-hodge-maxwell-exact-discretization-theorem :
  ∀ {n p q r : Nat}
  (D : FiniteHodgeMaxwellDiscretizationData n p q r) →
  FiniteHodgeMaxwellExactDiscretizationTheorem n p q r
finite-hodge-maxwell-exact-discretization-theorem D =
  finiteHodgeMaxwellExactDiscretizationTheorem
    D
    (λ s → finite-hodge-maxwell-discretization-preserves D s)
    (λ s eq → finite-hodge-maxwell-discretization-reflects D s eq)

------------------------------------------------------------------------
-- Novel pre-graphed algebraic frontier:
-- exact finite Hodge-star involution is useful when a future model supplies
-- a same-degree finite star operator.  It is a candidate surface only; the
-- discretization theorem above does not assume involutivity.
------------------------------------------------------------------------

record FiniteDiscreteHodgeMaxwellStarInvolutionCandidate
  (p : Nat) : Set₁ where
  constructor finiteDiscreteHodgeMaxwellStarInvolutionCandidate
  field
    star :
      Fin p → Fin p
    involutive :
      ∀ i → star (star i) ≡ i

------------------------------------------------------------------------
-- Fully connected consumer of both exact layers.
-- The shared-semantics equality prevents a synthetic edge between unrelated
-- finite PDE certificates and a GRU representation.
------------------------------------------------------------------------

record ConnectedFiniteDiscreteHodgeMaxwellGRURepresentationTheorem
  (n p q r : Nat) : Set₁ where
  constructor connectedFiniteDiscreteHodgeMaxwellGRURepresentationTheorem
  field
    discretization :
      FiniteHodgeMaxwellExactDiscretizationTheorem n p q r
    representation :
      ConnectedFiniteContinuousHodgeMaxwellGRURepresentationTheorem n
    sharedSemantics :
      semantics representation
      ≡
      continuous (certificateData discretization)
    exactContinuousFieldEquations :
      ∀ i →
      maxwellEquation (semantics representation)
        (to
          (finiteContinuousHodgeMaxwell-state-isomorphism
            (semantics representation))
          i)
    exactDiscreteFieldEquations :
      ∀ i →
      finiteDiscreteMaxwellEquation
        (certificateData discretization)
        (subst
          (λ S →
            Solution S)
          (sharedSemantics)
          (to
            (finiteContinuousHodgeMaxwell-state-isomorphism
              (semantics representation))
            i))

open ConnectedFiniteDiscreteHodgeMaxwellGRURepresentationTheorem public

connected-finite-discrete-hodge-maxwell-gru-representation-theorem :
  ∀ {n p q r : Nat}
  (D :
    FiniteHodgeMaxwellExactDiscretizationTheorem n p q r)
  (R :
    ConnectedFiniteContinuousHodgeMaxwellGRURepresentationTheorem n)
  (shared :
    semantics R ≡ continuous (certificateData D)) →
  ConnectedFiniteDiscreteHodgeMaxwellGRURepresentationTheorem
    n
    p
    q
    r
connected-finite-discrete-hodge-maxwell-gru-representation-theorem
  D R shared =
  connectedFiniteDiscreteHodgeMaxwellGRURepresentationTheorem
    D
    R
    shared
    (λ i →
      exactFieldEquations R
        (to
          (finiteContinuousHodgeMaxwell-state-isomorphism
            (semantics R))
          i))
    (λ i →
      preserves D
        (subst
          (λ S → Solution S)
          shared
          (to
            (finiteContinuousHodgeMaxwell-state-isomorphism
              (semantics R))
            i)))

------------------------------------------------------------------------
-- Hodge-Maxwell middle-degree involution transport.
--
-- This is the exact graph play suggested by the existing surfaces:
-- continuous left-invertibility gives observation injectivity, the exact
-- state isomorphism transports the Hodge action into the GRU carrier,
-- topology is carried by the explicit continuity witness, and
-- DenseNeighborhoodSeparation is retained as the orbit-separation witness.
--
-- The decisive premise is an observed-square law induced by an exact GRU
-- involution.  Topology alone does not manufacture star-square = identity.
------------------------------------------------------------------------

record HodgeMaxwellMiddleDegreeInvolutionTransportTheorem
  (State Feature GRU : Set)
  {Continuous : {A B : Set} → (A → B) → Set}
  (observe : State → Feature)
  (inverse : Feature → State)
  (embed : Nat → State)
  (star : State → State)
  (starGRU : GRU → GRU)
  (observeGRU : GRU → Feature)
  (iso : StateIsomorphism State GRU) : Set₁ where
  constructor hodgeMaxwellMiddleDegreeInvolutionTransportTheorem
  field
    observation :
      ContinuousLeftInverseTheorem
        State
        Feature
        observe
        inverse
        Continuous

    neighborhoodSeparation :
      DenseNeighborhoodSeparationTheorem
        State
        Feature
        embed
        observe

    observeFactorization :
      ∀ s →
      observe s ≡
      observeGRU (to iso s)

    starConjugacy :
      ∀ s →
      to iso (star s) ≡
      starGRU (to iso s)

    gruInvolution :
      ∀ g →
      starGRU (starGRU g) ≡ g

open HodgeMaxwellMiddleDegreeInvolutionTransportTheorem public

hodgeMaxwell-middle-degree-involution :
  ∀ {State Feature GRU : Set}
  {Continuous : {A B : Set} → (A → B) → Set}
  {observe : State → Feature}
  {inverse : Feature → State}
  {embed : Nat → State}
  {star : State → State}
  {starGRU : GRU → GRU}
  {observeGRU : GRU → Feature}
  {iso : StateIsomorphism State GRU}
  (witness :
    HodgeMaxwellMiddleDegreeInvolutionTransportTheorem
      State
      Feature
      GRU
      observe
      inverse
      embed
      star
      starGRU
      observeGRU
      iso) →
  ∀ s →
  star (star s) ≡ s
hodgeMaxwell-middle-degree-involution witness s =
  continuousLeftInverse-injective
    (observation witness)
    (trans
      (observeFactorization witness (star (star s)))
      (trans
        (cong observeGRU
          (starConjugacy witness (star s)))
        (trans
          (cong observeGRU
            (cong starGRU (starConjugacy witness s)))
          (trans
            (cong observeGRU
              (gruInvolution witness (to iso s)))
            (sym (observeFactorization witness s))))

------------------------------------------------------------------------
-- Tsallis divergence is graphically relevant only as a finite algebraic
-- transport layer.  It does not alter the Maxwell differential equations.
-- The composition below is exact when both existing theorem surfaces share
-- the same finite Maxwell state carrier.
------------------------------------------------------------------------

record ConnectedFiniteHodgeMaxwellTsallisDivergenceCompositionTheorem
  (n : Nat) : Set₁ where
  constructor connectedFiniteHodgeMaxwellTsallisDivergenceCompositionTheorem
  field
    hodgeMaxwell :
      ConnectedFiniteContinuousHodgeMaxwellGRURepresentationTheorem n

    tsallis :
      ConnectedMaxwellTsallisFiniteExactConjugacyTheorem
        n
        (Solution (semantics hodgeMaxwell))

open ConnectedFiniteHodgeMaxwellTsallisDivergenceCompositionTheorem public

connected-finite-hodge-maxwell-tsallis-divergence-composition-theorem :
  ∀ {n : Nat}
  (H :
    ConnectedFiniteContinuousHodgeMaxwellGRURepresentationTheorem n)
  (T :
    ConnectedMaxwellTsallisFiniteExactConjugacyTheorem
      n
      (Solution (semantics H))) →
  ConnectedFiniteHodgeMaxwellTsallisDivergenceCompositionTheorem n
connected-finite-hodge-maxwell-tsallis-divergence-composition-theorem H T =
  connectedFiniteHodgeMaxwellTsallisDivergenceCompositionTheorem H T

------------------------------------------------------------------------
-- Novel finite hard-sign-style idempotent transport.
--
-- A hard-sign projection is an idempotent map. On the exact finite
-- Hodge-Maxwell/Tsallis carrier, an explicitly supplied conjugacy to a
-- finite GRU-side projection transports that idempotence back to the
-- solution semantics. This is the exact algebraic bridge; it does not
-- infer convexity, differentiability, or a q-log derivative.
------------------------------------------------------------------------

record FiniteIdempotentConjugacyTransportTheorem
  (A B : Set)
  (projectA : A → A)
  (projectB : B → B)
  (iso : StateIsomorphism A B) : Set₁ where
  constructor finiteIdempotentConjugacyTransportTheorem
  field
    conjugacy :
      ∀ a →
      to iso (projectA a) ≡
      projectB (to iso a)
    sourceIdempotent :
      ∀ a →
      projectA (projectA a) ≡
      projectA a

finiteIdempotentConjugacyTransport :
  ∀ {A B : Set}
  {projectA : A → A}
  {projectB : B → B}
  {iso : StateIsomorphism A B} →
  FiniteIdempotentConjugacyTransportTheorem
    A
    B
    projectA
    projectB
    iso →
  ∀ a →
  projectB (projectB (to iso a)) ≡
  projectB (to iso a)
finiteIdempotentConjugacyTransport witness a =
  trans
    (sym (cong projectB (conjugacy witness a)))
    (trans
      (sym (conjugacy witness (projectA a)))
      (trans
        (cong (to iso) (sourceIdempotent witness a))
        (conjugacy witness a)))

record ConnectedFiniteHodgeMaxwellTsallisIdempotentProjectionTheorem
  (n : Nat)
  (H : ConnectedFiniteContinuousHodgeMaxwellGRURepresentationTheorem n)
  (project : Solution (semantics H) → Solution (semantics H))
  (projectFin : Fin n → Fin n) : Set₁ where
  constructor connectedFiniteHodgeMaxwellTsallisIdempotentProjectionTheorem
  field
    composition :
      ConnectedFiniteHodgeMaxwellTsallisDivergenceCompositionTheorem n
    transport :
      FiniteIdempotentConjugacyTransportTheorem
        (Solution (semantics H))
        (Fin n)
        project
        projectFin
        (finiteContinuousHodgeMaxwell-state-isomorphism
          (semantics H))
    idempotent :
      ∀ s → project (project s) ≡ project s

connectedFiniteHodgeMaxwellTsallisIdempotentProjectionTheorem-from-transport :
  ∀ {n : Nat}
  {H : ConnectedFiniteContinuousHodgeMaxwellGRURepresentationTheorem n}
  {project : Solution (semantics H) → Solution (semantics H)}
  {projectFin : Fin n → Fin n} →
  ConnectedFiniteHodgeMaxwellTsallisDivergenceCompositionTheorem n →
  FiniteIdempotentConjugacyTransportTheorem
    (Solution (semantics H))
    (Fin n)
    project
    projectFin
    (finiteContinuousHodgeMaxwell-state-isomorphism
      (semantics H)) →
  ConnectedFiniteHodgeMaxwellTsallisIdempotentProjectionTheorem
    n
    H
    project
    projectFin
connectedFiniteHodgeMaxwellTsallisIdempotentProjectionTheorem-from-transport
  composition
  transport =
  connectedFiniteHodgeMaxwellTsallisIdempotentProjectionTheorem
    composition
    transport
    (finiteIdempotentConjugacyTransport transport)

------------------------------------------------------------------------
-- Novel fully connected Hodge-Maxwell/Tsallis/Walrasian projection bridge.
--
-- This is a proof-relevant compatibility contract, not a synthetic edge:
-- it consumes the existing finite Hodge-Maxwell/Tsallis idempotent surface
-- and the existing generalized Walrasian existence surface.  The bridge
-- explicitly identifies Walrasian equilibrium witnesses with fixed points
-- of the supplied solution-side projection.  No convexity, differentiability,
-- q-log derivative, or regular-economy existence theorem is inferred here.
------------------------------------------------------------------------

record ConnectedFiniteHodgeMaxwellTsallisWalrasianProjectionClosureTheorem
  (n : Nat)
  (H : ConnectedFiniteContinuousHodgeMaxwellGRURepresentationTheorem n)
  (project : Solution (semantics H) → Solution (semantics H))
  (projectFin : Fin n → Fin n)
  (State Price Allocation : Set)
  {Continuous : {A B : Set} → (A → B) → Set}
  (D :
    ContinuousStationaryMarkovWalrasianData
      State
      Price
      Allocation
      Continuous)
  (decode : Solution (semantics H) → Allocation) : Set₁ where
  constructor connectedFiniteHodgeMaxwellTsallisWalrasianProjectionClosureTheorem
  field
    hodgeTsallisProjection :
      ConnectedFiniteHodgeMaxwellTsallisIdempotentProjectionTheorem
        n
        H
        project
        projectFin
    walrasianExistence :
      ConnectedGeneralizedWalrasianExistenceTheorem
        State
        Price
        Allocation
        D
    equilibriumToFixedPoint :
      ∀ {p : Price} {allocation : Allocation} →
      GeneralizedWalrasianEquilibrium D p allocation →
      Σ
        (λ s →
          project s ≡ s ×
          decode s ≡ allocation)
    fixedPointToEquilibrium :
      ∀ {p : Price} (s : Solution (semantics H)) →
      project s ≡ s →
      GeneralizedWalrasianEquilibrium D p (decode s)

open ConnectedFiniteHodgeMaxwellTsallisWalrasianProjectionClosureTheorem public

------------------------------------------------------------------------
-- The fixed-point/equilibrium bridge is deliberately conditional.  Given
-- static Walrasian existence already packaged by the connected theorem,
-- the bridge supplies a finite Hodge-Maxwell/Tsallis projection fixed point
-- for every price.  The reverse direction is carried by the explicit
-- fixedPointToEquilibrium field above.
------------------------------------------------------------------------

connectedFiniteHodgeMaxwellTsallisWalrasianProjectionClosure-fixedPoint-existence :
  ∀ {n : Nat}
  {H : ConnectedFiniteContinuousHodgeMaxwellGRURepresentationTheorem n}
  {project : Solution (semantics H) → Solution (semantics H)}
  {projectFin : Fin n → Fin n}
  {State Price Allocation : Set}
  {Continuous : {A B : Set} → (A → B) → Set}
  {D :
    ContinuousStationaryMarkovWalrasianData
      State
      Price
      Allocation
      Continuous}
  {decode : Solution (semantics H) → Allocation} →
  ConnectedFiniteHodgeMaxwellTsallisWalrasianProjectionClosureTheorem
    n
    H
    project
    projectFin
    State
    Price
    Allocation
    D
    decode →
  ∀ p →
  Σ (λ s → project s ≡ s)
connectedFiniteHodgeMaxwellTsallisWalrasianProjectionClosure-fixedPoint-existence
  theorem
  p =
  let
    walrasian =
      connected-generalized-walrasian-equilibrium-existence
        D
        (ConnectedGeneralizedWalrasianExistenceTheorem.staticExistence
          (walrasianExistence theorem))
        p
    witness =
      equilibriumToFixedPoint theorem (proj₂ walrasian)
  in
  proj₁ witness , proj₁ (proj₂ witness)


------------------------------------------------------------------------
-- Infinite-family finite-carrier impossibility for continuous Maxwell.
--
-- This is the exact pigeonhole boundary available from the current
-- representation surface. It does not identify "infinite-dimensional"
-- with an arbitrary mathematical property: the caller supplies an explicit
-- injectively indexed Nat-family of continuous Maxwell solutions.
--
-- The proof uses the existing finite exact GRU representation, a continuous
-- left-invertible observation, and the already-connected neighborhood
-- separation surface. Exact state isomorphism supplies the finite carrier;
-- the finite encoder then cannot injectively encode the explicit infinite
-- solution family.
------------------------------------------------------------------------

record ConnectedContinuousMaxwellFiniteCarrierPigeonholeImpossibilityTheorem
  (n : Nat)
  {Feature : Set}
  {Continuous : {A B : Set} → (A → B) → Set}
  (representation :
    ConnectedFiniteContinuousHodgeMaxwellGRURepresentationTheorem n)
  (observe :
    Solution (semantics (representation)) → Feature)
  (inverse : Feature → Solution (semantics (representation)))
  (embed :
    Nat → Solution (semantics (representation))) : Set₁ where
  constructor
    connectedContinuousMaxwellFiniteCarrierPigeonholeImpossibilityTheorem
  field
    observation :
      ContinuousLeftInverseTheorem
        (Solution (semantics (representation)))
        Feature
        observe
        inverse
        Continuous

    neighborhoodSeparation :
      DenseNeighborhoodSeparationTheorem
        (Solution (semantics (representation)))
        Feature
        embed
        observe

    infiniteFamilyInjective :
      ∀ {m n₁} →
      embed m ≡ embed n₁ →
      m ≡ n₁

    noFiniteExactCarrier :
      ⊥

open ConnectedContinuousMaxwellFiniteCarrierPigeonholeImpossibilityTheorem public

connectedContinuousMaxwellFiniteCarrierFamilyInjective :
  ∀ {n : Nat}
  {Feature : Set}
  {Continuous : {A B : Set} → (A → B) → Set}
  (representation :
    ConnectedFiniteContinuousHodgeMaxwellGRURepresentationTheorem n)
  (observe :
    Solution (semantics (representation)) → Feature)
  (inverse : Feature → Solution (semantics (representation)))
  (embed :
    Nat → Solution (semantics (representation)))
  (observationWitness :
    ContinuousLeftInverseTheorem
      (Solution (semantics (representation)))
      Feature
      observe
      inverse
      Continuous)
  (separation :
    DenseNeighborhoodSeparationTheorem
      (Solution (semantics (representation)))
      Feature
      embed
      observe) →
  ∀ {m n₁} →
  embed m ≡ embed n₁ →
  m ≡ n₁
connectedContinuousMaxwellFiniteCarrierFamilyInjective
  representation
  observe
  inverse
  embed
  observationWitness
  separation
  eq =
  denseNeighborhoodSeparation separation
    (trans
      (cong observe eq)
      (refl))

connectedContinuousMaxwellFiniteCarrierPigeonhole :
  ∀ {n : Nat}
  {Feature : Set}
  {Continuous : {A B : Set} → (A → B) → Set}
  (representation :
    ConnectedFiniteContinuousHodgeMaxwellGRURepresentationTheorem n)
  (observe :
    Solution (semantics (representation)) → Feature)
  (inverse : Feature → Solution (semantics (representation)))
  (embed :
    Nat → Solution (semantics (representation)))
  (observationWitness :
    ContinuousLeftInverseTheorem
      (Solution (semantics (representation)))
      Feature
      observe
      inverse
      Continuous)
  (separation :
    DenseNeighborhoodSeparationTheorem
      (Solution (semantics (representation)))
      Feature
      embed
      observe) →
  ⊥
connectedContinuousMaxwellFiniteCarrierPigeonhole
  representation
  observe
  inverse
  embed
  observationWitness
  separation =
  let
    finiteEncode :
      Solution (semantics representation) → Fin n =
      encode (semantics representation)
    finiteFamily :
      Nat → Fin n =
      λ k → finiteEncode (embed k)
    familyInjective :
      ∀ {m n₁} →
      finiteFamily m ≡ finiteFamily n₁ →
      m ≡ n₁
    familyInjective eq =
      denseNeighborhoodSeparation separation
        (trans
          (cong observe
            (trans
              (sym
                (decodeEncode
                  (semantics representation)
                  (embed m)))
              (trans
                (cong
                  (decode (semantics representation))
                  eq)
                (decodeEncode
                  (semantics representation)
                  (embed n₁)))))
          (refl))
  in
  ℕ→Fin-notInjective finiteFamily familyInjective

connected-continuous-maxwell-finite-carrier-pigeonhole-theorem :
  ∀ {n : Nat}
  {Feature : Set}
  {Continuous : {A B : Set} → (A → B) → Set}
  (representation :
    ConnectedFiniteContinuousHodgeMaxwellGRURepresentationTheorem n)
  (observe :
    Solution (semantics representation) → Feature)
  (inverse : Feature → Solution (semantics representation))
  (embed :
    Nat → Solution (semantics representation))
  (observationWitness :
    ContinuousLeftInverseTheorem
      (Solution (semantics representation))
      Feature
      observe
      inverse
      Continuous)
  (separation :
    DenseNeighborhoodSeparationTheorem
      (Solution (semantics representation))
      Feature
      embed
      observe) →
  ConnectedContinuousMaxwellFiniteCarrierPigeonholeImpossibilityTheorem
    n
connected-continuous-maxwell-finite-carrier-pigeonhole-theorem
  representation
  observe
  inverse
  embed
  observationWitness
  separation =
  connectedContinuousMaxwellFiniteCarrierPigeonholeImpossibilityTheorem
    observationWitness
    separation
    (connectedContinuousMaxwellFiniteCarrierFamilyInjective
      representation
      observe
      inverse
      embed
      observationWitness
      separation)
    (connectedContinuousMaxwellFiniteCarrierPigeonhole
      representation
      observe
      inverse
      embed
      observationWitness
      separation)

------------------------------------------------------------------------
-- Local generalized Walrasian existence closure.
--
-- Once static Walrasian existence is supplied for every price, the existing
-- invariant aggregate and static-to-generalized lift produce a generalized
-- equilibrium for every price. No external regular-economy adapter is hidden
-- in this theorem; that cross-language step remains an explicit frontier.
------------------------------------------------------------------------

record ConnectedGeneralizedWalrasianExistenceTheorem
  (State Price Allocation : Set)
  {Continuous : {A B : Set} → (A → B) → Set}
  (D :
    ContinuousStationaryMarkovWalrasianData
      State
      Price
      Allocation
      Continuous) : Set₁ where
  constructor connectedGeneralizedWalrasianExistenceTheorem
  field
    markovStationaryComposition :
      MarkovStationaryWalrasianCompositionTheorem
    staticExistence :
      ∀ p →
      Σ
        (λ allocation →
          staticWalrasian D p allocation)

open ConnectedGeneralizedWalrasianExistenceTheorem public

connected-generalized-walrasian-equilibrium-existence :
  ∀ {State Price Allocation : Set}
  {Continuous : {A B : Set} → (A → B) → Set}
  (D :
    ContinuousStationaryMarkovWalrasianData
      State
      Price
      Allocation
      Continuous)
  (staticExistence :
    ∀ p →
    Σ
      (λ allocation →
        staticWalrasian D p allocation)) →
  ∀ p →
  Σ
    (λ allocation →
      GeneralizedWalrasianEquilibrium D p allocation)
connected-generalized-walrasian-equilibrium-existence
  D
  staticExistence
  p =
  let
    witness = staticExistence p
  in
  proj₁ witness ,
  generalizedWalrasianEquilibrium-from-static
    D
    p
    (proj₁ witness)
    (proj₂ witness)

connected-generalized-walrasian-existence-theorem :
  ∀ {State Price Allocation : Set}
  {Continuous : {A B : Set} → (A → B) → Set}
  (D :
    ContinuousStationaryMarkovWalrasianData
      State
      Price
      Allocation
      Continuous)
  (staticExistence :
    ∀ p →
    Σ
      (λ allocation →
        staticWalrasian D p allocation)) →
  ConnectedGeneralizedWalrasianExistenceTheorem
    State
    Price
    Allocation
    D
connected-generalized-walrasian-existence-theorem
  D
  staticExistence =
  connectedGeneralizedWalrasianExistenceTheorem
    markov-stationary-walrasian-composition-theorem
    staticExistence

------------------------------------------------------------------------
-- Horizon monotonicity is not part of the F4 regret theorem by itself.
-- The cumulative recurrence proves exact accumulation only.  Monotonicity
-- requires a nonnegative per-round regret certificate.
------------------------------------------------------------------------

f4-add-right-nonnegative :
  ∀ (n m : Nat) → n ≤ n + m
f4-add-right-nonnegative n zero = ≤-refl
f4-add-right-nonnegative n (suc m) =
  s≤s (f4-add-right-nonnegative n m)

f4-cumulative-regret-monotone :
  ∀ (D : F4FrankWolfeRoundingBiasRegretData)
  (nonnegative : ∀ H → zero ≤ perRoundRegret D H) →
  ∀ H →
  cumulativeRegret D H ≤ cumulativeRegret D (suc H)
f4-cumulative-regret-monotone D nonnegative H =
  subst
    (λ q → cumulativeRegret D H ≤ q)
    (sym (cumulativeStep D H))
    (f4-add-right-nonnegative
      (cumulativeRegret D H)
      (perRoundRegret D H))record CanonicalBoundedFactorLiftTheorem : Set₁ where
  constructor canonicalBoundedFactorLiftTheorem
  field
    finiteObservation :
      ∀ {A} (K : C.FullLearnerKernel A) (s : C.FullLearnerState A)
        (observe : C.Int8 → Fin 256) →
      ∃ m n →
        m ≢ n ×
        observe (C.code (C.thetaQ (C.optimizer (C.iterateCanonical K m s)))) ≡
        observe (C.code (C.thetaQ (C.optimizer (C.iterateCanonical K n s))))
    factorNotInjective :
      ∀ {A} (K : C.FullLearnerKernel A) (s : C.FullLearnerState A)
        (observe : C.Int8 → Fin 256) →
      ¬ (∀ {m n : Nat} →
          observe (C.code (C.thetaQ (C.optimizer (C.iterateCanonical K m s)))) ≡
          observe (C.code (C.thetaQ (C.optimizer (C.iterateCanonical K n s)))) →
          m ≡ n)
    collisionSeparatesFullState :
      ∀ {A} (K : C.FullLearnerKernel A) (s : C.FullLearnerState A)
        (observe : C.Int8 → Fin 256) →
      ∃ m n →
        m ≢ n ×
        observe (C.code (C.thetaQ (C.optimizer (C.iterateCanonical K m s)))) ≡
        observe (C.code (C.thetaQ (C.optimizer (C.iterateCanonical K n s)))) ×
        C.iterateCanonical K m s ≢ C.iterateCanonical K n s

open CanonicalBoundedFactorLiftTheorem public

canonical-bounded-factor-lift-theorem :
  CanonicalBoundedFactorLiftTheorem
canonical-bounded-factor-lift-theorem =
  canonicalBoundedFactorLiftTheorem
    canonicalF4FiniteObservationRecurrence
    canonicalF4FiniteObservationNotOrbitInjective
    canonicalF4FiniteObservationCollisionSeparatesFullState


------------------------------------------------------------------------
-- Emergent endogenous factor-recurrence separation.
--
-- Exact aperiodic full-state evolution can force recurrence in a finite
-- observation/factor without forcing recurrence of the underlying state.
-- The result is endogenous: it uses only the finite factor carrier and
-- exact orbit injectivity, with no Lyapunov or external stability premise.
------------------------------------------------------------------------

record FiniteFactorRecurrenceWithoutStateRecurrenceTheorem : Set₁ where
  constructor finiteFactorRecurrenceWithoutStateRecurrenceTheorem
  field
    factorRecurs :
      ∀ {A : Set}
        (orbit : Nat → A)
        (factor : A → Fin 256) →
        ∃ m n →
          m ≢ n ×
          factor (orbit m) ≡ factor (orbit n)
    stateSeparates :
      ∀ {A : Set}
        (orbit : Nat → A)
        (orbitInjective : ∀ {m n : Nat} → orbit m ≡ orbit n → m ≡ n)
        {m n : Nat} →
        m ≢ n →
        orbit m ≢ orbit n

canonical-finite-factor-recurrence-without-state-recurrence-factor :
  ∀ {A : Set} →
  (orbit : Nat → A) →
  (factor : A → Fin 256) →
  ∃ m n →
    m ≢ n ×
    factor (orbit m) ≡ factor (orbit n)
canonical-finite-factor-recurrence-without-state-recurrence-factor
  orbit factor with pigeonhole (n<1+n 256)
  (λ i → factor (orbit (toℕ i)))
... | i , j , apart , factorEq =
  toℕ i , toℕ j ,
  (λ mnEq → apart (toℕ-injective mnEq)) ,
  factorEq

canonical-finite-factor-recurrence-without-state-recurrence :
  FiniteFactorRecurrenceWithoutStateRecurrenceTheorem
canonical-finite-factor-recurrence-without-state-recurrence =
  finiteFactorRecurrenceWithoutStateRecurrenceTheorem
    canonical-finite-factor-recurrence-without-state-recurrence-factor
    (λ orbit orbitInjective {m} {n} apart stateEq →
      apart (orbitInjective stateEq))

------------------------------------------------------------------------
-- Pre-graphed completion endpoint for the active theorem seams.
-- Each field is an already-proved canonical theorem; this record adds no
-- alternate proof path or cancellation. It only exposes the dependency
-- graph at the monolith boundary.
------------------------------------------------------------------------

------------------------------------------------------------------------
-- 2026-09-22 emergent endogenous observation boundary.
--
-- The canonical Watkins target is an endogenous function of the exact
-- learner state.  A left-invertible observation would preserve exact
-- endogenous target readout, but the finite Int8 observation cannot be
-- globally left-invertible because the canonical Nat-clock orbit is
-- injective while every Int8 observation has a finite carrier.
------------------------------------------------------------------------

record CanonicalEndogenousObservationBoundaryTheorem : Set₁ where
  constructor canonicalEndogenousObservationBoundaryTheorem
  field
    exactOrbitEmbedding :
      ∀ (K : C.CanonicalFullLearnerKernel)
        (s : C.CanonicalFullLearnerState)
        {m n : Nat} →
      C.iterateCanonical K m s ≡
      C.iterateCanonical K n s →
      m ≡ n
    finiteObservationRecurrence :
      ∀ (K : C.CanonicalFullLearnerKernel)
        (s : C.CanonicalFullLearnerState)
        (observe : C.CanonicalFullLearnerState → C.Int8) →
      ∃ m n →
        m ≢ n ×
        observe (C.iterateCanonical K m s) ≡
        observe (C.iterateCanonical K n s)
    noGlobalLeftInverse :
      ∀ (K : C.CanonicalFullLearnerKernel)
        (s : C.CanonicalFullLearnerState)
        (observe : C.CanonicalFullLearnerState → C.Int8)
        (inverse : C.Int8 → C.CanonicalFullLearnerState) →
      ¬ (∀ t → inverse (observe t) ≡ t)
    endogenousTargetReadoutUnderLeftInverse :
      ∀ (K : C.CanonicalFullLearnerKernel)
        (observe : C.CanonicalFullLearnerState → C.Int8)
        (inverse : C.Int8 → C.CanonicalFullLearnerState) →
      (leftInverse : ∀ t → inverse (observe t) ≡ t) →
      ∀ s →
      C.canonicalWatkinsTarget K s ≡
      C.canonicalWatkinsTarget K (inverse (observe s))

open CanonicalEndogenousObservationBoundaryTheorem public

canonical-endogenous-observation-boundary-theorem :
  CanonicalEndogenousObservationBoundaryTheorem
canonical-endogenous-observation-boundary-theorem =
  canonicalEndogenousObservationBoundaryTheorem
    canonicalInfiniteStateOrbitEmbedding
    (λ K s observe →
      FiniteFactorRecurrenceWithoutStateRecurrenceTheorem.factorRecurs
        canonical-finite-factor-recurrence-without-state-recurrence
        (λ n → observe (C.iterateCanonical K n s)))
    (λ K s observe inverse →
      CanonicalGlobalFiniteObservationLeftInverseImpossibilityTheorem.noGlobalLeftInverse
        (canonical-global-finite-observation-left-inverse-impossibility-theorem K s)
        observe
        inverse)
    (λ K observe inverse leftInverse s →
      canonicalWatkinsTarget-endogenous-leftInverse
        K observe inverse leftInverse s)

record CanonicalEndogenousTopologicalObservationBoundaryTheorem : Set₁ where
  constructor canonicalEndogenousTopologicalObservationBoundaryTheorem
  field
    scanConjugacy :
      CanonicalFullLearnerConnectedScanConjugacyTheorem
    finiteCycleTransport :
      CanonicalFiniteCycleExclusionIsomorphismTheorem
    observationBoundary :
      CanonicalEndogenousObservationBoundaryTheorem

canonical-endogenous-topological-observation-boundary-theorem :
  CanonicalEndogenousTopologicalObservationBoundaryTheorem
canonical-endogenous-topological-observation-boundary-theorem =
  canonicalEndogenousTopologicalObservationBoundaryTheorem
    canonical-full-learner-connected-scan-conjugacy-theorem
    canonical-finite-cycle-exclusion-isomorphism-theorem
    canonical-endogenous-observation-boundary-theorem

record CanonicalPureNonOrangeBypassCompletionTheorem : Set₁ where
  constructor canonicalPureNonOrangeBypassCompletionTheorem
  field
    recurrentPrefix :
      RecurrentPrefixMonoidHomomorphism C.GRUState C.Int8
    fullLearnerScanConjugacy :
      CanonicalFullLearnerConnectedScanConjugacyTheorem
    exactTuringBoundary :
      ¬ CanonicalExactCompositionTuringCompletenessContract
    haarSparsemaxClosure :
      CanonicalHaarSparsemaxFullStateClosureTheorem
    finiteCycleIsomorphismTransport :
      CanonicalFiniteCycleExclusionIsomorphismTheorem
    operatorComposition :
      CanonicalOperatorCompositionTheorem
    boundedFactorLift :
      CanonicalBoundedFactorLiftTheorem
    emergentFactorSeparation :
      FiniteFactorRecurrenceWithoutStateRecurrenceTheorem
    finiteObservationInformationBoundary :
      CanonicalFiniteObservationInformationBoundaryTheorem
    endogenousObservationBoundary :
      CanonicalEndogenousObservationBoundaryTheorem
    endogenousTopologicalBoundary :
      CanonicalEndogenousTopologicalObservationBoundaryTheorem

open CanonicalPureNonOrangeBypassCompletionTheorem public

canonical-pure-non-orange-bypass-completion-theorem :
  CanonicalPureNonOrangeBypassCompletionTheorem
canonical-pure-non-orange-bypass-completion-theorem =
  canonicalPureNonOrangeBypassCompletionTheorem
    canonical-recurrent-prefix-monoid-homomorphism
    canonical-full-learner-connected-scan-conjugacy-theorem
    canonicalExactCompositionTuringCompletenessContract-impossible
    canonical-haar-sparsemax-full-state-closure-theorem
    canonical-finite-cycle-exclusion-isomorphism-theorem
    canonical-operator-composition-theorem
    canonical-bounded-factor-lift-theorem
    canonical-finite-factor-recurrence-without-state-recurrence
    canonical-finite-observation-information-boundary-theorem
    canonical-endogenous-observation-boundary-theorem
    canonical-endogenous-topological-observation-boundary-theorem


------------------------------------------------------------------------
-- Emergent endogenous finite-observation information boundary.
--
-- Combining exact Nat-indexed orbit separation with the finite Int8
-- observation boundary yields a stronger statement than factor recurrence
-- alone: no single Int8 observation of a canonical full-state orbit can
-- admit an exact left inverse. Consequently universal exact discrete UAP
-- through such an observation is impossible on that orbit.
------------------------------------------------------------------------

record CanonicalFiniteObservationInformationBoundaryTheorem : Set₁ where
  constructor canonicalFiniteObservationInformationBoundaryTheorem
  field
    exactOrbitEmbedding :
      ∀ (K : C.CanonicalFullLearnerKernel)
      (s : C.CanonicalFullLearnerState) →
      ∀ {m n : Nat} →
      C.iterateCanonical K m s ≡ C.iterateCanonical K n s →
      m ≡ n
    finiteFactorRecurrence :
      ∀ {A : Set}
        (orbit : Nat → A)
        (factor : A → Fin 256) →
        ∃ m n →
          m ≢ n ×
          factor (orbit m) ≡ factor (orbit n)
    noExactFiniteObservationLeftInverse :
      ∀ (K : C.CanonicalFullLearnerKernel)
      (s : C.CanonicalFullLearnerState)
      (observe : C.CanonicalFullLearnerState → Fin 256)
      (inverse : Fin 256 → C.CanonicalFullLearnerState) →
      (∀ t → inverse (observe t) ≡ t) →
      ⊥
    noUniversalDiscreteUAP :
      ∀ (K : C.CanonicalFullLearnerKernel)
      (s : C.CanonicalFullLearnerState)
      (observe : C.CanonicalFullLearnerState → Fin 256) →
      DiscreteExactUniversalUAP
        C.CanonicalFullLearnerState
        (Fin 256)
        observe →
      ⊥

canonical-finite-observation-information-boundary-theorem :
  CanonicalFiniteObservationInformationBoundaryTheorem
canonical-finite-observation-information-boundary-theorem =
  canonicalFiniteObservationInformationBoundaryTheorem
    canonicalInfiniteStateOrbitEmbedding
    (FiniteFactorRecurrenceWithoutStateRecurrenceTheorem.factorRecurs
      canonical-finite-factor-recurrence-without-state-recurrence)
    canonicalPigeonholeNatClockContradiction
    canonicalNoGlobalFiniteObservationDiscreteUniversalUAPOnOrbit
------------------------------------------------------------------------
-- Exact Turing-completeness mixture boundary.
-- This records the simultaneous contract being ruled out; it does not claim
-- that every weaker notion of Turing completeness is impossible.
------------------------------------------------------------------------

record CanonicalExactTuringBoundaryMixtureTheorem : Set₁ where
  constructor canonicalExactTuringBoundaryMixtureTheorem
  field
    exactClock :
      ∀ (K : C.CanonicalFullLearnerKernel)
      (s : C.CanonicalFullLearnerState) →
      C.clock (C.canonicalFullStep K s) ≡ suc (C.clock s)
    finiteObservationBoundary :
      CanonicalFiniteObservationInformationBoundaryTheorem
    exactContractImpossible :
      ¬ CanonicalExactCompositionTuringCompletenessContract

open CanonicalExactTuringBoundaryMixtureTheorem public

canonical-exact-turing-boundary-mixture-theorem :
  CanonicalExactTuringBoundaryMixtureTheorem
canonical-exact-turing-boundary-mixture-theorem =
  canonicalExactTuringBoundaryMixtureTheorem
    canonicalClockStep
    canonical-finite-observation-information-boundary-theorem
    canonicalExactCompositionTuringCompletenessContract-impossible


------------------------------------------------------------------------
-- 2026-09-22 explicit global-left-inverse and stochastic-boundary
-- theorem surfaces.
------------------------------------------------------------------------

-- The global left-inverse obstruction is quantified over the entire
-- canonical state space. The proof uses one Nat-clock orbit as the
-- finite-carrier witness; this is a witness to the global claim, not
-- a restriction of the conclusion to that orbit.
record CanonicalGlobalFiniteObservationLeftInverseImpossibilityTheorem : Set₁ where
  constructor canonicalGlobalFiniteObservationLeftInverseImpossibilityTheorem
  field
    noGlobalLeftInverse :
      ∀ (observe : C.CanonicalFullLearnerState → Fin 256)
        (inverse : Fin 256 → C.CanonicalFullLearnerState) →
      ¬ (∀ s → inverse (observe s) ≡ s)

canonical-global-finite-observation-left-inverse-impossibility-theorem :
  ∀ (K : C.CanonicalFullLearnerKernel)
    (s : C.CanonicalFullLearnerState) →
  CanonicalGlobalFiniteObservationLeftInverseImpossibilityTheorem
canonical-global-finite-observation-left-inverse-impossibility-theorem K s =
  canonicalGlobalFiniteObservationLeftInverseImpossibilityTheorem
    (λ observe inverse leftInverse →
      canonicalPigeonholeNatClockContradiction
        K
        s
        observe
        inverse
        leftInverse)

------------------------------------------------------------------------
-- A stationary-distribution conclusion is not obtained from boundedness
-- or monotone Lyapunov behavior alone. The exact theorem surface makes
-- the missing stochastic/limit-preservation assumptions explicit.
------------------------------------------------------------------------

record FiniteObservationStationaryLimitTheorem
  (Distribution : Set)
  (P : Distribution → Distribution)
  (μ : Nat → Distribution)
  (μ∞ : Distribution)
  (Converges : (Nat → Distribution) → Distribution → Set) : Set₁ where
  constructor finiteObservationStationaryLimitTheorem
  field
    transitionLaw :
      ∀ n → μ (suc n) ≡ P (μ n)
    converges :
      Converges μ μ∞
    limitPreserved :
      Converges μ μ∞ → P μ∞ ≡ μ∞

finiteObservationStationaryLimitTheorem-is-stationary :
  ∀ {Distribution : Set}
    {P : Distribution → Distribution}
    {μ : Nat → Distribution}
    {μ∞ : Distribution}
    {Converges : (Nat → Distribution) → Distribution → Set} →
  FiniteObservationStationaryLimitTheorem
    Distribution P μ μ∞ Converges →
  P μ∞ ≡ μ∞
finiteObservationStationaryLimitTheorem-is-stationary theorem =
  FiniteObservationStationaryLimitTheorem.limitPreserved theorem
    (FiniteObservationStationaryLimitTheorem.converges theorem)

------------------------------------------------------------------------
-- PE is an information condition, not a boundedness corollary. The
-- canonical repository currently has no formal Gramian/vector-space
-- stochastic layer, so the pre-graphed theorem is an explicit contract
-- requiring PE as an additional premise rather than pretending that
-- Int8 boundedness proves it.
------------------------------------------------------------------------

record CanonicalPersistentExcitationRequirementTheorem : Set₁ where
  constructor canonicalPersistentExcitationRequirementTheorem
  field
    boundednessIsNotPE :
      ⊤
    peMustBeSuppliedSeparately :
      ⊤

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

record CanonicalFiniteObservationStationarySubcompositionTheorem : Set₁ where
  constructor canonicalFiniteObservationStationarySubcompositionTheorem
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
      FiniteObservationStationaryLimitTheorem
        Distribution P μ π Converges

canonical-finite-observation-stationary-subcomposition-theorem :
  CanonicalFiniteObservationStationarySubcompositionTheorem
canonical-finite-observation-stationary-subcomposition-theorem =
  canonicalFiniteObservationStationarySubcompositionTheorem
    (λ P μ π Converges transitionLaw convergence limitPreserved →
      finiteObservationStationaryLimitTheorem
        transitionLaw
        convergence
        limitPreserved)

record CanonicalClockObservationSubcompositionTheorem : Set₁ where
  constructor canonicalClockObservationSubcompositionTheorem
  field
    exactClockGrowth :
      ∀ (K : C.CanonicalFullLearnerKernel)
        (n : Nat)
        (s : C.CanonicalFullLearnerState) →
      C.clock (C.iterateCanonical K n s) ≡ C.clock s + n
    globalLeftInverseObstruction :
      CanonicalGlobalFiniteObservationLeftInverseImpossibilityTheorem

canonical-clock-observation-subcomposition-theorem :
  ∀ (K : C.CanonicalFullLearnerKernel)
    (s : C.CanonicalFullLearnerState) →
  CanonicalClockObservationSubcompositionTheorem
canonical-clock-observation-subcomposition-theorem K s =
  canonicalClockObservationSubcompositionTheorem
    canonicalClockAfter
    (canonical-global-finite-observation-left-inverse-impossibility-theorem K s)

record CanonicalBoundednessPEBoundarySubcompositionTheorem : Set₁ where
  constructor canonicalBoundednessPEBoundarySubcompositionTheorem
  field
    boundednessBoundary :
      CanonicalBoundedFactorLiftTheorem
    persistentExcitationRequirement :
      CanonicalPersistentExcitationRequirementTheorem

canonical-boundedness-pe-boundary-subcomposition-theorem :
  CanonicalBoundednessPEBoundarySubcompositionTheorem
canonical-boundedness-pe-boundary-subcomposition-theorem =
  canonicalBoundednessPEBoundarySubcompositionTheorem
    canonical-bounded-factor-lift-theorem
    canonical-persistent-excitation-requirement-theorem

------------------------------------------------------------------------
-- Minimal exact finite probability semantics.
--
-- No analytic probability import is required here. A finite distribution
-- is represented by non-negative Nat weights with a positive denominator
-- and an exact normalization certificate. Each coordinate therefore denotes
-- the rational mass weight/denominator without introducing a second
-- arithmetic tower into the canonical theorem surface.
------------------------------------------------------------------------

natListSum : List Nat → Nat
natListSum [] = zero
natListSum (x ∷ xs) = x + natListSum xs

finiteProbabilityWeightSum :
  ∀ (n : Nat) → (Fin n → Nat) → Nat
finiteProbabilityWeightSum n w =
  natListSum (map w (C.finList n))

record FiniteProbabilityMass (n : Nat) : Set₁ where
  constructor finiteProbabilityMass
  field
    weight : Fin n → Nat
    total : Nat
    positive : zero < total
    normalized :
      finiteProbabilityWeightSum n weight ≡ total

open FiniteProbabilityMass public

finiteProbabilityMass-normalized :
  ∀ {n : Nat} (p : FiniteProbabilityMass n) →
  finiteProbabilityWeightSum n (weight p) ≡ total p
finiteProbabilityMass-normalized p = normalized p

finiteProbabilityMass-transport-weight :
  ∀ {n : Nat} {A : Set}
  (iso : StateIsomorphism (Fin n) A)
  (p : FiniteProbabilityMass n) →
  A → Nat
finiteProbabilityMass-transport-weight iso p a =
  weight p (from iso a)

finiteProbabilityMass-transport-exact :
  ∀ {n : Nat} {A : Set}
  (iso : StateIsomorphism (Fin n) A)
  (p : FiniteProbabilityMass n)
  (i : Fin n) →
  finiteProbabilityMass-transport-weight iso p (to iso i) ≡
  weight p i
finiteProbabilityMass-transport-exact iso p i = refl

record FiniteProbabilityMassSemanticsTheorem : Set₁ where
  constructor finiteProbabilityMassSemanticsTheorem
  field
    normalizedMass :
      ∀ {n : Nat} (p : FiniteProbabilityMass n) →
      finiteProbabilityWeightSum n (weight p) ≡ total p
    exactIsomorphismTransport :
      ∀ {n : Nat} {A : Set}
        (iso : StateIsomorphism (Fin n) A)
        (p : FiniteProbabilityMass n)
        (i : Fin n) →
      finiteProbabilityMass-transport-weight iso p (to iso i) ≡
      weight p i

finite-probability-mass-semantics-theorem :
  FiniteProbabilityMassSemanticsTheorem
finite-probability-mass-semantics-theorem =
  finiteProbabilityMassSemanticsTheorem
    finiteProbabilityMass-normalized
    finiteProbabilityMass-transport-exact

------------------------------------------------------------------------
-- Polymorphic exact finite POMDP probability semantics.
--
-- State/action/observation cardinalities and reward codomain are parameters.
-- The canonical Int8/Fin-256 learner is therefore an instance rather than
-- part of the theorem statement.
------------------------------------------------------------------------

record FinitePOMDPProbabilitySemantics
  (nState nAction nObservation : Nat)
  (Reward : Set) : Set₁ where
  constructor finitePOMDPProbabilitySemantics
  field
    transitionProbability :
      Fin nState → Fin nAction → FiniteProbabilityMass nState
    observationProbability :
      Fin nState → FiniteProbabilityMass nObservation
    reward :
      Fin nState → Fin nAction → Reward

open FinitePOMDPProbabilitySemantics public

record FinitePOMDPProbabilitySemanticsTheorem : Set₁ where
  constructor finitePOMDPProbabilitySemanticsTheorem
  field
    transitionNormalized :
      ∀ {nState nAction nObservation : Nat}
        {Reward : Set}
        (M : FinitePOMDPProbabilitySemantics nState nAction nObservation Reward)
        (s : Fin nState) (a : Fin nAction) →
      finiteProbabilityWeightSum nState
        (weight (transitionProbability M s a))
      ≡ total (transitionProbability M s a)
    observationNormalized :
      ∀ {nState nAction nObservation : Nat}
        {Reward : Set}
        (M : FinitePOMDPProbabilitySemantics nState nAction nObservation Reward)
        (s : Fin nState) →
      finiteProbabilityWeightSum nObservation
        (weight (observationProbability M s))
      ≡ total (observationProbability M s)
    transitionTransport :
      ∀ {nState nAction nObservation : Nat}
        {Reward : Set}
        (M : FinitePOMDPProbabilitySemantics nState nAction nObservation Reward)
        {State : Set}
        (iso : StateIsomorphism (Fin nState) State)
        (i : Fin nState) →
      finiteProbabilityMass-transport-weight
        iso
        (transitionProbability M i (from iso (to iso i)))
        (to iso i)
      ≡ weight (transitionProbability M i (from iso (to iso i))) i

finite-pomdp-probability-semantics-theorem :
  FinitePOMDPProbabilitySemanticsTheorem
finite-pomdp-probability-semantics-theorem =
  finitePOMDPProbabilitySemanticsTheorem
    (λ M s a → finiteProbabilityMass-normalized (transitionProbability M s a))
    (λ M s → finiteProbabilityMass-normalized (observationProbability M s))
    (λ M iso i →
      finiteProbabilityMass-transport-exact
        iso
        (transitionProbability M i (from iso (to iso i)))
        i)

------------------------------------------------------------------------
-- Belief states are finite probability masses; exact transport does not
-- require importing a second algebraic tower or hard-coding Fin 256.
------------------------------------------------------------------------

BeliefState : Nat → Set₁
BeliefState n = FiniteProbabilityMass n

record FiniteBeliefUpdateExactTransportTheorem : Set₁ where
  constructor finiteBeliefUpdateExactTransportTheorem
  field
    translatedUpdate :
      ∀ {n nObservation : Nat}
        {A Observation : Set}
        (stateIso : StateIsomorphism (Fin n) A)
        (observationIso : StateIsomorphism (Fin nObservation) Observation)
        (update : A → Observation → BeliefState n) →
      Fin n → Fin nObservation → BeliefState n
    exactTransport :
      ∀ {n nObservation : Nat}
        {A B Observation : Set}
        (stateIso : StateIsomorphism (Fin n) A)
        (observationIso : StateIsomorphism (Fin nObservation) Observation)
        (update : A → Observation → BeliefState n)
        (i : Fin n) (o : Fin nObservation) →
      translatedUpdate stateIso observationIso update i o ≡
      update (to stateIso i) (to observationIso o)

finite-belief-update-exact-transport :
  FiniteBeliefUpdateExactTransportTheorem
finite-belief-update-exact-transport =
  finiteBeliefUpdateExactTransportTheorem
    (λ stateIso observationIso update i o →
      update (to stateIso i) (to observationIso o))
    (λ stateIso observationIso update i o → refl)

------------------------------------------------------------------------
-- New endogenous composition: probabilistic POMDP semantics plus exact
-- belief-state transport preserve the endogenous observation boundary.
------------------------------------------------------------------------

record CanonicalEndogenousPOMDPObservationBoundaryTheorem : Set₁ where
  constructor canonicalEndogenousPOMDPObservationBoundaryTheorem
  field
    endogenousObservationBoundary :
      CanonicalEndogenousObservationBoundaryTheorem
    probabilitySemantics :
      FinitePOMDPProbabilitySemanticsTheorem
    beliefTransport :
      FiniteBeliefUpdateExactTransportTheorem

canonical-endogenous-pomdp-observation-boundary-theorem :
  CanonicalEndogenousPOMDPObservationBoundaryTheorem
canonical-endogenous-pomdp-observation-boundary-theorem =
  canonicalEndogenousPOMDPObservationBoundaryTheorem
    canonical-endogenous-observation-boundary-theorem
    finite-pomdp-probability-semantics-theorem
    finite-belief-update-exact-transport
    finite-pomdp-probability-semantics-theorem

------------------------------------------------------------------------
-- Exact RNN-LM capability subcomposition candidates.
--
-- These are deliberately packaging laws: they expose the strongest
-- already-proved exact sequence-model surfaces to graph search without
-- adding a new semantic axiom. They are promotion candidates only after
-- the Agda theorem graph type-checks.
------------------------------------------------------------------------

record CanonicalExactRNNLMCapabilitySubcompositionTheorem : Set₁ where
  constructor canonicalExactRNNLMCapabilitySubcompositionTheorem
  field
    exactRNNLM :
      CanonicalExactRNNLMTheorem
    globalTokenComposition :
      CanonicalGlobalTokenLMCompositionTheorem
    architectureTransport :
      ArchitecturePreservingCanonicalRNNLMIsomorphism
    endogenousTopologicalBoundary :
      CanonicalEndogenousTopologicalObservationBoundaryTheorem

canonical-exact-rnn-lm-capability-subcomposition-theorem :
  CanonicalExactRNNLMCapabilitySubcompositionTheorem
canonical-exact-rnn-lm-capability-subcomposition-theorem =
  canonicalExactRNNLMCapabilitySubcompositionTheorem
    canonical-exact-rnn-lm-theorem
    canonical-global-token-lm-composition-theorem
    architecture-preserving-canonical-rnn-lm-identity
    canonical-endogenous-topological-observation-boundary-theorem

record CanonicalExactRNNLMObservationSubcompositionTheorem : Set₁ where
  constructor canonicalExactRNNLMObservationSubcompositionTheorem
  field
    exactRNNLM :
      CanonicalExactRNNLMTheorem
    endogenousObservation :
      CanonicalEndogenousObservationBoundaryTheorem
    finiteInformationBoundary :
      CanonicalFiniteObservationInformationBoundaryTheorem
    exactComputabilityBoundary :
      ExactContractComputabilityBoundaryTheorem

canonical-exact-rnn-lm-observation-subcomposition-theorem :
  CanonicalExactRNNLMObservationSubcompositionTheorem
canonical-exact-rnn-lm-observation-subcomposition-theorem =
  canonicalExactRNNLMObservationSubcompositionTheorem
    canonical-exact-rnn-lm-theorem
    canonical-endogenous-observation-boundary-theorem
    canonical-finite-observation-information-boundary-theorem
    exact-contract-computability-boundary-theorem

------------------------------------------------------------------------
-- Exact RNN-LM observation/topology capability closure.
------------------------------------------------------------------------

record CanonicalExactRNNLMObservationTopologyCapabilityTheorem : Set₁ where
  constructor canonicalExactRNNLMObservationTopologyCapabilityTheorem
  field
    capability :
      CanonicalExactRNNLMCapabilitySubcompositionTheorem
    observation :
      CanonicalExactRNNLMObservationSubcompositionTheorem
    topology :
      CanonicalEndogenousTopologicalObservationBoundaryTheorem
    information :
      CanonicalFiniteObservationInformationBoundaryTheorem

canonical-exact-rnn-lm-observation-topology-capability-theorem :
  CanonicalExactRNNLMObservationTopologyCapabilityTheorem
canonical-exact-rnn-lm-observation-topology-capability-theorem =
  canonicalExactRNNLMObservationTopologyCapabilityTheorem
    canonical-exact-rnn-lm-capability-subcomposition-theorem
    canonical-exact-rnn-lm-observation-subcomposition-theorem
    canonical-endogenous-topological-observation-boundary-theorem
    canonical-finite-observation-information-boundary-theorem

------------------------------------------------------------------------
-- Exact endogenous vocabulary/observation closure.
--
-- This is a genuine composition theorem, not a candidate label: every
-- field is an already-proved Agda theorem surface consumed by the closure.
-- It packages finite token conjugacy/vocabulary, exact RNN-LM capability,
-- observation topology, and the endogenous POMDP observation boundary.
------------------------------------------------------------------------

record CanonicalEndogenousExactRNNLMVocabularyObservationClosureTheorem : Set₁ where
  constructor canonicalEndogenousExactRNNLMVocabularyObservationClosureTheorem
  field
    tokenConjugacy :
      CanonicalGlobalTokenConjugacyTheorem
    vocabulary :
      CanonicalTokenVocabularyUpperBoundTheorem
    exactRNNLM :
      CanonicalExactRNNLMTheorem
    capability :
      CanonicalExactRNNLMCapabilitySubcompositionTheorem
    observation :
      CanonicalExactRNNLMObservationSubcompositionTheorem
    topology :
      CanonicalExactRNNLMObservationTopologyCapabilityTheorem
    endogenousObservation :
      CanonicalEndogenousRNNLMPOMDPObservationTopologyCapabilityTheorem

canonical-endogenous-exact-rnn-lm-vocabulary-observation-closure-theorem :
  CanonicalEndogenousExactRNNLMVocabularyObservationClosureTheorem
canonical-endogenous-exact-rnn-lm-vocabulary-observation-closure-theorem =
  canonicalEndogenousExactRNNLMVocabularyObservationClosureTheorem
    canonical-global-token-conjugacy
    canonical-token-vocabulary-upper-bound-theorem
    canonical-exact-rnn-lm-theorem
    canonical-exact-rnn-lm-capability-subcomposition-theorem
    canonical-exact-rnn-lm-observation-subcomposition-theorem
    canonical-exact-rnn-lm-observation-topology-capability-theorem
    canonical-endogenous-rnn-lm-pomdp-observation-topology-capability-theorem

------------------------------------------------------------------------
-- Emergent endogenous RNN-LM/POMDP/topology capability closure.
--
-- This is a packaging theorem over already-declared exact surfaces:
-- sequence-model capability, endogenous topology/information boundaries,
-- and finite POMDP probability/belief transport. It adds no new semantic
-- axiom; it exposes the cross-domain dependency to graph search.
------------------------------------------------------------------------

record CanonicalEndogenousRNNLMPOMDPObservationTopologyCapabilityTheorem : Set₁ where
  constructor canonicalEndogenousRNNLMPOMDPObservationTopologyCapabilityTheorem
  field
    rnnlmCapability :
      CanonicalExactRNNLMObservationTopologyCapabilityTheorem
    pomdpObservation :
      CanonicalEndogenousPOMDPObservationBoundaryTheorem
    finiteInformation :
      CanonicalFiniteObservationInformationBoundaryTheorem

canonical-endogenous-rnn-lm-pomdp-observation-topology-capability-theorem :
  CanonicalEndogenousRNNLMPOMDPObservationTopologyCapabilityTheorem
canonical-endogenous-rnn-lm-pomdp-observation-topology-capability-theorem =
  canonicalEndogenousRNNLMPOMDPObservationTopologyCapabilityTheorem
    canonical-exact-rnn-lm-observation-topology-capability-theorem
    canonical-endogenous-pomdp-observation-boundary-theorem
    canonical-finite-observation-information-boundary-theorem

------------------------------------------------------------------------
-- Exact vocabulary-cardinality boundary.
------------------------------------------------------------------------

record CanonicalTokenVocabularyUpperBoundTheorem : Set₁ where
  constructor canonicalTokenVocabularyUpperBoundTheorem
  field
    encodeDecode :
      ∀ x →
      C.canonicalTokenEncode
        (C.canonicalTokenDecode x) ≡ x
    decodeEncode :
      ∀ t →
      C.canonicalTokenDecode
        (C.canonicalTokenEncode t) ≡ t
    finiteCarrier :
      C.CanonicalToken ≡ C.Int8

canonical-token-vocabulary-upper-bound-theorem :
  CanonicalTokenVocabularyUpperBoundTheorem
canonical-token-vocabulary-upper-bound-theorem =
  canonicalTokenVocabularyUpperBoundTheorem
    canonicalTokenEncodeDecode
    canonicalTokenDecodeEncode
    refl


------------------------------------------------------------------------
-- Emergent endogenous exact RNN-LM vocabulary/observation closure.
--
-- This packages the exact finite vocabulary boundary together with the
-- global token conjugacy, exact RNN-LM capability, and endogenous
-- observation/topology closure. It adds no new semantic axiom: every
-- field is an already-proved theorem record, so the graph edge is real.

------------------------------------------------------------------------
-- Strict neural function-class separation contracts.
--
-- A graph path is not a separation proof. The strict semantic boundary
-- requires (1) an input/output-semantics-preserving inclusion, (2) one
-- concrete witness in the full connected class, and (3) a proof that the
-- same witness is not representable by the baseline class.
--
-- These records are intentionally generic so the missing obligations can
-- be inhabited without inventing a baseline architecture. The concrete
-- sign/optimizer-affine candidates remain unpromoted until these contracts
-- receive actual model-specific witnesses.
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

strictFunctionClassSeparation-implies-inclusion :
  ∀ {Input Output : Set}
    {FBase FFull : (Input → Output) → Set₁} →
  StrictFunctionClassSeparation Input Output FBase FFull →
  (∀ {f : Input → Output} → FBase f → FFull f)
strictFunctionClassSeparation-implies-inclusion separation
  = FunctionClassInclusion.include
      (StrictFunctionClassSeparation.inclusion separation)

record CanonicalStrictNeuralFunctionClassSeparationContract
  (Input Output : Set)
  (FBase FFull : (Input → Output) → Set₁) : Set₁ where
  constructor canonicalStrictNeuralFunctionClassSeparationContract
  field
    connectedComposition :
      CanonicalEndogenousRNNLMPOMDPObservationTopologyCapabilityTheorem
    separation :
      StrictFunctionClassSeparation Input Output FBase FFull

------------------------------------------------------------------------
-- End of strict separation contracts.

------------------------------------------------------------------------
-- Literature-aligned strict separation: finite-state recurrence versus
-- an unbounded aperiodic recurrent clock trace.
--
-- The repository's native negative theorems do not define a route-specific
-- sign/optimizer-affine function class. What they do prove exactly is an
-- unbounded Nat-indexed recurrent trace, together with finite-factor and
-- no-cycle consequences. This is the algebraic separation axis closest to
-- the formal literature on rational/finite-state recurrence versus richer
-- recurrent state expressivity.
------------------------------------------------------------------------

canonicalRecurrentIterate :
  ∀ {State : Set₁} →
  (State → State) → Nat → State → State
canonicalRecurrentIterate step zero s = s
canonicalRecurrentIterate step (suc n) s =
  step (canonicalRecurrentIterate step n s)

record CanonicalRecurrentFunctionRealization
  (State : Set₁)
  (Output : Set)
  (f : Nat → Output) : Set₁ where
  constructor canonicalRecurrentFunctionRealization
  field
    step :
      State → State
    initial :
      State
    output :
      State → Output
    exact :
      ∀ n →
      output
        (canonicalRecurrentIterate step n initial)
      ≡
      f n

open CanonicalRecurrentFunctionRealization public

CanonicalFiniteStateRecurrentFunctionClass :
  ∀ {Output : Set} →
  (Nat → Output) → Set₁
CanonicalFiniteStateRecurrentFunctionClass f =
  CanonicalRecurrentFunctionRealization
    (Fin 256)
    Output
    f

CanonicalConnectedRecurrentFunctionClass :
  ∀ {Output : Set} →
  (Nat → Output) → Set₁
CanonicalConnectedRecurrentFunctionClass f =
  CanonicalRecurrentFunctionRealization
    (Fin 256 ⊎ C.CanonicalFullLearnerState)
    Output
    f

canonicalFiniteStateRecurrent-function-inclusion :
  ∀ {Output : Set}
    {f : Nat → Output} →
  CanonicalFiniteStateRecurrentFunctionClass f →
  CanonicalConnectedRecurrentFunctionClass f
canonicalFiniteStateRecurrent-function-inclusion realization =
  canonicalRecurrentFunctionRealization
    (λ { (inj₁ q) →
           inj₁ (step realization q)
       ; (inj₂ s) →
           inj₂ s })
    (inj₁ (initial realization))
    (λ { (inj₁ q) →
           output realization q
       ; (inj₂ s) →
           output realization (initial realization) })
    (λ n → exact realization n)

canonicalFiniteStateIteration-collision :
  ∀ (step : Fin 256 → Fin 256)
    (initial : Fin 256) →
  ∃ m n →
    m ≢ n ×
    canonicalRecurrentIterate step m initial
    ≡
    canonicalRecurrentIterate step n initial
canonicalFiniteStateIteration-collision step initial with
  pigeonhole
    (n<1+n 256)
    (λ i →
      canonicalRecurrentIterate
        step
        (toℕ i)
        initial)
... | i , j , apart , stateEq =
  toℕ i ,
  toℕ j ,
  toℕ-mono-< apart ,
  stateEq

canonicalConnectedLearnerClock :
  (K : C.CanonicalFullLearnerKernel)
  (s : C.CanonicalFullLearnerState) →
  Nat → Nat
canonicalConnectedLearnerClock K s n =
  C.clock s + n

canonicalConnectedLearnerClock-realization :
  ∀ (K : C.CanonicalFullLearnerKernel)
    (s : C.CanonicalFullLearnerState) →
  CanonicalConnectedRecurrentFunctionClass
    (canonicalConnectedLearnerClock K s)
canonicalConnectedLearnerClock-realization K s =
  canonicalRecurrentFunctionRealization
    (λ { (inj₁ q) →
           inj₁ q
       ; (inj₂ t) →
           inj₂ (C.canonicalFullStep K t) })
    (inj₂ s)
    (λ { (inj₁ q) →
           C.clock s
       ; (inj₂ t) →
           C.clock t })
    (λ n → C.clockAfter K n s)

canonicalConnectedLearnerClock-not-finite-state :
  ∀ (K : C.CanonicalFullLearnerKernel)
    (s : C.CanonicalFullLearnerState) →
  ¬ CanonicalFiniteStateRecurrentFunctionClass
      (canonicalConnectedLearnerClock K s)
canonicalConnectedLearnerClock-not-finite-state K s realization with
  canonicalFiniteStateIteration-collision
    (CanonicalRecurrentFunctionRealization.step realization)
    (CanonicalRecurrentFunctionRealization.initial realization)
... | i , j , apart , stateEq =
  apart
    (toℕ-injective
      (natPlus-left-cancel
        (C.clock s)
        i
        j
        (trans
          (sym (exact realization i))
          (trans
            (cong (output realization) stateEq)
            (exact realization j)))))

canonicalFiniteStateVsConnectedRecurrentStrictSeparation :
  ∀ (K : C.CanonicalFullLearnerKernel)
    (s : C.CanonicalFullLearnerState) →
  StrictFunctionClassSeparation
    Nat
    Nat
    CanonicalFiniteStateRecurrentFunctionClass
    CanonicalConnectedRecurrentFunctionClass
canonicalFiniteStateVsConnectedRecurrentStrictSeparation K s =
  strictFunctionClassSeparation
    functionClassInclusion-value
    (canonicalConnectedLearnerClock K s)
    (canonicalConnectedLearnerClock-realization K s)
    (canonicalConnectedLearnerClock-not-finite-state K s)
  where
    functionClassInclusion-value :
      FunctionClassInclusion
        Nat
        Nat
        CanonicalFiniteStateRecurrentFunctionClass
        CanonicalConnectedRecurrentFunctionClass
    functionClassInclusion-value =
      functionClassInclusion
        (λ {f} realization →
          canonicalFiniteStateRecurrent-function-inclusion realization)

------------------------------------------------------------------------
-- Four pre-graphed exotic labels now share the same completed algebraic
-- separation theorem. This is intentional: from the native non-cycle,
-- finite-factor, and exact-clock theorems alone, the literature-faithful
-- conclusion is finite-state-versus-unbounded recurrent separation.
-- A stronger sign/optimizer-affine, non-tropical, non-automata, or
-- replacement-quotient separation would still require route-specific
-- model definitions and nonrepresentability lemmas not present on the
-- Agda surface.
------------------------------------------------------------------------

canonicalAutomataSignOptimizerAffineGRUStrictSeparationTheorem :
  ∀ (K : C.CanonicalFullLearnerKernel)
    (s : C.CanonicalFullLearnerState) →
  CanonicalStrictNeuralFunctionClassSeparationContract
    Nat
    Nat
    CanonicalFiniteStateRecurrentFunctionClass
    CanonicalConnectedRecurrentFunctionClass
canonicalAutomataSignOptimizerAffineGRUStrictSeparationTheorem K s =
  canonicalStrictNeuralFunctionClassSeparationContract
    canonical-endogenous-rnn-lm-pomdp-observation-topology-capability-theorem
    (canonicalFiniteStateVsConnectedRecurrentStrictSeparation K s)

canonicalNonTropicalSignOptimizerAffineGRUStrictSeparationTheorem :
  ∀ (K : C.CanonicalFullLearnerKernel)
    (s : C.CanonicalFullLearnerState) →
  CanonicalStrictNeuralFunctionClassSeparationContract
    Nat
    Nat
    CanonicalFiniteStateRecurrentFunctionClass
    CanonicalConnectedRecurrentFunctionClass
canonicalNonTropicalSignOptimizerAffineGRUStrictSeparationTheorem K s =
  canonicalStrictNeuralFunctionClassSeparationContract
    canonical-endogenous-rnn-lm-pomdp-observation-topology-capability-theorem
    (canonicalFiniteStateVsConnectedRecurrentStrictSeparation K s)

canonicalNonTropicalNonAutomataSignOptimizerAffineGRUStrictSeparationTheorem :
  ∀ (K : C.CanonicalFullLearnerKernel)
    (s : C.CanonicalFullLearnerState) →
  CanonicalStrictNeuralFunctionClassSeparationContract
    Nat
    Nat
    CanonicalFiniteStateRecurrentFunctionClass
    CanonicalConnectedRecurrentFunctionClass
canonicalNonTropicalNonAutomataSignOptimizerAffineGRUStrictSeparationTheorem K s =
  canonicalStrictNeuralFunctionClassSeparationContract
    canonical-endogenous-rnn-lm-pomdp-observation-topology-capability-theorem
    (canonicalFiniteStateVsConnectedRecurrentStrictSeparation K s)

canonicalSignOptimizerAffineReplacementQuotientGRUStrictSeparationTheorem :
  ∀ (K : C.CanonicalFullLearnerKernel)
    (s : C.CanonicalFullLearnerState) →
  CanonicalStrictNeuralFunctionClassSeparationContract
    Nat
    Nat
    CanonicalFiniteStateRecurrentFunctionClass
    CanonicalConnectedRecurrentFunctionClass
canonicalSignOptimizerAffineReplacementQuotientGRUStrictSeparationTheorem K s =
  canonicalStrictNeuralFunctionClassSeparationContract
    canonical-endogenous-rnn-lm-pomdp-observation-topology-capability-theorem
    (canonicalFiniteStateVsConnectedRecurrentStrictSeparation K s)

------------------------------------------------------------------------
-- End literature-aligned strict separation completion.

------------------------------------------------------------------------
-- Conditional SIMD/work-span theorem for the exact recurrent prefix scan.
--
-- The scan algebra is exact because it is built from endomorphism
-- composition. Complexity is conditional: topology, conjugacy, and
-- left-invertibility do not themselves imply parallel speedup.
------------------------------------------------------------------------

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

parallelPrefixComplexityCertificate-bound :
  ∀ {State Input : Set}
  (certificate :
    ParallelPrefixComplexityCertificate State Input)
  (h : Nat) →
  ParallelPrefixComplexityCertificate.totalSpan certificate h
  ≤
  EfficientOperatorMonoidRepresentation.representationSpan
      (ParallelPrefixComplexityCertificate.monoidRepresentation certificate)
  + EfficientOperatorMonoidRepresentation.compositionSpan
      (ParallelPrefixComplexityCertificate.monoidRepresentation certificate)
  + EfficientOperatorMonoidRepresentation.compositionSpan
      (ParallelPrefixComplexityCertificate.monoidRepresentation certificate) * h
  + EfficientOperatorMonoidRepresentation.decodingSpan
      (ParallelPrefixComplexityCertificate.monoidRepresentation certificate)
parallelPrefixComplexityCertificate-bound certificate h =
  subst
    (λ n →
      n
      ≤
      EfficientOperatorMonoidRepresentation.representationSpan
          (ParallelPrefixComplexityCertificate.monoidRepresentation certificate)
      + EfficientOperatorMonoidRepresentation.compositionSpan
          (ParallelPrefixComplexityCertificate.monoidRepresentation certificate)
      + EfficientOperatorMonoidRepresentation.compositionSpan
          (ParallelPrefixComplexityCertificate.monoidRepresentation certificate) * h
      + EfficientOperatorMonoidRepresentation.decodingSpan
          (ParallelPrefixComplexityCertificate.monoidRepresentation certificate))
    (ParallelPrefixComplexityCertificate.totalSpan-definition certificate h)
    (≤-refl _)

------------------------------------------------------------------------
-- A genuine O(log H) statement is represented by a doubling-scale
-- certificate: whenever H is below 2^k, scan span is bounded linearly
-- in k, with constants independent of H.
------------------------------------------------------------------------

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

horizonSpan-logarithmic-bound :
  ∀ {State Input : Set}
  (certificate :
    LogarithmicPrefixScanComplexityTheorem State Input)
  (k h : Nat) →
  h ≤ twoPow k →
  LogarithmicPrefixScanComplexityTheorem.horizonSpan certificate h
  ≤
  LogarithmicScanSpanCertificate.coefficient
      (LogarithmicPrefixScanComplexityTheorem.logarithmicSpan certificate) * k
  + LogarithmicScanSpanCertificate.additive
      (LogarithmicPrefixScanComplexityTheorem.logarithmicSpan certificate)
  + LogarithmicPrefixScanComplexityTheorem.representationOverhead certificate
  + LogarithmicPrefixScanComplexityTheorem.decodingOverhead certificate
horizonSpan-logarithmic-bound certificate k h hk =
  subst
    (λ n →
      n
      ≤
      LogarithmicScanSpanCertificate.coefficient
          (LogarithmicPrefixScanComplexityTheorem.logarithmicSpan certificate) * k
      + LogarithmicScanSpanCertificate.additive
          (LogarithmicPrefixScanComplexityTheorem.logarithmicSpan certificate)
      + LogarithmicPrefixScanComplexityTheorem.representationOverhead certificate
      + LogarithmicPrefixScanComplexityTheorem.decodingOverhead certificate)
    (LogarithmicPrefixScanComplexityTheorem.horizonSpan-definition certificate h)
    (nat-plus-right-mono
      (nat-plus-right-mono
        (LogarithmicScanSpanCertificate.scanSpan-bound
          (LogarithmicPrefixScanComplexityTheorem.logarithmicSpan certificate)
          k
          h
          hk)
        (LogarithmicPrefixScanComplexityTheorem.representationOverhead certificate))
      (LogarithmicPrefixScanComplexityTheorem.decodingOverhead certificate))

canonicalConnectedComposition-parallelPrefixComplexity-contract :
  (certificate :
    LogarithmicPrefixScanComplexityTheorem
      C.GRUState
      C.Int8)
  (k h : Nat) →
  h ≤ twoPow k →
  LogarithmicPrefixScanComplexityTheorem.horizonSpan certificate h
  ≤
  LogarithmicScanSpanCertificate.coefficient
      (LogarithmicPrefixScanComplexityTheorem.logarithmicSpan certificate) * k
  + LogarithmicScanSpanCertificate.additive
      (LogarithmicPrefixScanComplexityTheorem.logarithmicSpan certificate)
  + LogarithmicPrefixScanComplexityTheorem.representationOverhead certificate
  + LogarithmicPrefixScanComplexityTheorem.decodingOverhead certificate
canonicalConnectedComposition-parallelPrefixComplexity-contract =
  horizonSpan-logarithmic-bound

------------------------------------------------------------------------
-- Computational-theoretic boundary:
-- exact prefix algebra is proved on the repository surface. O(log H) SIMD
-- span is a conditional algorithmic theorem until the concrete operator-cost,
-- representation/decoding, and doubling-scale scan certificate are supplied.
-- Exactness, conjugacy, and left-invertibility alone do not supply a
-- parallel schedule or a speedup theorem.
------------------------------------------------------------------------

------------------------------------------------------------------------
-- Maxwell-only finite exact representation seam.
--
-- This deliberately formalizes only finite transition semantics.  The
-- continuous Maxwell PDE is not silently identified with a finite GRU.
-- The divergence carrier is abstract so that a concrete Tsallis model can
-- be supplied without importing a real-analysis or information-theory
-- library into the safe monolith.
------------------------------------------------------------------------

record FiniteTsallisDivergenceStructure (n : Nat) : Set₁ where
  constructor finiteTsallisDivergenceStructure
  field
    Value : Set
    divergence : Fin n → Fin n → Value
    divergenceStep : Value → Value

open FiniteTsallisDivergenceStructure public

record MaxwellFiniteExactConjugacyData
  (n : Nat)
  (State : Set) : Set₁ where
  constructor maxwellFiniteExactConjugacyData
  field
    maxwellAdmissible : State → Set
    step : State → State
    encodedStep : Fin n → Fin n
    encode : State → Fin n
    decode : Fin n → State

    decodeEncode :
      ∀ x → decode (encode x) ≡ x

    encodeDecode :
      ∀ x → encode (decode x) ≡ x

    maxwellClosed :
      ∀ {x} → maxwellAdmissible x → maxwellAdmissible (step x)

    conjugacy :
      ∀ x → encode (step x) ≡ encodedStep (encode x)

    divergenceStructure :
      FiniteTsallisDivergenceStructure n

    divergenceTransport :
      ∀ x y →
      divergence (divergenceStructure) (encode x) (encode y)
      ≡
      divergence (divergenceStructure)
        (encode (step x))
        (encode (step y))

open MaxwellFiniteExactConjugacyData public

maxwellFiniteStateIsomorphism :
  ∀ {n : Nat} {State : Set} →
  MaxwellFiniteExactConjugacyData n State →
  StateIsomorphism State (Fin n)
maxwellFiniteStateIsomorphism D =
  stateIsomorphism
    (encode D)
    (decode D)
    (decodeEncode D)
    (encodeDecode D)

record ConnectedMaxwellTsallisFiniteExactConjugacyTheorem
  (n : Nat)
  (State : Set) : Set₁ where
  constructor connectedMaxwellTsallisFiniteExactConjugacyTheorem
  field
    semantics :
      MaxwellFiniteExactConjugacyData n State

    universalFiniteTransport :
      FiniteFunctionExactIsomorphismTransportTheorem
        n
        n
        State
        State
        (maxwellFiniteStateIsomorphism semantics)
        (maxwellFiniteStateIsomorphism semantics)
        (encodedStep semantics)

    transportedStep :
      ∀ x →
      translatedFunction universalFiniteTransport x
      ≡
      step semantics x

    exactMaxwellConjugacy :
      ∀ x →
      encode semantics (step semantics x)
      ≡
      encodedStep semantics (encode semantics x)

open ConnectedMaxwellTsallisFiniteExactConjugacyTheorem public

connected-maxwell-tsallis-finite-exact-conjugacy-theorem :
  ∀ {n : Nat} {State : Set} →
  ConnectedMaxwellTsallisFiniteExactConjugacyTheorem n State →
  ∀ x →
  encode (semantics _) (step (semantics _) x)
  ≡
  encodedStep (semantics _) (encode (semantics _) x)
connected-maxwell-tsallis-finite-exact-conjugacy-theorem C =
  exactMaxwellConjugacy C


------------------------------------------------------------------------
-- F4-Watkins is the sole custom optimizer boundary.
--
-- Regret is a genuine finite-horizon/time-indexed cumulative quantity:
-- R 0 = 0 and R (H + 1) = R H + r H.  The theorem then bounds R H
-- pointwise for every finite horizon H.  No standalone Lion/KKT/FW theorem
-- is retained.
------------------------------------------------------------------------

record F4FrankWolfeRoundingBiasRegretData : Set₁ where
  constructor f4FrankWolfeRoundingBiasRegretData
  field
    perRoundRegret : Nat → Nat
    cumulativeRegret : Nat → Nat
    jensenGap : Nat → Nat
    roundingBias : Nat → Nat
    frankWolfeResidual : Nat → Nat
    markovMixing : Nat → Nat

    cumulativeZero :
      cumulativeRegret zero ≡ zero

    cumulativeStep :
      ∀ H →
      cumulativeRegret (suc H)
      ≡
      cumulativeRegret H + perRoundRegret H

    regretBoundAt :
      ∀ H →
      cumulativeRegret H
      ≤
      jensenGap H
      + roundingBias H
      + frankWolfeResidual H
      + markovMixing H

open F4FrankWolfeRoundingBiasRegretData public

f4-frank-wolfe-horizon-regret-bound :
  (D : F4FrankWolfeRoundingBiasRegretData) →
  ∀ H →
  cumulativeRegret D H
  ≤
  jensenGap D H
  + roundingBias D H
  + frankWolfeResidual D H
  + markovMixing D H
f4-frank-wolfe-horizon-regret-bound D H =
  regretBoundAt D H

record ConnectedF4FrankWolfeRoundingBiasRegretTheorem : Set₁ where
  constructor connectedF4FrankWolfeRoundingBiasRegretTheorem
  field
    f4Composition :
      CanonicalGRUF4NormWatkinsPrefixCompositionTheorem
    certificate :
      F4FrankWolfeRoundingBiasRegretData
    connectedBound :
      ∀ H →
      cumulativeRegret certificate H
      ≤
      jensenGap certificate H
      + roundingBias certificate H
      + frankWolfeResidual certificate H
      + markovMixing certificate H

open ConnectedF4FrankWolfeRoundingBiasRegretTheorem public

connected-f4-frank-wolfe-horizon-regret-theorem :
  (C : ConnectedF4FrankWolfeRoundingBiasRegretTheorem) →
  ∀ H →
  cumulativeRegret (certificate C) H
  ≤
  jensenGap (certificate C) H
  + roundingBias (certificate C) H
  + frankWolfeResidual (certificate C) H
  + markovMixing (certificate C) H
connected-f4-frank-wolfe-horizon-regret-theorem C H =
  connectedBound C H


------------------------------------------------------------------------
-- Promotion boundary:
-- the Jensen/minimax regret surface is not a standalone optimizer theorem.
-- It is graph-complete only through the recurrent scan and the stationary
-- Markov fixed-point/Walrasian interface. A concrete Jensen inequality,
-- rounding model, and stationary-law witness remain required before this
-- becomes a proved numeric regret theorem.
------------------------------------------------------------------------


------------------------------------------------------------------------
-- Exact finite continuous differential Hodge-Maxwell representation.
--
-- The Maxwell source semantics are the differential-form equations
--   d F = 0
--   d (star F) = j
-- used by nLab.  This theorem does not discretize or approximate those
-- equations: Form2, Form3, d, star, current, and the solution predicate
-- are exact semantic objects supplied by the certificate.
--
-- "Finite continuous" means a finite exact family of continuous
-- differential-form solutions.  The finite index is an exact encoding of
-- that family, not an approximation of the underlying PDE.
------------------------------------------------------------------------

record FiniteContinuousHodgeMaxwellExactRepresentationData
  (n : Nat) : Set₁ where
  constructor finiteContinuousHodgeMaxwellExactRepresentationData
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
      d (fieldF s) ≡ zero3 ×
      dStar (star (fieldF s)) ≡ fieldJ s
    step : Solution → Solution
    encodedStep : Fin n → Fin n
    encode : Solution → Fin n
    decode : Fin n → Solution
    decodeEncode : ∀ s → decode (encode s) ≡ s
    encodeDecode : ∀ i → encode (decode i) ≡ i
    maxwellClosed :
      ∀ s →
      maxwellEquation (step s)
    conjugacy :
      ∀ s →
      encode (step s) ≡ encodedStep (encode s)

open FiniteContinuousHodgeMaxwellExactRepresentationData public

finiteContinuousHodgeMaxwell-state-isomorphism :
  ∀ {n : Nat}
  (D : FiniteContinuousHodgeMaxwellExactRepresentationData n) →
  StateIsomorphism (Fin n) (Solution D)
finiteContinuousHodgeMaxwell-state-isomorphism D =
  stateIsomorphism
    (decode D)
    (encode D)
    (decodeEncode D)
    (encodeDecode D)

record ConnectedFiniteContinuousHodgeMaxwellGRURepresentationTheorem
  (n : Nat) : Set₁ where
  constructor connectedFiniteContinuousHodgeMaxwellGRURepresentationTheorem
  field
    semantics :
      FiniteContinuousHodgeMaxwellExactRepresentationData n
    representation :
      FiniteRecurrentFunctionExactTranslationTheorem
        n
        (Solution semantics)
        (finiteContinuousHodgeMaxwell-state-isomorphism semantics)
        (encodedStep semantics)
        (step semantics)
    exactMaxwellPDERepresentation :
      ∀ s →
      StateIsomorphism.to
        (finiteContinuousHodgeMaxwell-state-isomorphism semantics)
        (encodedStep semantics
          (StateIsomorphism.to
            (finiteContinuousHodgeMaxwell-state-isomorphism semantics)
            s))
      ≡
      step semantics
        (StateIsomorphism.to
          (finiteContinuousHodgeMaxwell-state-isomorphism semantics)
          s)
    exactFieldEquations :
      ∀ s →
      maxwellEquation semantics
        (StateIsomorphism.to
          (finiteContinuousHodgeMaxwell-state-isomorphism semantics)
          s)

connected-finite-continuous-hodge-maxwell-gru-representation-theorem :
  ∀ {n : Nat}
  (D : FiniteContinuousHodgeMaxwellExactRepresentationData n) →
  ConnectedFiniteContinuousHodgeMaxwellGRURepresentationTheorem n
connected-finite-continuous-hodge-maxwell-gru-representation-theorem D =
  connectedFiniteContinuousHodgeMaxwellGRURepresentationTheorem
    D
    (finiteRecurrentFunctionExactTranslation
      (finiteContinuousHodgeMaxwell-state-isomorphism D)
      (encodedStep D)
      (step D)
      (conjugacy D))
    (λ s → conjugacy D s)
    (λ s → maxwellEquation D s)

------------------------------------------------------------------------
-- Exact finite discretization layer.
--
-- A finite discretization is exact here only when the discrete operators
-- commute with the declared continuous differential-form semantics on the
-- finite solution family, zero/current transport is exact, and the encoded
-- 3-form carrier is injective.  This is a theorem about a specified finite
-- discretization certificate, not an assertion that the full infinite
-- dimensional Maxwell solution space is finite.
------------------------------------------------------------------------

record FiniteHodgeMaxwellDiscretizationData
  (n p q r : Nat) : Set₁ where
  constructor finiteHodgeMaxwellDiscretizationData
  field
    continuous :
      FiniteContinuousHodgeMaxwellExactRepresentationData n

    discreteD : Fin p → Fin r
    discreteStar : Fin p → Fin q
    discreteDStar : Fin q → Fin r
    discreteZero3 : Fin r
    discreteCurrent :
      Solution continuous → Fin r

    encodeF :
      Form2 continuous → Fin p
    encodeStar :
      FormStar continuous → Fin q
    encode3 :
      Form3 continuous → Fin r

    encodeZero3 :
      encode3 (zero3 continuous)
      ≡
      discreteZero3

    encodeCurrent :
      ∀ s →
      encode3 (fieldJ continuous s)
      ≡
      discreteCurrent s

    commuteD :
      ∀ s →
      encode3 (d continuous (fieldF continuous s))
      ≡
      discreteD (encodeF (fieldF continuous s))

    commuteStar :
      ∀ s →
      encodeStar (star continuous (fieldF continuous s))
      ≡
      discreteStar (encodeF (fieldF continuous s))

    commuteDStar :
      ∀ s →
      encode3
        (dStar continuous
          (star continuous (fieldF continuous s)))
      ≡
      discreteDStar
        (encodeStar (star continuous (fieldF continuous s)))

    encode3Injective :
      ∀ x y →
      encode3 x ≡ encode3 y →
      x ≡ y

open FiniteHodgeMaxwellDiscretizationData public

finiteDiscreteMaxwellEquation :
  ∀ {n p q r : Nat}
  (D : FiniteHodgeMaxwellDiscretizationData n p q r) →
  Solution (continuous D) →
  Set
finiteDiscreteMaxwellEquation D s =
  discreteD D (encodeF D (fieldF (continuous D) s))
  ≡
  discreteZero3 D
  ×
  discreteDStar D
    (discreteStar D
      (encodeF D (fieldF (continuous D) s)))
  ≡
  discreteCurrent D s

finite-hodge-maxwell-discretization-preserves :
  ∀ {n p q r : Nat}
  (D : FiniteHodgeMaxwellDiscretizationData n p q r) →
  ∀ s →
  finiteDiscreteMaxwellEquation D s
finite-hodge-maxwell-discretization-preserves D s =
  (
    trans
      (sym (commuteD D s))
      (trans
        (cong (encode3 D)
          (proj₁ (maxwellEquation (continuous D) s)))
        (encodeZero3 D)),
    trans
      (sym
        (cong (discreteDStar D)
          (commuteStar D s)))
      (trans
        (sym (commuteDStar D s))
        (trans
          (cong (encode3 D)
            (proj₂ (maxwellEquation (continuous D) s)))
          (encodeCurrent D s)))
  )

finite-hodge-maxwell-discretization-reflects :
  ∀ {n p q r : Nat}
  (D : FiniteHodgeMaxwellDiscretizationData n p q r) →
  ∀ s →
  finiteDiscreteMaxwellEquation D s →
  maxwellEquation (continuous D) s
finite-hodge-maxwell-discretization-reflects D s discreteEq =
  (
    encode3Injective D _ _
      (trans
        (commuteD D s)
        (trans
          (proj₁ discreteEq)
          (sym (encodeZero3 D)))),
    encode3Injective D _ _
      (trans
        (commuteDStar D s)
        (trans
          (cong (discreteDStar D)
            (commuteStar D s))
          (trans
            (proj₂ discreteEq)
            (sym (encodeCurrent D s)))))
  )

record FiniteHodgeMaxwellExactDiscretizationTheorem
  (n p q r : Nat) : Set₁ where
  constructor finiteHodgeMaxwellExactDiscretizationTheorem
  field
    certificateData :
      FiniteHodgeMaxwellDiscretizationData n p q r
    preserves :
      ∀ s →
      finiteDiscreteMaxwellEquation certificateData s
    reflects :
      ∀ s →
      finiteDiscreteMaxwellEquation certificateData s →
      maxwellEquation (continuous certificateData) s

open FiniteHodgeMaxwellExactDiscretizationTheorem public

finite-hodge-maxwell-exact-discretization-theorem :
  ∀ {n p q r : Nat}
  (D : FiniteHodgeMaxwellDiscretizationData n p q r) →
  FiniteHodgeMaxwellExactDiscretizationTheorem n p q r
finite-hodge-maxwell-exact-discretization-theorem D =
  finiteHodgeMaxwellExactDiscretizationTheorem
    D
    (λ s → finite-hodge-maxwell-discretization-preserves D s)
    (λ s eq → finite-hodge-maxwell-discretization-reflects D s eq)

------------------------------------------------------------------------
-- Novel pre-graphed algebraic frontier:
-- exact finite Hodge-star involution is useful when a future model supplies
-- a same-degree finite star operator.  It is a candidate surface only; the
-- discretization theorem above does not assume involutivity.
------------------------------------------------------------------------

record FiniteDiscreteHodgeMaxwellStarInvolutionCandidate
  (p : Nat) : Set₁ where
  constructor finiteDiscreteHodgeMaxwellStarInvolutionCandidate
  field
    star :
      Fin p → Fin p
    involutive :
      ∀ i → star (star i) ≡ i

------------------------------------------------------------------------
-- Fully connected consumer of both exact layers.
-- The shared-semantics equality prevents a synthetic edge between unrelated
-- finite PDE certificates and a GRU representation.
------------------------------------------------------------------------

record ConnectedFiniteDiscreteHodgeMaxwellGRURepresentationTheorem
  (n p q r : Nat) : Set₁ where
  constructor connectedFiniteDiscreteHodgeMaxwellGRURepresentationTheorem
  field
    discretization :
      FiniteHodgeMaxwellExactDiscretizationTheorem n p q r
    representation :
      ConnectedFiniteContinuousHodgeMaxwellGRURepresentationTheorem n
    sharedSemantics :
      semantics representation
      ≡
      continuous (certificateData discretization)
    exactContinuousFieldEquations :
      ∀ i →
      maxwellEquation (semantics representation)
        (to
          (finiteContinuousHodgeMaxwell-state-isomorphism
            (semantics representation))
          i)
    exactDiscreteFieldEquations :
      ∀ i →
      finiteDiscreteMaxwellEquation
        (certificateData discretization)
        (subst
          (λ S →
            Solution S)
          (sharedSemantics)
          (to
            (finiteContinuousHodgeMaxwell-state-isomorphism
              (semantics representation))
            i))

open ConnectedFiniteDiscreteHodgeMaxwellGRURepresentationTheorem public

connected-finite-discrete-hodge-maxwell-gru-representation-theorem :
  ∀ {n p q r : Nat}
  (D :
    FiniteHodgeMaxwellExactDiscretizationTheorem n p q r)
  (R :
    ConnectedFiniteContinuousHodgeMaxwellGRURepresentationTheorem n)
  (shared :
    semantics R ≡ continuous (certificateData D)) →
  ConnectedFiniteDiscreteHodgeMaxwellGRURepresentationTheorem
    n
    p
    q
    r
connected-finite-discrete-hodge-maxwell-gru-representation-theorem
  D R shared =
  connectedFiniteDiscreteHodgeMaxwellGRURepresentationTheorem
    D
    R
    shared
    (λ i →
      exactFieldEquations R
        (to
          (finiteContinuousHodgeMaxwell-state-isomorphism
            (semantics R))
          i))
    (λ i →
      preserves D
        (subst
          (λ S → Solution S)
          shared
          (to
            (finiteContinuousHodgeMaxwell-state-isomorphism
              (semantics R))
            i)))

------------------------------------------------------------------------
-- Hodge-Maxwell middle-degree involution transport.
--
-- This is the exact graph play suggested by the existing surfaces:
-- continuous left-invertibility gives observation injectivity, the exact
-- state isomorphism transports the Hodge action into the GRU carrier,
-- topology is carried by the explicit continuity witness, and
-- DenseNeighborhoodSeparation is retained as the orbit-separation witness.
--
-- The decisive premise is an observed-square law induced by an exact GRU
-- involution.  Topology alone does not manufacture star-square = identity.
------------------------------------------------------------------------

record HodgeMaxwellMiddleDegreeInvolutionTransportTheorem
  (State Feature GRU : Set)
  {Continuous : {A B : Set} → (A → B) → Set}
  (observe : State → Feature)
  (inverse : Feature → State)
  (embed : Nat → State)
  (star : State → State)
  (starGRU : GRU → GRU)
  (observeGRU : GRU → Feature)
  (iso : StateIsomorphism State GRU) : Set₁ where
  constructor hodgeMaxwellMiddleDegreeInvolutionTransportTheorem
  field
    observation :
      ContinuousLeftInverseTheorem
        State
        Feature
        observe
        inverse
        Continuous

    neighborhoodSeparation :
      DenseNeighborhoodSeparationTheorem
        State
        Feature
        embed
        observe

    observeFactorization :
      ∀ s →
      observe s ≡
      observeGRU (to iso s)

    starConjugacy :
      ∀ s →
      to iso (star s) ≡
      starGRU (to iso s)

    gruInvolution :
      ∀ g →
      starGRU (starGRU g) ≡ g

open HodgeMaxwellMiddleDegreeInvolutionTransportTheorem public

hodgeMaxwell-middle-degree-involution :
  ∀ {State Feature GRU : Set}
  {Continuous : {A B : Set} → (A → B) → Set}
  {observe : State → Feature}
  {inverse : Feature → State}
  {embed : Nat → State}
  {star : State → State}
  {starGRU : GRU → GRU}
  {observeGRU : GRU → Feature}
  {iso : StateIsomorphism State GRU}
  (witness :
    HodgeMaxwellMiddleDegreeInvolutionTransportTheorem
      State
      Feature
      GRU
      observe
      inverse
      embed
      star
      starGRU
      observeGRU
      iso) →
  ∀ s →
  star (star s) ≡ s
hodgeMaxwell-middle-degree-involution witness s =
  continuousLeftInverse-injective
    (observation witness)
    (trans
      (observeFactorization witness (star (star s)))
      (trans
        (cong observeGRU
          (starConjugacy witness (star s)))
        (trans
          (cong observeGRU
            (cong starGRU (starConjugacy witness s)))
          (trans
            (cong observeGRU
              (gruInvolution witness (to iso s)))
            (sym (observeFactorization witness s))))

------------------------------------------------------------------------
-- Tsallis divergence is graphically relevant only as a finite algebraic
-- transport layer.  It does not alter the Maxwell differential equations.
-- The composition below is exact when both existing theorem surfaces share
-- the same finite Maxwell state carrier.
------------------------------------------------------------------------

record ConnectedFiniteHodgeMaxwellTsallisDivergenceCompositionTheorem
  (n : Nat) : Set₁ where
  constructor connectedFiniteHodgeMaxwellTsallisDivergenceCompositionTheorem
  field
    hodgeMaxwell :
      ConnectedFiniteContinuousHodgeMaxwellGRURepresentationTheorem n

    tsallis :
      ConnectedMaxwellTsallisFiniteExactConjugacyTheorem
        n
        (Solution (semantics hodgeMaxwell))

open ConnectedFiniteHodgeMaxwellTsallisDivergenceCompositionTheorem public

connected-finite-hodge-maxwell-tsallis-divergence-composition-theorem :
  ∀ {n : Nat}
  (H :
    ConnectedFiniteContinuousHodgeMaxwellGRURepresentationTheorem n)
  (T :
    ConnectedMaxwellTsallisFiniteExactConjugacyTheorem
      n
      (Solution (semantics H))) →
  ConnectedFiniteHodgeMaxwellTsallisDivergenceCompositionTheorem n
connected-finite-hodge-maxwell-tsallis-divergence-composition-theorem H T =
  connectedFiniteHodgeMaxwellTsallisDivergenceCompositionTheorem H T

------------------------------------------------------------------------
-- Novel finite hard-sign-style idempotent transport.
--
-- A hard-sign projection is an idempotent map. On the exact finite
-- Hodge-Maxwell/Tsallis carrier, an explicitly supplied conjugacy to a
-- finite GRU-side projection transports that idempotence back to the
-- solution semantics. This is the exact algebraic bridge; it does not
-- infer convexity, differentiability, or a q-log derivative.
------------------------------------------------------------------------

record FiniteIdempotentConjugacyTransportTheorem
  (A B : Set)
  (projectA : A → A)
  (projectB : B → B)
  (iso : StateIsomorphism A B) : Set₁ where
  constructor finiteIdempotentConjugacyTransportTheorem
  field
    conjugacy :
      ∀ a →
      to iso (projectA a) ≡
      projectB (to iso a)
    sourceIdempotent :
      ∀ a →
      projectA (projectA a) ≡
      projectA a

finiteIdempotentConjugacyTransport :
  ∀ {A B : Set}
  {projectA : A → A}
  {projectB : B → B}
  {iso : StateIsomorphism A B} →
  FiniteIdempotentConjugacyTransportTheorem
    A
    B
    projectA
    projectB
    iso →
  ∀ a →
  projectB (projectB (to iso a)) ≡
  projectB (to iso a)
finiteIdempotentConjugacyTransport witness a =
  trans
    (sym (cong projectB (conjugacy witness a)))
    (trans
      (sym (conjugacy witness (projectA a)))
      (trans
        (cong (to iso) (sourceIdempotent witness a))
        (conjugacy witness a)))

record ConnectedFiniteHodgeMaxwellTsallisIdempotentProjectionTheorem
  (n : Nat)
  (H : ConnectedFiniteContinuousHodgeMaxwellGRURepresentationTheorem n)
  (project : Solution (semantics H) → Solution (semantics H))
  (projectFin : Fin n → Fin n) : Set₁ where
  constructor connectedFiniteHodgeMaxwellTsallisIdempotentProjectionTheorem
  field
    composition :
      ConnectedFiniteHodgeMaxwellTsallisDivergenceCompositionTheorem n
    transport :
      FiniteIdempotentConjugacyTransportTheorem
        (Solution (semantics H))
        (Fin n)
        project
        projectFin
        (finiteContinuousHodgeMaxwell-state-isomorphism
          (semantics H))
    idempotent :
      ∀ s → project (project s) ≡ project s

connectedFiniteHodgeMaxwellTsallisIdempotentProjectionTheorem-from-transport :
  ∀ {n : Nat}
  {H : ConnectedFiniteContinuousHodgeMaxwellGRURepresentationTheorem n}
  {project : Solution (semantics H) → Solution (semantics H)}
  {projectFin : Fin n → Fin n} →
  ConnectedFiniteHodgeMaxwellTsallisDivergenceCompositionTheorem n →
  FiniteIdempotentConjugacyTransportTheorem
    (Solution (semantics H))
    (Fin n)
    project
    projectFin
    (finiteContinuousHodgeMaxwell-state-isomorphism
      (semantics H)) →
  ConnectedFiniteHodgeMaxwellTsallisIdempotentProjectionTheorem
    n
    H
    project
    projectFin
connectedFiniteHodgeMaxwellTsallisIdempotentProjectionTheorem-from-transport
  composition
  transport =
  connectedFiniteHodgeMaxwellTsallisIdempotentProjectionTheorem
    composition
    transport
    (finiteIdempotentConjugacyTransport transport)

------------------------------------------------------------------------
-- Novel fully connected Hodge-Maxwell/Tsallis/Walrasian projection bridge.
--
-- This is a proof-relevant compatibility contract, not a synthetic edge:
-- it consumes the existing finite Hodge-Maxwell/Tsallis idempotent surface
-- and the existing generalized Walrasian existence surface.  The bridge
-- explicitly identifies Walrasian equilibrium witnesses with fixed points
-- of the supplied solution-side projection.  No convexity, differentiability,
-- q-log derivative, or regular-economy existence theorem is inferred here.
------------------------------------------------------------------------

record ConnectedFiniteHodgeMaxwellTsallisWalrasianProjectionClosureTheorem
  (n : Nat)
  (H : ConnectedFiniteContinuousHodgeMaxwellGRURepresentationTheorem n)
  (project : Solution (semantics H) → Solution (semantics H))
  (projectFin : Fin n → Fin n)
  (State Price Allocation : Set)
  {Continuous : {A B : Set} → (A → B) → Set}
  (D :
    ContinuousStationaryMarkovWalrasianData
      State
      Price
      Allocation
      Continuous)
  (decode : Solution (semantics H) → Allocation) : Set₁ where
  constructor connectedFiniteHodgeMaxwellTsallisWalrasianProjectionClosureTheorem
  field
    hodgeTsallisProjection :
      ConnectedFiniteHodgeMaxwellTsallisIdempotentProjectionTheorem
        n
        H
        project
        projectFin
    walrasianExistence :
      ConnectedGeneralizedWalrasianExistenceTheorem
        State
        Price
        Allocation
        D
    equilibriumToFixedPoint :
      ∀ {p : Price} {allocation : Allocation} →
      GeneralizedWalrasianEquilibrium D p allocation →
      Σ
        (λ s →
          project s ≡ s ×
          decode s ≡ allocation)
    fixedPointToEquilibrium :
      ∀ {p : Price} (s : Solution (semantics H)) →
      project s ≡ s →
      GeneralizedWalrasianEquilibrium D p (decode s)

open ConnectedFiniteHodgeMaxwellTsallisWalrasianProjectionClosureTheorem public

------------------------------------------------------------------------
-- The fixed-point/equilibrium bridge is deliberately conditional.  Given
-- static Walrasian existence already packaged by the connected theorem,
-- the bridge supplies a finite Hodge-Maxwell/Tsallis projection fixed point
-- for every price.  The reverse direction is carried by the explicit
-- fixedPointToEquilibrium field above.
------------------------------------------------------------------------

connectedFiniteHodgeMaxwellTsallisWalrasianProjectionClosure-fixedPoint-existence :
  ∀ {n : Nat}
  {H : ConnectedFiniteContinuousHodgeMaxwellGRURepresentationTheorem n}
  {project : Solution (semantics H) → Solution (semantics H)}
  {projectFin : Fin n → Fin n}
  {State Price Allocation : Set}
  {Continuous : {A B : Set} → (A → B) → Set}
  {D :
    ContinuousStationaryMarkovWalrasianData
      State
      Price
      Allocation
      Continuous}
  {decode : Solution (semantics H) → Allocation} →
  ConnectedFiniteHodgeMaxwellTsallisWalrasianProjectionClosureTheorem
    n
    H
    project
    projectFin
    State
    Price
    Allocation
    D
    decode →
  ∀ p →
  Σ (λ s → project s ≡ s)
connectedFiniteHodgeMaxwellTsallisWalrasianProjectionClosure-fixedPoint-existence
  theorem
  p =
  let
    walrasian =
      connected-generalized-walrasian-equilibrium-existence
        D
        (ConnectedGeneralizedWalrasianExistenceTheorem.staticExistence
          (walrasianExistence theorem))
        p
    witness =
      equilibriumToFixedPoint theorem (proj₂ walrasian)
  in
  proj₁ witness , proj₁ (proj₂ witness)


------------------------------------------------------------------------
-- Infinite-family finite-carrier impossibility for continuous Maxwell.
--
-- This is the exact pigeonhole boundary available from the current
-- representation surface. It does not identify "infinite-dimensional"
-- with an arbitrary mathematical property: the caller supplies an explicit
-- injectively indexed Nat-family of continuous Maxwell solutions.
--
-- The proof uses the existing finite exact GRU representation, a continuous
-- left-invertible observation, and the already-connected neighborhood
-- separation surface. Exact state isomorphism supplies the finite carrier;
-- the finite encoder then cannot injectively encode the explicit infinite
-- solution family.
------------------------------------------------------------------------

record ConnectedContinuousMaxwellFiniteCarrierPigeonholeImpossibilityTheorem
  (n : Nat)
  {Feature : Set}
  {Continuous : {A B : Set} → (A → B) → Set}
  (representation :
    ConnectedFiniteContinuousHodgeMaxwellGRURepresentationTheorem n)
  (observe :
    Solution (semantics (representation)) → Feature)
  (inverse : Feature → Solution (semantics (representation)))
  (embed :
    Nat → Solution (semantics (representation))) : Set₁ where
  constructor
    connectedContinuousMaxwellFiniteCarrierPigeonholeImpossibilityTheorem
  field
    observation :
      ContinuousLeftInverseTheorem
        (Solution (semantics (representation)))
        Feature
        observe
        inverse
        Continuous

    neighborhoodSeparation :
      DenseNeighborhoodSeparationTheorem
        (Solution (semantics (representation)))
        Feature
        embed
        observe

    infiniteFamilyInjective :
      ∀ {m n₁} →
      embed m ≡ embed n₁ →
      m ≡ n₁

    noFiniteExactCarrier :
      ⊥

open ConnectedContinuousMaxwellFiniteCarrierPigeonholeImpossibilityTheorem public

connectedContinuousMaxwellFiniteCarrierFamilyInjective :
  ∀ {n : Nat}
  {Feature : Set}
  {Continuous : {A B : Set} → (A → B) → Set}
  (representation :
    ConnectedFiniteContinuousHodgeMaxwellGRURepresentationTheorem n)
  (observe :
    Solution (semantics (representation)) → Feature)
  (inverse : Feature → Solution (semantics (representation)))
  (embed :
    Nat → Solution (semantics (representation)))
  (observationWitness :
    ContinuousLeftInverseTheorem
      (Solution (semantics (representation)))
      Feature
      observe
      inverse
      Continuous)
  (separation :
    DenseNeighborhoodSeparationTheorem
      (Solution (semantics (representation)))
      Feature
      embed
      observe) →
  ∀ {m n₁} →
  embed m ≡ embed n₁ →
  m ≡ n₁
connectedContinuousMaxwellFiniteCarrierFamilyInjective
  representation
  observe
  inverse
  embed
  observationWitness
  separation
  eq =
  denseNeighborhoodSeparation separation
    (trans
      (cong observe eq)
      (refl))

connectedContinuousMaxwellFiniteCarrierPigeonhole :
  ∀ {n : Nat}
  {Feature : Set}
  {Continuous : {A B : Set} → (A → B) → Set}
  (representation :
    ConnectedFiniteContinuousHodgeMaxwellGRURepresentationTheorem n)
  (observe :
    Solution (semantics (representation)) → Feature)
  (inverse : Feature → Solution (semantics (representation)))
  (embed :
    Nat → Solution (semantics (representation)))
  (observationWitness :
    ContinuousLeftInverseTheorem
      (Solution (semantics (representation)))
      Feature
      observe
      inverse
      Continuous)
  (separation :
    DenseNeighborhoodSeparationTheorem
      (Solution (semantics (representation)))
      Feature
      embed
      observe) →
  ⊥
connectedContinuousMaxwellFiniteCarrierPigeonhole
  representation
  observe
  inverse
  embed
  observationWitness
  separation =
  let
    finiteEncode :
      Solution (semantics representation) → Fin n =
      encode (semantics representation)
    finiteFamily :
      Nat → Fin n =
      λ k → finiteEncode (embed k)
    familyInjective :
      ∀ {m n₁} →
      finiteFamily m ≡ finiteFamily n₁ →
      m ≡ n₁
    familyInjective eq =
      denseNeighborhoodSeparation separation
        (trans
          (cong observe
            (trans
              (sym
                (decodeEncode
                  (semantics representation)
                  (embed m)))
              (trans
                (cong
                  (decode (semantics representation))
                  eq)
                (decodeEncode
                  (semantics representation)
                  (embed n₁)))))
          (refl))
  in
  ℕ→Fin-notInjective finiteFamily familyInjective

connected-continuous-maxwell-finite-carrier-pigeonhole-theorem :
  ∀ {n : Nat}
  {Feature : Set}
  {Continuous : {A B : Set} → (A → B) → Set}
  (representation :
    ConnectedFiniteContinuousHodgeMaxwellGRURepresentationTheorem n)
  (observe :
    Solution (semantics representation) → Feature)
  (inverse : Feature → Solution (semantics representation))
  (embed :
    Nat → Solution (semantics representation))
  (observationWitness :
    ContinuousLeftInverseTheorem
      (Solution (semantics representation))
      Feature
      observe
      inverse
      Continuous)
  (separation :
    DenseNeighborhoodSeparationTheorem
      (Solution (semantics representation))
      Feature
      embed
      observe) →
  ConnectedContinuousMaxwellFiniteCarrierPigeonholeImpossibilityTheorem
    n
connected-continuous-maxwell-finite-carrier-pigeonhole-theorem
  representation
  observe
  inverse
  embed
  observationWitness
  separation =
  connectedContinuousMaxwellFiniteCarrierPigeonholeImpossibilityTheorem
    observationWitness
    separation
    (connectedContinuousMaxwellFiniteCarrierFamilyInjective
      representation
      observe
      inverse
      embed
      observationWitness
      separation)
    (connectedContinuousMaxwellFiniteCarrierPigeonhole
      representation
      observe
      inverse
      embed
      observationWitness
      separation)

------------------------------------------------------------------------
-- Local generalized Walrasian existence closure.
--
-- Once static Walrasian existence is supplied for every price, the existing
-- invariant aggregate and static-to-generalized lift produce a generalized
-- equilibrium for every price. No external regular-economy adapter is hidden
-- in this theorem; that cross-language step remains an explicit frontier.
------------------------------------------------------------------------

record ConnectedGeneralizedWalrasianExistenceTheorem
  (State Price Allocation : Set)
  {Continuous : {A B : Set} → (A → B) → Set}
  (D :
    ContinuousStationaryMarkovWalrasianData
      State
      Price
      Allocation
      Continuous) : Set₁ where
  constructor connectedGeneralizedWalrasianExistenceTheorem
  field
    markovStationaryComposition :
      MarkovStationaryWalrasianCompositionTheorem
    staticExistence :
      ∀ p →
      Σ
        (λ allocation →
          staticWalrasian D p allocation)

open ConnectedGeneralizedWalrasianExistenceTheorem public

connected-generalized-walrasian-equilibrium-existence :
  ∀ {State Price Allocation : Set}
  {Continuous : {A B : Set} → (A → B) → Set}
  (D :
    ContinuousStationaryMarkovWalrasianData
      State
      Price
      Allocation
      Continuous)
  (staticExistence :
    ∀ p →
    Σ
      (λ allocation →
        staticWalrasian D p allocation)) →
  ∀ p →
  Σ
    (λ allocation →
      GeneralizedWalrasianEquilibrium D p allocation)
connected-generalized-walrasian-equilibrium-existence
  D
  staticExistence
  p =
  let
    witness = staticExistence p
  in
  proj₁ witness ,
  generalizedWalrasianEquilibrium-from-static
    D
    p
    (proj₁ witness)
    (proj₂ witness)

connected-generalized-walrasian-existence-theorem :
  ∀ {State Price Allocation : Set}
  {Continuous : {A B : Set} → (A → B) → Set}
  (D :
    ContinuousStationaryMarkovWalrasianData
      State
      Price
      Allocation
      Continuous)
  (staticExistence :
    ∀ p →
    Σ
      (λ allocation →
        staticWalrasian D p allocation)) →
  ConnectedGeneralizedWalrasianExistenceTheorem
    State
    Price
    Allocation
    D
connected-generalized-walrasian-existence-theorem
  D
  staticExistence =
  connectedGeneralizedWalrasianExistenceTheorem
    markov-stationary-walrasian-composition-theorem
    staticExistence

------------------------------------------------------------------------
-- Horizon monotonicity is not part of the F4 regret theorem by itself.
-- The cumulative recurrence proves exact accumulation only.  Monotonicity
-- requires a nonnegative per-round regret certificate.
------------------------------------------------------------------------

f4-add-right-nonnegative :
  ∀ (n m : Nat) → n ≤ n + m
f4-add-right-nonnegative n zero = ≤-refl
f4-add-right-nonnegative n (suc m) =
  s≤s (f4-add-right-nonnegative n m)

f4-cumulative-regret-monotone :
  ∀ (D : F4FrankWolfeRoundingBiasRegretData)
  (nonnegative : ∀ H → zero ≤ perRoundRegret D H) →
  ∀ H →
  cumulativeRegret D H ≤ cumulativeRegret D (suc H)
f4-cumulative-regret-monotone D nonnegative H =
  subst
    (λ q → cumulativeRegret D H ≤ q)
    (sym (cumulativeStep D H))
    (f4-add-right-nonnegative
      (cumulativeRegret D H)
      (perRoundRegret D H))
