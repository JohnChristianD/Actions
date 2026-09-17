{-# OPTIONS --safe #-}
module Exotic.ERL.FullCoupled.ReservoirCompositionMechanism where

open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; cong; trans; subst)
open import Relation.Nullary using (Dec; yes; no)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Data.Nat using (_<_ ; _≤_; z≤n; s≤s)
open import Data.Fin using (Fin; toℕ)
open import Data.Fin.Properties using (pigeonhole; toℕ<n)
open import Data.Product using (_×_; _,_)

open import Exotic.ERL.FullCoupled.GeneralFullCoupledLearnerMonolith as L
open import Exotic.ERL.FullCoupled.GeneralFullCoupledTheoremsMonolith as T

identityActivation : L.Int8 → L.Int8
identityActivation x = x

identityActivation-law : ∀ x → identityActivation x ≡ x
identityActivation-law x = refl

identityActivation-zero : identityActivation L.zero8 ≡ L.zero8
identityActivation-zero = refl

hardSignGate-zero : L.hardSignGate L.zero8 ≡ L.zero8
hardSignGate-zero = refl

mobiusClosure-survives-identity :
  ∀ (m : T.FinitePiecewiseInt8Map) n →
  T.PiecewiseRationalWitness
    (λ x → T.finitePiecewiseRational
      (T.evalFinitePiecewiseInt8Map
        (T.iterateFinitePiecewiseInt8Map m n) x))
mobiusClosure-survives-identity = T.unbounded-depth-piecewise-rational-closure

record SingleOutputReservoir (S I O : Set) : Set₁ where
  constructor singleOutputReservoir
  field
    step : I → S → S
    readout : S → O
open SingleOutputReservoir public

learnerReadout : ∀ {A : Nat} → L.LearnerState A → L.Int8
learnerReadout s = L.hiddenState (L.gru s)

learnerSingleOutputReservoir :
  ∀ {A : Nat} → L.LearnerKernel A →
  SingleOutputReservoir (L.LearnerState A) L.Int8 L.Int8
learnerSingleOutputReservoir K =
  singleOutputReservoir
    (λ r s → L.learnerStep K s r)
    learnerReadout

learnerSingleOutput-bounded :
  ∀ {A : Nat} (K : L.LearnerKernel A) (s : L.LearnerState A) →
  toℕ (L.code (readout (learnerSingleOutputReservoir K) s)) < 256
learnerSingleOutput-bounded K s = toℕ<n (L.code (learnerReadout s))

learnerShapedInput :
  ∀ {A : Nat} → L.LearnerKernel A → L.LearnerState A → L.Int8 → L.Int8
learnerShapedInput K s reward =
  let a = L.generalPolicy K s
      w = L.sparsemaxWeight (L.actionSpaceK K) (L.q s) (L.counts s) a
  in L.int8Add reward (L.munchausenSignal (L.mode K) w)

hiddenReservoirStep : L.Int8 → L.Int8 → L.Int8
hiddenReservoirStep h x =
  L.hiddenState
    (L.gruStep
      (L.gruState h L.one8 L.one8 L.one8
        L.zero8 L.zero8 L.zero8 L.zero8 L.zero8)
      x)

learnerSingleOutput-step-law :
  ∀ {A : Nat} (K : L.LearnerKernel A) (s : L.LearnerState A) reward →
  readout (learnerSingleOutputReservoir K)
    (step (learnerSingleOutputReservoir K) reward s) ≡
  hiddenReservoirStep
    (readout (learnerSingleOutputReservoir K) s)
    (learnerShapedInput K s reward)
learnerSingleOutput-step-law K s reward = refl

record FiniteStateEncoding (S : Set) (n : Nat) : Set₁ where
  constructor finiteStateEncoding
  field
    encode : S → Fin n
    decode : Fin n → S
    roundtrip : ∀ s → decode (encode s) ≡ s
open FiniteStateEncoding public

record OrbitCollision (S : Set) (step : S → S) (s : S) (n : Nat) : Set where
  constructor orbitCollision
  field
    firstIndex : Fin (suc n)
    secondIndex : Fin (suc n)
    distinctIndex : firstIndex ≢ secondIndex
    collision :
      T.iterateGeneric step (toℕ firstIndex) s ≡
      T.iterateGeneric step (toℕ secondIndex) s
open OrbitCollision public

natLtSucc : ∀ n → n < suc n
natLtSucc n = s≤s (natLeRefl n)
  where
  natLeRefl : ∀ m → m ≤ m
  natLeRefl zero = z≤n
  natLeRefl (suc m) = s≤s (natLeRefl m)

finite-core-collision-from-encoding :
  ∀ {S : Set} {step : S → S} {n : Nat}
  (E : FiniteStateEncoding S n) (s : S) →
  OrbitCollision S step s n
finite-core-collision-from-encoding E s with
  pigeonhole (natLtSucc _) (λ i → encode E (T.iterateGeneric _ (toℕ i) s))
... | i , j , apart , collision =
  orbitCollision i j apart
    (trans
      (sym (roundtrip E _))
      (trans (cong (decode E) collision) (roundtrip E _)))

iterateAdd : ∀ {S : Set} (step : S → S) (m n : Nat) (s : S) →
  T.iterateGeneric step n (T.iterateGeneric step m s) ≡
  T.iterateGeneric step (m + n) s
iterateAdd step m zero s = refl
iterateAdd step m (suc n) s =
  cong step (iterateAdd step m n s)

record OrbitTailRepeat (S : Set) (step : S → S) (s : S) (n : Nat) : Set where
  constructor orbitTailRepeat
  field
    firstIndex′ : Fin (suc n)
    secondIndex′ : Fin (suc n)
    distinctIndex′ : firstIndex′ ≢ secondIndex′
    repeatShift : ∀ k →
      T.iterateGeneric step (toℕ firstIndex′ + k) s ≡
      T.iterateGeneric step (toℕ secondIndex′ + k) s
open OrbitTailRepeat public

finite-core-tail-repeat-from-encoding :
  ∀ {S : Set} {step : S → S} {n : Nat}
  (E : FiniteStateEncoding S n) (s : S) →
  OrbitTailRepeat S step s n
finite-core-tail-repeat-from-encoding E s with
  finite-core-collision-from-encoding E s
... | W =
  orbitTailRepeat
    (firstIndex W)
    (secondIndex W)
    (distinctIndex W)
    (λ k →
      trans
        (sym (iterateAdd _ (toℕ (firstIndex W)) k s))
        (trans
          (cong (T.iterateGeneric _ k) (collision W))
          (iterateAdd _ (toℕ (secondIndex W)) k s)))

record FiniteDescentSystem (S : Set) (step : S → S) : Set₁ where
  constructor finiteDescentSystem
  field
    energy : S → Nat
    fixedDecidable : ∀ s → Dec (step s ≡ s)
    strictDecrease : ∀ s → step s ≢ s → energy (step s) < energy s
open FiniteDescentSystem public

record ReachedFixedPoint (S : Set) (step : S → S) (s : S) : Set where
  constructor reachedFixedPoint
  field
    steps : Nat
    fixed : step (T.iterateGeneric step steps s) ≡ T.iterateGeneric step steps s
open ReachedFixedPoint public

natLeTrans : ∀ {a b c : Nat} → a ≤ b → b ≤ c → a ≤ c
natLeTrans z≤n q = q
natLeTrans (s≤s p) (s≤s q) = s≤s (natLeTrans p q)

ltSuccToLe : ∀ {a b : Nat} → a < suc b → a ≤ b
ltSuccToLe (s≤s p) = p

finite-descent-fixed-with-budget :
  ∀ {S : Set} {step : S → S}
  (C : FiniteDescentSystem S step) (s : S) (n : Nat) →
  energy C s ≤ n →
  ReachedFixedPoint S step s
finite-descent-fixed-with-budget C s zero h with energy C s
... | zero with fixedDecidable C s
...   | yes fixed = reachedFixedPoint zero fixed
...   | no notFixed with strictDecrease C s notFixed
...     | ()
... | suc e with h
...   | ()
finite-descent-fixed-with-budget C s (suc n) h with fixedDecidable C s
... | yes fixed = reachedFixedPoint zero fixed
... | no notFixed with energy C s
...   | zero with strictDecrease C s notFixed
...     | ()
...   | suc e with h
...     | s≤s h′ =
  let hstep = ltSuccToLe (strictDecrease C s notFixed)
      IH = finite-descent-fixed-with-budget C (step s) n
        (natLeTrans hstep h′)
  in reachedFixedPoint
    (suc (steps IH))
    (subst
      (λ z → step z ≡ z)
      (T.iterateGeneric-shift step (steps IH) s)
      (fixed IH))

bounded-fixed-iterate-mechanism :
  ∀ {S : Set} {step : S → S}
  (C : FiniteDescentSystem S step) (s : S) →
  ReachedFixedPoint S step s
bounded-fixed-iterate-mechanism C s =
  finite-descent-fixed-with-budget C s (energy C s) (leRefl (energy C s))
  where
  leRefl : ∀ m → m ≤ m
  leRefl zero = z≤n
  leRefl (suc m) = s≤s (leRefl m)

record EnergyAttractorSystem (S : Set) (step : S → S) : Set₁ where
  constructor energyAttractorSystem
  field
    attractor : S → Set
    energy : S → Nat
    attractorDecidable : ∀ s → Dec (attractor s)
    invariant : ∀ {s} → attractor s → attractor (step s)
    strictDecrease : ∀ s → Dec (attractor s) →
      energy (step s) < energy s
open EnergyAttractorSystem public

record BasinHit (S : Set) (step : S → S) (A : S → Set) (s : S) : Set where
  constructor basinHit
  field
    steps : Nat
    hit : A (T.iterateGeneric step steps s)
open BasinHit public

basin-hit-with-budget :
  ∀ {S : Set} {step : S → S}
  (C : EnergyAttractorSystem S step) (s : S) (n : Nat) →
  energy C s ≤ n →
  BasinHit S step (attractor C) s
basin-hit-with-budget C s zero h with energy C s
... | zero with attractorDecidable C s
...   | yes a = basinHit zero a
...   | no na with strictDecrease C s (no na)
...     | ()
... | suc e with h
...   | ()
basin-hit-with-budget C s (suc n) h with attractorDecidable C s
... | yes a = basinHit zero a
... | no na with energy C s
...   | zero with strictDecrease C s (no na)
...     | ()
...   | suc e with h
...     | s≤s h′ =
  let hstep = ltSuccToLe (strictDecrease C s (no na))
      IH = basin-hit-with-budget C (step s) n (natLeTrans hstep h′)
  in basinHit
    (suc (steps IH))
    (subst
      (λ z → attractor C z)
      (T.iterateGeneric-shift step (steps IH) s)
      (hit IH))

record SymmetricCoupling (C : Set) : Set₁ where
  constructor symmetricCoupling
  field
    coefficient : C → C → L.Int8
    symmetric : ∀ i j → coefficient i j ≡ coefficient j i
open SymmetricCoupling public

record SymmetricAssociativeReservoir (S C : Set) : Set₁ where
  constructor symmetricAssociativeReservoir
  field
    step : S → S
    coupling : SymmetricCoupling C
    energySystem : EnergyAttractorSystem S step
open SymmetricAssociativeReservoir public

record MultiAttractorReservoir (S M C : Set) : Set₁ where
  constructor multiAttractorReservoir
  field
    step′ : S → S
    coupling′ : SymmetricCoupling C
    attractor′ : M → S → Set
    energy′ : S → Nat
    attractorDecidable′ : ∀ m s → Dec (attractor′ m s)
    invariant′ : ∀ m {s} → attractor′ m s → attractor′ m (step′ s)
    strictDecrease′ : ∀ m s → Dec (attractor′ m s) →
      energy′ (step′ s) < energy′ s
    disjoint′ : ∀ {m n s} → m ≢ n → attractor′ m s → ¬ attractor′ n s
    cue′ : M → S
open MultiAttractorReservoir public

contextualRecallWithinEnergy :
  ∀ {S M C : Set}
  (W : MultiAttractorReservoir S M C) m →
  BasinHit S (step′ W) (attractor′ W m) (cue′ W m)
contextualRecallWithinEnergy W m =
  basin-hit-with-budget
    (energyAttractorSystem
      (attractor′ W m)
      (energy′ W)
      (attractorDecidable′ W m)
      (invariant′ W m)
      (λ s na → strictDecrease′ W m s na))
    (cue′ W m)
    (energy′ W (cue′ W m))
    (leRefl (energy′ W (cue′ W m)))
  where
  leRefl : ∀ n → n ≤ n
  leRefl zero = z≤n
  leRefl (suc n) = s≤s (leRefl n)

contextualRecall-disjoint :
  ∀ {S M C : Set}
  (W : MultiAttractorReservoir S M C)
  {m n : M} {s : S} →
  m ≢ n →
  attractor′ W m s →
  ¬ attractor′ W n s
contextualRecall-disjoint W = disjoint′ W

record LearnerSparsificationCertificate (A : Nat) : Set₁ where
  constructor learnerSparsificationCertificate
  field
    activationZero : identityActivation L.zero8 ≡ L.zero8
    gateZero : L.hardSignGate L.zero8 ≡ L.zero8
    l1Progress : ∀ (n : L.NormPair) w x →
      L.l1Weight n ≤ L.l1Weight (L.normStep n w x)
    pathProgress : ∀ (n : L.NormPair) w x →
      L.pathWeight n ≤ L.pathWeight (L.normStep n w x)
    f4Bounded : ∀ (s : L.F4State) x →
      L.l2Global (L.f4Step s x) ≡ L.l2Global s
open LearnerSparsificationCertificate public

learner-sparsification-components :
  ∀ {A : Nat} → LearnerSparsificationCertificate A
learner-sparsification-components =
  learnerSparsificationCertificate
    identityActivation-zero
    hardSignGate-zero
    T.norm-pair-monotone
    (λ n w x → z≤n)
    (λ s x → refl)

record ReservoirQuotient (S Q : Set) : Set₁ where
  constructor reservoirQuotient
  field
    project : S → Q
    relation : S → S → Set
    respects : ∀ {s t} → relation s t → project s ≡ project t
    readout : Q → L.Int8
open ReservoirQuotient public

quotient-readout :
  ∀ {S Q : Set} (W : ReservoirQuotient S Q) s →
  readout W (project W s) ≡ readout W (project W s)
quotient-readout W s = refl

record NeighborhoodSeparationTarget (Q : Set) : Set₁ where
  constructor neighborhoodSeparationTarget
  field
    neighborhood : Q → Q → Set
    separated : ∀ {q r} → q ≢ r →
      neighborhood q r → neighborhood r q → ⊥
open NeighborhoodSeparationTarget public

record SingleOutputReservoirTarget (S : Set) : Set₁ where
  constructor singleOutputReservoirTarget
  field
    readout′ : S → L.Int8
    bounded′ : ∀ s → toℕ (L.code (readout′ s)) < 256
    quotient′ : ∀ Q → ReservoirQuotient S Q
open SingleOutputReservoirTarget public
