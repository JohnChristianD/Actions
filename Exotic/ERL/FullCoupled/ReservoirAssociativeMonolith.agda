{-# OPTIONS --safe #-}
module Exotic.ERL.FullCoupled.ReservoirAssociativeMonolith where

open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; cong; trans; subst)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Data.Nat using (_<_ ; _≤_; z≤n; s≤s)
open import Data.Nat.Properties using (n<1+n; m+[n∸m]≡n; m>n⇒m∸n≢0)
open import Data.Fin using (Fin; toℕ)
open import Data.Fin.Properties using (pigeonhole)
open import Data.Product using (_×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Induction.WellFounded using (Acc; acc)
open import Data.Nat.Induction using (<-wellFounded)

open import Exotic.ERL.FullCoupled.GeneralFullCoupledLearnerMonolith as L
open import Exotic.ERL.FullCoupled.GeneralFullCoupledTheoremsMonolith as T

record FiniteOrbitEventuallyPeriodic (S : Set) (step : S → S) (s : S) : Set where
  constructor finiteOrbitEventuallyPeriodic
  field
    preperiod : Nat
    period : Nat
    positivePeriod : period ≢ zero
    repeatLaw : T.iterateGeneric step (preperiod + period) s
      ≡ T.iterateGeneric step preperiod s
open FiniteOrbitEventuallyPeriodic public

int8-code-injective : ∀ {x y : L.Int8} → L.code x ≡ L.code y → x ≡ y
int8-code-injective {L.int8 x} {L.int8 .x} refl = refl

orbitCode :
  (step : L.Int8 → L.Int8) → L.Int8 → Fin 257 → Fin 256
orbitCode step s i =
  L.code (T.iterateGeneric step (toℕ i) s)

fin-lt→nat-lt : ∀ {i j : Fin 257} → i < j → toℕ i < toℕ j
fin-lt→nat-lt p = p

lt-to-le : ∀ {m n : Nat} → m < n → m ≤ n
lt-to-le {zero} {zero} ()
lt-to-le {zero} {suc n} p = z≤n
lt-to-le {suc m} {zero} ()
lt-to-le {suc m} {suc n} (s≤s p) = s≤s (lt-to-le p)

int8-orbit-eventually-periodic :
  ∀ (step : L.Int8 → L.Int8) (s : L.Int8) →
  FiniteOrbitEventuallyPeriodic L.Int8 step s
int8-orbit-eventually-periodic step s with pigeonhole (n<1+n 256) (orbitCode step s)
... | i , j , i<j , codeEq =
  finiteOrbitEventuallyPeriodic
    (toℕ i)
    (toℕ j ∸ toℕ i)
    (m>n⇒m∸n≢0 (fin-lt→nat-lt i<j))
    (trans
      (cong
        (λ n → T.iterateGeneric step n s)
        (m+[n∸m]≡n (lt-to-le (fin-lt→nat-lt i<j))))
      (sym (int8-code-injective codeEq)))

learnerNoPeriodicOrbit : ∀ {A} K n s r →
  n ≢ zero →
  L.iterateLearner K n s r ≢ s
learnerNoPeriodicOrbit K zero s r nz = nz refl
learnerNoPeriodicOrbit K (suc n) s r nz eq =
  lt-irrefl (L.clock s)
    (trans
      (cong L.clock eq)
      (sym (T.iterateLearner-clock K (suc n) s r)) )

record ReservoirProjectionWitness (X S : Set) : Set₁ where
  constructor reservoirProjectionWitness
  field
    projectState : X → S
    projectedStep : S → S
    sourceStep : X → X
    commute : ∀ x →
      projectState (sourceStep x) ≡ projectedStep (projectState x)
open ReservoirProjectionWitness public

Int8Vector : Nat → Set
Int8Vector d = Fin d → L.Int8

record SymmetricCouplingMatrix (d : Nat) : Set₁ where
  constructor symmetricCouplingMatrix
  field
    coefficient : Fin d → Fin d → L.Int8
    symmetric : ∀ i j → coefficient i j ≡ coefficient j i
open SymmetricCouplingMatrix public

record BasinWitness {S : Set} (step : S → S) (A : S → Set) (s : S) : Set where
  constructor basinWitness
  field
    steps : Nat
    hits : A (T.iterateGeneric step steps s)
open BasinWitness public

record AttractorLyapunovCertificate (S : Set) : Set₁ where
  constructor attractorLyapunovCertificate
  field
    step : S → S
    attractor : S → Set
    energy : S → Nat
    decidableAttractor : ∀ s → attractor s ⊎ ¬ attractor s
    invariant : ∀ s → attractor s → attractor (step s)
    outsideDecrease : ∀ s → ¬ attractor s → energy (step s) < energy s
open AttractorLyapunovCertificate public

lyapunov-basin : ∀ {S : Set}
  (C : AttractorLyapunovCertificate S) (s : S) →
  BasinWitness (step C) (attractor C) s
lyapunov-basin C s = descend s (<-wellFounded (energy C s))
  where
  descend : ∀ x → Acc _<_ (energy C x) →
    BasinWitness (step C) (attractor C) x
  descend x (acc rec) with decidableAttractor C x
  ... | inj₁ ax = basinWitness zero ax
  ... | inj₂ nx =
    let next = descend
          (step C x)
          (rec (energy C (step C x)) (outsideDecrease C x nx))
    in basinWitness
         (suc (steps next))
         (subst
           (λ z → attractor C z)
           (T.iterateGeneric-shift (step C) (steps next) x)
           (hits next))

record AssociativeReservoirDecomposition (S C : Set) (d : Nat) : Set₁ where
  constructor associativeReservoirDecomposition
  field
    coreStep : S → S
    coupling : SymmetricCouplingMatrix d
    coupledStep : S → S
    lyapunov : AttractorLyapunovCertificate S
    coupledAgreement : ∀ s → step lyapunov s ≡ coupledStep s
open AssociativeReservoirDecomposition public

record MultipleAttractorWitness (S I : Set) (step : S → S) : Set₁ where
  constructor multipleAttractorWitness
  field
    attractorFamily : I → S → Set
    pairwiseDisjoint : ∀ {i j s} → i ≢ j →
      attractorFamily i s → ¬ attractorFamily j s
    invariantFamily : ∀ i s →
      attractorFamily i s → attractorFamily i (step s)
    cueFamily : I → S → Set
    contextualRecall : ∀ i s →
      cueFamily i s → BasinWitness step (attractorFamily i) s
open MultipleAttractorWitness public

record StaticReadoutWitness (S O : Set) : Set₁ where
  constructor staticReadoutWitness
  field
    readout : S → O
open StaticReadoutWitness public

record AlgebraicSeparationWitness (S O : Set) : Set₁ where
  constructor algebraicSeparationWitness
  field
    observe : S → O
    separate : ∀ {s t} → observe s ≡ observe t → s ≡ t
open AlgebraicSeparationWitness public
