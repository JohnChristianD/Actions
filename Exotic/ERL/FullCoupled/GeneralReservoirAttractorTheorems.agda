{-# OPTIONS --safe #-}
module Exotic.ERL.FullCoupled.GeneralReservoirAttractorTheorems where

open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; cong; subst; trans)
open import Relation.Nullary using (Dec; yes; no)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Data.Nat using (_<_ ; _≤_; z≤n; s≤s)
open import Data.Nat.Properties using (m≤m+n)
open import Data.Fin using (Fin; toℕ)
open import Data.Fin.Properties using (pigeonhole)
open import Data.Product using (_×_; _,_)

open import Exotic.ERL.FullCoupled.GeneralFullCoupledLearnerMonolith as L
open import Exotic.ERL.FullCoupled.GeneralFullCoupledTheoremsMonolith as T

natLeRefl : ∀ n → n ≤ n
natLeRefl zero = z≤n
natLeRefl (suc n) = s≤s (natLeRefl n)

natLtSucc : ∀ n → n < suc n
natLtSucc n = s≤s (natLeRefl n)

natLeTrans : ∀ {a b c : Nat} → a ≤ b → b ≤ c → a ≤ c
natLeTrans z≤n q = q
natLeTrans (s≤s p) (s≤s q) = s≤s (natLeTrans p q)

ltSuccToLe : ∀ {a b : Nat} → a < suc b → a ≤ b
ltSuccToLe (s≤s p) = p

iterateAdd : ∀ {S : Set} (step : S → S) (m n : Nat) (s : S) →
  T.iterateGeneric step n (T.iterateGeneric step m s) ≡
  T.iterateGeneric step (m + n) s
iterateAdd step m zero s = refl
iterateAdd step m (suc n) s =
  cong step (iterateAdd step m n s)

record FiniteOrbitCollision
  (R : L.Int8 → L.Int8)
  (s : L.Int8) : Set where
  constructor finiteOrbitCollision
  field
    firstIndex : Fin 257
    secondIndex : Fin 257
    distinctIndex : firstIndex ≢ secondIndex
    collision :
      T.iterateGeneric R (toℕ firstIndex) s ≡
      T.iterateGeneric R (toℕ secondIndex) s
open FiniteOrbitCollision public

orbitCode :
  (R : L.Int8 → L.Int8) → L.Int8 → Fin 257 → Fin 256
orbitCode R s i =
  L.code (T.iterateGeneric R (toℕ i) s)

finiteCore-collision :
  ∀ (R : L.Int8 → L.Int8) (s : L.Int8) →
  FiniteOrbitCollision R s
finiteCore-collision R s with pigeonhole (natLtSucc 256) (orbitCode R s)
... | i , j , apart , collision =
  finiteOrbitCollision i j apart (cong L.int8 collision)

record FiniteOrbitTailRepeat
  (R : L.Int8 → L.Int8)
  (s : L.Int8) : Set where
  constructor finiteOrbitTailRepeat
  field
    firstIndex′ : Fin 257
    secondIndex′ : Fin 257
    distinctIndex′ : firstIndex′ ≢ secondIndex′
    repeatShift : ∀ n →
      T.iterateGeneric R (toℕ firstIndex′ + n) s ≡
      T.iterateGeneric R (toℕ secondIndex′ + n) s
open FiniteOrbitTailRepeat public

finiteCore-tail-repeat :
  ∀ (R : L.Int8 → L.Int8) (s : L.Int8) →
  FiniteOrbitTailRepeat R s
finiteCore-tail-repeat R s with finiteCore-collision R s
... | W =
  finiteOrbitTailRepeat
    (firstIndex W)
    (secondIndex W)
    (distinctIndex W)
    (λ n →
      trans
        (sym (iterateAdd R (toℕ (firstIndex W)) n s))
        (trans
          (cong
            (T.iterateGeneric R n)
            (collision W))
          (iterateAdd R (toℕ (secondIndex W)) n s)))

hiddenReservoirStep : L.Int8 → L.Int8 → L.Int8
hiddenReservoirStep h x =
  L.hiddenState
    (L.gruStep
      (L.gruState h L.one8 L.one8 L.one8
        L.zero8 L.zero8 L.zero8 L.zero8 L.zero8)
      x)

hiddenReservoirStep-law : ∀ (s : L.GRUState) x →
  L.hiddenState (L.gruStep s x) ≡
  hiddenReservoirStep (L.hiddenState s) x
hiddenReservoirStep-law s x = refl

hiddenProjection : ∀ {A : Nat} → L.LearnerState A → L.Int8
hiddenProjection s = L.hiddenState (L.gru s)

learnerShapedInput : ∀ {A : Nat} → L.LearnerKernel A → L.LearnerState A → L.Int8 → L.Int8
learnerShapedInput K s reward =
  let a = L.generalPolicy K s
      w = L.sparsemaxWeight (L.actionSpaceK K) (L.q s) (L.counts s) a
  in L.int8Add reward (L.munchausenSignal (L.mode K) w)

hiddenProjection-step : ∀ {A : Nat} K s reward →
  hiddenProjection (L.learnerStep K s reward) ≡
  hiddenReservoirStep
    (hiddenProjection s)
    (learnerShapedInput K s reward)
hiddenProjection-step K s reward = refl

hiddenExactObservability : T.ObservabilityWitness L.Int8 L.Int8
hiddenExactObservability =
  T.observabilityWitness
    (λ s → s)
    (λ eq → eq)

l1Weight-step-monotone : ∀ (n : L.NormPair) w x →
  L.l1Weight n ≤ L.l1Weight (L.normStep n w x)
l1Weight-step-monotone n w x =
  m≤m+n (L.l1Weight n) (toℕ (L.code w))

l1Weight-is-progress-not-dissipation : ∀ n w x →
  L.l1Weight n ≤ L.l1Weight (L.normStep n w x)
l1Weight-is-progress-not-dissipation = l1Weight-step-monotone

record SymmetricCoupling (C : Set) : Set₁ where
  constructor symmetricCoupling
  field
    coefficient : C → C → L.Int8
    symmetric : ∀ i j → coefficient i j ≡ coefficient j i
open SymmetricCoupling public

record SymmetricAssociativeReservoir
  (S C : Set) : Set₁ where
  constructor symmetricAssociativeReservoir
  field
    step : S → S
    coupling : SymmetricCoupling C
    attractor : S → Set
    energy : S → Nat
    attractorDecidable : ∀ s → Dec (attractor s)
    invariant : ∀ {s} → attractor s → attractor (step s)
    strictDecrease : ∀ s → ¬ attractor s → energy (step s) < energy s
open SymmetricAssociativeReservoir public

record BasinHit
  (S : Set)
  (step : S → S)
  (A : S → Set)
  (s : S) : Set where
  constructor basinHit
  field
    steps : Nat
    hit : A (T.iterateGeneric step steps s)
open BasinHit public

basin-by-energy :
  ∀ {S : Set} (C : SymmetricAssociativeReservoir S L.Int8)
    (s : S) (n : Nat) →
    energy C s ≤ n →
    BasinHit S (step C) (attractor C) s
basin-by-energy C s zero h with energy C s
... | zero with attractorDecidable C s
...   | yes a = basinHit zero a
...   | no na with strictDecrease C s na
...     | ()
... | suc e with h
...   | ()
basin-by-energy C s (suc n) h with attractorDecidable C s
... | yes a = basinHit zero a
... | no na with energy C s
...   | zero with strictDecrease C s na
...     | ()
...   | suc e with h
...     | s≤s h′ =
  let hstep = ltSuccToLe (strictDecrease C s na)
      IH = basin-by-energy C (step C s) n (natLeTrans hstep h′)
  in basinHit
    (suc (steps IH))
    (subst
      (λ z → attractor C z)
      (T.iterateGeneric-shift (step C) (steps IH) s)
      (hit IH))

invariant-after-hit :
  ∀ {S : Set}
  (C : SymmetricAssociativeReservoir S L.Int8)
  {s : S} →
  attractor C s →
  ∀ n → attractor C (T.iterateGeneric (step C) n s)
invariant-after-hit C a zero = a
invariant-after-hit C a (suc n) =
  invariant-after-hit C (invariant C a) n

record MultiAttractorReservoir
  (S M C : Set) : Set₁ where
  constructor multiAttractorReservoir
  field
    step′ : S → S
    coupling′ : SymmetricCoupling C
    attractor′ : M → S → Set
    energy′ : S → Nat
    attractorDecidable′ : ∀ m s → Dec (attractor′ m s)
    invariant′ : ∀ m {s} → attractor′ m s → attractor′ m (step′ s)
    strictDecrease′ : ∀ m s → ¬ attractor′ m s → energy′ (step′ s) < energy′ s
    disjoint′ : ∀ {m n s} → m ≢ n → attractor′ m s → ¬ attractor′ n s
    cue′ : M → S
open MultiAttractorReservoir public

contextualRecall :
  ∀ {S M C : Set}
  (W : MultiAttractorReservoir S M C) m →
  BasinHit S (step′ W) (attractor′ W m) (cue′ W m)
contextualRecall W m =
  basin-by-energy
    (symmetricAssociativeReservoir
      (step′ W)
      (coupling′ W)
      (attractor′ W m)
      (energy′ W)
      (attractorDecidable′ W m)
      (invariant′ W m)
      (strictDecrease′ W m))
    (cue′ W m)
    (energy′ W (cue′ W m))
    (natLeRefl (energy′ W (cue′ W m)))

contextualRecall-disjoint :
  ∀ {S M C : Set}
  (W : MultiAttractorReservoir S M C)
  {m n : M} {s : S} →
  m ≢ n →
  attractor′ W m s →
  ¬ attractor′ W n s
contextualRecall-disjoint W = disjoint′ W
