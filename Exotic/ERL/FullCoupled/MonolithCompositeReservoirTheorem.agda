{-# OPTIONS --safe #-}
module Exotic.ERL.FullCoupled.MonolithCompositeReservoirTheorem where

open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Nat using (_<_; _≤_; _*_)
open import Data.Nat.Properties using (m≤m+n)
open import Data.Fin using (toℕ)
open import Data.Fin.Properties using (toℕ<n)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; cong; trans; sym)

open import Exotic.ERL.FullCoupled.GeneralFullCoupledLearnerMonolith as L
open import Exotic.ERL.FullCoupled.GeneralFullCoupledTheoremsMonolith as T

stepAt : ∀ {A} → L.LearnerKernel A → L.Int8 → L.LearnerState A → L.LearnerState A
stepAt K reward s = L.learnerStep K s reward

nat-suc-not-self : ∀ n → suc n ≢ n
nat-suc-not-self zero ()
nat-suc-not-self (suc n) eq = nat-suc-not-self n (cong pred eq)
  where
  pred : Nat → Nat
  pred zero = zero
  pred (suc k) = k

learnerStep-clock : ∀ {A} (K : L.LearnerKernel A) s r →
  L.clock (L.learnerStep K s r) ≡ suc (L.clock s)
learnerStep-clock K s r = refl

learnerStep-no-fixed-point : ∀ {A} (K : L.LearnerKernel A) s r →
  L.learnerStep K s r ≢ s
learnerStep-no-fixed-point K s r eq =
  nat-suc-not-self (L.clock s)
    (trans (sym (learnerStep-clock K s r)) (cong L.clock eq))

norm-l1-monotone : ∀ n w x →
  L.l1Weight n ≤ L.l1Weight (L.normStep n w x)
norm-l1-monotone n w x =
  m≤m+n (L.l1Weight n) (toℕ (L.code w))

norm-path-monotone : ∀ n w x →
  L.pathWeight n ≤ L.pathWeight (L.normStep n w x)
norm-path-monotone n w x =
  m≤m+n (L.pathWeight n) (toℕ (L.code w) * toℕ (L.code x))

gru-persistent-invariant : ∀ s x →
  L.gruPersistent (L.gruStep s x) ≡ L.gruPersistent s
gru-persistent-invariant s x = refl

f4-global-l2-law : ∀ {A} (K : L.LearnerKernel A) s g →
  L.f4DeltaTheta (L.f4ParamsK K) s g ≡
  L.f4Sub
    (L.scaledF4
      (L.f4Pow2Level (L.level s))
      (L.hardSignGate g))
    (L.scaledF4
      (L.betaTheta (L.f4ParamsK K))
      (L.f4ThetaFull s))
f4-global-l2-law K s g = refl

gru-hidden-state-law : ∀ s x →
  L.hiddenState (L.gruStep s x) ≡
  L.int8Add
    (L.hiddenState s)
    (L.int8Mul
      (L.hardSignGate x)
      (L.int8Sub x (L.hiddenState s)))
gru-hidden-state-law s x = refl

record DiscreteObservation (S O : Set) : Set₁ where
  constructor discreteObservation
  field
    observe : S → O
    injective : ∀ {s t} → observe s ≡ observe t → s ≡ t
open DiscreteObservation public

discrete-separation : ∀ {S O} (W : DiscreteObservation S O) {s t} →
  s ≢ t → observe W s ≢ observe W t
discrete-separation W apart eq = apart (injective W eq)

int8-output-bounded : ∀ {S : Set} (ρ : S → L.Int8) s →
  toℕ (L.code (ρ s)) < 256
int8-output-bounded ρ s = toℕ<n (L.code (ρ s))

record LeftInverseCertificate (S O : Set) (ρ : S → O) : Set₁ where
  constructor leftInverseCertificate
  field
    inverse : O → S
    leftInverse : ∀ s → inverse (ρ s) ≡ s
open LeftInverseCertificate public

leftInverse-implies-injective : ∀ {S O : Set} {ρ : S → O}
  (W : LeftInverseCertificate S O ρ) {s t} →
  ρ s ≡ ρ t → s ≡ t
leftInverse-implies-injective W eq =
  trans (sym (leftInverse W _))
    (trans (cong (inverse W) eq) (leftInverse W _))

iterate : ∀ {S : Set} → (S → S) → Nat → S → S
iterate step zero s = s
iterate step (suc n) s = step (iterate step n s)

record LyapunovCertificate (S : Set) (step : S → S) : Set₁ where
  constructor lyapunovCertificate
  field
    energy : S → Nat
    strictDecrease : ∀ s → step s ≢ s → energy (step s) < energy s
open LyapunovCertificate public

record AttractorRecallCertificate (S : Set) (step : S → S) : Set₁ where
  constructor attractorRecallCertificate
  field
    attractor : S → Set
    cue : S
    invariant : ∀ {s} → attractor s → attractor (step s)
    basinSteps : Nat
    basinHit : attractor (iterate step basinSteps cue)
open AttractorRecallCertificate public

record KKTPathCertificate (KKTStatement : Set) : Set₁ where
  constructor kKTPathCertificate
  field
    l1Budget : Nat
    pathBudget : Nat
    kktProof : KKTStatement
open KKTPathCertificate public

record ReservoirConditionCertificate (S : Set) : Set₁ where
  constructor reservoirConditionCertificate
  field
    observe : S → L.Int8
    inverse : L.Int8 → S
    inverseLaw : ∀ s → inverse (observe s) ≡ s
open ReservoirConditionCertificate public

reservoir-condition-sufficient : ∀ {S : Set}
  (R : ReservoirConditionCertificate S) (s : S) →
  inverse R (observe R s) ≡ s
reservoir-condition-sufficient R s = inverseLaw R s

reservoir-condition-necessary : ∀ {S : Set}
  (R : ReservoirConditionCertificate S) {s t : S} →
  observe R s ≡ observe R t → s ≡ t
reservoir-condition-necessary R eq =
  trans
    (sym (inverseLaw R _))
    (trans (cong (inverse R) eq) (inverseLaw R _))

reservoir-injective : ∀ {S : Set}
  (R : ReservoirConditionCertificate S) →
  ∀ {s t} → observe R s ≡ observe R t → s ≡ t
reservoir-injective = reservoir-condition-necessary

reservoir-discreteNSP : ∀ {S : Set}
  (R : ReservoirConditionCertificate S) {s t} →
  s ≢ t → observe R s ≢ observe R t
reservoir-discreteNSP R apart eq = apart (reservoir-injective R eq)

reservoir-exact-readout :
  ∀ {S O Y : Set} {ρ : S → O}
  (R : LeftInverseCertificate S O ρ)
  (target : S → Y) →
  (O → Y) × (∀ s → (λ o → target (inverse R o)) (observe R s) ≡ target s)
reservoir-exact-readout R target =
  (λ o → target (inverse R o)) ,
  (λ s → cong target (leftInverse R s))

history-factor-collision :
  ∀ {S X O : Set} {ρ : X → O}
  (history : S → X)
  (R : LeftInverseCertificate X O ρ)
  {s t : S} →
  (λ u → observe R (history u)) s ≡
  (λ u → observe R (history u)) t →
  history s ≡ history t
history-factor-collision history R eq =
  leftInverse-implies-injective R eq

fin256HistoryReservoir : LeftInverseCertificate (Fin 256) L.Int8 (λ i → L.int8 i)
fin256HistoryReservoir =
  leftInverseCertificate
    (λ x → L.code x)
    (λ i → refl)

fin256HistoryReservoir-injective :
  ∀ {i j : Fin 256} →
  L.int8 i ≡ L.int8 j → i ≡ j
fin256HistoryReservoir-injective =
  leftInverse-implies-injective fin256HistoryReservoir

fin256HistoryReservoir-exact-readout :
  ∀ {Y : Set} (target : Fin 256 → Y) →
  (L.Int8 → Y) ×
  (∀ i → (λ o → target (L.code o)) (L.int8 i) ≡ target i)
fin256HistoryReservoir-exact-readout target =
  reservoir-exact-readout fin256HistoryReservoir target

fullLearnerReservoirCondition-impossible :
  ∀ {A} (K : L.LearnerKernel A)
  (R : ReservoirConditionCertificate (L.LearnerState A)) →
  ⊥
fullLearnerReservoirCondition-impossible K R =
  T.fullLearnerState-no-left-inverse
    K
    (observe R)
    (inverse R)
    (inverseLaw R)

record CertifiedCompositeConclusion
  (A : Nat)
  (K : L.LearnerKernel A)
  (reward : L.Int8)
  (KKTStatement : Set) : Set₁ where
  constructor certifiedCompositeConclusion
  field
    currentComposition :
      ∀ s → stepAt K reward s ≢ s
    l1PathProgress :
      ∀ s →
        (L.l1Weight (L.normState s) ≤
          L.l1Weight (L.normStep (L.normState s) (L.q s (L.generalPolicy K s)) reward))
        ×
        (L.pathWeight (L.normState s) ≤
          L.pathWeight (L.normStep (L.normState s) (L.q s (L.generalPolicy K s)) reward))
    f4Coupling :
      ∀ s →
        L.f4DeltaTheta (L.f4ParamsK K) (L.optimizer s) reward ≡
        L.f4Sub
          (L.scaledF4
            (L.f4Pow2Level (L.level (L.optimizer s)))
            (L.hardSignGate reward))
          (L.scaledF4
            (L.betaTheta (L.f4ParamsK K))
            (L.f4ThetaFull (L.optimizer s)))
    gruCoupling :
      ∀ s →
        L.gruPersistent (L.gruStep (L.gru s) reward) ≡ L.gruPersistent (L.gru s)
    normKKT : KKTPathCertificate KKTStatement
    lyapunov : LyapunovCertificate (L.LearnerState A) (stepAt K reward)
    attractor : AttractorRecallCertificate (L.LearnerState A) (stepAt K reward)
    reservoir : ReservoirConditionCertificate (L.LearnerState A)
open CertifiedCompositeConclusion public

composeMonolith : ∀ {A} (K : L.LearnerKernel A) (reward : L.Int8)
  {KKTStatement : Set} →
  (normKKT : KKTPathCertificate KKTStatement) →
  (lyapunov : LyapunovCertificate (L.LearnerState A) (stepAt K reward)) →
  (attractor : AttractorRecallCertificate (L.LearnerState A) (stepAt K reward)) →
  (reservoir : ReservoirConditionCertificate (L.LearnerState A)) →
  CertifiedCompositeConclusion A K reward KKTStatement
composeMonolith K reward normKKT lyapunov attractor reservoir =
  certifiedCompositeConclusion
    (λ s → learnerStep-no-fixed-point K s reward)
    (λ (s : L.LearnerState _) →
      norm-l1-monotone (L.normState s) (L.q s (L.generalPolicy K s)) reward ,
      norm-path-monotone (L.normState s) (L.q s (L.generalPolicy K s)) reward)
    (λ (s : L.LearnerState _) → f4-global-l2-law K (L.optimizer s) reward)
    (λ (s : L.LearnerState _) → gru-persistent-invariant (L.gru s) reward)
    normKKT
    lyapunov
    attractor
    reservoir
