{-# OPTIONS --safe #-}
module Exotic.ERL.FullCoupled.CanonicalSparsemaxLearner where

open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; cong; sym; trans)
import Agda.Builtin.Int as I
open import Agda.Builtin.Nat using (Nat; zero; suc; _∸_; _+_; _*_; _<ᵇ_)
open import Data.Fin using (toℕ)
open import Data.Product using (_×_; _,_)
open import Exotic.ERL.FullCoupled.SparsemaxWatkinsMonolith
open import Exotic.ERL.FullCoupled.Int8StabilityComposition

------------------------------------------------------------------------
-- Fixed Q7 temperature: 16/128 = 1/8. This is policy configuration,
-- not a learned actor parameter.
------------------------------------------------------------------------

sparsemaxTemperature : Int8
sparsemaxTemperature = int8OfNat 16

halfNat : Nat → Nat
halfNat zero = zero
halfNat (suc zero) = zero
halfNat (suc (suc n)) = suc (halfNat n)

halfInt : I.Int → I.Int
halfInt (I.pos n) = I.pos (halfNat n)
halfInt (I.negsuc n) = I.pos zero

signedCode : Int8 → I.Int
signedCode x with toℕ (code x) <ᵇ 128
... | true = I.pos (toℕ (code x))
... | false = I.negsuc (255 ∸ toℕ (code x))

q7Clamp : I.Int → Int8
q7Clamp (I.pos n) with n <ᵇ 129
... | true = int8OfNat n
... | false = int8OfNat 128
q7Clamp (I.negsuc n) = zero8

q7Complement128 : Int8 → Int8
q7Complement128 x = int8OfNat (128 ∸ toℕ (code x))

scaledTwoActionLeft : I.Int → Int8
scaledTwoActionLeft d =
  q7Clamp
    (halfInt
      (I._+_ (I.pos 128) (I._*_ (I.pos 8) d)))

scaledTwoActionSparsemax : ActionScore → Sparsemax2Pair
scaledTwoActionSparsemax (actionScore l r) =
  let d = I._-_ (signedCode l) (signedCode r)
      left = scaledTwoActionLeft d
  in left , q7Complement128 left

temperatureScaledSparsemax : ActionScore → Sparsemax2Pair
temperatureScaledSparsemax = scaledTwoActionSparsemax

temperatureCodeLaw : sparsemaxTemperature ≡ int8OfNat 16
temperatureCodeLaw = refl

temperatureTieLaw :
  temperatureScaledSparsemax (actionScore (int8OfNat 0) (int8OfNat 0))
    ≡ int8OfNat 64 , int8OfNat 64
temperatureTieLaw = refl

temperaturePositiveUnitLaw :
  temperatureScaledSparsemax (actionScore (int8OfNat 1) (int8OfNat 0))
    ≡ int8OfNat 68 , int8OfNat 60
temperaturePositiveUnitLaw = refl

temperatureNegativeUnitLaw :
  temperatureScaledSparsemax (actionScore (int8OfNat 0) (int8OfNat 1))
    ≡ int8OfNat 60 , int8OfNat 68
temperatureNegativeUnitLaw = refl

------------------------------------------------------------------------
-- Exact finite-rational negative q-log boundary.
-- The reciprocal-at-zero convention is finite: recip 0 = 0, hence
-- qLog(0) = 1 and the negative value is -1. For positive code n,
-- qLog(n) = (n-1)/n and its negative is -((n-1)/n).
------------------------------------------------------------------------

record FiniteRational : Set where
  constructor finiteRational
  field numerator denominator : I.Int
open FiniteRational public

negInt : I.Int → I.Int
negInt (I.pos zero) = I.pos zero
negInt (I.pos (suc n)) = I.negsuc n
negInt (I.negsuc n) = I.pos (suc n)

finiteQLog8 : Int8 → FiniteRational
finiteQLog8 x with toℕ (code x)
... | zero = finiteRational (I.pos 1) (I.pos 1)
... | suc n = finiteRational (I.pos n) (I.pos (suc n))

negativeFiniteQLog8 : Int8 → FiniteRational
negativeFiniteQLog8 x =
  let q = finiteQLog8 x
  in finiteRational
       (negInt (numerator q))
       (denominator q)

negativeFiniteQLogLaw :
  ∀ x →
  negativeFiniteQLog8 x
    ≡ finiteRational (negInt (numerator (finiteQLog8 x)))
                     (denominator (finiteQLog8 x))
negativeFiniteQLogLaw x = refl

------------------------------------------------------------------------
-- Separate learned attention state. Its parameters live in the same
-- canonical learner state as the Watkins critic and global optimizer.
------------------------------------------------------------------------

record LearnedSparsemaxAttention : Set where
  constructor learnedSparsemaxAttention
  field leftParameter rightParameter : Int8
open LearnedSparsemaxAttention public

attentionActionScore : LearnedSparsemaxAttention → ActionScore
attentionActionScore a =
  actionScore (leftParameter a) (rightParameter a)

learnedSparsemaxAttentionWeights : LearnedSparsemaxAttention → Sparsemax2Pair
learnedSparsemaxAttentionWeights a =
  temperatureScaledSparsemax (attentionActionScore a)

------------------------------------------------------------------------
-- Frozen unnormalised Haar sandwich.
------------------------------------------------------------------------

IntVec2 : Set
IntVec2 = I.Int × I.Int

liftAttention : Sparsemax2Pair → IntVec2
liftAttention (x , y) = I.pos (toℕ (code x)) , I.pos (toℕ (code y))

haarApply : IntVec2 → IntVec2
haarApply (x , y) = I._+_ x y , I._-_ x y

haarRow0 : IntVec2
haarRow0 = I.pos 1 , I.pos 1

haarRow1 : IntVec2
haarRow1 = I.pos 1 , I.negsuc 0

dot2 : IntVec2 → IntVec2 → I.Int
dot2 (a , b) (c , d) = I._+_ (I._*_ a c) (I._*_ b d)

haar00 : dot2 haarRow0 haarRow0 ≡ I.pos 2
haar00 = refl

haar11 : dot2 haarRow1 haarRow1 ≡ I.pos 2
haar11 = refl

haar01 : dot2 haarRow0 haarRow1 ≡ I.pos 0
haar01 = refl

------------------------------------------------------------------------
-- Canonical endogenous state and kernel.
------------------------------------------------------------------------

record CanonicalSparsemaxState (A : F4Scalar) : Set₁ where
  constructor canonicalSparsemaxState
  field
    core : FullCoupledState A
    attention : LearnedSparsemaxAttention
    qLogValue : FiniteRational
open CanonicalSparsemaxState public

record CanonicalSparsemaxKernel (A : F4Scalar) : Set₁ where
  constructor canonicalSparsemaxKernel
  field
    coreKernel : FullCoupledKernel A
    attentionStep : LearnedSparsemaxAttention → Int8 → LearnedSparsemaxAttention
    attentionToGRU : IntVec2 → Int8
open CanonicalSparsemaxKernel public

canonicalActionScore :
  CanonicalSparsemaxKernel A →
  CanonicalSparsemaxState A →
  ActionScore
canonicalActionScore K s =
  scheduledActionScore
    (lcbKernel (coreKernel K))
    (clock (core s))
    (lcbCounts (core s))
    (critic (criticWatkins (core s)))

canonicalPolicy :
  CanonicalSparsemaxKernel A →
  CanonicalSparsemaxState A →
  Sparsemax2Pair
canonicalPolicy K s =
  temperatureScaledSparsemax (canonicalActionScore K s)

canonicalSignal :
  CanonicalSparsemaxKernel A →
  CanonicalSparsemaxState A →
  Int8
canonicalSignal K s =
  let p = canonicalPolicy K s
      r = clock (core s)
  in signedSignal
       (qLogControl (core s))
       (int8Add (policyLeftWeight p) (schedulerSignal r))

canonicalOptimizerStep :
  CanonicalSparsemaxKernel A →
  CanonicalSparsemaxState A →
  F4IntUState A
canonicalOptimizerStep K s =
  f4Step
    (optimizerKernel (coreKernel K))
    (optimizer (core s))
    (f4GradientFromSignal (canonicalSignal K s))

canonicalCriticStep :
  CanonicalSparsemaxKernel A →
  CanonicalSparsemaxState A →
  SparsemaxCriticWatkinsState
canonicalCriticStep K s =
  let x = canonicalSignal K s
  in wholeStep
       (criticKernel (coreKernel K))
       (setSignals x (criticWatkins (core s)))

canonicalGRUStep :
  CanonicalSparsemaxKernel A →
  CanonicalSparsemaxState A →
  GRUState
canonicalGRUStep K s =
  let p = canonicalPolicy K s
      transformed = haarApply (liftAttention p)
      recurrentSignal = attentionToGRU K transformed
  in gruStep (gru (core s)) (int8Add (canonicalSignal K s) recurrentSignal)

canonicalAttentionStep :
  CanonicalSparsemaxKernel A →
  CanonicalSparsemaxState A →
  LearnedSparsemaxAttention
canonicalAttentionStep K s =
  attentionStep K (attention s) (canonicalSignal K s)

canonicalCountStep :
  CanonicalSparsemaxKernel A →
  CanonicalSparsemaxState A →
  LCBCountState
canonicalCountStep K s =
  updateLCBCount (canonicalPolicy K s) (lcbCounts (core s))

canonicalQLogStep :
  CanonicalSparsemaxKernel A →
  CanonicalSparsemaxState A →
  FiniteRational
canonicalQLogStep K s =
  negativeFiniteQLog8 (policyLeftWeight (canonicalPolicy K s))

canonicalFullStep :
  CanonicalSparsemaxKernel A →
  CanonicalSparsemaxState A →
  CanonicalSparsemaxState A
canonicalFullStep K s =
  let c = core s
      c' = fullCoupledState
        (suc (clock c))
        (canonicalCriticStep K s)
        (canonicalGRUStep K s)
        (canonicalOptimizerStep K s)
        (norm c)
        (canonicalCountStep K s)
        (qLogControl c)
  in canonicalSparsemaxState
       c'
       (canonicalAttentionStep K s)
       (canonicalQLogStep K s)

canonicalFullStep-clock :
  ∀ K s →
  clock (core (canonicalFullStep K s)) ≡ suc (clock (core s))
canonicalFullStep-clock K s = refl

canonicalFullStep-critic :
  ∀ K s →
  criticWatkins (core (canonicalFullStep K s)) ≡ canonicalCriticStep K s
canonicalFullStep-critic K s = refl

canonicalFullStep-gru :
  ∀ K s →
  gru (core (canonicalFullStep K s)) ≡ canonicalGRUStep K s
canonicalFullStep-gru K s = refl

canonicalFullStep-optimizer :
  ∀ K s →
  optimizer (core (canonicalFullStep K s)) ≡ canonicalOptimizerStep K s
canonicalFullStep-optimizer K s = refl

canonicalFullStep-attention :
  ∀ K s →
  attention (canonicalFullStep K s) ≡ canonicalAttentionStep K s
canonicalFullStep-attention K s = refl

canonicalFullStep-counts :
  ∀ K s →
  lcbCounts (core (canonicalFullStep K s)) ≡ canonicalCountStep K s
canonicalFullStep-counts K s = refl

canonicalFullStep-qLog :
  ∀ K s →
  qLogValue (canonicalFullStep K s) ≡ canonicalQLogStep K s
canonicalFullStep-qLog K s = refl

------------------------------------------------------------------------
-- Combined theorem boundary for the actual global optimizer.
-- `energy` is a canonical coercive quadratic witness over the complete
-- learner state. No detached optimizer-only map is accepted here.
------------------------------------------------------------------------

record FullLearnerCoerciveQuadratic {A : F4Scalar}
    (K : CanonicalSparsemaxKernel A) : Set₁ where
  constructor fullLearnerCoerciveQuadratic
  field
    energy : CanonicalSparsemaxState A → Nat
    strictDecrease :
      ∀ s → canonicalFullStep K s ≢ s →
        energy (canonicalFullStep K s) < energy s
open FullLearnerCoerciveQuadratic public

canonicalQuadraticDecay :
  ∀ {A : F4Scalar} {K : CanonicalSparsemaxKernel A}
  (W : FullLearnerCoerciveQuadratic K)
  (s : CanonicalSparsemaxState A)
  → canonicalFullStep K s ≢ s
  → energy W (canonicalFullStep K s) < energy W s
canonicalQuadraticDecay W s moved = strictDecrease W s moved

------------------------------------------------------------------------
-- Deterministic aperiodicity of the actual canonical monolith, from the
-- unbounded Nat scheduler clock. This does not depend on the energy witness.
------------------------------------------------------------------------

iterateCanonical :
  ∀ {A : F4Scalar} →
  CanonicalSparsemaxKernel A → Nat → CanonicalSparsemaxState A →
  CanonicalSparsemaxState A
iterateCanonical K zero s = s
iterateCanonical K (suc n) s = canonicalFullStep K (iterateCanonical K n s)

canonicalClockAfter :
  ∀ {A : F4Scalar} (K : CanonicalSparsemaxKernel A) (n : Nat)
  (s : CanonicalSparsemaxState A) →
  clock (core (iterateCanonical K n s)) ≡ clock (core s) + n
canonicalClockAfter K zero s = refl
canonicalClockAfter K (suc n) s =
  trans
    (cong suc (canonicalClockAfter K n s))
    (sym (plus-suc (clock (core s)) n))

canonicalAperiodic :
  ∀ {A : F4Scalar} (K : CanonicalSparsemaxKernel A)
  (s : CanonicalSparsemaxState A) (n : Nat) →
  iterateCanonical K (suc n) s ≢ s
canonicalAperiodic K s n cyc =
  plus-suc-not-self (clock (core s)) n
    (trans
      (sym (canonicalClockAfter K (suc n) s))
      (cong (λ z → clock (core z)) cyc))

canonicalCoerciveNoCycle :
  ∀ {A : F4Scalar} {K : CanonicalSparsemaxKernel A}
  (W : FullLearnerCoerciveQuadratic K) {s : CanonicalSparsemaxState A} (n : Nat) →
  iterateCanonical K (suc n) s ≡ s →
  OrbitNonFixed s →
  ⊥
canonicalCoerciveNoCycle W n cyc nf =
  noNontrivialFiniteCycle
    (lyapunovCertificate (energy W) (strictDecrease W))
    n
    cyc
    nf
