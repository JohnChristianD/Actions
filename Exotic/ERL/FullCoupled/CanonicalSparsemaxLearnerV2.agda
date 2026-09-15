{-# OPTIONS --safe #-}
module Exotic.ERL.FullCoupled.CanonicalSparsemaxLearnerV2 where

open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; cong; sym; trans)
import Agda.Builtin.Int as I
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Empty using (⊥)
open import Data.Fin using (toℕ)
open import Data.Nat using (_+_; _*_; _∸_; _<ᵇ_)
open import Data.Product using (_×_; _,_)
open import Exotic.efficient_chad.Int8 using (Int8; code; int8OfNat; int8Add; zero8)
open import Exotic.ERL.FullCoupled.Int8StabilityComposition using (OrbitNonFixed; noNontrivialFiniteCycle)
open import Exotic.ERL.FullCoupled.MobiusGroup using (MobiusAction; composeAction; composeAction-assoc)
open import Exotic.ERL.FullCoupled.SparsemaxCriticWatkins using
  ( CriticState; criticState; qLeft; qRight; BoolLike; enabled; disabled
  ; SignedQLogControl; signedQLogControl; SparsemaxCriticWatkinsState
  ; sparsemaxCriticWatkinsState; critic; learnerSignal; traceSignal; trace
  ; SparsemaxCriticWatkinsKernel; wholeStep )
open import Exotic.ERL.FullCoupled.DyadicGRU using
  ( GRUState; gruStep; persistentGRU; persistent-preservation )

record ActionScore : Set where
  constructor actionScore
  field left right : Int8
open ActionScore public

Sparsemax2Pair : Set
Sparsemax2Pair = Int8 × Int8

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
scaledTwoActionLeft d = q7Clamp (halfInt (I._+_ (I.pos 128) (I._*_ (I.pos 8) d)))

temperatureScaledSparsemax : ActionScore → Sparsemax2Pair
temperatureScaledSparsemax (actionScore l r) =
  let d = I._-_ (signedCode l) (signedCode r)
      leftWeight = scaledTwoActionLeft d
  in leftWeight , q7Complement128 leftWeight

temperatureCodeLaw : sparsemaxTemperature ≡ int8OfNat 16
temperatureCodeLaw = refl

temperatureTieLaw : temperatureScaledSparsemax (actionScore (int8OfNat 0) (int8OfNat 0)) ≡ int8OfNat 64 , int8OfNat 64
temperatureTieLaw = refl

temperaturePositiveUnitLaw : temperatureScaledSparsemax (actionScore (int8OfNat 1) (int8OfNat 0)) ≡ int8OfNat 68 , int8OfNat 60
temperaturePositiveUnitLaw = refl

temperatureNegativeUnitLaw : temperatureScaledSparsemax (actionScore (int8OfNat 0) (int8OfNat 1)) ≡ int8OfNat 60 , int8OfNat 68
temperatureNegativeUnitLaw = refl

pessimisticInit : Int8
pessimisticInit = zero8

pessimisticCritic : CriticState
pessimisticCritic = criticState pessimisticInit pessimisticInit

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
negativeFiniteQLog8 x = let q = finiteQLog8 x in finiteRational (negInt (numerator q)) (denominator q)

negativeFiniteQLogLaw : ∀ x → negativeFiniteQLog8 x ≡ finiteRational (negInt (numerator (finiteQLog8 x))) (denominator (finiteQLog8 x))
negativeFiniteQLogLaw x = refl

negativeAlpha8 : Int8
negativeAlpha8 = int8OfNat 255

canonicalQLogControl : SignedQLogControl
canonicalQLogControl = signedQLogControl enabled negativeAlpha8

qLogSignal : SignedQLogControl → Int8 → Int8
qLogSignal c x with SignedQLogControl.mode c
... | disabled = x
... | enabled = int8Add x (SignedQLogControl.coefficient c)

finiteLCBBonus8 : Nat → Int8
finiteLCBBonus8 zero = int8OfNat 127
finiteLCBBonus8 (suc zero) = int8OfNat 63
finiteLCBBonus8 (suc (suc zero)) = int8OfNat 31
finiteLCBBonus8 (suc (suc (suc zero))) = int8OfNat 15
finiteLCBBonus8 (suc (suc (suc (suc zero)))) = int8OfNat 7
finiteLCBBonus8 (suc (suc (suc (suc (suc zero))))) = int8OfNat 3
finiteLCBBonus8 (suc (suc (suc (suc (suc (suc zero)))))) = int8OfNat 1
finiteLCBBonus8 _ = zero8

record LCBCountKernel : Set where
  constructor lcbCountKernel
  field bonus : Nat → Int8
open LCBCountKernel public

record LCBCountState : Set where
  constructor lcbCountState
  field leftCount rightCount totalCount : Nat
open LCBCountState public

initialLCBCount : LCBCountState
initialLCBCount = lcbCountState zero zero zero

lcbNegative : Int8 → Int8
lcbNegative x = int8OfNat (256 ∸ toℕ (code x))

lcbActionScore : LCBCountKernel → LCBCountState → CriticState → ActionScore
lcbActionScore L counts c = actionScore
  (int8Add (qLeft c) (lcbNegative (bonus L (leftCount counts))))
  (int8Add (qRight c) (lcbNegative (bonus L (rightCount counts))))

scheduledActionScore : LCBCountKernel → Nat → LCBCountState → CriticState → ActionScore
scheduledActionScore L r counts c = let s = lcbActionScore L counts c in actionScore
  (int8Add (left s) (int8OfNat ((r * 37) + 17)))
  (int8Add (right s) (int8OfNat (((suc r) * 37) + 17)))

policyLeftWeight : Sparsemax2Pair → Int8
policyLeftWeight (l , r) = l

policyChoosesLeft : Sparsemax2Pair → BoolLike
policyChoosesLeft (l , r) with toℕ (code r) <ᵇ toℕ (code l)
... | true = enabled
... | false = disabled

updateLCBCount : Sparsemax2Pair → LCBCountState → LCBCountState
updateLCBCount p (lcbCountState l r t) with policyChoosesLeft p
... | enabled = lcbCountState (suc l) r (suc t)
... | disabled = lcbCountState l (suc r) (suc t)

record LearnedSparsemaxAttention : Set where
  constructor learnedSparsemaxAttention
  field leftParameter rightParameter : Int8
open LearnedSparsemaxAttention public

attentionActionScore : LearnedSparsemaxAttention → ActionScore
attentionActionScore a = actionScore (leftParameter a) (rightParameter a)

learnedSparsemaxAttentionWeights : LearnedSparsemaxAttention → Sparsemax2Pair
learnedSparsemaxAttentionWeights a = temperatureScaledSparsemax (attentionActionScore a)

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

mobiusAssociativity :
  ∀ (f g h : MobiusAction) (x : Int8) →
    MobiusAction.run (composeAction (composeAction f g) h) x
      ≡ MobiusAction.run (composeAction f (composeAction g h)) x
mobiusAssociativity = composeAction-assoc

persistentGRUMonolith :
  ∀ (s : GRUState) (x : Int8) →
    persistentGRU (gruStep s x) ≡ persistentGRU s
persistentGRUMonolith = persistent-preservation

record F4Scalar : Set₁ where
  field
    R : Set
    zero one halfULP : R
    addS subS mulS : R → R → R
    intToR : I.Int → R
    quantize8 : R → R
    roundInt : R → I.Int
    quantizedReconstruction : ∀ x → addS (quantize8 x) (subS x (quantize8 x)) ≡ x
open F4Scalar public

record F4IntUState (A : F4Scalar) : Set₁ where
  constructor f4IntUState
  field thetaQ rTheta eQ rE rL : R A
open F4IntUState public

record F4IntUKernel (A : F4Scalar) : Set₁ where
  constructor f4IntUKernel
  field globalL2 : R A
open F4IntUKernel public

f4ThetaStep : ∀ {A : F4Scalar} → F4IntUKernel A → F4IntUState A → R A → F4IntUState A
f4ThetaStep {A} K s g = let base = addS A (thetaQ s) (rTheta s)
                            raw = subS A (addS A base g) (mulS A (globalL2 K) base)
                            q = quantize8 A raw
                        in f4IntUState q (subS A raw q) (eQ s) (rE s) (rL s)

f4ParameterInvariant : ∀ {A : F4Scalar} (K : F4IntUKernel A) (s : F4IntUState A) (g : R A) →
  addS A (thetaQ (f4ThetaStep K s g)) (rTheta (f4ThetaStep K s g)) ≡
  subS A (addS A (addS A (thetaQ s) (rTheta s)) g) (mulS A (globalL2 K) (addS A (thetaQ s) (rTheta s)))
f4ParameterInvariant {A} K s g = quantizedReconstruction A
  (subS A (addS A (addS A (thetaQ s) (rTheta s)) g) (mulS A (globalL2 K) (addS A (thetaQ s) (rTheta s))))

record NormPair (A : F4Scalar) : Set₁ where
  constructor normPair
  field l1 path : R A
open NormPair public

record FullCoupledState (A : F4Scalar) : Set₁ where
  constructor fullCoupledState
  field
    clock : Nat
    criticWatkins : SparsemaxCriticWatkinsState
    attention : LearnedSparsemaxAttention
    gru : GRUState
    optimizer : F4IntUState A
    norm : NormPair A
    lcbCounts : LCBCountState
    qLogControl : SignedQLogControl
    qLogValue : FiniteRational
open FullCoupledState public

record FullCoupledKernel (A : F4Scalar) : Set₁ where
  constructor fullCoupledKernel
  field
    criticKernel : SparsemaxCriticWatkinsKernel
    attentionStep : LearnedSparsemaxAttention → Int8 → LearnedSparsemaxAttention
    attentionToGRU : IntVec2 → Int8
    optimizerKernel : F4IntUKernel A
    lcbKernel : LCBCountKernel
open FullCoupledKernel public

canonicalPolicy : ∀ {A : F4Scalar} → FullCoupledKernel A → FullCoupledState A → Sparsemax2Pair
canonicalPolicy K s = temperatureScaledSparsemax
  (scheduledActionScore (lcbKernel K) (clock s) (lcbCounts s) (critic (criticWatkins s)))

canonicalSignal : ∀ {A : F4Scalar} → FullCoupledKernel A → FullCoupledState A → Int8
canonicalSignal K s = qLogSignal (qLogControl s)
  (int8Add (policyLeftWeight (canonicalPolicy K s)) (int8OfNat ((clock s * 37) + 17)))

canonicalCriticStep : ∀ {A : F4Scalar} → FullCoupledKernel A → FullCoupledState A → SparsemaxCriticWatkinsState
canonicalCriticStep K s = wholeStep (criticKernel K)
  (sparsemaxCriticWatkinsState (critic (criticWatkins s)) (canonicalSignal K s) (traceSignal (criticWatkins s)) (trace (criticWatkins s)))

canonicalAttentionStep : ∀ {A : F4Scalar} → FullCoupledKernel A → FullCoupledState A → LearnedSparsemaxAttention
canonicalAttentionStep K s = attentionStep K (attention s) (canonicalSignal K s)

canonicalGRUStep : ∀ {A : F4Scalar} → FullCoupledKernel A → FullCoupledState A → GRUState
canonicalGRUStep K s = let transformed = haarApply (liftAttention (canonicalPolicy K s)); extra = attentionToGRU K transformed
                         in gruStep (gru s) (int8Add (canonicalSignal K s) extra)

canonicalOptimizerStep : ∀ {A : F4Scalar} → FullCoupledKernel A → FullCoupledState A → F4IntUState A
canonicalOptimizerStep {A} K s = f4ThetaStep (optimizerKernel K) (optimizer s) (intToR A (I.pos (toℕ (code (canonicalSignal K s)))))

canonicalCountStep : ∀ {A : F4Scalar} → FullCoupledKernel A → FullCoupledState A → LCBCountState
canonicalCountStep K s = updateLCBCount (canonicalPolicy K s) (lcbCounts s)

canonicalQLogStep : ∀ {A : F4Scalar} → FullCoupledKernel A → FullCoupledState A → FiniteRational
canonicalQLogStep K s = negativeFiniteQLog8 (policyLeftWeight (canonicalPolicy K s))

canonicalFullStep : ∀ {A : F4Scalar} → FullCoupledKernel A → FullCoupledState A → FullCoupledState A
canonicalFullStep K s = fullCoupledState (suc (clock s)) (canonicalCriticStep K s) (canonicalAttentionStep K s)
  (canonicalGRUStep K s) (canonicalOptimizerStep K s) (norm s) (canonicalCountStep K s) (qLogControl s) (canonicalQLogStep K s)

canonicalFullStep-clock : ∀ K s → clock (canonicalFullStep K s) ≡ suc (clock s)
canonicalFullStep-clock K s = refl

canonicalFullStep-critic : ∀ K s → criticWatkins (canonicalFullStep K s) ≡ canonicalCriticStep K s
canonicalFullStep-critic K s = refl

canonicalFullStep-attention : ∀ K s → attention (canonicalFullStep K s) ≡ canonicalAttentionStep K s
canonicalFullStep-attention K s = refl

canonicalFullStep-gru : ∀ K s → gru (canonicalFullStep K s) ≡ canonicalGRUStep K s
canonicalFullStep-gru K s = refl

canonicalFullStep-optimizer : ∀ K s → optimizer (canonicalFullStep K s) ≡ canonicalOptimizerStep K s
canonicalFullStep-optimizer K s = refl

canonicalFullStep-counts : ∀ K s → lcbCounts (canonicalFullStep K s) ≡ canonicalCountStep K s
canonicalFullStep-counts K s = refl

canonicalFullStep-qLog : ∀ K s → qLogValue (canonicalFullStep K s) ≡ canonicalQLogStep K s
canonicalFullStep-qLog K s = refl

record FullLearnerCoerciveQuadratic {A : F4Scalar} (K : FullCoupledKernel A) : Set₁ where
  constructor fullLearnerCoerciveQuadratic
  field energy : FullCoupledState A → Nat
        strictDecrease : ∀ s → canonicalFullStep K s ≢ s → energy (canonicalFullStep K s) < energy s
open FullLearnerCoerciveQuadratic public

canonicalQuadraticDecay : ∀ {A : F4Scalar} {K : FullCoupledKernel A} (W : FullLearnerCoerciveQuadratic K) (s : FullCoupledState A) → canonicalFullStep K s ≢ s → energy W (canonicalFullStep K s) < energy W s
canonicalQuadraticDecay W s moved = strictDecrease W s moved

iterateCanonical : ∀ {A : F4Scalar} → FullCoupledKernel A → Nat → FullCoupledState A → FullCoupledState A
iterateCanonical K zero s = s
iterateCanonical K (suc n) s = canonicalFullStep K (iterateCanonical K n s)

plus-suc : ∀ (m n : Nat) → m + suc n ≡ suc (m + n)
plus-suc zero n = refl
plus-suc (suc m) n = cong suc (plus-suc m n)

suc-injective : ∀ {m n : Nat} → suc m ≡ suc n → m ≡ n
suc-injective refl = refl

clockAfter : ∀ {A : F4Scalar} (K : FullCoupledKernel A) (n : Nat) (s : FullCoupledState A) → clock (iterateCanonical K n s) ≡ clock s + n
clockAfter K zero s = refl
clockAfter K (suc n) s = trans (cong suc (clockAfter K n s)) (sym (plus-suc (clock s) n))

plus-suc-not-self : ∀ (r n : Nat) → r + suc n ≢ r
plus-suc-not-self zero n = λ ()
plus-suc-not-self (suc r) n eq = plus-suc-not-self r n (suc-injective eq)

canonicalAperiodic : ∀ {A : F4Scalar} (K : FullCoupledKernel A) (s : FullCoupledState A) (n : Nat) → iterateCanonical K (suc n) s ≢ s
canonicalAperiodic K s n cyc = plus-suc-not-self (clock s) n (trans (sym (clockAfter K (suc n) s)) (cong clock cyc))

canonicalCoerciveNoCycle : ∀ {A : F4Scalar} {K : FullCoupledKernel A} (W : FullLearnerCoerciveQuadratic K) {s : FullCoupledState A} (n : Nat) → iterateCanonical K (suc n) s ≡ s → OrbitNonFixed s → ⊥
canonicalCoerciveNoCycle W n cyc nf = noNontrivialFiniteCycle (lyapunovCertificate (energy W) (strictDecrease W)) n cyc nf
