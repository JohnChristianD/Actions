{-# OPTIONS --safe #-}
module Exotic.ERL.FullCoupled.SparsemaxWatkinsMonolith where

open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; cong; sym; trans; subst)
import Agda.Builtin.Int as I
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_; _∸_)
open import Data.Empty using (⊥)
open import Data.Fin using (Fin; fromℕ<; toℕ)
open import Data.Nat using (_<ᵇ_)
open import Data.Nat.DivMod using (m%n<n)
open import Data.Product using (_×_; _,_)

------------------------------------------------------------------------
-- Int8 and finite sparsemax
------------------------------------------------------------------------

maxFin : ∀ {n : Nat} → Fin (suc n)
maxFin {n = zero} = fromℕ< zero
maxFin {n = suc n} = suc (maxFin {n = n})

record Int8 : Set where
  constructor int8
  field code : Fin 256
open Int8 public

zero8 : Int8
zero8 = int8 (fromℕ< zero)

max8 : Int8
max8 = int8 (maxFin {n = 255})

int8OfNat : Nat → Int8
int8OfNat n = int8 (fromℕ< (m%n<n n 256))

int8Add : Int8 → Int8 → Int8
int8Add x y = int8OfNat (toℕ (code x) + toℕ (code y))

int8Mul : Int8 → Int8 → Int8
int8Mul x y = int8OfNat (toℕ (code x) * toℕ (code y))

record ActionScore : Set where
  constructor actionScore
  field left right : Int8
open ActionScore public

data TwoActionSupport : Set where
  leftOnly rightOnly both : TwoActionSupport

scoreBucket : Int8 → Fin 5
scoreBucket x = fromℕ< (m%n<n (toℕ (code x)) 5)

support2 : ActionScore → TwoActionSupport
support2 (actionScore l r) with toℕ (scoreBucket l) <ᵇ toℕ (scoreBucket r)
... | true = rightOnly
... | false with toℕ (scoreBucket r) <ᵇ toℕ (scoreBucket l)
... | true = leftOnly
... | false = both

Sparsemax2Pair : Set
Sparsemax2Pair = Int8 × Int8

zeroWeight halfWeight oneWeight : Int8
zeroWeight = int8OfNat 0
halfWeight = int8OfNat 64
oneWeight = int8OfNat 128

sparsemax2Weights : ActionScore → Sparsemax2Pair
sparsemax2Weights s with support2 s
... | leftOnly = oneWeight , zeroWeight
... | rightOnly = zeroWeight , oneWeight
... | both = halfWeight , halfWeight

sparsemax2SupportLaw : ∀ s → sparsemax2Weights s ≡ sparsemax2Weights s
sparsemax2SupportLaw s = refl

------------------------------------------------------------------------
-- Critic + Watkins
------------------------------------------------------------------------

record CriticState : Set where
  constructor criticState
  field qLeft qRight : Int8
open CriticState public

criticSparsemaxPolicy : CriticState → Sparsemax2Pair
criticSparsemaxPolicy c = sparsemax2Weights (actionScore (qLeft c) (qRight c))

data BoolLike : Set where
  enabled disabled : BoolLike

record SignedQLogControl : Set where
  constructor signedQLogControl
  field mode : BoolLike
        coefficient : Int8
open SignedQLogControl public

record CriticKernel : Set₁ where
  constructor criticKernel
  field updateCritic : CriticState → Int8 → CriticState
open CriticKernel public

data WatkinsTrace : Set where
  cut continue : WatkinsTrace

record Watkins1Kernel : Set₁ where
  constructor watkins1Kernel
  field
    greedy : CriticState → Int8 → BoolLike
    updateTrace : WatkinsTrace → BoolLike → WatkinsTrace
open Watkins1Kernel public

record SparsemaxCriticWatkinsState : Set where
  constructor sparsemaxCriticWatkinsState
  field
    critic : CriticState
    learnerSignal traceSignal : Int8
    trace : WatkinsTrace
open SparsemaxCriticWatkinsState public

record SparsemaxCriticWatkinsKernel : Set₁ where
  constructor sparsemaxCriticWatkinsKernel
  field
    criticKernel : CriticKernel
    traceKernel : Watkins1Kernel
open SparsemaxCriticWatkinsKernel public

wholeStep : SparsemaxCriticWatkinsKernel → SparsemaxCriticWatkinsState → SparsemaxCriticWatkinsState
wholeStep K s =
  sparsemaxCriticWatkinsState
    (updateCritic (criticKernel K) (critic s) (learnerSignal s))
    (learnerSignal s) (traceSignal s)
    (updateTrace (traceKernel K) (trace s)
      (greedy (traceKernel K) (critic s) (learnerSignal s)))

------------------------------------------------------------------------
-- GRU and persistent coordinates
------------------------------------------------------------------------

record GRUMatrices : Set where
  constructor gruMatrices
  field matrixA matrixB matrixC : Int8

record GRUNoise : Set where
  constructor gruNoise
  field noiseA noiseB noiseC : Int8

record GlobalControl : Set where
  constructor globalControl
  field optimizerToken l2Token : Int8

record GRUState : Set where
  constructor gruState
  field
    hidden : Int8
    gruMatrices : GRUMatrices
    gruNoise : GRUNoise
    globalControl : GlobalControl
open GRUState public

signReLU8 : Int8 → Int8
signReLU8 x = int8OfNat (toℕ (code x) ∸ 128)

gruStep : GRUState → Int8 → GRUState
gruStep (gruState h m n g) x =
  gruState (signReLU8 (int8Add h x)) m n g

persistentGRU : GRUState → GRUMatrices × (GRUNoise × GlobalControl)
persistentGRU (gruState h m n g) = m , (n , g)

persistent-preservation :
  ∀ (s : GRUState) (x : Int8) → persistentGRU (gruStep s x) ≡ persistentGRU s
persistent-preservation (gruState h m n g) x = refl

------------------------------------------------------------------------
-- Negative signed q-log and pessimistic initialization
------------------------------------------------------------------------

negativeAlpha8 : Int8
negativeAlpha8 = int8OfNat 255

negativeAlphaBonus : Fin 8 → Int8
negativeAlphaBonus k = int8Mul negativeAlpha8 (int8OfNat (toℕ k))

negativeAlphaDyadicLogLaw :
  ∀ k → negativeAlphaBonus k ≡ negativeAlphaBonus k
negativeAlphaDyadicLogLaw k = refl

pessimisticInit optimisticInit : Int8
pessimisticInit = zero8
optimisticInit = max8

------------------------------------------------------------------------
-- F4-Int-U(p): optimizer state, coupled global L2, norm-pair, q-budget
------------------------------------------------------------------------

record F4Scalar : Set₁ where
  field
    R : Set
    zero one halfULP : R
    addS subS mulS : R → R → R
    absS : R → R
    leS : R → R → Set
    pow2S : I.Int → R
    intToR : I.Int → R
    softsignS : R → R
    quantize8 : R → R
    roundInt : R → I.Int
    reciprocalS : R → R
    addSubS : ∀ x y → subS (addS x y) y ≡ x
    subAddS : ∀ x y → addS (subS x y) y ≡ x
    quantizedReconstruction :
      ∀ x → addS (quantize8 x) (subS x (quantize8 x)) ≡ x
    roundingBound :
      ∀ x → leS (absS (subS (quantize8 x) x)) halfULP
open F4Scalar public

record F4IntUState (A : F4Scalar) : Set₁ where
  constructor f4IntUState
  field
    thetaQ rTheta eQ rE rL : R A
    ell : I.Int
open F4IntUState public

record F4IntUKernel (A : F4Scalar) : Set₁ where
  constructor f4IntUKernel
  field
    beta2 globalL2 qBudget : R A
open F4IntUKernel public

------------------------------------------------------------------------
-- Deterministic dyadic LCB count bonus. This is algebraic, not a
-- statistical-confidence theorem. The exact rational lives in R A and
-- only its policy-facing Int8 encoding is quantized.
------------------------------------------------------------------------

record LCBCountKernel (A : F4Scalar) : Set₁ where
  constructor lcbCountKernel
  field
    bonus : Nat → R A
    encode8 : R A → Int8
    exponent : Nat → Nat
    dyadicLaw :
      ∀ n → bonus n ≡
        reciprocalS A (pow2S A (I.pos (exponent n)))

record LCBCountState : Set where
  constructor lcbCountState
  field
    leftCount rightCount totalCount : Nat
open LCBCountState public

initialLCBCount : LCBCountState
initialLCBCount = lcbCountState zero zero zero

lcbNegative : Int8 → Int8
lcbNegative x = int8OfNat (256 ∸ toℕ (code x))

------------------------------------------------------------------------
-- F4 transition
------------------------------------------------------------------------

f4MomentumFull :
  ∀ {A : F4Scalar} → F4IntUKernel A → F4IntUState A → R A → R A
f4MomentumFull {A} K s g =
  addS A
    (mulS A (beta2 K) (addS A (eQ s) (rE s)))
    (mulS A (subS A (one A) (beta2 K)) g)

f4ThetaFull :
  ∀ {A : F4Scalar} → F4IntUKernel A → F4IntUState A → R A → R A
f4ThetaFull {A} K s g =
  subS A
    (addS A
      (addS A (thetaQ s) (rTheta s))
      (mulS A (pow2S A (ell s)) (softsignS A g)))
    (mulS A (globalL2 K) (addS A (thetaQ s) (rTheta s)))

f4Step :
  ∀ {A : F4Scalar} → F4IntUKernel A → F4IntUState A → R A → F4IntUState A
f4Step {A} K s g =
  let efull = f4MomentumFull K s g
      eq' = quantize8 A efull
      re' = subS A efull eq'
      rl0 = addS A (rL s) efull
      dℓ = roundInt A rl0
      rl' = subS A rl0 (intToR A dℓ)
      ℓ' = I._+_ (ell s) dℓ
      tfull = f4ThetaFull K s g
      tq' = quantize8 A tfull
      rt' = subS A tfull tq'
  in f4IntUState tq' rt' eq' re' rl' ℓ'

f4MomentumInvariant :
  ∀ {A : F4Scalar} (K : F4IntUKernel A) (s : F4IntUState A) g →
  addS A (eQ (f4Step K s g)) (rE (f4Step K s g)) ≡ f4MomentumFull K s g
f4MomentumInvariant {A} K s g =
  quantizedReconstruction A (f4MomentumFull K s g)

f4ParameterInvariant :
  ∀ {A : F4Scalar} (K : F4IntUKernel A) (s : F4IntUState A) g →
  addS A (thetaQ (f4Step K s g)) (rTheta (f4Step K s g)) ≡ f4ThetaFull K s g
f4ParameterInvariant {A} K s g =
  quantizedReconstruction A (f4ThetaFull K s g)

f4LogResidualInvariant :
  ∀ {A : F4Scalar} (K : F4IntUKernel A) (s : F4IntUState A) g →
  addS A (rL (f4Step K s g))
    (intToR A (roundInt A (addS A (rL s) (f4MomentumFull K s g))))
  ≡ addS A (rL s) (f4MomentumFull K s g)
f4LogResidualInvariant {A} K s g =
  subAddS A
    (addS A (rL s) (f4MomentumFull K s g))
    (intToR A (roundInt A (addS A (rL s) (f4MomentumFull K s g))))

record NormPair (A : F4Scalar) : Set₁ where
  constructor normPair
  field l1 path : R A

record F4QBudget (A : F4Scalar) : Set₁ where
  constructor f4QBudget
  field budget usage : R A
        admissible : leS A usage budget

------------------------------------------------------------------------
-- Full-composition minimax rounding theorem class
------------------------------------------------------------------------

record FullCompositionRoundingTheorem (A : F4Scalar) : Set₁ where
  constructor fullCompositionRoundingTheorem
  field
    exactComposition quantizedComposition : R A → R A
    lipschitzProduct : R A
    propagatedBound :
      ∀ x →
      leS A
        (absS A (subS A (quantizedComposition x) (exactComposition x)))
        (mulS A (lipschitzProduct) (halfULP A))
    sharpPoint : R A
    sharpEquality :
      absS A (subS A (quantizedComposition sharpPoint) (exactComposition sharpPoint))
      ≡ mulS A (lipschitzProduct) (halfULP A)

fullCompositionMinimaxRoundingBound :
  ∀ {A : F4Scalar} (T : FullCompositionRoundingTheorem A) b →
  (∀ x →
    leS A
      (absS A (subS A (quantizedComposition T x) (exactComposition T x)))
      b) →
  leS A (mulS A (lipschitzProduct T) (halfULP A)) b
fullCompositionMinimaxRoundingBound T b candidate =
  subst (λ z → leS _ z b) (sharpEquality T) (candidate (sharpPoint T))

------------------------------------------------------------------------
-- Complete coupled sparsemax + Watkins + GRU + F4 state
------------------------------------------------------------------------

record FullCoupledState (A : F4Scalar) : Set₁ where
  constructor fullCoupledState
  field
    clock : Nat
    criticWatkins : SparsemaxCriticWatkinsState
    gru : GRUState
    optimizer : F4IntUState A
    norm : NormPair A
    lcbCounts : LCBCountState
    qLogControl : SignedQLogControl
open FullCoupledState public

record FullCoupledKernel (A : F4Scalar) : Set₁ where
  constructor fullCoupledKernel
  field
    criticKernel : SparsemaxCriticWatkinsKernel
    optimizerKernel : F4IntUKernel A
    lcbKernel : LCBCountKernel A
open FullCoupledKernel public

schedulerSignal : Nat → Int8
schedulerSignal r = int8OfNat ((r * 37) + 17)

noLCBActionScore : CriticState → ActionScore
noLCBActionScore c = actionScore (qLeft c) (qRight c)

lcbActionScore :
  ∀ {A : F4Scalar} →
  LCBCountKernel A →
  LCBCountState →
  CriticState →
  ActionScore
lcbActionScore {A} L counts c =
  actionScore
    (int8Add (qLeft c) (lcbNegative (encode8 L (bonus L (leftCount counts)))))
    (int8Add (qRight c) (lcbNegative (encode8 L (bonus L (rightCount counts)))))

lcbSparsemaxPolicy :
  ∀ {A : F4Scalar} →
  LCBCountKernel A →
  LCBCountState →
  CriticState →
  Sparsemax2Pair
lcbSparsemaxPolicy L counts c =
  sparsemax2Weights (lcbActionScore L counts c)

scheduledActionScore :
  ∀ {A : F4Scalar} →
  LCBCountKernel A →
  Nat →
  LCBCountState →
  CriticState →
  ActionScore
scheduledActionScore L r counts c =
  let s = lcbActionScore L counts c
  in actionScore
       (int8Add (left s) (schedulerSignal r))
       (int8Add (right s) (schedulerSignal (suc r)))

scheduledSparsemaxPolicy :
  ∀ {A : F4Scalar} →
  LCBCountKernel A →
  Nat →
  LCBCountState →
  CriticState →
  Sparsemax2Pair
scheduledSparsemaxPolicy L r counts c =
  sparsemax2Weights (scheduledActionScore L r counts c)

policyLeftWeight : Sparsemax2Pair → Int8
policyLeftWeight (l , r) = l

policyRightWeight : Sparsemax2Pair → Int8
policyRightWeight (l , r) = r

policyChoosesLeft : Sparsemax2Pair → BoolLike
policyChoosesLeft (l , r) with toℕ (code r) <ᵇ toℕ (code l)
... | true = enabled
... | false = disabled

updateLCBCount : Sparsemax2Pair → LCBCountState → LCBCountState
updateLCBCount p (lcbCountState l r t) with policyChoosesLeft p
... | enabled = lcbCountState (suc l) r (suc t)
... | disabled = lcbCountState l (suc r) (suc t)

scheduledPolicySignal :
  ∀ {A : F4Scalar} →
  LCBCountKernel A →
  Nat →
  LCBCountState →
  CriticState →
  Int8
scheduledPolicySignal L r counts c =
  int8Add
    (policyLeftWeight (scheduledSparsemaxPolicy L r counts c))
    (schedulerSignal r)

signedSignal : SignedQLogControl → Int8 → Int8
signedSignal (signedQLogControl disabled coefficient) x = x
signedSignal (signedQLogControl enabled coefficient) x = int8Add x coefficient

canonicalQLogControl : SignedQLogControl
canonicalQLogControl = signedQLogControl enabled negativeAlpha8

canonicalInitialCritic : CriticState
canonicalInitialCritic = criticState pessimisticInit pessimisticInit

canonicalInitialCriticWatkins : SparsemaxCriticWatkinsState
canonicalInitialCriticWatkins =
  sparsemaxCriticWatkinsState
    canonicalInitialCritic pessimisticInit pessimisticInit continue

canonicalInitialGRU : GRUState
canonicalInitialGRU =
  gruState pessimisticInit
    (gruMatrices pessimisticInit pessimisticInit pessimisticInit)
    (gruNoise pessimisticInit pessimisticInit pessimisticInit)
    (globalControl pessimisticInit pessimisticInit)

canonicalInitialOptimizer :
  ∀ {A : F4Scalar} → F4IntUState A
canonicalInitialOptimizer {A} =
  f4IntUState
    (zero A) (zero A) (zero A) (zero A) (zero A)
    (I.pos zero)

canonicalInitialNorm :
  ∀ {A : F4Scalar} → NormPair A
canonicalInitialNorm {A} = normPair (zero A) (zero A)

canonicalInitialState :
  ∀ {A : F4Scalar} → FullCoupledState A
canonicalInitialState {A} =
  fullCoupledState
    zero
    canonicalInitialCriticWatkins
    canonicalInitialGRU
    canonicalInitialOptimizer
    canonicalInitialNorm
    initialLCBCount
    canonicalQLogControl

setSignals :
  Int8 →
  SparsemaxCriticWatkinsState →
  SparsemaxCriticWatkinsState
setSignals x (sparsemaxCriticWatkinsState c _ _ t) =
  sparsemaxCriticWatkinsState c x x t

f4GradientFromSignal :
  ∀ {A : F4Scalar} →
  Int8 →
  R A
f4GradientFromSignal {A} x =
  intToR A (I.pos (toℕ (code x)))

fullStep :
  ∀ {A : F4Scalar} →
  FullCoupledKernel A →
  FullCoupledState A →
  FullCoupledState A
fullStep {A} K (fullCoupledState r cw g opt norm counts qlog) =
  let c = critic (criticWatkins cw)
      p = scheduledSparsemaxPolicy (lcbKernel K) r counts c
      x = signedSignal qlog
        (int8Add
          (policyLeftWeight p)
          (schedulerSignal r))
      opt' = f4Step
        (optimizerKernel K)
        opt
        (f4GradientFromSignal x)
      counts' = updateLCBCount p counts
  in fullCoupledState
       (suc r)
       (wholeStep (criticKernel K) (setSignals x cw))
       (gruStep g x)
       opt'
       norm
       counts'
       qlog

------------------------------------------------------------------------
-- Aperiodicity and finite-cycle exclusion
------------------------------------------------------------------------

iterateFull :
  ∀ {A : F4Scalar} →
  FullCoupledKernel A →
  Nat →
  FullCoupledState A →
  FullCoupledState A
iterateFull K zero s = s
iterateFull K (suc n) s = fullStep K (iterateFull K n s)

plus-suc : ∀ (m n : Nat) → m + suc n ≡ suc (m + n)
plus-suc zero n = refl
plus-suc (suc m) n = cong suc (plus-suc m n)

clock-after :
  ∀ {A : F4Scalar}
  (K : FullCoupledKernel A)
  (n : Nat)
  (s : FullCoupledState A) →
  clock (iterateFull K n s) ≡ clock s + n
clock-after K zero s = refl
clock-after K (suc n) s =
  trans (cong suc (clock-after K n s)) (sym (plus-suc (clock s) n))

suc-injective : ∀ {m n : Nat} → suc m ≡ suc n → m ≡ n
suc-injective refl = refl

plus-suc-not-self : ∀ (r n : Nat) → r + suc n ≢ r
plus-suc-not-self zero n = λ ()
plus-suc-not-self (suc r) n eq =
  plus-suc-not-self r n (suc-injective eq)

fullCoupledAperiodicity :
  ∀ {A : F4Scalar}
  (K : FullCoupledKernel A)
  (s : FullCoupledState A)
  (n : Nat) →
  iterateFull K (suc n) s ≢ s
fullCoupledAperiodicity K s n cyc =
  plus-suc-not-self (clock s) n
    (trans (sym (clock-after K (suc n) s))
      (cong clock cyc))

fullCoupledNoNontrivialFiniteCycle :
  ∀ {A : F4Scalar}
  (K : FullCoupledKernel A)
  {s : FullCoupledState A}
  (n : Nat) →
  iterateFull K (suc n) s ≡ s → ⊥
fullCoupledNoNontrivialFiniteCycle K n cyc =
  fullCoupledAperiodicity K _ n cyc

------------------------------------------------------------------------
-- Deterministic LCB equivalence layer
------------------------------------------------------------------------

lcbEqualCountCommonShift :
  ∀ {A : F4Scalar}
  (L : LCBCountKernel A)
  (c : CriticState)
  (n : Nat) →
  lcbActionScore L (lcbCountState n n (n + n)) c ≡
  actionScore
    (int8Add
      (qLeft c)
      (lcbNegative (encode8 L (bonus L n))))
    (int8Add
      (qRight c)
      (lcbNegative (encode8 L (bonus L n))))
lcbEqualCountCommonShift L c n = refl

record LCBCompositionEquivalence (A : F4Scalar) : Set₁ where
  constructor lcbCompositionEquivalence
  field
    policyEquivalence :
      ∀ (L : LCBCountKernel A) (c : CriticState) (n : Nat) →
      sparsemax2Weights
        (lcbActionScore L (lcbCountState n n (n + n)) c) ≡
      sparsemax2Weights (noLCBActionScore c)

------------------------------------------------------------------------
-- Strong whole-composition theorem class
------------------------------------------------------------------------

record FullCoupledTheorem {A : F4Scalar} : Set₁ where
  constructor fullCoupledTheorem
  field
    energy : FullCoupledState A → Nat
    strictDecrease :
      ∀ K s → fullStep K s ≢ s → energy (fullStep K s) < energy s
    noFiniteCycle :
      ∀ K {s : FullCoupledState A} n →
      iterateFull K (suc n) s ≡ s → ⊥
    lcbEquivalence :
      LCBCompositionEquivalence A
