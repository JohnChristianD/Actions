{-# OPTIONS --safe #-}
module Exotic.ERL.FullCoupled.EfficientCHAD_v164 where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl; trans; cong)
open import Agda.Builtin.Int using (Int)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)

data Bottom : Set where

_≠_ : ∀ {A : Set} → A → A → Set
x ≠ y = x ≡ y → Bottom

record FiniteOrderedRational : Set₁ where
  field
    R : Set
    zero one : R
    _+_ _*_ : R → R → R
    neg magnitude reciprocal : R → R
    maximum sign softsign : R → R
    deadZone : R → R → R
    pow2 log2 : R → R
    intEmbed : Int → R
    _≤_ _<_ : R → R → Set
    addNeg : ∀ x → x + neg x ≡ zero
    addZero : ∀ x → x + zero ≡ x
    addAssoc : ∀ x y z → (x + y) + z ≡ x + (y + z)
    mulAssoc : ∀ x y z → (x * y) * z ≡ x * (y * z)
    mulOne : ∀ x → x * one ≡ x
    onePlusMagnitudeNeqZero : ∀ x → (one + magnitude x) ≠ zero
    reciprocalLaw : ∀ {x} → x ≠ zero → x * reciprocal x ≡ one
    softsignFormula : ∀ x → softsign x ≡ x * reciprocal (one + magnitude x)
    deadZoneZero : ∀ {eps y} → y ≤ eps → neg eps ≤ y → deadZone eps y ≡ zero
    deadZonePass : ∀ {eps y} → eps < magnitude y → deadZone eps y ≡ y
    pow2Nonnegative : ∀ x → zero ≤ pow2 x
    log2Pow2 : ∀ x → log2 (pow2 x) ≡ x
    signIdempotent : ∀ x → sign (sign x) ≡ sign x
    intAdd : Int → Int → Int
    intEmbedAdd : ∀ x y → intEmbed (intAdd x y) ≡ intEmbed x + intEmbed y
    pow2Int : Int → R

open FiniteOrderedRational

mapL : ∀ {A B : Set} → (A → B) → List A → List B
mapL f [] = []
mapL f (x ∷ xs) = f x ∷ mapL f xs

FeatureVec : FiniteOrderedRational → Set
FeatureVec A = List (R A)

record DyadicCode : Set where
  field numerator exponent : Nat

dyadicEpsilon dyadicL2 : DyadicCode
dyadicEpsilon = record { numerator = 1 ; exponent = 1 }
dyadicL2 = record { numerator = 1 ; exponent = 3 }

dyadicPrecision dyadicBoundBits : Nat
dyadicPrecision = 16
dyadicBoundBits = 7

record Base2IDBD (A : FiniteOrderedRational) : Set₁ where
  field beta alpha : FeatureVec A
        alphaLaw : alpha ≡ mapL (pow2 A) beta

idbdPow2 : ∀ {A : FiniteOrderedRational} → FeatureVec A → FeatureVec A
idbdPow2 {A} = mapL (pow2 A)

idbdLog2 : ∀ {A : FiniteOrderedRational} → FeatureVec A → FeatureVec A
idbdLog2 {A} = mapL (log2 A)

idbdBase2RoundTrip : ∀ {A : FiniteOrderedRational} xs → idbdLog2 A (idbdPow2 A xs) ≡ xs
idbdBase2RoundTrip {A} [] = refl
idbdBase2RoundTrip {A} (x ∷ xs) = cong₂ _∷_ (log2Pow2 A x) (idbdBase2RoundTrip xs)
  where
  cong₂ : ∀ {X Y Z : Set} (f : X → Y → Z) {x x' : X} {y y' : Y} →
    x ≡ x' → y ≡ y' → f x y ≡ f x' y'
  cong₂ f refl refl = refl

record SigmaDeltaMomentumQuantizer (A : FiniteOrderedRational) : Set₁ where
  field
    quantize : R A → R A
    residual : R A → R A
    reconstruct : ∀ x → quantize x + residual x ≡ x
    residualBound : ∀ x → magnitude (residual x) ≤ one A

record SigmaDeltaLogQuantizer (A : FiniteOrderedRational) : Set₁ where
  field
    round : R A → Int
    residual : R A → R A
    reconstruct : ∀ x → intEmbed A (round x) + residual x ≡ x
    residualBound : ∀ x → magnitude (residual x) ≤ one A

record F4IntSigmaDeltaConfig (A : FiniteOrderedRational) : Set₁ where
  field
    beta2 thetaDecay : R A
    momentumQ : SigmaDeltaMomentumQuantizer A
    logQ : SigmaDeltaLogQuantizer A
    threshold : R A

record F4IntSigmaDeltaState (A : FiniteOrderedRational) : Set₁ where
  field
    theta eQ rE rL : R A
    logStep : Int

open F4IntSigmaDeltaConfig
open F4IntSigmaDeltaState

fullEffectiveState : ∀ {A : FiniteOrderedRational} → F4IntSigmaDeltaState A → R A
fullEffectiveState s = eQ s + rE s

fullPrequantizedState : ∀ {A : FiniteOrderedRational} →
  F4IntSigmaDeltaConfig A → F4IntSigmaDeltaState A → R A → R A
fullPrequantizedState cfg s g =
  beta2 cfg * fullEffectiveState s + (one _ + neg _ (beta2 cfg)) * g

f4IntSigmaDeltaStep : ∀ {A : FiniteOrderedRational} →
  F4IntSigmaDeltaConfig A → F4IntSigmaDeltaState A → R A → F4IntSigmaDeltaState A
f4IntSigmaDeltaStep {A} cfg s g =
  let e* = fullPrequantizedState cfg s g
      eq* = SigmaDeltaMomentumQuantizer.quantize (momentumQ cfg) e*
      re* = SigmaDeltaMomentumQuantizer.residual (momentumQ cfg) e*
      rl* = rL s + e*
      ell* = SigmaDeltaLogQuantizer.round (logQ cfg) rl*
      rll* = SigmaDeltaLogQuantizer.residual (logQ cfg) rl*
      h = pow2Int A (logStep s)
      update = h * deadZone A (threshold cfg) (softsign A g)
      restore = neg A (thetaDecay cfg * theta s)
  in record
    { theta = (theta s + update) + restore
    ; eQ = eq*
    ; rE = re*
    ; rL = rll*
    ; logStep = intAdd A (logStep s) ell* }

f4IntSigmaDeltaFormula : ∀ {A : FiniteOrderedRational}
  (cfg : F4IntSigmaDeltaConfig A) (s : F4IntSigmaDeltaState A) g →
  theta (f4IntSigmaDeltaStep cfg s g) ≡
    (theta s + (pow2Int A (logStep s) * deadZone A (threshold cfg) (softsign A g)))
      + neg A (thetaDecay cfg * theta s)
f4IntSigmaDeltaFormula cfg s g = refl

f4IntSigmaDeltaMomentumReconstruction : ∀ {A : FiniteOrderedRational}
  (cfg : F4IntSigmaDeltaConfig A) (s : F4IntSigmaDeltaState A) g →
  fullEffectiveState (f4IntSigmaDeltaStep cfg s g) ≡ fullPrequantizedState cfg s g
f4IntSigmaDeltaMomentumReconstruction cfg s g =
  SigmaDeltaMomentumQuantizer.reconstruct (momentumQ cfg) (fullPrequantizedState cfg s g)

f4IntSigmaDeltaIntegratorLaw : ∀ {A : FiniteOrderedRational}
  (cfg : F4IntSigmaDeltaConfig A) (s : F4IntSigmaDeltaState A) g →
  intEmbed A (logStep (f4IntSigmaDeltaStep cfg s g))
    + rL (f4IntSigmaDeltaStep cfg s g)
    ≡ (intEmbed A (logStep s) + rL s) + fullPrequantizedState cfg s g
f4IntSigmaDeltaIntegratorLaw {A} cfg s g =
  trans
    (cong (λ x → x + SigmaDeltaLogQuantizer.residual (logQ cfg) (rL s + fullPrequantizedState cfg s g))
      (intEmbedAdd A (logStep s) (SigmaDeltaLogQuantizer.round (logQ cfg) (rL s + fullPrequantizedState cfg s g))))
    (trans
      (addAssoc A (intEmbed A (logStep s))
        (SigmaDeltaLogQuantizer.round (logQ cfg) (rL s + fullPrequantizedState cfg s g) |> intEmbed A)
        (SigmaDeltaLogQuantizer.residual (logQ cfg) (rL s + fullPrequantizedState cfg s g)))
      (cong (λ x → intEmbed A (logStep s) + x)
        (SigmaDeltaLogQuantizer.reconstruct (logQ cfg) (rL s + fullPrequantizedState cfg s g))))

-- The only optimizer-bearing state is F4-Int+SigmaDelta: one EMA state, one momentum residual,
-- one integration residual, the parameter, and the integer log-step. No additional optimizer state appears.
canonicalOnlyOptimizer : ∀ {A : FiniteOrderedRational} →
  F4IntSigmaDeltaConfig A → F4IntSigmaDeltaState A → R A → F4IntSigmaDeltaState A
canonicalOnlyOptimizer = f4IntSigmaDeltaStep

canonicalOptimizerValueLaw : ∀ {A : FiniteOrderedRational}
  (cfg : F4IntSigmaDeltaConfig A) (s : F4IntSigmaDeltaState A) g →
  theta (canonicalOnlyOptimizer cfg s g) ≡ theta (f4IntSigmaDeltaStep cfg s g)
canonicalOptimizerValueLaw cfg s g = refl

record NormPair (A : FiniteOrderedRational) : Set₁ where
  field l1 path : R A

record SignReLU (A : FiniteOrderedRational) : Set₁ where
  field act : R A → R A
        branchSign : ∀ x → sign A (act x) ≡ sign A x

record CanonicalFFNAffine (A : FiniteOrderedRational) : Set₁ where
  field affine : FeatureVec A → FeatureVec A
        norm : NormPair A

record CanonicalSoftsignSignReLUFFN (A : FiniteOrderedRational) : Set₁ where
  field affine1 affine2 affine3 : CanonicalFFNAffine A
        signReLU1 signReLU2 : SignReLU A

runCanonicalSoftsignSignReLUFFN : ∀ {A : FiniteOrderedRational} →
  CanonicalSoftsignSignReLUFFN A → FeatureVec A → FeatureVec A
runCanonicalSoftsignSignReLUFFN {A} f x =
  mapL (softsign A)
    (CanonicalFFNAffine.affine (CanonicalSoftsignSignReLUFFN.affine3 f)
      (mapL (SignReLU.act (CanonicalSoftsignSignReLUFFN.signReLU2 f))
        (CanonicalFFNAffine.affine (CanonicalSoftsignSignReLUFFN.affine2 f)
          (mapL (SignReLU.act (CanonicalSoftsignSignReLUFFN.signReLU1 f))
            (CanonicalFFNAffine.affine (CanonicalSoftsignSignReLUFFN.affine1 f) x)))))

canonicalFFNLayeringLaw : ∀ {A : FiniteOrderedRational}
  (f : CanonicalSoftsignSignReLUFFN A) x →
  runCanonicalSoftsignSignReLUFFN f x ≡ runCanonicalSoftsignSignReLUFFN f x
canonicalFFNLayeringLaw f x = refl

record Tsallis2Attention (A : FiniteOrderedRational) : Set₁ where
  field weights : FeatureVec A
        values : List (FeatureVec A)

weightedAttention : ∀ {A : FiniteOrderedRational} → Tsallis2Attention A → FeatureVec A
weightedAttention {A} a = weighted (Tsallis2Attention.weights a) (Tsallis2Attention.values a)
  where
  scale : R A → FeatureVec A → FeatureVec A
  scale c [] = []
  scale c (x ∷ xs) = c * x ∷ scale c xs
  add : FeatureVec A → FeatureVec A → FeatureVec A
  add [] ys = ys
  add xs [] = xs
  add (x ∷ xs) (y ∷ ys) = x + y ∷ add xs ys
  weighted : FeatureVec A → List (FeatureVec A) → FeatureVec A
  weighted [] _ = []
  weighted (_ ∷ _) [] = []
  weighted (w ∷ ws) (v ∷ vs) = add (scale w v) (weighted ws vs)

record SoftsignAffineBlock (A : FiniteOrderedRational) : Set₁ where
  field affine output : FeatureVec A → FeatureVec A
        norm : NormPair A

record TransformerLayer (A : FiniteOrderedRational) : Set₁ where
  field first : SignReLU A
        second : SoftsignAffineBlock A
        attention : Tsallis2Attention A

runTransformer : ∀ {A : FiniteOrderedRational} → TransformerLayer A → FeatureVec A → FeatureVec A
runTransformer l x = SoftsignAffineBlock.output (TransformerLayer.second l)
  (mapL (SignReLU.act (TransformerLayer.first l)) (weightedAttention (TransformerLayer.attention l)))

record ActorActionMode : Set where
  field useSoftsign : Bool
identityActor : ActorActionMode
identityActor = record { useSoftsign = false }
evalActorAction : ∀ {A : FiniteOrderedRational} → ActorActionMode → R A → R A
evalActorAction mode x with ActorActionMode.useSoftsign mode
... | false = x
... | true = softsign _ x
canonicalActorIdentity : ∀ {A : FiniteOrderedRational} x → evalActorAction {A = A} identityActor x ≡ x
canonicalActorIdentity x = refl

hStepReturn : ∀ {A : FiniteOrderedRational} → List (R A) → R A → R A → R A
hStepReturn [] gamma bootstrap = bootstrap
hStepReturn (r ∷ rs) gamma bootstrap = r + (gamma * hStepReturn rs gamma bootstrap)

hStepRecursionLaw : ∀ {A : FiniteOrderedRational} r gamma bootstrap rs →
  hStepReturn (r ∷ rs) gamma bootstrap ≡ r + (gamma * hStepReturn rs gamma bootstrap)
hStepRecursionLaw r gamma bootstrap rs = refl

record QProjection (A : FiniteOrderedRational) : Set₁ where
  field project : FeatureVec A → FeatureVec A
        idempotent : ∀ x → project (project x) ≡ project x
qProjectionLaw : ∀ {A : FiniteOrderedRational} (q : QProjection A) x →
  QProjection.project q (QProjection.project q x) ≡ QProjection.project q x
qProjectionLaw q x = QProjection.idempotent q x

sumStepPowers : ∀ {A : FiniteOrderedRational} → List (F4IntSigmaDeltaState A) → R A
sumStepPowers {A} [] = zero A
sumStepPowers {A} (s ∷ ss) = pow2Int A (logStep s) + sumStepPowers ss

record StepBudget (A : FiniteOrderedRational) : Set₁ where
  field steps : List (F4IntSigmaDeltaState A)
        budget : R A
        budgetLaw : sumStepPowers steps ≤ budget

record FullFiniteOrderedRationalLearner (A : FiniteOrderedRational) : Set₁ where
  field critic actor transformer representation : List (F4IntSigmaDeltaState A)
        attention : Tsallis2Attention A
        transformerLayer : TransformerLayer A
        qProjection : QProjection A
        qBudget : StepBudget A

mapOptimizer : ∀ {A : FiniteOrderedRational} →
  F4IntSigmaDeltaConfig A → List (F4IntSigmaDeltaState A) → R A → List (F4IntSigmaDeltaState A)
mapOptimizer cfg [] g = []
mapOptimizer cfg (s ∷ ss) g = canonicalOnlyOptimizer cfg s g ∷ mapOptimizer cfg ss g

canonicalLearnerUpdate : ∀ {A : FiniteOrderedRational} →
  F4IntSigmaDeltaConfig A → FullFiniteOrderedRationalLearner A → R A → FullFiniteOrderedRationalLearner A
canonicalLearnerUpdate {A} cfg s g = record
  { FullFiniteOrderedRationalLearner.critic = mapOptimizer cfg (FullFiniteOrderedRationalLearner.critic s) g
  ; FullFiniteOrderedRationalLearner.actor = mapOptimizer cfg (FullFiniteOrderedRationalLearner.actor s) g
  ; FullFiniteOrderedRationalLearner.transformer = mapOptimizer cfg (FullFiniteOrderedRationalLearner.transformer s) g
  ; FullFiniteOrderedRationalLearner.representation = mapOptimizer cfg (FullFiniteOrderedRationalLearner.representation s) g
  ; FullFiniteOrderedRationalLearner.attention = FullFiniteOrderedRationalLearner.attention s
  ; FullFiniteOrderedRationalLearner.transformerLayer = FullFiniteOrderedRationalLearner.transformerLayer s
  ; FullFiniteOrderedRationalLearner.qProjection = FullFiniteOrderedRationalLearner.qProjection s
  ; FullFiniteOrderedRationalLearner.qBudget = FullFiniteOrderedRationalLearner.qBudget s }

canonicalCriticLaw : ∀ {A : FiniteOrderedRational}
  (cfg : F4IntSigmaDeltaConfig A) (s : FullFiniteOrderedRationalLearner A) g →
  FullFiniteOrderedRationalLearner.critic (canonicalLearnerUpdate cfg s g) ≡
    mapOptimizer cfg (FullFiniteOrderedRationalLearner.critic s) g
canonicalCriticLaw cfg s g = refl

canonicalActorLaw : ∀ {A : FiniteOrderedRational}
  (cfg : F4IntSigmaDeltaConfig A) (s : FullFiniteOrderedRationalLearner A) g →
  FullFiniteOrderedRationalLearner.actor (canonicalLearnerUpdate cfg s g) ≡
    mapOptimizer cfg (FullFiniteOrderedRationalLearner.actor s) g
canonicalActorLaw cfg s g = refl

canonicalTransformerLaw : ∀ {A : FiniteOrderedRational}
  (cfg : F4IntSigmaDeltaConfig A) (s : FullFiniteOrderedRationalLearner A) g →
  FullFiniteOrderedRationalLearner.transformer (canonicalLearnerUpdate cfg s g) ≡
    mapOptimizer cfg (FullFiniteOrderedRationalLearner.transformer s) g
canonicalTransformerLaw cfg s g = refl

canonicalRepresentationLaw : ∀ {A : FiniteOrderedRational}
  (cfg : F4IntSigmaDeltaConfig A) (s : FullFiniteOrderedRationalLearner A) g →
  FullFiniteOrderedRationalLearner.representation (canonicalLearnerUpdate cfg s g) ≡
    mapOptimizer cfg (FullFiniteOrderedRationalLearner.representation s) g
canonicalRepresentationLaw cfg s g = refl
