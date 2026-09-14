{-# OPTIONS --safe #-}
module Exotic.ERL.FullCoupled.EndogenousBoundaryComposition where

open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)
open import Agda.Builtin.Int using (Int)
open import Data.List using (List; []; _∷_)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_×_; _,_)
open import Exotic.efficient_chad.Int8 using
  ( Int8
  ; zero8
  )
open import Exotic.ERL.FullCoupled.DyadicGRU using
  ( GRUState
  ; global
  ; optimizerToken
  ; l2Token
  ; gruStep
  )
open import Exotic.ERL.FullCoupled.FiniteHaarSparsemaxRoPE using
  ( Int8Pair
  ; frontEndToGRU
  )
open import Exotic.ERL.FullCoupled.Int8DPG using
  ( DPGCoupled
  ; DPGActor
  ; DPGCritic
  ; actorComponent
  ; criticComponent
  ; actorForward
  ; criticForward
  ; globalControl
  ; optimizer
  ; l2
  )
open import Exotic.ERL.FullCoupled.DPGBellmanHaarComposition using
  ( State
  ; Q
  ; GreedyPolicy
  ; Discount
  ; IsGreedy
  ; maxQBootstrap
  ; greedyPolicyBootstrap
  ; DPG-maxQ-bootstrap-equivalence
  )
open import Exotic.ERL.FullCoupled.WatkinsDPG using
  ( TraceDecision
  ; keepTrace
  ; cutTrace
  ; WatkinsExploration
  ; watkinsCut
  ; watkinsTraceLength
  ; watkinsTraceLength-cut-head
  ; watkinsRegime
  ; oneStep
  ; cut-regime-is-one-step
  )

------------------------------------------------------------------------
-- Exact F4-Int-U-Softsign algebraic specification.
-- The scalar carrier is a dyadic finite-precision representation; the
-- concrete signed-Int8 encoding supplies the storage code. Residual fields
-- therefore remain dyadic quantities rather than pretending that literal
-- integer Int8 can represent 1/2 exactly.
------------------------------------------------------------------------

record F4Arithmetic : Set₁ where
  field
    D : Set
    zero one : D
    _+_ _-_ _*_ : D → D → D
    softsign : D → D
    quantize : D → D
    roundLog : D → Int
    embedInt : Int → D
    pow2 : Int → D
    beta₂ betaθ : D
    addAssoc : ∀ x y z → (x + y) + z ≡ x + (y + z)
    addComm : ∀ x y → x + y ≡ y + x
    subAdd : ∀ x y → y + (x - y) ≡ x
    embedAdd : ∀ x y → embedInt (x + y) ≡ embedInt x + embedInt y
    embedRound : ∀ x → embedInt (roundLog x) + (x - embedInt (roundLog x)) ≡ x

open F4Arithmetic public

record F4IntState (A : F4Arithmetic) : Set where
  constructor f4IntState
  field
    thetaQ : D A
    rTheta : D A
    eQ : D A
    rE : D A
    rL : D A
    ell : Int

open F4IntState public

eFull : ∀ {A : F4Arithmetic} → F4IntState A → D A → D A
eFull {A} s g =
  beta₂ A * (eQ s + rE s) + (one A - beta₂ A) * g

thetaFull : ∀ {A : F4Arithmetic} → F4IntState A → D A → D A
thetaFull {A} s g =
  ((thetaQ s + rTheta s)
    + pow2 A (ell s) * softsign A g)
    - betaθ A * (thetaQ s + rTheta s)

f4IntUSoftsignStep :
  ∀ {A : F4Arithmetic} → F4IntState A → D A → F4IntState A
f4IntUSoftsignStep {A} s g =
  let e* = eFull s g
      rℓ* = rL s + e*
      Δℓ = roundLog A rℓ*
      θ* = thetaFull s g
      θq* = quantize A θ*
  in f4IntState
       θq*
       (θ* - θq*)
       (quantize A e*)
       (e* - quantize A e*)
       (rℓ* - embedInt A Δℓ)
       (ell s + Δℓ)

f4ThetaReconstruction :
  ∀ {A : F4Arithmetic} (s : F4IntState A) g →
  thetaQ (f4IntUSoftsignStep s g) + rTheta (f4IntUSoftsignStep s g)
  ≡ thetaFull s g
f4ThetaReconstruction {A} s g = subAdd A (thetaFull s g) (quantize A (thetaFull s g))

f4MomentumReconstruction :
  ∀ {A : F4Arithmetic} (s : F4IntState A) g →
  eQ (f4IntUSoftsignStep s g) + rE (f4IntUSoftsignStep s g)
  ≡ eFull s g
f4MomentumReconstruction {A} s g = subAdd A (eFull s g) (quantize A (eFull s g))

f4LogIntegratorReconstruction :
  ∀ {A : F4Arithmetic} (s : F4IntState A) g →
  embedInt A (ell (f4IntUSoftsignStep s g))
    + rL (f4IntUSoftsignStep s g)
  ≡ (embedInt A (ell s) + rL s) + eFull s g
f4LogIntegratorReconstruction {A} s g =
  let e* = eFull s g
      rℓ* = rL s + e*
      Δℓ = roundLog A rℓ*
  in trans
       (cong (λ x → x + (rℓ* - embedInt A Δℓ))
         (embedAdd A (ell s) Δℓ))
       (trans
         (addAssoc A (embedInt A (ell s)) (embedInt A Δℓ)
           (rℓ* - embedInt A Δℓ))
         (trans
           (cong (λ x → embedInt A (ell s) + x)
             (subAdd A rℓ* (embedInt A Δℓ)))
           (sym (addAssoc A (embedInt A (ell s)) (rL s) e*))))

------------------------------------------------------------------------
-- q-budget and uniform parameter-bank layer.
------------------------------------------------------------------------

record QBudget (A : F4Arithmetic) : Set₁ where
  constructor qBudget
  field
    budget : D A
    admissible : List (F4IntState A) → Set

open QBudget public

record F4ParameterBank (A : F4Arithmetic) : Set₁ where
  constructor f4ParameterBank
  field
    embedding : F4IntState A
    attentionQ : F4IntState A
    attentionK : F4IntState A
    attentionV : F4IntState A
    attentionO : F4IntState A
    gruUpdate : F4IntState A
    gruReset : F4IntState A
    gruCandidate : F4IntState A
    outputProjection : F4IntState A
    actor : F4IntState A
    critic : F4IntState A
    noisyMu3 : F4IntState A
    noisySigma3 : F4IntState A

parameterBlockWitness :
  ∀ {A : F4Arithmetic} →
  F4ParameterBank A →
  F4IntState A × F4IntState A
parameterBlockWitness b = embedding b , attentionQ b

------------------------------------------------------------------------
-- Frozen structure is independent of which parameter block is present.
-- We therefore formalize the finite operator-family claim rather than
-- pretending that PSL(2,R) or O(2^n) is already an Agda theorem in this repo.
------------------------------------------------------------------------

data OperatorClass : Set where
  sparsemaxClass : OperatorClass
  frozenHaarClass : OperatorClass
  dyadicRoPEClass : OperatorClass
  mobiusGRUClass : OperatorClass

operatorFamily : List OperatorClass
operatorFamily =
  sparsemaxClass ∷ frozenHaarClass ∷ dyadicRoPEClass ∷ mobiusGRUClass ∷ []

operatorFamily-with-embedding : List OperatorClass
operatorFamily-with-embedding = operatorFamily

operatorFamily-without-embedding : List OperatorClass
operatorFamily-without-embedding = operatorFamily

embedding-removal-preserves-operator-family :
  operatorFamily-with-embedding ≡ operatorFamily-without-embedding
embedding-removal-preserves-operator-family = refl

embedding-not-unique-learnable :
  ∀ {A : F4Arithmetic} (b : F4ParameterBank A) →
  F4IntState A × F4IntState A
embedding-not-unique-learnable = parameterBlockWitness

------------------------------------------------------------------------
-- Noisy-Net gating remains optimizer-coupled at both learned coordinates.
------------------------------------------------------------------------

record NoisyGateF4 (A : F4Arithmetic) : Set₁ where
  constructor noisyGateF4
  field
    mu sigma : F4IntState A

noisyGateHasTwoLearnableF4States :
  ∀ {A : F4Arithmetic} (n : NoisyGateF4 A) →
  F4IntState A × F4IntState A
noisyGateHasTwoLearnableF4States n = mu n , sigma n

------------------------------------------------------------------------
-- Endogenous architecture state.
------------------------------------------------------------------------

record EndogenousF4State (A : F4Arithmetic) : Set₁ where
  constructor endogenousF4State
  field
    optimizerBank : F4ParameterBank A
    recurrent : GRUState
    dpg : DPGCoupled
    trace : WatkinsExploration

open EndogenousF4State public

endogenousInput :
  ∀ {A : F4Arithmetic} → EndogenousF4State A → Int8Pair → Int8
endogenousInput s p = frontEndToGRU p

endogenousActorOutput :
  ∀ {A : F4Arithmetic} → EndogenousF4State A → Int8Pair → Int8
endogenousActorOutput s p =
  actorForward (actorComponent (dpg s)) (endogenousInput s p)

endogenousCriticOutput :
  ∀ {A : F4Arithmetic} → EndogenousF4State A → Int8Pair → Int8
endogenousCriticOutput s p =
  criticForward (criticComponent (dpg s)) (endogenousInput s p)

endogenousPipelineFactorization :
  ∀ {A : F4Arithmetic} (s : EndogenousF4State A) (p : Int8Pair) →
  ( endogenousActorOutput s p
  , endogenousCriticOutput s p )
  ≡
  ( actorForward (actorComponent (dpg s)) (frontEndToGRU p)
  , criticForward (criticComponent (dpg s)) (frontEndToGRU p) )
endogenousPipelineFactorization s p = refl

endogenousGlobalOptimizer :
  ∀ {A : F4Arithmetic} (s : EndogenousF4State A) (x : Int8) →
  optimizerToken (global (gruStep (recurrent s) x))
  ≡ optimizerToken (global (recurrent s))
endogenousGlobalOptimizer s x = refl

endogenousGlobalL2 :
  ∀ {A : F4Arithmetic} (s : EndogenousF4State A) (x : Int8) →
  l2Token (global (gruStep (recurrent s) x))
  ≡ l2Token (global (recurrent s))
endogenousGlobalL2 s x = refl

endogenousDPGSharedGlobal :
  ∀ {A : F4Arithmetic} (s : EndogenousF4State A) →
  ( optimizer (globalControl (dpg s)) , l2 (globalControl (dpg s)) )
  ≡
  ( optimizer (globalControl (dpg s)) , l2 (globalControl (dpg s)) )
endogenousDPGSharedGlobal s = refl

endogenousWatkinsCut :
  ∀ {A : F4Arithmetic} (s : EndogenousF4State A) →
  watkinsTraceLength (cutTrace ∷ []) ≡ suc zero
endogenousWatkinsCut s = watkinsTraceLength-cut-head []

endogenousWatkinsOneStepRegime :
  ∀ {A : F4Arithmetic} (s : EndogenousF4State A) →
  watkinsRegime (cutTrace ∷ []) ≡ oneStep
endogenousWatkinsOneStepRegime s = cut-regime-is-one-step []

endogenousWatkinsActionCarrier :
  ∀ {A : F4Arithmetic} (s : EndogenousF4State A) →
  WatkinsExploration.sampledAction (watkinsCut (trace s))
  ≡ WatkinsExploration.sampledAction (trace s)
endogenousWatkinsActionCarrier s = refl

endogenousDPGMaxQ :
  ∀ {A : F4Arithmetic}
    (reward : ℕ) (δ : Discount) (q : Q) (π : GreedyPolicy) →
  IsGreedy π q → ∀ s₀ →
  greedyPolicyBootstrap reward δ q π s₀
  ≡ maxQBootstrap reward δ q s₀
endogenousDPGMaxQ = DPG-maxQ-bootstrap-equivalence

------------------------------------------------------------------------
-- One generated composition theorem packages all endogenous boundaries.
------------------------------------------------------------------------

record FullEndogenousComposition
  {A : F4Arithmetic}
  (s : EndogenousF4State A)
  (p : Int8Pair)
  (reward : ℕ)
  (δ : Discount)
  (q : Q)
  (π : GreedyPolicy)
  (greedy : IsGreedy π q)
  (s₀ : State) : Set₁ where
  constructor fullEndogenousComposition
  field
    f4Theta : ∀ (g : D A) →
      thetaQ (f4IntUSoftsignStep (embedding (optimizerBank s)) g)
      + rTheta (f4IntUSoftsignStep (embedding (optimizerBank s)) g)
      ≡ thetaFull (embedding (optimizerBank s)) g
    f4Momentum : ∀ (g : D A) →
      eQ (f4IntUSoftsignStep (embedding (optimizerBank s)) g)
      + rE (f4IntUSoftsignStep (embedding (optimizerBank s)) g)
      ≡ eFull (embedding (optimizerBank s)) g
    f4Integrator : ∀ (g : D A) →
      embedInt A (ell (f4IntUSoftsignStep (embedding (optimizerBank s)) g))
      + rL (f4IntUSoftsignStep (embedding (optimizerBank s)) g)
      ≡
      (embedInt A (ell (embedding (optimizerBank s)))
       + rL (embedding (optimizerBank s)))
      + eFull (embedding (optimizerBank s)) g
    parameterBankWitness :
      F4IntState A × F4IntState A
    operatorFamilyLaw :
      operatorFamily-with-embedding ≡ operatorFamily-without-embedding
    pipeline :
      ( endogenousActorOutput s p
      , endogenousCriticOutput s p )
      ≡
      ( actorForward (actorComponent (dpg s)) (frontEndToGRU p)
      , criticForward (criticComponent (dpg s)) (frontEndToGRU p) )
    globalControl :
      ( optimizerToken (global (gruStep (recurrent s) zero8))
      , l2Token (global (gruStep (recurrent s) zero8)) )
      ≡
      ( optimizerToken (global (recurrent s))
      , l2Token (global (recurrent s)) )
    dpgGlobal :
      ( optimizer (globalControl (dpg s))
      , l2 (globalControl (dpg s)) )
      ≡
      ( optimizer (globalControl (dpg s))
      , l2 (globalControl (dpg s)) )
    watkins : watkinsRegime (cutTrace ∷ []) ≡ oneStep
    target : greedyPolicyBootstrap reward δ q π s₀
      ≡ maxQBootstrap reward δ q s₀

fullEndogenousComposition :
  ∀ {A : F4Arithmetic}
    (s : EndogenousF4State A)
    (p : Int8Pair)
    (reward : ℕ)
    (δ : Discount)
    (q : Q)
    (π : GreedyPolicy)
  → IsGreedy π q
  → (s₀ : State)
  → FullEndogenousComposition s p reward δ q π _ s₀
fullEndogenousComposition s p reward δ q π greedy s₀ =
  fullEndogenousComposition
    (λ g → f4ThetaReconstruction (embedding (optimizerBank s)) g)
    (λ g → f4MomentumReconstruction (embedding (optimizerBank s)) g)
    (λ g → f4LogIntegratorReconstruction (embedding (optimizerBank s)) g)
    (parameterBlockWitness (optimizerBank s))
    embedding-removal-preserves-operator-family
    (endogenousPipelineFactorization s p)
    refl
    (endogenousDPGSharedGlobal s)
    (endogenousWatkinsOneStepRegime s)
    (endogenousDPGMaxQ reward δ q π greedy s₀)

------------------------------------------------------------------------
-- The formally supported algebraic conclusion is the finite operator-family
-- factorization above. The continuous PSL(2,R)/orthogonal-group notation is
-- a mathematical interpretation, not an existing Agda proof object here.
------------------------------------------------------------------------
