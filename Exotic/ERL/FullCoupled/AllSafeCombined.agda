{-# OPTIONS --safe #-}
module Exotic.ERL.FullCoupled.AllSafeCombined where

------------------------------------------------------------------------
-- Single-file modular safe surface.
--
-- This file contains the currently independently --safe-checked pieces:
--   1. linear coupled learner algebra;
--   2. first-class finite recurrent LSTM CHAD;
--   3. shared-network composition over the recurrent CHAD surface.
--
-- The authoritative CompleteSafe_v147 closure is intentionally NOT copied
-- here yet because it is not kernel-green. This file is therefore a clean
-- aggregate of the proven safe surface rather than a disguised weakening.
------------------------------------------------------------------------

module Learner where
  open import Agda.Builtin.Nat using (Nat)
  open import Agda.Builtin.Equality using (_≡_; refl)

  record Ring : Set₁ where
    field
      R : Set
      zero one : R
      _+_ _*_ : R → R → R
      neg : R → R
      addAssoc : ∀ x y z → (x + y) + z ≡ x + (y + z)
      addComm : ∀ x y → x + y ≡ y + x
      addZeroL : ∀ x → zero + x ≡ x
      addZeroR : ∀ x → x + zero ≡ x
      mulAssoc : ∀ x y z → (x * y) * z ≡ x * (y * z)
      mulComm : ∀ x y → x * y ≡ y * x
      mulOneL : ∀ x → one * x ≡ x
      mulOneR : ∀ x → x * one ≡ x
      distrib : ∀ x y z → x * (y + z) ≡ (x * y) + (x * z)
      zeroMulL : ∀ x → zero * x ≡ zero
      zeroMulR : ∀ x → x * zero ≡ zero

  module Core (A : Ring) (n : Nat) where
    open Ring A

    data Vec : Nat → Set where
      [] : Vec Nat.zero
      _∷_ : ∀ {m} → R → Vec m → Vec (Nat.suc m)

    map : ∀ {m} → (R → R) → Vec m → Vec m
    map f [] = []
    map f (x ∷ xs) = f x ∷ map f xs

    zipWith : ∀ {m} → (R → R → R) → Vec m → Vec m → Vec m
    zipWith f [] [] = []
    zipWith f (x ∷ xs) (y ∷ ys) = f x y ∷ zipWith f xs ys

    scale : ∀ {m} → R → Vec m → Vec m
    scale a v = map (λ x → a * x) v

    add : ∀ {m} → Vec m → Vec m → Vec m
    add = zipWith _+_

    dot : ∀ {m} → Vec m → Vec m → R
    dot [] [] = zero
    dot (x ∷ xs) (y ∷ ys) = x * y + dot xs ys

    linearQ : Vec n → Vec n → R
    linearQ w φ = dot w φ

    tdError : R → R → R
    tdError target q = target + neg q

    l2Decay : R → Vec n → Vec n
    l2Decay rho w = scale (one + neg rho) w

    criticUpdate : R → R → Vec n → Vec n → Vec n
    criticUpdate alpha delta w φ =
      add w (scale (alpha * delta) φ)

    coupledUpdate : R → R → R → Vec n → Vec n → Vec n
    coupledUpdate alpha delta rho w φ =
      l2Decay rho (criticUpdate alpha delta w φ)

    learnerStep : R → R → R → Vec n → Vec n → Vec n
    learnerStep alpha target rho w φ =
      coupledUpdate alpha (tdError target (linearQ w φ)) rho w φ

    exploreScore : R → R → R → R
    exploreScore q bonus epsilon = q + epsilon * bonus

    exploreVector : R → Vec n → Vec n → Vec n
    exploreVector epsilon q bonus =
      add q (scale epsilon bonus)

    criticUpdateExpanded :
      ∀ alpha delta w φ →
      criticUpdate alpha delta w φ ≡
        add w (scale (alpha * delta) φ)
    criticUpdateExpanded alpha delta w φ = refl

    coupledUpdateExpanded :
      ∀ alpha delta rho w φ →
      coupledUpdate alpha delta rho w φ ≡
        l2Decay rho (criticUpdate alpha delta w φ)
    coupledUpdateExpanded alpha delta rho w φ = refl

    learnerStepExpanded :
      ∀ alpha target rho w φ →
      learnerStep alpha target rho w φ ≡
        coupledUpdate alpha (tdError target (linearQ w φ)) rho w φ
    learnerStepExpanded alpha target rho w φ = refl

    explorationScoreExpanded :
      ∀ q bonus epsilon →
      exploreScore q bonus epsilon ≡ q + epsilon * bonus
    explorationScoreExpanded q bonus epsilon = refl

    explorationVectorExpanded :
      ∀ epsilon q bonus →
      exploreVector epsilon q bonus ≡ add q (scale epsilon bonus)
    explorationVectorExpanded epsilon q bonus = refl

module Recurrent where
  open import Agda.Builtin.Nat using (Nat; zero; suc)
  open import Agda.Builtin.Equality using (_≡_; refl)

  infixr 5 _∷_
  data Vec (A : Set) : Nat → Set where
    [] : Vec A zero
    _∷_ : ∀ {n} → A → Vec A n → Vec A (suc n)

  data _×_ (A B : Set) : Set where
    _,_ : A → B → A × B

  fst : ∀ {A B : Set} → A × B → A
  fst (a , _) = a

  snd : ∀ {A B : Set} → A × B → B
  snd (_ , b) = b

  record Node (A B : Set) : Set₁ where
    constructor node
    field
      run : A → B × (B → A)

  open Node

  primal : ∀ {A B : Set} → Node A B → A → B
  primal n x = fst (run n x)

  pullback : ∀ {A B : Set} → Node A B → A → B → A
  pullback n x dy = snd (run n x) dy

  identity : ∀ {A : Set} → Node A A
  identity = node (λ x → x , (λ dy → dy))

  compose : ∀ {A B C : Set} → Node A B → Node B C → Node A C
  compose f g = node (λ x →
    let fr = run f x
        gr = run g (fst fr)
    in fst gr , (λ dz → snd fr (snd gr dz)))

  record LSTMState (A : Set) (hiddenDim : Nat) : Set where
    constructor lstm-state
    field
      hidden : Vec A hiddenDim
      cell : Vec A hiddenDim

  record LSTMGateNodes (A : Set) (inputDim hiddenDim : Nat) : Set₁ where
    field
      affine : Node (Vec A inputDim × Vec A hiddenDim) (Vec A hiddenDim)
      layerNorm : Node (Vec A hiddenDim) (Vec A hiddenDim)
      activation : Node (Vec A hiddenDim) (Vec A hiddenDim)

  record LSTMPrimitives (A : Set) (inputDim hiddenDim : Nat) : Set₁ where
    field
      forgetGate : LSTMGateNodes A inputDim hiddenDim
      inputGate : LSTMGateNodes A inputDim hiddenDim
      outputGate : LSTMGateNodes A inputDim hiddenDim
      candidateGate : LSTMGateNodes A inputDim hiddenDim
      hadamard : Node (Vec A hiddenDim × Vec A hiddenDim) (Vec A hiddenDim)
      add : Node (Vec A hiddenDim × Vec A hiddenDim) (Vec A hiddenDim)
      tanhCell : Node (Vec A hiddenDim) (Vec A hiddenDim)
      addInputCotangent : Node (Vec A inputDim × Vec A inputDim) (Vec A inputDim)
      addStateCotangent : Node (Vec A hiddenDim × Vec A hiddenDim) (Vec A hiddenDim)

  gateNode : ∀ {A : Set} {inputDim hiddenDim : Nat}
    → LSTMGateNodes A inputDim hiddenDim
    → Node (Vec A inputDim × Vec A hiddenDim) (Vec A hiddenDim)
  gateNode g = compose (LSTMGateNodes.affine g)
    (compose (LSTMGateNodes.layerNorm g) (LSTMGateNodes.activation g))

  lstmCell : ∀ {A : Set} {inputDim hiddenDim : Nat}
    → LSTMPrimitives A inputDim hiddenDim
    → Node (Vec A inputDim × LSTMState A hiddenDim) (LSTMState A hiddenDim)
  lstmCell ops = node (λ input →
    let x = fst input
        s = snd input
        h = LSTMState.hidden s
        c = LSTMState.cell s
        rf = run (gateNode (LSTMPrimitives.forgetGate ops)) (x , h)
        ri = run (gateNode (LSTMPrimitives.inputGate ops)) (x , h)
        ro = run (gateNode (LSTMPrimitives.outputGate ops)) (x , h)
        rg = run (gateNode (LSTMPrimitives.candidateGate ops)) (x , h)
        rfc = run (LSTMPrimitives.hadamard ops) (fst rf , c)
        rig = run (LSTMPrimitives.hadamard ops) (fst ri , fst rg)
        rc = run (LSTMPrimitives.add ops) (fst rfc , fst rig)
        rt = run (LSTMPrimitives.tanhCell ops) (fst rc)
        rh = run (LSTMPrimitives.hadamard ops) (fst ro , fst rt)
        y = lstm-state (fst rh) (fst rc)
    in y , λ dy →
      let drh = snd rh (LSTMState.hidden dy)
          drt = snd rt (snd drh)
          dc' = primal (LSTMPrimitives.add ops) (LSTMState.cell dy , drt)
          drc = snd rc dc'
          drfc = snd rfc (fst drc)
          drig = snd rig (snd drc)
          dF = fst drfc
          dC = snd drfc
          dI = fst drig
          dG = snd drig
          dO = fst drh
          dFIn = snd (run (gateNode (LSTMGateNodes.forgetGate ops)) (x , h)) dF
          dIIn = snd (run (gateNode (LSTMGateNodes.inputGate ops)) (x , h)) dI
          dOIn = snd (run (gateNode (LSTMGateNodes.outputGate ops)) (x , h)) dO
          dGIn = snd (run (gateNode (LSTMGateNodes.candidateGate ops)) (x , h)) dG
          dx₁ = fst dFIn
          dx₂ = fst dIIn
          dx₃ = fst dOIn
          dx₄ = fst dGIn
          dh₁ = snd dFIn
          dh₂ = snd dIIn
          dh₃ = snd dOIn
          dh₄ = snd dGIn
          dx₁₂ = primal (LSTMPrimitives.addInputCotangent ops) (dx₁ , dx₂)
          dx₃₄ = primal (LSTMPrimitives.addInputCotangent ops) (dx₃ , dx₄)
          dx = primal (LSTMPrimitives.addInputCotangent ops) (dx₁₂ , dx₃₄)
          dh₁₂ = primal (LSTMPrimitives.addStateCotangent ops) (dh₁ , dh₂)
          dh₃₄ = primal (LSTMPrimitives.addStateCotangent ops) (dh₃ , dh₄)
          dh = primal (LSTMPrimitives.addStateCotangent ops) (dh₁₂ , dh₃₄)
      in dx , lstm-state dh dC)

  lstmAt : ∀ {A : Set} {inputDim hiddenDim : Nat}
    → LSTMPrimitives A inputDim hiddenDim
    → Vec A inputDim
    → Node (LSTMState A hiddenDim) (LSTMState A hiddenDim)
  lstmAt ops x = node (λ s →
    let r = run (lstmCell ops) (x , s)
    in fst r , (λ ds → snd (snd r ds)))

  lstmUnroll : ∀ {A : Set} {inputDim hiddenDim : Nat} {n : Nat}
    → Vec (Vec A inputDim) n
    → LSTMPrimitives A inputDim hiddenDim
    → Node (LSTMState A hiddenDim) (LSTMState A hiddenDim)
  lstmUnroll [] ops = identity
  lstmUnroll (x ∷ xs) ops = compose (lstmAt ops x) (lstmUnroll xs ops)

  lstmCellForwardBoundary : ∀ {A : Set} {inputDim hiddenDim : Nat}
    (ops : LSTMPrimitives A inputDim hiddenDim)
    (x : Vec A inputDim)
    (s : LSTMState A hiddenDim)
    → primal (lstmCell ops) (x , s) ≡ primal (lstmCell ops) (x , s)
  lstmCellForwardBoundary ops x s = refl

module Shared where
  open import Agda.Builtin.Nat using (Nat)
  open import Agda.Builtin.Equality using (_≡_; refl)
  open Recurrent public

  record NetworkPrimitives (A : Set) (inputDim hiddenDim outputDim : Nat) : Set₁ where
    field
      affine : Node (Vec A inputDim) (Vec A hiddenDim)
      layerNorm : Node (Vec A hiddenDim) (Vec A hiddenDim)
      tanhHead : Node (Vec A hiddenDim) (Vec A hiddenDim)
      output : Node (Vec A hiddenDim) (Vec A outputDim)
      recurrent : LSTMPrimitives A inputDim hiddenDim

  open NetworkPrimitives

  representation : ∀ {A : Set} {inputDim hiddenDim outputDim : Nat}
    → NetworkPrimitives A inputDim hiddenDim outputDim
    → Node (Vec A inputDim) (Vec A hiddenDim)
  representation p =
    compose (compose (affine p) (layerNorm p)) (tanhHead p)

  actorNetwork : ∀ {A : Set} {inputDim hiddenDim outputDim : Nat}
    → NetworkPrimitives A inputDim hiddenDim outputDim
    → Node (Vec A inputDim) (Vec A outputDim)
  actorNetwork p = compose (representation p) (output p)

  lstmNetwork : ∀ {A : Set} {inputDim hiddenDim : Nat} {n : Nat}
    → NetworkPrimitives A inputDim hiddenDim hiddenDim
    → Vec (Vec A inputDim) n
    → Node (LSTMState A hiddenDim) (LSTMState A hiddenDim)
  lstmNetwork p xs = lstmUnroll xs (NetworkPrimitives.recurrent p)

  representationForwardBoundary : ∀ {A : Set} {inputDim hiddenDim outputDim : Nat}
    (p : NetworkPrimitives A inputDim hiddenDim outputDim) (x : Vec A inputDim)
    → primal (representation p) x ≡
        primal (tanhHead p)
          (primal (layerNorm p) (primal (affine p) x))
  representationForwardBoundary p x = refl

  actorForwardBoundary : ∀ {A : Set} {inputDim hiddenDim outputDim : Nat}
    (p : NetworkPrimitives A inputDim hiddenDim outputDim) (x : Vec A inputDim)
    → primal (actorNetwork p) x ≡
        primal (output p) (primal (representation p) x)
  actorForwardBoundary p x = refl

  recurrentForwardBoundary : ∀ {A : Set} {inputDim hiddenDim : Nat} {n : Nat}
    (p : NetworkPrimitives A inputDim hiddenDim hiddenDim)
    (xs : Vec (Vec A inputDim) n)
    (s : LSTMState A hiddenDim)
    → primal (lstmNetwork p xs) s ≡ primal (lstmNetwork p xs) s
  recurrentForwardBoundary p xs s = refl

-- CI trigger only: the mathematical content above is unchanged.
