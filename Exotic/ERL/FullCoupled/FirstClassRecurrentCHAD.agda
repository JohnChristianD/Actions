{-# OPTIONS --safe #-}
module Exotic.ERL.FullCoupled.FirstClassRecurrentCHAD where

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
  → Node
      (Vec A inputDim × LSTMState A hiddenDim)
      (LSTMState A hiddenDim)
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
        dFIn = snd (run (gateNode (LSTMPrimitives.forgetGate ops)) (x , h)) dF
        dIIn = snd (run (gateNode (LSTMPrimitives.inputGate ops)) (x , h)) dI
        dOIn = snd (run (gateNode (LSTMPrimitives.outputGate ops)) (x , h)) dO
        dGIn = snd (run (gateNode (LSTMPrimitives.candidateGate ops)) (x , h)) dG
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
