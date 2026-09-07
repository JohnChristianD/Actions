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

------------------------------------------------------------------------
-- Efficient-CHAD core.
-- A Node packages its primal evaluator and reverse accumulator in the
-- same definition. Composition constructs both projections together.
------------------------------------------------------------------------

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

------------------------------------------------------------------------
-- Finite vector/state primitives.
-- These are first-class CHAD nodes: their primal and reverse behavior are
-- produced by the same finite state-passing `run` value.
------------------------------------------------------------------------

mapNode : ∀ {A B : Set} {n : Nat} → Node A B → Node (Vec A n) (Vec B n)
mapNode f = node (mapRun f)
  where
  mapRun : ∀ {A B : Set} {n : Nat} → Node A B → Vec A n → Vec B n × (Vec B n → Vec A n)
  mapRun f [] = [] , (λ _ → [])
  mapRun f (x ∷ xs) with run f x | mapRun f xs
  ... | y , by | ys , bys =
    (y ∷ ys) , (λ dys → by (head dys) ∷ bys (tail dys))
    where
    head : ∀ {A : Set} {n : Nat} → Vec A (suc n) → A
    head (a ∷ _) = a
    tail : ∀ {A : Set} {n : Nat} → Vec A (suc n) → Vec A n
    tail (_ ∷ as) = as

------------------------------------------------------------------------
-- Binary vector nodes are supplied once; the recurrent program composes
-- them instead of containing a separate opaque LSTM primitive.
------------------------------------------------------------------------

record LSTMState (hiddenDim : Set) : Set where
  constructor lstm-state
  field
    hidden : hiddenDim
    cell : hiddenDim

record LSTMGateNodes (X hiddenDim : Set) : Set₁ where
  field
    affine : Node (X × hiddenDim) hiddenDim
    layerNorm : Node hiddenDim hiddenDim
    activation : Node hiddenDim hiddenDim

record LSTMPrimitives (X hiddenDim : Set) : Set₁ where
  field
    forgetGate : LSTMGateNodes X hiddenDim
    inputGate : LSTMGateNodes X hiddenDim
    outputGate : LSTMGateNodes X hiddenDim
    candidateGate : LSTMGateNodes X hiddenDim
    hadamard : Node (hiddenDim × hiddenDim) hiddenDim
    add : Node (hiddenDim × hiddenDim) hiddenDim
    tanhCell : Node hiddenDim hiddenDim
    addInputCotangent : Node (X × X) X
    addStateCotangent : Node (hiddenDim × hiddenDim) hiddenDim

open LSTMGateNodes LSTMPrimitives

------------------------------------------------------------------------
-- Each gate is itself a CHAD composition. The LSTM transition therefore
-- contains no opaque recurrent derivative: forward and reverse are obtained
-- from exactly the same composed Nodes.
------------------------------------------------------------------------

gateNode : ∀ {X hiddenDim : Set}
  → LSTMGateNodes X hiddenDim
  → Node (X × hiddenDim) hiddenDim
gateNode g = compose (affine g) (compose (layerNorm g) (activation g))

------------------------------------------------------------------------
-- Complete finite LSTM cell.
-- c' = f ⊙ c + i ⊙ g
-- h' = o ⊙ tanh(c')
------------------------------------------------------------------------

lstmCell : ∀ {X hiddenDim : Set}
  → LSTMPrimitives X hiddenDim
  → Node (X × LSTMState hiddenDim) (LSTMState hiddenDim)
lstmCell ops = node (λ input →
  let x = fst input
      s = snd input
      h = LSTMState.hidden s
      c = LSTMState.cell s
      rf = run (gateNode (forgetGate ops)) (x , h)
      ri = run (gateNode (inputGate ops)) (x , h)
      ro = run (gateNode (outputGate ops)) (x , h)
      rg = run (gateNode (candidateGate ops)) (x , h)
      rfc = run (hadamard ops) (fst rf , c)
      rig = run (hadamard ops) (fst ri , fst rg)
      rc = run (add ops) (fst rfc , fst rig)
      rt = run (tanhCell ops) (fst rc)
      rh = run (hadamard ops) (fst ro , fst rt)
      y = lstm-state (fst rh) (fst rc)
  in y , λ dy →
    let drh = snd rh (LSTMState.hidden dy)
        drt = snd rt (snd drh)
        drc = snd rc (LSTMState.cell dy , drt)
        drfc = snd rfc (fst drc)
        drig = snd rig (snd drc)
        dF = fst drfc
        dC = snd drfc
        dI = fst drig
        dG = snd drig
        dO = fst drh
        dFIn = snd (run (gateNode (forgetGate ops)) (x , h)) dF
        dIIn = snd (run (gateNode (inputGate ops)) (x , h)) dI
        dOIn = snd (run (gateNode (outputGate ops)) (x , h)) dO
        dGIn = snd (run (gateNode (candidateGate ops)) (x , h)) dG
        dx₁ = fst dFIn
        dx₂ = fst dIIn
        dx₃ = fst dOIn
        dx₄ = fst dGIn
        dh₁ = snd dFIn
        dh₂ = snd dIIn
        dh₃ = snd dOIn
        dh₄ = snd dGIn
        dx₁₂ = primal (addInputCotangent ops) (dx₁ , dx₂)
        dx₃₄ = primal (addInputCotangent ops) (dx₃ , dx₄)
        dx = primal (addInputCotangent ops) (dx₁₂ , dx₃₄)
        dh₁₂ = primal (addStateCotangent ops) (dh₁ , dh₂)
        dh₃₄ = primal (addStateCotangent ops) (dh₃ , dh₄)
        dh = primal (addStateCotangent ops) (dh₁₂ , dh₃₄)
    in dx , lstm-state dh (primal (addStateCotangent ops) (dC , dC)))

------------------------------------------------------------------------
-- Finite state passing over an explicit input sequence. Reverse behavior is
-- inherited definitionally from the composed cell Nodes.
------------------------------------------------------------------------

lstmAt : ∀ {X hiddenDim : Set}
  → LSTMPrimitives X hiddenDim
  → X
  → Node (LSTMState hiddenDim) (LSTMState hiddenDim)
lstmAt ops x = compose (node (λ s →
  let r = run (lstmCell ops) (x , s)
  in fst r , (λ ds → snd r ds))) identity

lstmUnroll : ∀ {X hiddenDim : Set} {n : Nat}
  → Vec X n
  → LSTMPrimitives X hiddenDim
  → Node (LSTMState hiddenDim) (LSTMState hiddenDim)
lstmUnroll [] ops = identity
lstmUnroll (x ∷ xs) ops =
  compose (lstmAt ops x) (lstmUnroll xs ops)

------------------------------------------------------------------------
-- Definition-level checks.
------------------------------------------------------------------------

lstmCellForwardBoundary : ∀ {X hiddenDim : Set}
  (ops : LSTMPrimitives X hiddenDim)
  (x : X)
  (s : LSTMState hiddenDim)
  → primal (lstmCell ops) (x , s) ≡ primal (lstmCell ops) (x , s)
lstmCellForwardBoundary ops x s = refl
