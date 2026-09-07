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
    primal : A → B
    pullback : A → B → A

open Node

identity : ∀ {A : Set} → Node A A
identity = node (λ x → x) (λ _ dy → dy)

compose : ∀ {A B C : Set} → Node A B → Node B C → Node A C
compose f g = node
  (λ x → primal g (primal f x))
  (λ x dz → pullback f x (pullback g (primal f x) dz))

record LSTMState (hiddenDim : Set) : Set where
  constructor lstm-state
  field
    hidden : hiddenDim
    cell : hiddenDim

record LSTMGateNodes (X hiddenDim : Set) : Set₁ where
  field
    affine : Node (X × hiddenDim) hiddenDim
    layerNorm : Node hiddenDim hiddenDim

record LSTMNodes (X hiddenDim : Set) : Set₁ where
  field
    forgetGate : LSTMGateNodes X hiddenDim
    inputGate : LSTMGateNodes X hiddenDim
    outputGate : LSTMGateNodes X hiddenDim
    candidateGate : LSTMGateNodes X hiddenDim
    sigmoidH : Node hiddenDim hiddenDim
    tanhH : Node hiddenDim hiddenDim
    hadamardH : Node (hiddenDim × hiddenDim) hiddenDim
    addH : Node (hiddenDim × hiddenDim) hiddenDim
    addX : Node (X × X) X

open LSTMGateNodes LSTMNodes

gateSigmoid : ∀ {X hiddenDim : Set}
  → LSTMGateNodes X hiddenDim
  → LSTMNodes X hiddenDim
  → Node (X × hiddenDim) hiddenDim
gateSigmoid g ops =
  compose (LSTMGateNodes.affine g)
    (compose (LSTMGateNodes.layerNorm g) (LSTMNodes.sigmoidH ops))

gateTanh : ∀ {X hiddenDim : Set}
  → LSTMGateNodes X hiddenDim
  → LSTMNodes X hiddenDim
  → Node (X × hiddenDim) hiddenDim
gateTanh g ops =
  compose (LSTMGateNodes.affine g)
    (compose (LSTMGateNodes.layerNorm g) (LSTMNodes.tanhH ops))

lstmCell : ∀ {X hiddenDim : Set}
  → LSTMNodes X hiddenDim
  → Node (X × LSTMState hiddenDim) (LSTMState hiddenDim)
lstmCell {X} {hiddenDim} ops = node forward reverse
  where
  forward : X × LSTMState hiddenDim → LSTMState hiddenDim
  forward input =
    let x = fst input
        s = snd input
        h = LSTMState.hidden s
        c = LSTMState.cell s
        f = primal (gateSigmoid (LSTMNodes.forgetGate ops) ops) (x , h)
        i = primal (gateSigmoid (LSTMNodes.inputGate ops) ops) (x , h)
        o = primal (gateSigmoid (LSTMNodes.outputGate ops) ops) (x , h)
        g = primal (gateTanh (LSTMNodes.candidateGate ops) ops) (x , h)
        fc = primal (LSTMNodes.hadamardH ops) (f , c)
        ig = primal (LSTMNodes.hadamardH ops) (i , g)
        c' = primal (LSTMNodes.addH ops) (fc , ig)
        tc = primal (LSTMNodes.tanhH ops) c'
        h' = primal (LSTMNodes.hadamardH ops) (o , tc)
    in lstm-state h' c'

  reverse : X × LSTMState hiddenDim → LSTMState hiddenDim → X × LSTMState hiddenDim
  reverse input dy =
    let x = fst input
        s = snd input
        h = LSTMState.hidden s
        c = LSTMState.cell s
        fN = gateSigmoid (LSTMNodes.forgetGate ops) ops
        iN = gateSigmoid (LSTMNodes.inputGate ops) ops
        oN = gateSigmoid (LSTMNodes.outputGate ops) ops
        gN = gateTanh (LSTMNodes.candidateGate ops) ops
        f = primal fN (x , h)
        i = primal iN (x , h)
        o = primal oN (x , h)
        g = primal gN (x , h)
        fcN = LSTMNodes.hadamardH ops
        igN = LSTMNodes.hadamardH ops
        addN = LSTMNodes.addH ops
        fc = primal fcN (f , c)
        ig = primal igN (i , g)
        c' = primal addN (fc , ig)
        tcN = LSTMNodes.tanhH ops
        tc = primal tcN c'
        hN = LSTMNodes.hadamardH ops
        dRh = pullback hN (o , tc) (LSTMState.hidden dy)
        dTc = pullback tcN c' (snd dRh)
        dC' = pullback addN (fc , ig)
          (primal addN (LSTMState.cell dy , dTc))
        dFc = pullback fcN (f , c) (fst dC')
        dIg = pullback igN (i , g) (snd dC')
        dF = fst dFc
        dC = snd dFc
        dI = fst dIg
        dG = snd dIg
        dO = fst dRh
        dFIn = pullback fN (x , h) dF
        dIIn = pullback iN (x , h) dI
        dOIn = pullback oN (x , h) dO
        dGIn = pullback gN (x , h) dG
        dX1 = fst dFIn
        dX2 = fst dIIn
        dX3 = fst dOIn
        dX4 = fst dGIn
        dH1 = snd dFIn
        dH2 = snd dIIn
        dH3 = snd dOIn
        dH4 = snd dGIn
        dX12 = primal (LSTMNodes.addX ops) (dX1 , dX2)
        dX34 = primal (LSTMNodes.addX ops) (dX3 , dX4)
        dX = primal (LSTMNodes.addX ops) (dX12 , dX34)
        dH12 = primal (LSTMNodes.addH ops) (dH1 , dH2)
        dH34 = primal (LSTMNodes.addH ops) (dH3 , dH4)
        dH = primal (LSTMNodes.addH ops) (dH12 , dH34)
    in dX , lstm-state dH dC

lstmAt : ∀ {X hiddenDim : Set}
  → LSTMNodes X hiddenDim
  → X
  → Node (LSTMState hiddenDim) (LSTMState hiddenDim)
lstmAt ops x = node
  (λ s → primal (lstmCell ops) (x , s))
  (λ s ds → snd (pullback (lstmCell ops) (x , s) ds))

lstmUnroll : ∀ {X hiddenDim : Set} {n : Nat}
  → Vec X n
  → LSTMNodes X hiddenDim
  → Node (LSTMState hiddenDim) (LSTMState hiddenDim)
lstmUnroll [] ops = identity
lstmUnroll (x ∷ xs) ops = compose (lstmAt ops x) (lstmUnroll xs ops)

lstmCellBoundary : ∀ {X hiddenDim : Set}
  (ops : LSTMNodes X hiddenDim)
  (x : X)
  (s : LSTMState hiddenDim)
  → primal (lstmCell ops) (x , s) ≡ primal (lstmCell ops) (x , s)
lstmCellBoundary ops x s = refl
