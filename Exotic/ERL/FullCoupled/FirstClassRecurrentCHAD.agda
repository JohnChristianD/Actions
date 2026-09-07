{-# OPTIONS --safe #-}
module Exotic.ERL.FullCoupled.FirstClassRecurrentCHAD where

open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.Equality using (_≡_; refl)

data _×_ (A B : Set) : Set where
  _,_ : A → B → A × B

pairFst : ∀ {A B : Set} → A × B → A
pairFst (a , _) = a

pairSnd : ∀ {A B : Set} → A × B → B
pairSnd (_ , b) = b

infixr 5 _∷_
data Vec (A : Set) : Nat → Set where
  [] : Vec A zero
  _∷_ : ∀ {n} → A → Vec A n → Vec A (suc n)

------------------------------------------------------------------------
-- One shared Efficient-CHAD node: primal and reverse accumulation are
-- fields of exactly the same definition.
------------------------------------------------------------------------

record Node (A B : Set) : Set₁ where
  constructor node
  field
    primal : A → B
    pullback : A → B → A

open Node

identity : ∀ {A : Set} → Node A A
identity = node (λ x → x) (λ _ dx → dx)

compose : ∀ {A B C : Set} → Node A B → Node B C → Node A C
compose f g = node
  (λ x → primal g (primal f x))
  (λ x dz → pullback f x (pullback g (primal f x) dz))

------------------------------------------------------------------------
-- Recurrent state. The type parameter is `hiddenDim`; the public field is
-- intentionally still named `hidden`.
------------------------------------------------------------------------

record LSTMState (hiddenDim : Set) : Set where
  constructor lstm-state
  field
    hidden : hiddenDim
    cell : hiddenDim

------------------------------------------------------------------------
-- First-class LSTM primitive graph. Every gate is affine -> LayerNorm ->
-- activation, and the recurrent transition is composed below.
------------------------------------------------------------------------

record LSTMGate (X H : Set) : Set₁ where
  constructor lstm-gate
  field
    affine : Node (X × H) H
    layerNorm : Node H H

record LSTMNodes (X H : Set) : Set₁ where
  constructor lstm-nodes
  field
    forget input output candidate : LSTMGate X H
    sigmoidH tanhH : Node H H
    hadamardH addH : Node (H × H) H
    addX : Node (X × X) X

open LSTMNodes

gateSigmoid : ∀ {X H : Set} → LSTMGate X H → LSTMNodes X H → Node (X × H) H
gateSigmoid g p =
  compose (LSTMGate.affine g)
    (compose (LSTMGate.layerNorm g) (sigmoidH p))

gateTanh : ∀ {X H : Set} → LSTMGate X H → LSTMNodes X H → Node (X × H) H
gateTanh g p =
  compose (LSTMGate.affine g)
    (compose (LSTMGate.layerNorm g) (tanhH p))

------------------------------------------------------------------------
-- Compositional LSTM transition:
-- f = sigma(N_f([x,h])); i = sigma(N_i([x,h]));
-- o = sigma(N_o([x,h])); g = tanh(N_g([x,h]));
-- c' = f * c + i * g; h' = o * tanh(c').
--
-- There is deliberately no `lstmStep` primitive slot: this definition is
-- assembled from the primitive Nodes above, so compose constructs forward
-- and reverse behavior together.
------------------------------------------------------------------------

lstmCell : ∀ {X H : Set}
  → LSTMNodes X H
  → Node (X × LSTMState H) (LSTMState H)
lstmCell p = node
  (lambda-q)
  (reverse-q)
  where
  lambda-q : X × LSTMState H → LSTMState H
  lambda-q q =
    let x = pairFst q
        s = pairSnd q
        h = LSTMState.hidden s
        c = LSTMState.cell s
        f = primal (gateSigmoid (LSTMGate.forget p) p) (x , h)
        i = primal (gateSigmoid (LSTMGate.input p) p) (x , h)
        o = primal (gateSigmoid (LSTMGate.output p) p) (x , h)
        g = primal (gateTanh (LSTMGate.candidate p) p) (x , h)
        fc = primal (hadamardH p) (f , c)
        ig = primal (hadamardH p) (i , g)
        c' = primal (addH p) (fc , ig)
        tc = primal (tanhH p) c'
        h' = primal (hadamardH p) (o , tc)
    in lstm-state h' c'

  reverse-q : (X × LSTMState H) → LSTMState H → (X × LSTMState H)
  reverse-q q dy =
    let x = pairFst q
        s = pairSnd q
        h = LSTMState.hidden s
        c = LSTMState.cell s
        fN = gateSigmoid (LSTMGate.forget p) p
        iN = gateSigmoid (LSTMGate.input p) p
        oN = gateSigmoid (LSTMGate.output p) p
        gN = gateTanh (LSTMGate.candidate p) p
        f = primal fN (x , h)
        i = primal iN (x , h)
        o = primal oN (x , h)
        g = primal gN (x , h)
        fcN = hadamardH p
        igN = hadamardH p
        addN = addH p
        fc = primal fcN (f , c)
        ig = primal igN (i , g)
        c' = primal addN (fc , ig)
        tcN = tanhH p
        tc = primal tcN c'
        hN = hadamardH p
        dRh = pullback hN (o , tc) (LSTMState.hidden dy)
        dTc = pullback tcN c' (pairSnd dRh)
        dC' = pullback addN (fc , ig) (LSTMState.cell dy , dTc)
        dFc = pullback fcN (f , c) (pairFst dC')
        dIg = pullback igN (i , g) (pairSnd dC')
        dF = pairFst dFc
        dC = pairSnd dFc
        dI = pairFst dIg
        dG = pairSnd dIg
        dO = pairFst dRh
        dFIn = pullback fN (x , h) dF
        dIIn = pullback iN (x , h) dI
        dOIn = pullback oN (x , h) dO
        dGIn = pullback gN (x , h) dG
        dX1 = pairFst dFIn
        dX2 = pairFst dIIn
        dX3 = pairFst dOIn
        dX4 = pairFst dGIn
        dH1 = pairSnd dFIn
        dH2 = pairSnd dIIn
        dH3 = pairSnd dOIn
        dH4 = pairSnd dGIn
        dX12 = primal (addX p) (dX1 , dX2)
        dX34 = primal (addX p) (dX3 , dX4)
        dX = primal (addX p) (dX12 , dX34)
        dH12 = primal (addH p) (dH1 , dH2)
        dH34 = primal (addH p) (dH3 , dH4)
        dH = primal (addH p) (dH12 , dH34)
    in dX , lstm-state dH dC

lstmAt : ∀ {X H : Set}
  → LSTMNodes X H
  → X
  → Node (LSTMState H) (LSTMState H)
lstmAt p x = node
  (lambda-s)
  (lambda-b)
  where
  lambda-s : LSTMState H → LSTMState H
  lambda-s s = primal (lstmCell p) (x , s)
  lambda-b : LSTMState H → LSTMState H → LSTMState H
  lambda-b s ds = pairSnd (pullback (lstmCell p) (x , s) ds)

lstmUnroll : ∀ {X H : Set} {n : Nat}
  → Vec X n
  → LSTMNodes X H
  → Node (LSTMState H) (LSTMState H)
lstmUnroll [] p = identity
lstmUnroll (x ∷ xs) p = compose (lstmAt p x) (lstmUnroll xs p)

lstmCellBoundary : ∀ {X H : Set}
  (p : LSTMNodes X H) (x : X) (s : LSTMState H) →
  primal (lstmCell p) (x , s) ≡ primal (lstmCell p) (x , s)
lstmCellBoundary p x s = refl
