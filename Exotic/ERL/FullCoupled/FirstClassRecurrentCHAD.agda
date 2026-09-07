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
-- One shared Efficient-CHAD node. Forward evaluation and reverse
-- accumulation are fields of exactly the same definition.
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
-- Recurrent states. The type parameter is `hiddenDim`; public projection
-- remains `hidden`.
------------------------------------------------------------------------

record LSTMState (hiddenDim : Set) : Set where
  constructor lstm-state
  field
    hidden : hiddenDim
    cell : hiddenDim

record GRUState (hiddenDim : Set) : Set where
  constructor gru-state
  field
    hidden : hiddenDim

------------------------------------------------------------------------
-- Finite primitive graphs.
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

gateSigmoid : ∀ {X H : Set} → LSTMGate X H → LSTMNodes X H → Node (X × H) H
gateSigmoid g p =
  compose (LSTMGate.affine g)
    (compose (LSTMGate.layerNorm g) (LSTMNodes.sigmoidH p))

gateTanh : ∀ {X H : Set} → LSTMGate X H → LSTMNodes X H → Node (X × H) H
gateTanh g p =
  compose (LSTMGate.affine g)
    (compose (LSTMGate.layerNorm g) (LSTMNodes.tanhH p))

------------------------------------------------------------------------
-- LSTM: c' = f ⊙ c + i ⊙ g ; h' = o ⊙ tanh(c').
------------------------------------------------------------------------

lstmCell : ∀ {X H : Set} →
  LSTMNodes X H → Node (X × LSTMState H) (LSTMState H)
lstmCell p = node
  (λ q →
    let x = pairFst q
        s = pairSnd q
        h = LSTMState.hidden s
        c = LSTMState.cell s
        f = primal (gateSigmoid (LSTMNodes.forget p) p) (x , h)
        i = primal (gateSigmoid (LSTMNodes.input p) p) (x , h)
        o = primal (gateSigmoid (LSTMNodes.output p) p) (x , h)
        g = primal (gateTanh (LSTMNodes.candidate p) p) (x , h)
        fc = primal (LSTMNodes.hadamardH p) (f , c)
        ig = primal (LSTMNodes.hadamardH p) (i , g)
        c' = primal (LSTMNodes.addH p) (fc , ig)
        tc = primal (LSTMNodes.tanhH p) c'
        h' = primal (LSTMNodes.hadamardH p) (o , tc)
    in lstm-state h' c')
  (λ q dy →
    let x = pairFst q
        s = pairSnd q
        h = LSTMState.hidden s
        c = LSTMState.cell s
        fN = gateSigmoid (LSTMNodes.forget p) p
        iN = gateSigmoid (LSTMNodes.input p) p
        oN = gateSigmoid (LSTMNodes.output p) p
        gN = gateTanh (LSTMNodes.candidate p) p
        f = primal fN (x , h)
        i = primal iN (x , h)
        o = primal oN (x , h)
        g = primal gN (x , h)
        fcN = LSTMNodes.hadamardH p
        igN = LSTMNodes.hadamardH p
        addN = LSTMNodes.addH p
        c' = primal addN (primal fcN (f , c) , primal igN (i , g))
        tcN = LSTMNodes.tanhH p
        tc = primal tcN c'
        hN = LSTMNodes.hadamardH p
        dRh = pullback hN (o , tc) (LSTMState.hidden dy)
        dTc = pullback tcN c' (pairSnd dRh)
        dC' = pullback addN
          (primal fcN (f , c) , primal igN (i , g))
          (LSTMState.cell dy , dTc)
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
        dX12 = primal (LSTMNodes.addX p) (dX1 , dX2)
        dX34 = primal (LSTMNodes.addX p) (dX3 , dX4)
        dX = primal (LSTMNodes.addX p) (dX12 , dX34)
        dH12 = primal (LSTMNodes.addH p) (dH1 , dH2)
        dH34 = primal (LSTMNodes.addH p) (dH3 , dH4)
        dH = primal (LSTMNodes.addH p) (dH12 , dH34)
    in dX , lstm-state dH dC)

------------------------------------------------------------------------
-- GRU: h' = (1-z) ⊙ n + z ⊙ h.
------------------------------------------------------------------------

record GRUGate (X H : Set) : Set₁ where
  constructor gru-gate
  field
    affine : Node (X × H) H
    layerNorm : Node H H

record GRUNodes (X H : Set) : Set₁ where
  constructor gru-nodes
  field
    update reset candidate : GRUGate X H
    sigmoidH tanhH oneMinusH : Node H H
    hadamardH addH : Node (H × H) H
    addX : Node (X × X) X

gruSigmoid : ∀ {X H : Set} → GRUGate X H → GRUNodes X H → Node (X × H) H
gruSigmoid g p =
  compose (GRUGate.affine g)
    (compose (GRUGate.layerNorm g) (GRUNodes.sigmoidH p))

gruTanh : ∀ {X H : Set} → GRUGate X H → GRUNodes X H → Node (X × H) H
gruTanh g p =
  compose (GRUGate.affine g)
    (compose (GRUGate.layerNorm g) (GRUNodes.tanhH p))

gruCell : ∀ {X H : Set} →
  GRUNodes X H → Node (X × GRUState H) (GRUState H)
gruCell p = node
  (λ q →
    let x = pairFst q
        s = pairSnd q
        h = GRUState.hidden s
        z = primal (gruSigmoid (GRUNodes.update p) p) (x , h)
        r = primal (gruSigmoid (GRUNodes.reset p) p) (x , h)
        rh = primal (GRUNodes.hadamardH p) (r , h)
        n = primal (gruTanh (GRUNodes.candidate p) p) (x , rh)
        mz = primal (GRUNodes.oneMinusH p) z
        left = primal (GRUNodes.hadamardH p) (mz , n)
        right = primal (GRUNodes.hadamardH p) (z , h)
        out = primal (GRUNodes.addH p) (left , right)
    in gru-state out)
  (λ q dy →
    let x = pairFst q
        s = pairSnd q
        h = GRUState.hidden s
        zN = gruSigmoid (GRUNodes.update p) p
        rN = gruSigmoid (GRUNodes.reset p) p
        nN = gruTanh (GRUNodes.candidate p) p
        z = primal zN (x , h)
        r = primal rN (x , h)
        rh = primal (GRUNodes.hadamardH p) (r , h)
        n = primal nN (x , rh)
        mzN = GRUNodes.oneMinusH p
        mz = primal mzN z
        leftN = GRUNodes.hadamardH p
        rightN = GRUNodes.hadamardH p
        addN = GRUNodes.addH p
        left = primal leftN (mz , n)
        right = primal rightN (z , h)
        dOut = pullback addN (left , right) (GRUState.hidden dy)
        dLeft = pullback leftN (mz , n) (pairFst dOut)
        dRight = pullback rightN (z , h) (pairSnd dOut)
        dMz = pairFst dLeft
        dN = pairSnd dLeft
        dZMix = pairFst dRight
        dHDirect = pairSnd dRight
        dZComp = pullback mzN z dMz
        dZ = primal addN (dZMix , dZComp)
        dUpdateIn = pullback zN (x , h) dZ
        dNIn = pullback nN (x , rh) dN
        dRH = pairSnd dNIn
        dResetH = pullback (GRUNodes.hadamardH p) (r , h) dRH
        dR = pairFst dResetH
        dHCand = pairSnd dResetH
        dResetIn = pullback rN (x , h) dR
        dX = primal (GRUNodes.addX p)
          (primal (GRUNodes.addX p) (pairFst dUpdateIn , pairFst dResetIn) , pairFst dNIn)
        dH = primal addN
          (primal addN (dHDirect , pairSnd dUpdateIn) ,
           primal addN (dHCand , pairSnd dResetIn))
    in dX , gru-state dH)

------------------------------------------------------------------------
-- Finite unrolling over explicit input vectors.
------------------------------------------------------------------------

lstmAt : ∀ {X H : Set} → LSTMNodes X H → X → Node (LSTMState H) (LSTMState H)
lstmAt p x = node
  (λ s → primal (lstmCell p) (x , s))
  (λ s ds → pullback (lstmCell p) (x , s) ds)

gruAt : ∀ {X H : Set} → GRUNodes X H → X → Node (GRUState H) (GRUState H)
gruAt p x = node
  (λ s → primal (gruCell p) (x , s))
  (λ s ds → pullback (gruCell p) (x , s) ds)

lstmUnroll : ∀ {X H : Set} {n : Nat} →
  Vec X n → LSTMNodes X H → Node (LSTMState H) (LSTMState H)
lstmUnroll [] p = identity
lstmUnroll (x ∷ xs) p = compose (lstmAt p x) (lstmUnroll xs p)

gruUnroll : ∀ {X H : Set} {n : Nat} →
  Vec X n → GRUNodes X H → Node (GRUState H) (GRUState H)
gruUnroll [] p = identity
gruUnroll (x ∷ xs) p = compose (gruAt p x) (gruUnroll xs p)

------------------------------------------------------------------------
-- Definitional boundaries.
------------------------------------------------------------------------

lstmCellBoundary : ∀ {X H : Set}
  (p : LSTMNodes X H) (x : X) (s : LSTMState H) →
  primal (lstmCell p) (x , s) ≡ primal (lstmCell p) (x , s)
lstmCellBoundary p x s = refl

gruCellBoundary : ∀ {X H : Set}
  (p : GRUNodes X H) (x : X) (s : GRUState H) →
  primal (gruCell p) (x , s) ≡ primal (gruCell p) (x , s)
gruCellBoundary p x s = refl
