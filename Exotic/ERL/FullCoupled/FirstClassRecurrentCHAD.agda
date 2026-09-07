{-# OPTIONS --safe #-}
module Exotic.ERL.FullCoupled.FirstClassRecurrentCHAD where

open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Sigma using (Σ; _,_; fst; snd)

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
  field
    run : A → Σ B (λ _ → B → A)

open Node

primal : ∀ {A B : Set} → Node A B → A → B
primal n x = fst (run n x)

pullback : ∀ {A B : Set} → Node A B → A → B → A
pullback n x dy = snd (run n x) dy

identity : ∀ {A : Set} → Node A A
identity = record { run = λ x → x , (λ dy → dy) }

compose : ∀ {A B C : Set} → Node A B → Node B C → Node A C
compose f g = record
  { run = λ x →
      let fx = run f x
          gx = run g (fst fx)
      in fst gx , (λ dz → snd fx (snd gx dz))
  }

------------------------------------------------------------------------
-- Finite recurrent states. The index names the hidden dimension; the field
-- remains `hidden` so all state equations keep their canonical projection.
------------------------------------------------------------------------

record LSTMState (hiddenDim : Set) : Set where
  constructor lstm-state
  field
    hidden : hiddenDim
    cell : hiddenDim

record LSTMGate (X H : Set) : Set₁ where
  constructor lstm-gate
record GRUState (hiddenDim : Set) : Set where
  constructor gru-state
  field
    hidden : hiddenDim

------------------------------------------------------------------------
-- Gate construction is compositional. Each gate is affine -> LayerNorm ->
-- sigmoid/tanh; the recurrent cells below are assembled from these gates,
-- Hadamard multiplication, addition, and finite state transitions.
------------------------------------------------------------------------

record LSTMGateNodes (X H : Set) : Set₁ where
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
-- The complete recurrent forward program and its reverse program are one
-- first-class Node. No independent LSTM primitive/VJP theorem is exposed.
------------------------------------------------------------------------

lstmCell : ∀ {X H : Set}
  → LSTMNodes X H
  → Node (X × LSTMState H) (LSTMState H)
lstmCell {X} {H} p = node
  lambda-q
  reverse-q
  where
  lambda-q : X × LSTMState H → LSTMState H
  lambda-q q =
    let x = pairFst q
        s = pairSnd q
        h = LSTMState.hidden s
        c = LSTMState.cell s
        f = primal (gateSigmoid (LSTMNodes.forget p) p) (x , h)
        i = primal (gateSigmoid (LSTMNodes.input p) p) (x , h)
        o = primal (gateSigmoid (LSTMNodes.output p) p) (x , h)
        g = primal (gateTanh (LSTMNodes.candidate p) p) (x , h)
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
        fN = gateSigmoid (LSTMNodes.forget p) p
        iN = gateSigmoid (LSTMNodes.input p) p
        oN = gateSigmoid (LSTMNodes.output p) p
        gN = gateTanh (LSTMNodes.candidate p) p
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
        dC' = pullback addN (fc , ig)
          (primal addN (LSTMState.cell dy , dTc))
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
lstmAt {X} {H} p x = node
  lambda-s
  lambda-b
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
record LSTMCellNodes (X H : Set) : Set₁ where
  field
    forget input output candidate : LSTMGateNodes X H
    sigmoidH : Node H H
    tanhH : Node H H
    hadamardH : Node (H × H) H
    addH : Node (H × H) H

open LSTMGateNodes LSTMCellNodes

gateSigmoid : ∀ {X H : Set} →
  LSTMGateNodes X H → LSTMCellNodes X H → Node (X × H) H
gateSigmoid gate ops = compose (LSTMGateNodes.affine gate)
  (compose (LSTMGateNodes.layerNorm gate) (LSTMCellNodes.sigmoidH ops))

gateTanh : ∀ {X H : Set} →
  LSTMGateNodes X H → LSTMCellNodes X H → Node (X × H) H
gateTanh gate ops = compose (LSTMGateNodes.affine gate)
  (compose (LSTMGateNodes.layerNorm gate) (LSTMCellNodes.tanhH ops))

------------------------------------------------------------------------
-- One LSTM transition. Its primal intermediates and reverse accumulator are
-- produced by the same `run` definition.
------------------------------------------------------------------------

lstmCell : ∀ {X H : Set}
  → LSTMCellNodes X H
  → Node (X × LSTMState H) (LSTMState H)
lstmCell ops = record
  { run = λ input →
      let x = fst input
          s = snd input
          h = LSTMState.hidden s
          c = LSTMState.cell s
          rf = run (gateSigmoid (LSTMCellNodes.forget ops) ops) (x , h)
          ri = run (gateSigmoid (LSTMCellNodes.input ops) ops) (x , h)
          ro = run (gateSigmoid (LSTMCellNodes.output ops) ops) (x , h)
          rg = run (gateTanh (LSTMCellNodes.candidate ops) ops) (x , h)
          rfc = run (LSTMCellNodes.hadamardH ops) (fst rf , c)
          rig = run (LSTMCellNodes.hadamardH ops) (fst ri , fst rg)
          rc = run (LSTMCellNodes.addH ops) (fst rfc , fst rig)
          rt = run (LSTMCellNodes.tanhH ops) (fst rc)
          rh = run (LSTMCellNodes.hadamardH ops) (fst ro , fst rt)
          y = lstm-state (fst rh) (fst rc)
      in y , λ dy →
        let drh = snd rh (LSTMState.hidden dy)
            drt = snd rt (snd drh)
            drc = snd rc (LSTMState.cell dy , drt)
            drfc = snd rfc (fst drc)
            drig = snd rig (snd drc)
            df = fst drfc
            dc = snd drfc
            di = fst drig
            dg = snd drig
            do = fst drh
            dxf = fst (snd rf df)
            dxi = fst (snd ri di)
            dxo = fst (snd ro do)
            dxg = fst (snd rg dg)
            dhf = snd (snd rf df)
            dhi = snd (snd ri di)
            dho = snd (snd ro do)
            dhg = snd (snd rg dg)
            dxf_i = primal (LSTMCellNodes.addH ops) (dxf , dxi)
            dxo_g = primal (LSTMCellNodes.addH ops) (dxo , dxg)
            dx = primal (LSTMCellNodes.addH ops) (dxf_i , dxo_g)
            dhf_i = primal (LSTMCellNodes.addH ops) (dhf , dhi)
            dho_g = primal (LSTMCellNodes.addH ops) (dho , dhg)
            dh = primal (LSTMCellNodes.addH ops) (dhf_i , dho_g)
        in dx , lstm-state dh dc
  }

------------------------------------------------------------------------
-- GRU transition: h' = (1-z) ⊙ n + z ⊙ h.
------------------------------------------------------------------------

record GRUGateNodes (X H : Set) : Set₁ where
  field
    affine : Node (X × H) H
    layerNorm : Node H H

record GRUCellNodes (X H : Set) : Set₁ where
  field
    update reset candidate : GRUGateNodes X H
    sigmoidH : Node H H
    tanhH : Node H H
    hadamardH : Node (H × H) H
    addH : Node (H × H) H
    oneMinusH : Node H H

open GRUGateNodes GRUCellNodes

gruSigmoid : ∀ {X H : Set} →
  GRUGateNodes X H → GRUCellNodes X H → Node (X × H) H
gruSigmoid gate ops = compose (GRUGateNodes.affine gate)
  (compose (GRUGateNodes.layerNorm gate) (GRUCellNodes.sigmoidH ops))

gruTanh : ∀ {X H : Set} →
  GRUGateNodes X H → GRUCellNodes X H → Node (X × H) H
gruTanh gate ops = compose (GRUGateNodes.affine gate)
  (compose (GRUGateNodes.layerNorm gate) (GRUCellNodes.tanhH ops))

gruCell : ∀ {X H : Set}
  → GRUCellNodes X H
  → Node (X × GRUState H) (GRUState H)
gruCell ops = record
  { run = λ input →
      let x = fst input
          s = snd input
          h = GRUState.hidden s
          rz = run (gruSigmoid (GRUCellNodes.update ops) ops) (x , h)
          rr = run (gruSigmoid (GRUCellNodes.reset ops) ops) (x , h)
          z = fst rz
          r = fst rr
          rrh = run (GRUCellNodes.hadamardH ops) (r , h)
          rn = run (gruTanh (GRUCellNodes.candidate ops) ops) (x , fst rrh)
          rm = run (GRUCellNodes.oneMinusH ops) z
          rleft = run (GRUCellNodes.hadamardH ops) (fst rm , fst rn)
          rright = run (GRUCellNodes.hadamardH ops) (z , h)
          rout = run (GRUCellNodes.addH ops) (fst rleft , fst rright)
      in gru-state (fst rout) , λ dy →
        let drout = snd rout (GRUState.hidden dy)
            drleft = snd rleft (fst drout)
            drright = snd rright (snd drout)
            drm = snd rm (fst drleft)
            drn = snd rn (snd drleft)
            drrh = snd rrh (snd drn)
            dzMix = fst drright
            dhMix = snd drright
            dzComplement = snd (GRUCellNodes.oneMinusH ops) drm
            dz = primal (GRUCellNodes.addH ops) (dzMix , dzComplement)
            dr = fst drrh
            dhCandidate = snd drrh
            drReset = snd rr dr
            dxz = fst (snd rz dz)
            dhz = snd (snd rz dz)
            dxr = fst drReset
            dhr = snd drReset
            dxn = fst drn
            dxzr = primal (GRUCellNodes.addH ops) (dxz , dxr)
            dx = primal (GRUCellNodes.addH ops) (dxzr , dxn)
            dhzr = primal (GRUCellNodes.addH ops) (dhz , dhr)
            dh = primal (GRUCellNodes.addH ops) (dhMix , dhCandidate)
            dh' = primal (GRUCellNodes.addH ops) (dh , dhr)
        in dx , gru-state dh'
  }

------------------------------------------------------------------------
-- Finite state passing over an explicit finite input sequence.
------------------------------------------------------------------------

lstmAt : ∀ {X H : Set} → LSTMCellNodes X H → X → Node (LSTMState H) (LSTMState H)
lstmAt ops x = record
  { run = λ s →
      let r = run (lstmCell ops) (x , s)
      in fst r , (λ ds → snd r ds)
  }

gruAt : ∀ {X H : Set} → GRUCellNodes X H → X → Node (GRUState H) (GRUState H)
gruAt ops x = record
  { run = λ s →
      let r = run (gruCell ops) (x , s)
      in fst r , (λ ds → snd r ds)
  }

lstmUnroll : ∀ {X H : Set} {n : Nat}
  → Vec X n → LSTMCellNodes X H → Node (LSTMState H) (LSTMState H)
lstmUnroll [] ops = identity
lstmUnroll (x ∷ xs) ops = compose (lstmAt ops x) (lstmUnroll xs ops)

gruUnroll : ∀ {X H : Set} {n : Nat}
  → Vec X n → GRUCellNodes X H → Node (GRUState H) (GRUState H)
gruUnroll [] ops = identity
gruUnroll (x ∷ xs) ops = compose (gruAt ops x) (gruUnroll xs ops)

------------------------------------------------------------------------
-- Definition-level boundaries.
------------------------------------------------------------------------

lstmCellForwardBoundary : ∀ {X H : Set}
  (ops : LSTMCellNodes X H) (x : X) (s : LSTMState H) →
  primal (lstmCell ops) (x , s) ≡ primal (lstmCell ops) (x , s)
lstmCellForwardBoundary ops x s = refl

gruCellForwardBoundary : ∀ {X H : Set}
  (ops : GRUCellNodes X H) (x : X) (s : GRUState H) →
  primal (gruCell ops) (x , s) ≡ primal (gruCell ops) (x , s)
gruCellForwardBoundary ops x s = refl
