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
-- Efficient-CHAD node: one total functional program contains both the
-- primal result and its reverse accumulation function.
------------------------------------------------------------------------

record Result (A B : Set) : Set₁ where
  constructor result
  field
    value : B
    back : B → A

record Node (A B : Set) : Set₁ where
  field
    run : A → Result A B

open Result
open Node

primal : ∀ {A B : Set} → Node A B → A → B
primal n x = value (run n x)

pullback : ∀ {A B : Set} → Node A B → A → B → A
pullback n x dy = back (run n x) dy

identity : ∀ {A : Set} → Node A A
identity = record { run = λ x → result x (λ dx → dx) }

compose : ∀ {A B C : Set} → Node A B → Node B C → Node A C
compose f g = record
  { run = λ x →
      let rf = run f x
          rg = run g (value rf)
      in result (value rg) (λ dz → back rf (back rg dz))
  }

------------------------------------------------------------------------
-- Sized recurrent states. `hiddenDim` names the hidden carrier; public
-- projections remain `hidden` and `cell`.
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
-- Gate graphs contain only finite primitive Nodes. The recurrent cells are
-- constructed from these nodes rather than supplied as opaque step nodes.
------------------------------------------------------------------------

record LSTMGate (X H : Set) : Set₁ where
  field
    affine : Node (X × H) H
    layerNorm : Node H H

record LSTMNodes (X H : Set) : Set₁ where
  field
    forget input output candidate : LSTMGate X H
    sigmoidH tanhH : Node H H
    hadamardH addH : Node (H × H) H


gateSigmoid : ∀ {X H : Set} → LSTMGate X H → LSTMNodes X H → Node (X × H) H
gateSigmoid g p = compose (LSTMGate.affine g)
  (compose (LSTMGate.layerNorm g) (LSTMNodes.sigmoidH p))

gateTanh : ∀ {X H : Set} → LSTMGate X H → LSTMNodes X H → Node (X × H) H
gateTanh g p = compose (LSTMGate.affine g)
  (compose (LSTMGate.layerNorm g) (LSTMNodes.tanhH p))

------------------------------------------------------------------------
-- LSTM transition: primal and reverse accumulation are fields of the same
-- `Result` constructed by this one functional run.
------------------------------------------------------------------------

lstmCell : ∀ {X H : Set} →
  LSTMNodes X H → Node (X × LSTMState H) (LSTMState H)
lstmCell p = record
  { run = λ q →
      let x = pairFst q
          s = pairSnd q
          h = LSTMState.hidden s
          c = LSTMState.cell s
          rf = run (gateSigmoid (LSTMNodes.forget p) p) (x , h)
          ri = run (gateSigmoid (LSTMNodes.input p) p) (x , h)
          ro = run (gateSigmoid (LSTMNodes.output p) p) (x , h)
          rg = run (gateTanh (LSTMNodes.candidate p) p) (x , h)
          rfc = run (LSTMNodes.hadamardH p) (value rf , c)
          rig = run (LSTMNodes.hadamardH p) (value ri , value rg)
          rc = run (LSTMNodes.addH p) (value rfc , value rig)
          rt = run (LSTMNodes.tanhH p) (value rc)
          rh = run (LSTMNodes.hadamardH p) (value ro , value rt)
          y = lstm-state (value rh) (value rc)
      in result y (λ dy →
        let dRh = back rh (LSTMState.hidden dy)
            dRt = back rt (pairSnd dRh)
            dRc = back rc (LSTMState.cell dy , dRt)
            dRfc = back rfc (pairFst dRc)
            dRig = back rig (pairSnd dRc)
            dF = pairFst dRfc
            dC = pairSnd dRfc
            dI = pairFst dRig
            dG = pairSnd dRig
            dO = pairFst dRh
            dXf = pairFst (back rf dF)
            dXi = pairFst (back ri dI)
            dXo = pairFst (back ro dO)
            dXg = pairFst (back rg dG)
            dHf = pairSnd (back rf dF)
            dHi = pairSnd (back ri dI)
            dHo = pairSnd (back ro dO)
            dHg = pairSnd (back rg dG)
            dXfi = primal (LSTMNodes.addH p) (dXf , dXi)
            dXog = primal (LSTMNodes.addH p) (dXo , dXg)
            dX = primal (LSTMNodes.addH p) (dXfi , dXog)
            dHfi = primal (LSTMNodes.addH p) (dHf , dHi)
            dHog = primal (LSTMNodes.addH p) (dHo , dHg)
            dH = primal (LSTMNodes.addH p) (dHfi , dHog)
        in dX , lstm-state dH dC)
  }

------------------------------------------------------------------------
-- GRU transition: h' = (1-z) ⊙ n + z ⊙ h.
------------------------------------------------------------------------

record GRUGate (X H : Set) : Set₁ where
  field
    affine : Node (X × H) H
    layerNorm : Node H H

record GRUNodes (X H : Set) : Set₁ where
  field
    update reset candidate : GRUGate X H
    sigmoidH tanhH oneMinusH : Node H H
    hadamardH addH : Node (H × H) H


gruSigmoid : ∀ {X H : Set} → GRUGate X H → GRUNodes X H → Node (X × H) H
gruSigmoid g p = compose (GRUGate.affine g)
  (compose (GRUGate.layerNorm g) (GRUNodes.sigmoidH p))

gruTanh : ∀ {X H : Set} → GRUGate X H → GRUNodes X H → Node (X × H) H
gruTanh g p = compose (GRUGate.affine g)
  (compose (GRUGate.layerNorm g) (GRUNodes.tanhH p))

gruCell : ∀ {X H : Set} →
  GRUNodes X H → Node (X × GRUState H) (GRUState H)
gruCell p = record
  { run = λ q →
      let x = pairFst q
          s = pairSnd q
          h = GRUState.hidden s
          rz = run (gruSigmoid (GRUNodes.update p) p) (x , h)
          rr = run (gruSigmoid (GRUNodes.reset p) p) (x , h)
          z = value rz
          r = value rr
          rrh = run (GRUNodes.hadamardH p) (r , h)
          rn = run (gruTanh (GRUNodes.candidate p) p) (x , value rrh)
          rm = run (GRUNodes.oneMinusH p) z
          rleft = run (GRUNodes.hadamardH p) (value rm , value rn)
          rright = run (GRUNodes.hadamardH p) (z , h)
          rout = run (GRUNodes.addH p) (value rleft , value rright)
      in result (gru-state (value rout)) (λ dy →
        let dOut = back rout (GRUState.hidden dy)
            dLeft = back rleft (pairFst dOut)
            dRight = back rright (pairSnd dOut)
            dMinus = back rm (pairFst dLeft)
            dN = back rn (pairSnd dLeft)
            dRH = back rrh (pairSnd dN)
            dZMix = pairFst dRight
            dZMinus = back rm dMinus
            dZ = primal (GRUNodes.addH p) (dZMix , dZMinus)
            dR = pairFst dRH
            dHCand = pairSnd dRH
            dReset = back rr dR
            dUpdate = back rz dZ
            dXReset = pairFst dReset
            dHReset = pairSnd dReset
            dXUpdate = pairFst dUpdate
            dHUpdate = pairSnd dUpdate
            dXCandidate = pairFst dN
            dHX = primal (GRUNodes.addH p) (dXUpdate , dXReset)
            dX = primal (GRUNodes.addH p) (dHX , dXCandidate)
            dH0 = primal (GRUNodes.addH p) (dHUpdate , dHReset)
            dH = primal (GRUNodes.addH p) (dH0 , dHCand)
        in dX , gru-state dH)
  }

------------------------------------------------------------------------
-- Finite state passing over an explicit finite sequence. Capturing an input
-- turns each recurrent cell into a state-to-state Node; finite compose then
-- generates the complete forward/reverse chain.
------------------------------------------------------------------------

lstmAt : ∀ {X H : Set} → LSTMNodes X H → X → Node (LSTMState H) (LSTMState H)
lstmAt p x = record
  { run = λ s →
      let r = run (lstmCell p) (x , s)
      in result (value r) (λ ds → back r ds)
  }

gruAt : ∀ {X H : Set} → GRUNodes X H → X → Node (GRUState H) (GRUState H)
gruAt p x = record
  { run = λ s →
      let r = run (gruCell p) (x , s)
      in result (value r) (λ ds → back r ds)
  }

lstmUnroll : ∀ {X H : Set} {n : Nat} →
  Vec X n → LSTMNodes X H → Node (LSTMState H) (LSTMState H)
lstmUnroll [] p = identity
lstmUnroll (x ∷ xs) p = compose (lstmAt p x) (lstmUnroll xs p)

gruUnroll : ∀ {X H : Set} {n : Nat} →
  Vec X n → GRUNodes X H → Node (GRUState H) (GRUState H)
gruUnroll [] p = identity
gruUnroll (x ∷ xs) p = compose (gruAt p x) (gruUnroll xs p)

------------------------------------------------------------------------
-- Definitional identity boundaries.
------------------------------------------------------------------------

lstmCellBoundary : ∀ {X H : Set}
  (p : LSTMNodes X H) (x : X) (s : LSTMState H) →
  primal (lstmCell p) (x , s) ≡ primal (lstmCell p) (x , s)
lstmCellBoundary p x s = refl

gruCellBoundary : ∀ {X H : Set}
  (p : GRUNodes X H) (x : X) (s : GRUState H) →
  primal (gruCell p) (x , s) ≡ primal (gruCell p) (x , s)
gruCellBoundary p x s = refl
