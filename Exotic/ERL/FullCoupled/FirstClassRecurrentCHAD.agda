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

------------------------------------------------------------------------
-- Efficient-CHAD node: one total functional program contains both the
-- primal result and its reverse accumulation function.
------------------------------------------------------------------------

record Node (A B : Set) : Set₁ where
  field
    run : A → Σ B (λ _ → B → A)

open Node

primal : ∀ {A B : Set} → Node A B → A → B
primal n x = fst (run n x)

pullback : ∀ {A B : Set} → Node A B → A → B → A
pullback n x dy = snd (run n x) dy

identity : ∀ {A : Set} → Node A A
identity = record { run = λ x → x , (λ dx → dx) }

compose : ∀ {A B C : Set} → Node A B → Node B C → Node A C
compose f g = record
  { run = λ x →
      let rf = run f x
          rg = run g (fst rf)
      in fst rg , (λ dz → snd rf (snd rg dz))
  }

------------------------------------------------------------------------
-- Sized recurrent states. `hiddenDim` names the hidden carrier while the
-- public projection remains `hidden`.
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
-- LSTM transition: one `run` produces its primal state and reverse
-- state/input accumulation.
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
          rfc = run (LSTMNodes.hadamardH p) (fst rf , c)
          rig = run (LSTMNodes.hadamardH p) (fst ri , fst rg)
          rc = run (LSTMNodes.addH p) (fst rfc , fst rig)
          rt = run (LSTMNodes.tanhH p) (fst rc)
          rh = run (LSTMNodes.hadamardH p) (fst ro , fst rt)
          y = lstm-state (fst rh) (fst rc)
      in y , λ dy →
        let dRh = snd rh (LSTMState.hidden dy)
            dRt = snd rt (snd dRh)
            dRc = snd rc (LSTMState.cell dy , dRt)
            dRfc = snd rfc (fst dRc)
            dRig = snd rig (snd dRc)
            dF = fst dRfc
            dC = snd dRfc
            dI = fst dRig
            dG = snd dRig
            dO = fst dRh
            dXf = fst (snd rf dF)
            dXi = fst (snd ri dI)
            dXo = fst (snd ro dO)
            dXg = fst (snd rg dG)
            dHf = snd (snd rf dF)
            dHi = snd (snd ri dI)
            dHo = snd (snd ro dO)
            dHg = snd (snd rg dG)
            dXfi = primal (LSTMNodes.addH p) (dXf , dXi)
            dXog = primal (LSTMNodes.addH p) (dXo , dXg)
            dX = primal (LSTMNodes.addH p) (dXfi , dXog)
            dHfi = primal (LSTMNodes.addH p) (dHf , dHi)
            dHog = primal (LSTMNodes.addH p) (dHo , dHg)
            dH = primal (LSTMNodes.addH p) (dHfi , dHog)
        in dX , lstm-state dH dC
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
          z = fst rz
          r = fst rr
          rrh = run (GRUNodes.hadamardH p) (r , h)
          rn = run (gruTanh (GRUNodes.candidate p) p) (x , fst rrh)
          rm = run (GRUNodes.oneMinusH p) z
          rleft = run (GRUNodes.hadamardH p) (fst rm , fst rn)
          rright = run (GRUNodes.hadamardH p) (z , h)
          rout = run (GRUNodes.addH p) (fst rleft , fst rright)
      in gru-state (fst rout) , λ dy →
        let dOut = snd rout (GRUState.hidden dy)
            dLeft = snd rleft (fst dOut)
            dRight = snd rright (snd dOut)
            dMinus = snd rm (fst dLeft)
            dN = snd rn (snd dLeft)
            dRH = snd rrh (snd dN)
            dZMix = fst dRight
            dHMix = snd dRight
            dZMinus = snd (GRUNodes.oneMinusH p) dMinus
            dZ = primal (GRUNodes.addH p) (dZMix , dZMinus)
            dR = fst dRH
            dHCand = snd dRH
            dReset = snd rr dR
            dUpdate = snd rz dZ
            dXReset = fst dReset
            dHReset = snd dReset
            dXUpdate = fst dUpdate
            dHUpdate = snd dUpdate
            dXCandidate = fst dN
            dHX = primal (GRUNodes.addH p) (dXUpdate , dXReset)
            dX = primal (GRUNodes.addH p) (dHX , dXCandidate)
            dH0 = primal (GRUNodes.addH p) (dHUpdate , dHReset)
            dH = primal (GRUNodes.addH p) (dH0 , dHCand)
        in dX , gru-state dH
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
      in fst r , (λ ds → snd r ds)
  }

gruAt : ∀ {X H : Set} → GRUNodes X H → X → Node (GRUState H) (GRUState H)
gruAt p x = record
  { run = λ s →
      let r = run (gruCell p) (x , s)
      in fst r , (λ ds → snd r ds)
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
