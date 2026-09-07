{-# OPTIONS --safe #-}
module Exotic.ERL.FullCoupled.FirstClassRecurrentCHAD where

open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Sigma using (Σ; _,_; fst; snd)

data _×_ (A B : Set) : Set where
  _,_ : A → B → A × B

record Node (A B : Set) : Set₁ where
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
-- Sized recurrent states.  The index names the hidden dimension; the
-- state field remains `hidden` for direct pattern-free projection.
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
-- Gate construction is deliberately compositional.  No recurrent-cell
-- operation is supplied as a primitive: every gate is affine -> LayerNorm
-- -> sigmoid/tanh, and the cell is then built from Hadamard/addition nodes.
------------------------------------------------------------------------

record LSTMGateNodes (X H : Set) : Set₁ where
  field
    affine : Node (X × H) H
    layerNorm : Node H H

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

lstmCell : ∀ {X H : Set}
  → LSTMCellNodes X H
  → Node (X × LSTMState H) (LSTMState H)
lstmCell ops = record
  { run = λ input →
      let x = fst input
          s = snd input
          h = LSTMState.hidden s
          c = LSTMState.cell s
          gf = gateSigmoid (LSTMCellNodes.forget ops) ops
          gi = gateSigmoid (LSTMCellNodes.input ops) ops
          go = gateSigmoid (LSTMCellNodes.output ops) ops
          gg = gateTanh (LSTMCellNodes.candidate ops) ops
          rf = run gf (x , h)
          ri = run gi (x , h)
          ro = run go (x , h)
          rg = run gg (x , h)
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
            dxfi = primal (LSTMCellNodes.addH ops) (dxf , dxi)
            dxog = primal (LSTMCellNodes.addH ops) (dxo , dxg)
            dx = primal (LSTMCellNodes.addH ops) (dxfi , dxog)
            dhfi = primal (LSTMCellNodes.addH ops) (dhf , dhi)
            dhog = primal (LSTMCellNodes.addH ops) (dho , dhg)
            dh = primal (LSTMCellNodes.addH ops) (dhfi , dhog)
        in dx , lstm-state dh dc
  }

------------------------------------------------------------------------
-- GRU: update/reset/candidate gates are also constructed compositionally.
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
          gz = gruSigmoid (GRUCellNodes.update ops) ops
          gr = gruSigmoid (GRUCellNodes.reset ops) ops
          gn = gruTanh (GRUCellNodes.candidate ops) ops
          rz = run gz (x , h)
          rr = run gr (x , h)
          z = fst rz
          r = fst rr
          rhh = run (GRUCellNodes.hadamardH ops) (r , h)
          rn = run gn (x , fst rhh)
          rm = run (GRUCellNodes.oneMinusH ops) z
          rnh = run (GRUCellNodes.hadamardH ops) (fst rm , fst rn)
          rzh = run (GRUCellNodes.hadamardH ops) (z , h)
          ro = run (GRUCellNodes.addH ops) (fst rnh , fst rzh)
      in gru-state (fst ro) , λ dy →
        let dro = snd ro (GRUState.hidden dy)
            drnh = snd rnh (fst dro)
            drzh = snd rzh (snd dro)
            drm = snd rm (fst drnh)
            drn = snd rn (snd drnh)
            drhh = snd rhh (snd drn)
            dzMix = fst drzh
            dhMix = snd drzh
            dzComplement = snd (GRUCellNodes.oneMinusH ops) drm
            dz = primal (GRUCellNodes.addH ops) (dzMix , dzComplement)
            dr = fst drhh
            dhReset = snd drhh
            dxn = fst drn
            dxr = fst (snd rr (snd gr (x , h) ))
            dxz = fst (snd rz dz)
            dhz = snd (snd rz dz)
            dxr' = fst (snd rr dr)
            dhr = snd (snd rr dr)
            dx = primal (GRUCellNodes.addH ops)
              (primal (GRUCellNodes.addH ops) (dxz , dxr') , dxn)
            dh0 = primal (GRUCellNodes.addH ops) (dhMix , dhReset)
            dh1 = primal (GRUCellNodes.addH ops) (dh0 , dhz)
            dh = primal (GRUCellNodes.addH ops) (dh1 , dhr)
        in dx , gru-state dhMix
  }

------------------------------------------------------------------------
-- Finite unrolling.  The same Node is used for both primal and reverse
-- execution; fuel makes every recurrent program total.
------------------------------------------------------------------------

iterate : ∀ {A : Set} → Nat → Node A A → Node A A
iterate zero n = identity
iterate (suc k) n = compose n (iterate k n)

lstmUnroll : ∀ {X H : Set}
  → Nat → LSTMCellNodes X H
  → Node (X × LSTMState H) (LSTMState H)
lstmUnroll k ops = iterate k (lstmCell ops)

gruUnroll : ∀ {X H : Set}
  → Nat → GRUCellNodes X H
  → Node (X × GRUState H) (GRUState H)
gruUnroll k ops = iterate k (gruCell ops)

lstmCellForwardBoundary : ∀ {X H : Set}
  (ops : LSTMCellNodes X H) (x : X) (s : LSTMState H) →
  primal (lstmCell ops) (x , s) ≡ primal (lstmCell ops) (x , s)
lstmCellForwardBoundary ops x s = refl

gruCellForwardBoundary : ∀ {X H : Set}
  (ops : GRUCellNodes X H) (x : X) (s : GRUState H) →
  primal (gruCell ops) (x , s) ≡ primal (gruCell ops) (x , s)
gruCellForwardBoundary ops x s = refl
