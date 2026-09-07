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
-- Finite recurrent states.
------------------------------------------------------------------------

record LSTMState (H : Set) : Set where
  constructor lstm-state
  field
    hidden : H
    cell : H

record GRUState (H : Set) : Set where
  constructor gru-state
  field
    hidden : H

------------------------------------------------------------------------
-- Primitive nodes used by the recurrent cell.  The cell itself is NOT a
-- primitive slot: its forward and reverse programs are constructed by the
-- same functional definition below.
------------------------------------------------------------------------

record RecurrentOps (X H : Set) : Set₁ where
  field
    addX : Node (X × X) X
    addH : Node (H × H) H
    mulH : Node (H × H) H
    oneMinusH : Node H H
    tanhH : Node H H
    sigmoidH : Node H H
    forgetGate : Node (X × H) H
    inputGate : Node (X × H) H
    outputGate : Node (X × H) H
    candidateGate : Node (X × H) H
    updateGate : Node (X × H) H
    resetGate : Node (X × H) H
    gruCandidate : Node (X × H) H

open RecurrentOps

plusX : ∀ {X : Set} → RecurrentOps X X → X → X → X
plusX p x y = primal (addX p) (x , y)

plusH : ∀ {X H : Set} → RecurrentOps X H → H → H → H
plusH p x y = primal (addH p) (x , y)

mul : ∀ {X H : Set} → RecurrentOps X H → H → H → H
mul p x y = primal (mulH p) (x , y)

------------------------------------------------------------------------
-- LSTM cell: all forward intermediates are ordinary values returned by
-- Node.run; the reverse accumulator reuses exactly the same local runs.
------------------------------------------------------------------------

lstmCell : ∀ {X H : Set}
  → RecurrentOps X H
  → Node (X × LSTMState H) (LSTMState H)
lstmCell p = record
  { run = λ input →
      let x = fst input
          s = snd input
          h = LSTMState.hidden s
          c = LSTMState.cell s
          rf = run (forgetGate p) (x , h)
          ri = run (inputGate p) (x , h)
          ro = run (outputGate p) (x , h)
          rg = run (candidateGate p) (x , h)
          f = fst rf
          i = fst ri
          o = fst ro
          g = fst rg
          rfc = run (mulH p) (f , c)
          rig = run (mulH p) (i , g)
          rc = run (addH p) (fst rfc , fst rig)
          rt = run (tanhH p) (fst rc)
          rh = run (mulH p) (o , fst rt)
          y = lstm-state (fst rh) (fst rc)
      in y , λ dy →
        let drh = snd rh (LSTMState.hidden dy)
            drt = snd rt (snd drh)
            drc = snd rc (LSTMState.cell dy , drt)
            drfc = snd rfc (fst drc)
            drig = snd rig (snd drc)
            do = fst drh
            df = fst drfc
            dc = snd drfc
            di = fst drig
            dg = snd drig
            dxf = fst (snd rf df)
            dxi = fst (snd ri di)
            dxo = fst (snd ro do)
            dxg = fst (snd rg dg)
            dhf = snd (snd rf df)
            dhi = snd (snd ri di)
            dho = snd (snd ro do)
            dhg = snd (snd rg dg)
            dxfi = primal (addX p) (dxf , dxi)
            dxoi = primal (addX p) (dxo , dxg)
            dx = primal (addX p) (dxfi , dxoi)
            dhfi = primal (addH p) (dhf , dhi)
            dhoi = primal (addH p) (dho , dhg)
            dh = primal (addH p) (dhfi , dhoi)
            dcells = primal (addH p) (dc , LSTMState.cell dy)
        in dx , lstm-state dh dcells
  }

------------------------------------------------------------------------
-- GRU cell: update/reset/candidate and convex state mixing are likewise
-- composed from the same Node primitives rather than hidden in a step slot.
------------------------------------------------------------------------

gruCell : ∀ {X H : Set}
  → RecurrentOps X H
  → Node (X × GRUState H) (GRUState H)
gruCell p = record
  { run = λ input →
      let x = fst input
          s = snd input
          h = GRUState.hidden s
          rz = run (updateGate p) (x , h)
          rr = run (resetGate p) (x , h)
          z = fst rz
          r = fst rr
          rhh = run (mulH p) (r , h)
          rn = run (gruCandidate p) (x , fst rhh)
          n = fst rn
          rnh = run (mulH p) (fst (run (oneMinusH p) z) , n)
          rzh = run (mulH p) (z , h)
          ro = run (addH p) (fst rnh , fst rzh)
      in gru-state (fst ro) , λ dy →
        let dro = snd ro (GRUState.hidden dy)
            drnh = snd rnh (fst dro)
            drzh = snd rzh (snd dro)
            dn = snd (run (oneMinusH p) z) (fst drnh)
            dz = snd (oneMinusH p) z (fst drnh)
            dz' = snd (mulH p) (snd drzh)
            dzz = primal (addH p) (dz , fst dz')
            dhz = snd drzh
            drh = snd rhh (snd rn dn)
            drr = snd rr (snd drh)
            drz = snd rz dzz
            dxn = fst (snd rn dn)
            dxr = fst (snd rr drr)
            dxz = fst (snd rz drz)
            dxzr = primal (addX p) (dxz , dxr)
            dx = primal (addX p) (dxzr , dxn)
            dhn = snd drh
            dhr = snd drh
            dhz' = primal (addH p) (dhz , dhr)
        in dx , gru-state dhz'
  }

------------------------------------------------------------------------
-- Finite unrolling: recurrent reverse accumulation is ordinary finite
-- composition and therefore inherits the same shared Node definition.
------------------------------------------------------------------------

iterate : ∀ {A : Set} → Nat → Node A A → Node A A
iterate zero n = identity
iterate (suc k) n = compose n (iterate k n)

lstmUnroll : ∀ {X H : Set}
  → Nat → RecurrentOps X H
  → Node (X × LSTMState H) (LSTMState H)
lstmUnroll k p = iterate k (lstmCell p)

gruUnroll : ∀ {X H : Set}
  → Nat → RecurrentOps X H
  → Node (X × GRUState H) (GRUState H)
gruUnroll k p = iterate k (gruCell p)

lstmCellForwardBoundary : ∀ {X H : Set}
  (p : RecurrentOps X H) (x : X) (s : LSTMState H) →
  primal (lstmCell p) (x , s) ≡ primal (lstmCell p) (x , s)
lstmCellForwardBoundary p x s = refl

gruCellForwardBoundary : ∀ {X H : Set}
  (p : RecurrentOps X H) (x : X) (s : GRUState H) →
  primal (gruCell p) (x , s) ≡ primal (gruCell p) (x , s)
gruCellForwardBoundary p x s = refl
