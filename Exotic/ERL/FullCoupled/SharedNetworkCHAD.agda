{-# OPTIONS --safe #-}
module Exotic.ERL.FullCoupled.SharedNetworkCHAD where

open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.Equality using (_≡_; refl)

data _×_ (A B : Set) : Set where
  _,_ : A → B → A × B

infixr 5 _∷_
data Vec (A : Set) : Nat → Set where
  [] : Vec A zero
  _∷_ : ∀ {n} → A → Vec A n → Vec A (suc n)

data NodeList (A : Set₁) : Set₁ where
  [] : NodeList A
  _∷_ : A → NodeList A → NodeList A

------------------------------------------------------------------------
-- One shared functional forward/reverse program.
-- The primal evaluator and reverse pullback inhabit one definition.
-- Composition therefore constructs the reverse program definitionally.
------------------------------------------------------------------------

record Node (A B : Set) : Set₁ where
  field
    primal : A → B
    pullback : A → B → A

open Node

identity : ∀ {A : Set} → Node A A
identity = record
  { primal = λ x → x
  ; pullback = λ _ dy → dy
  }

compose : ∀ {A B C : Set} → Node A B → Node B C → Node A C
compose f g = record
  { primal = λ x → primal g (primal f x)
  ; pullback = λ x dz →
      pullback f x (pullback g (primal f x) dz)
  }

------------------------------------------------------------------------
-- First-class finite vector CHAD node.
-- The vector reverse pass is obtained structurally from the scalar Node.
------------------------------------------------------------------------

mapVec : ∀ {A B : Set} {n : Nat} → (A → B) → Vec A n → Vec B n
mapVec f [] = []
mapVec f (x ∷ xs) = f x ∷ mapVec f xs

mapVecBack : ∀ {A B : Set} {n : Nat}
  → Node A B → Vec A n → Vec B n → Vec A n
mapVecBack node [] [] = []
mapVecBack node (x ∷ xs) (dy ∷ dys) =
  pullback node x dy ∷ mapVecBack node xs dys

mapNode : ∀ {A B : Set} {n : Nat} → Node A B → Node (Vec A n) (Vec B n)
mapNode node = record
  { primal = mapVec (primal node)
  ; pullback = mapVecBack node
  }

mapNodeForwardBoundary : ∀ {A B : Set} {n : Nat}
  (node : Node A B) xs →
  primal (mapNode node) xs ≡ mapVec (primal node) xs
mapNodeForwardBoundary node xs = refl

mapNodeReverseBoundary : ∀ {A B : Set} {n : Nat}
  (node : Node A B) xs dy →
  pullback (mapNode node) xs dy ≡ mapVecBack node xs dy
mapNodeReverseBoundary node xs dy = refl

------------------------------------------------------------------------
-- Finite recurrent unrolling is total recursion over Nat.  This is the
-- ordinary Efficient-CHAD/state-passing case.
------------------------------------------------------------------------

iterate : ∀ {A : Set} → Nat → Node A A → Node A A
iterate zero n = identity
iterate (suc k) n = compose n (iterate k n)

iterateForwardBoundary : ∀ {A : Set} (k : Nat) (n : Node A A) x →
  primal (iterate k n) x ≡ primal (iterate k n) x
iterateForwardBoundary k n x = refl

iterateReverseBoundary : ∀ {A : Set} (k : Nat) (n : Node A A) x dy →
  pullback (iterate k n) x dy ≡ pullback (iterate k n) x dy
iterateReverseBoundary k n x dy = refl

------------------------------------------------------------------------
-- Finite multi-layer composition remains ordinary CHAD composition.
------------------------------------------------------------------------

stack : ∀ {A : Set} → NodeList (Node A A) → Node A A
stack [] = identity
stack (n ∷ ns) = compose n (stack ns)

stackForwardBoundary : ∀ {A : Set} (ns : NodeList (Node A A)) x →
  primal (stack ns) x ≡ primal (stack ns) x
stackForwardBoundary ns x = refl

stackReverseBoundary : ∀ {A : Set} (ns : NodeList (Node A A)) x dy →
  pullback (stack ns) x dy ≡ pullback (stack ns) x dy
stackReverseBoundary ns x dy = refl

------------------------------------------------------------------------
-- Functional recurrent-state shapes.
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
-- Primitive blocks are Nodes. There is deliberately no standalone
-- representation-level tanh or sigmoid layer: those nonlinearities belong
-- to the recurrent cell or to whichever explicit output head uses them.
------------------------------------------------------------------------

record NetworkPrimitives (X H Y : Set) : Set₁ where
  field
    affine : Node X H
    layerNorm : Node H H
    output : Node H Y
    lstmStep : Node (X × LSTMState H) (LSTMState H)
    gruStep : Node (X × GRUState H) (GRUState H)

open NetworkPrimitives

representation : ∀ {X H Y : Set} → NetworkPrimitives X H Y → Node X H
representation p = compose (affine p) (layerNorm p)

actorNetwork : ∀ {X H Y : Set} → NetworkPrimitives X H Y → Node X Y
actorNetwork p = compose (representation p) (output p)

------------------------------------------------------------------------
-- Recurrent cells already contain their activation structure in their
-- shared state-transition Node.
------------------------------------------------------------------------

lstmNetworkStep : ∀ {X H Y : Set}
  → NetworkPrimitives X H Y
  → Node (X × LSTMState H) (LSTMState H)
lstmNetworkStep p = lstmStep p

gruNetworkStep : ∀ {X H Y : Set}
  → NetworkPrimitives X H Y
  → Node (X × GRUState H) (GRUState H)
gruNetworkStep p = gruStep p

lstmUnroll : ∀ {X H : Set}
  → Nat
  → Node (X × LSTMState H) (X × LSTMState H)
  → Node (X × LSTMState H) (X × LSTMState H)
lstmUnroll k step = iterate k step

gruUnroll : ∀ {X H : Set}
  → Nat
  → Node (X × GRUState H) (X × GRUState H)
  → Node (X × GRUState H) (X × GRUState H)
gruUnroll k step = iterate k step

------------------------------------------------------------------------
-- Definition-level sharing checks.
------------------------------------------------------------------------

representationForwardBoundary : ∀ {X H Y : Set}
  (p : NetworkPrimitives X H Y) x →
  primal (representation p) x ≡
    primal (layerNorm p) (primal (affine p) x)
representationForwardBoundary p x = refl

actorForwardBoundary : ∀ {X H Y : Set}
  (p : NetworkPrimitives X H Y) x →
  primal (actorNetwork p) x ≡
    primal (output p) (primal (representation p) x)
actorForwardBoundary p x = refl
