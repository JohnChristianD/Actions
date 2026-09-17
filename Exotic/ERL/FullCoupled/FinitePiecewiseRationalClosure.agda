{-# OPTIONS --safe #-}
module Exotic.ERL.FullCoupled.FinitePiecewiseRationalClosure where

open import Relation.Binary.PropositionalEquality using (_≢_)
open import Agda.Builtin.Nat using (Nat; zero; suc)

open import Exotic.ERL.FullCoupled.GeneralFullCoupledLearnerMonolith as L
open import Exotic.ERL.FullCoupled.GeneralFullCoupledTheoremsMonolith as T
open import Exotic.ERL.FullCoupled.GeneralReservoirAttractorTheorems as R
open R public

WellFormedFiniteRational : L.FiniteRational → Set
WellFormedFiniteRational q = L.denominator q ≢ zero

WellFormedPiecewiseRational : (L.Int8 → L.FiniteRational) → Set
WellFormedPiecewiseRational f = ∀ x → WellFormedFiniteRational (f x)

record FinitePiecewiseRationalClosed
  (f : L.Int8 → L.FiniteRational) : Set where
  constructor finitePiecewiseRationalClosed
  field
    representation : T.PiecewiseRationalWitness f
    denominator-nonzero : WellFormedPiecewiseRational f
open FinitePiecewiseRationalClosed public

wellFormedConstWitness :
  ∀ q → WellFormedFiniteRational q →
  FinitePiecewiseRationalClosed (λ _ → q)
wellFormedConstWitness q qnz =
  finitePiecewiseRationalClosed
    (T.prConstWitness q)
    (λ _ → qnz)

wellFormedMobiusWitness :
  FinitePiecewiseRationalClosed L.mobiusRatio
wellFormedMobiusWitness =
  finitePiecewiseRationalClosed
    T.prMobiusWitness
    (λ x → λ ())

branchFunction :
  ∀ {f g h : L.Int8 → L.FiniteRational} →
  L.Int8 → L.FiniteRational
branchFunction {f = f} {g = g} {h = h} x with L.hardSign x
... | L.negative = f x
... | L.zeroSign = g x
... | L.positive = h x

branchDenominatorProof :
  ∀ {f g h : L.Int8 → L.FiniteRational} →
  FinitePiecewiseRationalClosed f →
  FinitePiecewiseRationalClosed g →
  FinitePiecewiseRationalClosed h →
  WellFormedPiecewiseRational (branchFunction {f = f} {g = g} {h = h})
branchDenominatorProof F G H x with L.hardSign x
... | L.negative = denominator-nonzero F x
... | L.zeroSign = denominator-nonzero G x
... | L.positive = denominator-nonzero H x

wellFormedBranchClosure :
  ∀ {f g h}
  → FinitePiecewiseRationalClosed f
  → FinitePiecewiseRationalClosed g
  → FinitePiecewiseRationalClosed h
  → FinitePiecewiseRationalClosed
      (branchFunction {f = f} {g = g} {h = h})
wellFormedBranchClosure F G H =
  finitePiecewiseRationalClosed
    (T.prBranch-closure
      (representation F)
      (representation G)
      (representation H))
    (branchDenominatorProof F G H)

wellFormedInputCompositionClosure :
  ∀ {f}
  → (m : T.FinitePiecewiseInt8Map)
  → FinitePiecewiseRationalClosed f
  → FinitePiecewiseRationalClosed
      (λ x → f (T.evalFinitePiecewiseInt8Map m x))
wellFormedInputCompositionClosure m F =
  finitePiecewiseRationalClosed
    (T.prComposeInput-closure m (representation F))
    (λ x → denominator-nonzero F (T.evalFinitePiecewiseInt8Map m x))

finitePiecewiseRational-closed :
  FinitePiecewiseRationalClosed T.finitePiecewiseRational
finitePiecewiseRational-closed =
  wellFormedBranchClosure
    (wellFormedConstWitness (L.finiteRational 255 1) (λ ()))
    (wellFormedConstWitness (L.finiteRational 0 1) (λ ()))
    wellFormedMobiusWitness

iterateClosed :
  ∀ {f}
  → FinitePiecewiseRationalClosed f
  → (m : T.FinitePiecewiseInt8Map)
  → ∀ n →
  FinitePiecewiseRationalClosed
    (λ x → f (T.evalFinitePiecewiseInt8Map
      (T.iterateFinitePiecewiseInt8Map m n) x))
iterateClosed F m zero = F
iterateClosed F m (suc n) =
  wellFormedInputCompositionClosure m (iterateClosed F m n)

unbounded-depth-piecewise-rational-closed :
  ∀ (m : T.FinitePiecewiseInt8Map) n →
  FinitePiecewiseRationalClosed
    (λ x → T.finitePiecewiseRational
      (T.evalFinitePiecewiseInt8Map
        (T.iterateFinitePiecewiseInt8Map m n) x))
unbounded-depth-piecewise-rational-closed m n =
  iterateClosed finitePiecewiseRational-closed m n

finitePiecewiseRational-denominator-nonzero :
  ∀ x → L.denominator (T.finitePiecewiseRational x) ≢ zero
finitePiecewiseRational-denominator-nonzero x =
  denominator-nonzero finitePiecewiseRational-closed x

unbounded-depth-piecewise-rational-denominator-nonzero :
  ∀ (m : T.FinitePiecewiseInt8Map) n x →
  L.denominator
    (T.finitePiecewiseRational
      (T.evalFinitePiecewiseInt8Map
        (T.iterateFinitePiecewiseInt8Map m n) x)) ≢ zero
unbounded-depth-piecewise-rational-denominator-nonzero m n x =
  denominator-nonzero
    (unbounded-depth-piecewise-rational-closed m n) x
