{-# OPTIONS --safe #-}

module Exotic.efficient_chad.ParallelPrefix where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List using (List; []; _∷_; _++_)
open import Exotic.efficient_chad.Int8 using (Int8)

------------------------------------------------------------------------
-- Endogenous finite parallel-prefix algebra.
--
-- Modern SSM/scan work motivates the shape: a recurrent update is useful
-- for parallel execution when its transition-composition law is associative.
-- The theorem below does not import an external SSM claim.  It constructs
-- the finite transition algebra itself and proves the scan invariant from
-- its definitions.
------------------------------------------------------------------------

record Step : Set₁ where
  constructor step
  field
    run : Int8 → Int8

open Step public

identityStep : Step
identityStep = step (λ x → x)

composeStep : Step → Step → Step
composeStep f g = step (λ x → run f (run g x))

composeStep-pointwise :
  ∀ (f g x) → run (composeStep f g) x ≡ run f (run g x)
composeStep-pointwise f g x = refl

composeStep-associative :
  ∀ (f g h : Step) (x : Int8) →
  run (composeStep (composeStep f g) h) x
    ≡ run (composeStep f (composeStep g h)) x
composeStep-associative f g h x = refl

serial : List Step → Step
serial [] = identityStep
serial (s ∷ ss) = composeStep (serial ss) s

serial-append :
  ∀ (xs ys : List Step) (x : Int8) →
  run (serial (xs ++ ys)) x
    ≡ run (composeStep (serial ys) (serial xs)) x
serial-append [] ys x = refl
serial-append (s ∷ xs) ys x =
  composeStep-associative (serial ys) (serial xs) s x

------------------------------------------------------------------------
-- A binary reduction tree is the algebraic parallel-prefix substrate.
------------------------------------------------------------------------

data Tree : Set₁ where
  leaf : Step → Tree
  node : Tree → Tree → Tree

flatten : Tree → List Step
flatten (leaf s) = s ∷ []
flatten (node l r) = flatten l ++ flatten r

treeProduct : Tree → Step
treeProduct (leaf s) = s
treeProduct (node l r) = composeStep (treeProduct r) (treeProduct l)

treeProduct-correct :
  ∀ (t : Tree) (x : Int8) →
  run (treeProduct t) x ≡ run (serial (flatten t)) x
treeProduct-correct (leaf s) x = refl
treeProduct-correct (node l r) x =
  serial-append (flatten l) (flatten r) x

------------------------------------------------------------------------
-- Endogenous parallel-prefix theorem: any binary parenthesization of the
-- same finite transition sequence computes the same state at every input.
-- This is the algebraic core needed before adding a concrete work/depth
-- schedule; no external SSM semantics are assumed.
------------------------------------------------------------------------

parallelPrefix-correct :
  ∀ (t : Tree) (x : Int8) →
  run (treeProduct t) x ≡ run (serial (flatten t)) x
parallelPrefix-correct = treeProduct-correct
