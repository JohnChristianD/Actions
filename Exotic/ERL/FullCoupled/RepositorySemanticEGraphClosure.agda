{-# OPTIONS --safe #-}

------------------------------------------------------------------------
-- Repository-wide semantic e-graph closure.
--
-- This module closes the semantic layer for every indexed Agda module
-- without pretending that module names or search costs are physical laws.
-- A module contributes a sound interpretation; e-graph paths then compose
-- exact semantic equality, and A* supplies traversal cost/heuristic data
-- without entering the equality proof.
------------------------------------------------------------------------

module Exotic.ERL.FullCoupled.RepositorySemanticEGraphClosure where

open import Relation.Binary.PropositionalEquality using (_≡_)
open import Exotic.ERL.FullCoupled.EGraphSemanticTransport

record AgdaSemanticModuleFamily (Module : Set) : Set₁ where
  constructor agdaSemanticModuleFamily
  field
    Expression : Module → Set
    State : Module → Set
    closure :
      ∀ m →
      AStarSemanticClosure
        (Expression m)
        (State m)

open AgdaSemanticModuleFamily public

repositoryAgdaAStarSemanticClosure :
  ∀ {Module : Set}
  (F : AgdaSemanticModuleFamily Module)
  (m : Module)
  {e f : Expression F m} →
  EGraphSemanticPath
    (semantics (closure F m))
    e
    f →
  interpret (semantics (closure F m)) e
  ≡
  interpret (semantics (closure F m)) f
repositoryAgdaAStarSemanticClosure F m =
  aStar-guided-semantic-closure (closure F m)

record UnconditionalAgdaEGraphAStarClosure : Set₁ where
  constructor unconditionalAgdaEGraphAStarClosure
  field
    closeAll :
      ∀ {Module : Set}
      (F : AgdaSemanticModuleFamily Module)
      (m : Module)
      {e f : Expression F m} →
      EGraphSemanticPath
        (semantics (closure F m))
        e
        f →
      interpret (semantics (closure F m)) e
      ≡
      interpret (semantics (closure F m)) f

unconditional-agda-egraph-astar-closure :
  UnconditionalAgdaEGraphAStarClosure
unconditional-agda-egraph-astar-closure =
  unconditionalAgdaEGraphAStarClosure
    repositoryAgdaAStarSemanticClosure

------------------------------------------------------------------------
-- The theorem is unconditional over the supplied semantic family:
-- sound interpretation + finite sound path imply exact equality.
-- It does not assert that every physical Maxwell witness exists.
------------------------------------------------------------------------
