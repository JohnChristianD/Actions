{-# OPTIONS --safe #-}

------------------------------------------------------------------------
-- Repository-wide semantic e-graph closure.
--
-- This module closes the semantic layer for every indexed Agda module
-- without pretending that module names or search costs are physical laws.
-- A module contributes a sound interpretation; e-graph paths then compose
-- exact semantic equality, and A* supplies traversal cost/heuristic data
-- without entering the equality proof.
--
-- The repository index below is deliberately finite and explicit.  It names
-- every surviving Agda file in Exotic/ERL/FullCoupled on this branch.  The
-- closure theorem is still parametric in the semantic interpretation for
-- each file: enumeration does not manufacture semantic soundness.
------------------------------------------------------------------------

module Exotic.ERL.FullCoupled.RepositorySemanticEGraphClosure where

open import Relation.Binary.PropositionalEquality using (_≡_)
open import Exotic.ERL.FullCoupled.EGraphSemanticTransport

data RepositoryAgdaModule : Set where
  canonicalLearnerMonolith :
    RepositoryAgdaModule
  theoremsMonolith :
    RepositoryAgdaModule
  eGraphSemanticTransport :
    RepositoryAgdaModule
  fourLawClosureWitnesses :
    RepositoryAgdaModule
  fourLawClosureImpossibility :
    RepositoryAgdaModule
  gruStatisticalInjectivity :
    RepositoryAgdaModule
  zpfStatisticalRepresentation :
    RepositoryAgdaModule
  tsallisStatisticalRepresentation :
    RepositoryAgdaModule
  repositorySemanticEGraphClosure :
    RepositoryAgdaModule

record AgdaSemanticModuleFamily : Set₁ where
  constructor agdaSemanticModuleFamily
  field
    Expression : RepositoryAgdaModule → Set
    State : RepositoryAgdaModule → Set
    closure :
      (m : RepositoryAgdaModule) →
      AStarSemanticClosure
        (Expression m)
        (State m)

open AgdaSemanticModuleFamily public

repositoryAgdaAStarSemanticClosure :
  (F : AgdaSemanticModuleFamily)
  (m : RepositoryAgdaModule)
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
      (F : AgdaSemanticModuleFamily)
      (m : RepositoryAgdaModule)
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
-- The theorem is unconditional over the complete surviving Agda-file
-- index and any supplied semantic family:
--
--   enumerated file
--     -> supplied sound interpretation
--     -> sound e-graph path
--     -> exact endpoint equality
--
-- A* costs/heuristics guide discovery but are not equality evidence.
-- This does not assert that every physical Maxwell witness, economic
-- equilibrium witness, or other domain-specific inhabitant exists.
------------------------------------------------------------------------
