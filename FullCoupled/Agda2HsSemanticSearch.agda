{-# OPTIONS --erasure --no-projection-like #-}

module FullCoupled.Agda2HsSemanticSearch where

-- BEGIN MIRTH-SYNC COMMON IMPORTS
open import Haskell.Prelude
import Unsafe.Haskell as Unsafe
open import Equality
open import Naturals
open import Naturals.Properties
open import MLTT.Two-Properties
open import UF.FunExt
-- END MIRTH-SYNC COMMON IMPORTS

module ExactRealSearchSurface (fe : FunExt) where

  open import TWA.Thesis.Chapter3.ClosenessSpaces fe
    using (ClosenessSpace)

  open import TWA.Thesis.Chapter3.SearchableTypes fe
    using (searchable; csearchable; searchable→csearchable)

  exactSearchPreservesSearchability :
    ∀ {X : ClosenessSpace 𝓤₀} →
    searchable 𝓤₀ ⟨ X ⟩ →
    csearchable 𝓤₀ X
  exactSearchPreservesSearchability {X} =
    searchable→csearchable X


-- BEGIN MIRTH-SYNC CANONICAL COMMAND
-- "$AGDA_COMMAND" -i .
-- END MIRTH-SYNC CANONICAL COMMAND

data Capability : Type where
  inversion : Capability
  exact-search : Capability
  uniform-continuity : Capability

instance
  iEqCapability : Eq Capability
  iEqCapability ._==_ inversion inversion = True
  iEqCapability ._==_ exact-search exact-search = True
  iEqCapability ._==_ uniform-continuity uniform-continuity = True
  iEqCapability ._==_ _ _ = False

record SemanticLaw : Type where
  constructor semanticLaw
  field
    lawName : String
    capabilities : List Capability
    dependencies : List String
    qPrior : Nat

open SemanticLaw public

record SearchNode : Type where
  constructor searchNode
  field
    plan : List String
    covered : List Capability
    qScore : Nat

open SearchNode public

requiredCapabilities : List Capability
requiredCapabilities =
  inversion ∷ exact-search ∷ uniform-continuity ∷ []

capabilityCovered : Capability → List Capability → Bool
capabilityCovered c [] = False
capabilityCovered c (x ∷ xs) =
  if c == x then
    True
  else
    capabilityCovered c xs

addCapability : Capability → List Capability → List Capability
addCapability c cs =
  if capabilityCovered c cs then
    cs
  else
    c ∷ cs

allRequiredCovered : List Capability → List Capability → Bool
allRequiredCovered [] covered = True
allRequiredCovered (c ∷ cs) covered =
  if capabilityCovered c covered then
    allRequiredCovered cs covered
  else
    False

missingCount : List Capability → List Capability → Nat
missingCount [] covered = zero
missingCount (c ∷ cs) covered =
  (if capabilityCovered c covered then zero else suc zero)
  + missingCount cs covered

planContains : String → List String → Bool
planContains name [] = False
planContains name (x ∷ xs) =
  if name == x then
    True
  else
    planContains name xs

dependenciesSatisfied : List String → List String → Bool
dependenciesSatisfied [] plan = True
dependenciesSatisfied (dependency ∷ dependencies) plan =
  if planContains dependency plan then
    dependenciesSatisfied dependencies plan
  else
    False

coversLaw : Capability → SemanticLaw → Bool
coversLaw capability law =
  capabilityCovered capability (capabilities law)

firstMissing :
  List Capability →
  List Capability →
  Maybe Capability
firstMissing [] covered = Nothing
firstMissing (c ∷ cs) covered =
  if capabilityCovered c covered then
    firstMissing cs covered
  else
    Just c

expandForCapability :
  Capability →
  List SemanticLaw →
  SearchNode →
  List SearchNode
expandForCapability capability [] node = []
expandForCapability capability (law ∷ laws) node =
  let rest = expandForCapability capability laws node
  in
  if coversLaw capability law then
    if dependenciesSatisfied (dependencies law) (plan node) then
      if planContains (lawName law) (plan node) then
        rest
      else
        searchNode
          (lawName law ∷ plan node)
          (addCapability capability (covered node))
          (qScore node + qPrior law)
        ∷ rest
    else
      rest
  else
    rest
nodeCost : SearchNode → Nat
nodeCost node =
  length (plan node)

nodeHeuristic :
  List Capability →
  SearchNode →
  Nat
nodeHeuristic required node =
  missingCount required (covered node)

nodeScore :
  List Capability →
  SearchNode →
  Nat
nodeScore required node =
  nodeCost node + nodeHeuristic required node

higherQ :
  SearchNode →
  SearchNode →
  Bool
higherQ left right =
  qScore left >= qScore right

insertByScore :
  List Capability →
  SearchNode →
  List SearchNode →
  List SearchNode
insertByScore required node [] =
  node ∷ []
insertByScore required node (head ∷ tail) =
  if nodeScore required node < nodeScore required head then
    node ∷ head ∷ tail
  else
    if nodeScore required node == nodeScore required head then
      if higherQ node head then
        node ∷ head ∷ tail
      else
        head ∷ insertByScore required node tail
    else
      head ∷ insertByScore required node tail

insertAll :
  List Capability →
  List SearchNode →
  List SearchNode →
  List SearchNode
insertAll required [] frontier = frontier
insertAll required (node ∷ nodes) frontier =
  insertAll
    required
    nodes
    (insertByScore required node frontier)

factorial : Nat → Nat
factorial zero = suc zero
factorial (suc n) = suc n * factorial n

searchFuel : List SemanticLaw → Nat
searchFuel laws =
  suc (suc (suc (factorial (length laws))))

astarWithFuel :
  Nat →
  List Capability →
  List SemanticLaw →
  List SearchNode →
  Maybe SearchNode
astarWithFuel zero required laws frontier = Nothing
astarWithFuel (suc fuel) required laws [] = Nothing
astarWithFuel (suc fuel) required laws (node ∷ frontier) =
  if allRequiredCovered required (covered node) then
    Just node
  else
    case firstMissing required (covered node) of λ where
      Nothing →
        Just node

      Just capability →
        let children = expandForCapability capability laws node
            frontier' = insertAll required children frontier
        in
        astarWithFuel fuel required laws frontier'

astar :
  List Capability →
  List SemanticLaw →
  List SearchNode →
  Maybe SearchNode
astar required laws frontier =
  astarWithFuel
    (searchFuel laws)
    required
    laws
    frontier

canonicalLaws : List SemanticLaw
canonicalLaws =
  semanticLaw
    "inverse-correct"
    (inversion ∷ [])
    []
    (suc (suc (suc zero)))
  ∷ semanticLaw
      "inverse-csearchable"
      (exact-search ∷ [])
      ("inverse-correct" ∷ [])
      (suc (suc zero))
  ∷ semanticLaw
      "inverse-preserves-csearchability"
      (uniform-continuity ∷ [])
      ("inverse-csearchable" ∷ [])
      (suc zero)
  ∷ []

canonicalSearch : Maybe SearchNode
canonicalSearch =
  astar
    requiredCapabilities
    canonicalLaws
    (searchNode [] [] zero ∷ [])

canonicalPlan : List String
canonicalPlan =
  case canonicalSearch of λ where
    Nothing → []
    Just node → plan node

canonicalSearchComplete : Bool
canonicalSearchComplete =
  allRequiredCovered
    requiredCapabilities
    (case canonicalSearch of λ where
      Nothing → []
      Just node → covered node)

canonicalSearchIsComplete :
  canonicalSearchComplete ≡ True
canonicalSearchIsComplete = refl

canonicalPlanNontrivial : Bool
canonicalPlanNontrivial =
  length canonicalPlan == suc (suc (suc zero))

canonicalPlanIsNontrivial :
  canonicalPlanNontrivial ≡ True
canonicalPlanIsNontrivial = refl

pathAppend : List String → List String → List String
pathAppend [] ys = ys
pathAppend (x ∷ xs) ys = x ∷ pathAppend xs ys

splitTarget : List String
splitTarget =
  "inverse-correct" ∷ "inverse-csearchable" ∷ []

semanticSearchReport : String
semanticSearchReport =
  "ghc-agda2hs semantic search: "
  ++ show (length canonicalPlan)
  ++ " laws; target capabilities covered; A* cost is proof-independent guidance"

{-# COMPILE AGDA2HS Capability #-}
{-# COMPILE AGDA2HS SemanticLaw #-}
{-# COMPILE AGDA2HS SearchNode #-}
{-# COMPILE AGDA2HS requiredCapabilities #-}
{-# COMPILE AGDA2HS canonicalLaws #-}
{-# COMPILE AGDA2HS astar #-}
{-# COMPILE AGDA2HS canonicalSearch #-}
{-# COMPILE AGDA2HS canonicalPlan #-}
{-# COMPILE AGDA2HS canonicalSearchComplete #-}
{-# COMPILE AGDA2HS canonicalPlanNontrivial #-}
{-# COMPILE AGDA2HS pathAppend #-}
{-# COMPILE AGDA2HS splitTarget #-}
{-# COMPILE AGDA2HS semanticSearchReport #-}
