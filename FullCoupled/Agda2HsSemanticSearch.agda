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

open import FullCoupled.Agda2HsSemanticExtractor as Extractor
open import FullCoupled.Agda2HsTheoremGraphEGraph using
  ( symbolicEGraphRegression
  ; eGraphAssociativityRegression
  )

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
  suc (suc (suc (suc zero))) * factorial (length laws)

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

record GraphLaw : Type where
  constructor graphLaw
  field
    graphLawName : String
    graphLawDependencies : List String

open GraphLaw public

record GraphNode : Type where
  constructor graphNode
  field
    graphNodePlan : List String

open GraphNode public

graphLawForName :
  String -> List GraphLaw -> Maybe GraphLaw
graphLawForName _ [] = Nothing
graphLawForName name (law ∷ laws) =
  if name == graphLawName law then
    Just law
  else
    graphLawForName name laws

removeDuplicateStrings : List String -> List String -> List String
removeDuplicateStrings [] seen = seen
removeDuplicateStrings (x ∷ xs) seen =
  if planContains x seen then
    removeDuplicateStrings xs seen
  else
    removeDuplicateStrings xs (x ∷ seen)

graphLawAddDependency :
  String -> String -> List GraphLaw -> List GraphLaw
graphLawAddDependency name dependency [] =
  graphLaw name (dependency ∷ []) ∷ []
graphLawAddDependency name dependency
  (law ∷ laws) =
  if name == graphLawName law then
    let deps =
          if planContains dependency (graphLawDependencies law) then
            graphLawDependencies law
          else
            dependency ∷ graphLawDependencies law
    in graphLaw name deps ∷ laws
  else
    law ∷ graphLawAddDependency name dependency laws

ensureGraphLaw : String -> List GraphLaw -> List GraphLaw
ensureGraphLaw name [] = graphLaw name [] ∷ []
ensureGraphLaw name (law ∷ laws) =
  if name == graphLawName law then
    law ∷ laws
  else
    law ∷ ensureGraphLaw name laws

graphLawsFromEdges :
  List (String × String) -> List GraphLaw
graphLawsFromEdges [] = []
graphLawsFromEdges ((source , target) ∷ edges) =
  graphLawAddDependency
    source
    target
    (ensureGraphLaw target (graphLawsFromEdges edges))

graphLawSeeds : List GraphLaw -> List GraphNode
graphLawSeeds [] = []
graphLawSeeds (law ∷ laws) =
  graphNode (graphLawName law ∷ [])
  ∷ graphLawSeeds laws

graphContains : String -> List String -> Bool
graphContains = planContains

graphExpandNode :
  GraphNode -> List GraphLaw -> List GraphNode
graphExpandNode (graphNode []) _ = []
graphExpandNode (graphNode (terminal ∷ rest)) laws =
  case graphLawForName terminal laws of λ where
    Nothing -> []
    Just law ->
      graphExpandDependencies
        (graphLawDependencies law)
        (terminal ∷ rest)
        []

graphExpandDependencies :
  List String ->
  List String ->
  List GraphNode ->
  List GraphNode
graphExpandDependencies [] _ acc = acc
graphExpandDependencies (dependency ∷ dependencies) plan acc =
  if graphContains dependency plan then
    graphExpandDependencies dependencies plan acc
  else
    graphExpandDependencies
      dependencies
      (dependency ∷ plan)
      (graphNode (dependency ∷ plan) ∷ acc)

graphNodeScore : GraphNode -> Nat
graphNodeScore node = length (graphNodePlan node)

graphInsert :
  GraphNode -> List GraphNode -> List GraphNode
graphInsert node [] = node ∷ []
graphInsert node (head ∷ tail) =
  if graphNodeScore node < graphNodeScore head then
    node ∷ head ∷ tail
  else
    head ∷ graphInsert node tail

graphInsertAll :
  List GraphNode -> List GraphNode -> List GraphNode
graphInsertAll [] frontier = frontier
graphInsertAll (node ∷ nodes) frontier =
  graphInsertAll nodes (graphInsert node frontier)

graphValidChain :
  List String -> List GraphLaw -> Bool
graphValidChain [] _ = False
graphValidChain (_ ∷ []) _ = True
graphValidChain (child ∷ parent ∷ rest) laws =
  case graphLawForName parent laws of λ where
    Nothing -> False
    Just law →
      if planContains child (graphLawDependencies law) then
        graphValidChain (parent ∷ rest) laws
      else
        False

graphAllUnique :
  List String -> Bool
graphAllUnique [] = True
graphAllUnique (x ∷ xs) =
  if planContains x xs then
    False
  else
    graphAllUnique xs

graphValidPlan :
  List String -> List GraphLaw -> Bool
graphValidPlan [] _ = False
graphValidPlan plan laws =
  graphAllUnique plan && graphValidChain plan laws

graphLast :
  List String ->
  Maybe String
graphLast [] = Nothing
graphLast (name ∷ []) = Just name
graphLast (_ ∷ names) = graphLast names

graphMaximalDependencyChain :
  List String ->
  List GraphLaw ->
  Bool
graphMaximalDependencyChain plan laws =
  if graphValidPlan plan laws then
    case graphLast plan of λ where
      Nothing -> False
      Just terminal ->
        case graphLawForName terminal laws of λ where
          Nothing -> False
          Just law -> graphLawDependencies law == []
  else
    False

graphAppend : {A : Type} -> List A -> List A -> List A
graphAppend [] ys = ys
graphAppend (x ∷ xs) ys = x ∷ graphAppend xs ys

graphConcatMap :
  {A B : Type} ->
  (A -> List B) ->
  List A ->
  List B
graphConcatMap _ [] = []
graphConcatMap f (x ∷ xs) =
  graphAppend (f x) (graphConcatMap f xs)

mutual
  graphSearchChildren :
    Nat ->
    List GraphLaw ->
    List GraphNode ->
    List (List String)
  graphSearchChildren depth laws [] = []
  graphSearchChildren depth laws (node ∷ nodes) =
    graphAppend
      (graphSearchDepth depth laws node)
      (graphSearchChildren depth laws nodes)

  graphSearchDepth :
    Nat ->
    List GraphLaw ->
    GraphNode ->
    List (List String)
  graphSearchDepth zero _ _ = []
  graphSearchDepth (suc depth) laws node =
    if graphMaximalDependencyChain (graphNodePlan node) laws then
      (graphNodePlan node) ∷ []
    else
      graphSearchChildren
        depth
        laws
        (graphExpandNode node laws)

graphSearchSeeds :
  Nat ->
  List GraphLaw ->
  List GraphNode ->
  List (List String)
graphSearchSeeds depth laws [] = []
graphSearchSeeds depth laws (node ∷ nodes) =
  graphAppend
    (graphSearchDepth depth laws node)
    (graphSearchSeeds depth laws nodes)

graphPlanScore : List String -> Nat
graphPlanScore = length

graphInsertPlan :
  List String ->
  List (List String) ->
  List (List String)
graphInsertPlan plan [] = plan ∷ []
graphInsertPlan plan (head ∷ tail) =
  if graphPlanScore plan < graphPlanScore head then
    plan ∷ head ∷ tail
  else
    head ∷ graphInsertPlan plan tail

graphSortPlans :
  List (List String) ->
  List (List String)
graphSortPlans [] = []
graphSortPlans (plan ∷ plans) =
  graphInsertPlan plan (graphSortPlans plans)

autonomousGraphSearch :
  List (String × String) ->
  List (List String)
autonomousGraphSearch edges =
  let laws = graphLawsFromEdges edges
      seeds = graphLawSeeds laws
      candidates =
        graphSearchSeeds
          (length laws)
          laws
          seeds
  in
  graphSortPlans candidates

autonomousGraphSearchCount :
  List (String × String) ->
  Nat
autonomousGraphSearchCount edges =
  length (autonomousGraphSearch edges)

autonomousGraphSearchReport :
  List (String × String) ->
  String
autonomousGraphSearchReport edges =
  "agda2hs autonomous theorem-graph A*: "
  ++ show (autonomousGraphSearchCount edges)
  ++ " dependency chains"

stripDotPrefix : String -> String
stripDotPrefix ('"' ∷ rest) = stripDotPrefix rest
stripDotPrefix text = text

stripDotSuffixRev : String -> String
stripDotSuffixRev [] = []
stripDotSuffixRev (';' ∷ rest) = stripDotSuffixRev rest
stripDotSuffixRev ('"' ∷ rest) = stripDotSuffixRev rest
stripDotSuffixRev (']' ∷ rest) = stripDotSuffixRev rest
stripDotSuffixRev rest = rest

stripDotSuffix : String -> String
stripDotSuffix text =
  reverse (stripDotSuffixRev (reverse text))

stripDotToken : String -> String
stripDotToken text =
  stripDotSuffix (stripDotPrefix text)

parseDotLine : String -> List (String × String)
parseDotLine line =
  case words line of λ where
    (source ∷ "->" ∷ target ∷ rest) ->
      (stripDotToken source , stripDotToken target) ∷ []
    _ -> []

parseDotEdges : String -> List (String × String)
parseDotEdges source =
  concatMap parseDotLine (lines source)

canonicalGraphRoot : String
canonicalGraphRoot = "FullCoupled.TheoremsMonolith"

autonomousGraphSearchFromRoot :
  String ->
  List (String × String) ->
  List (List String)
autonomousGraphSearchFromRoot root edges =
  let laws = ensureGraphLaw root (graphLawsFromEdges edges)
  in
  graphSortPlans
    (graphSearchDepth
      (length laws)
      laws
      (graphNode (root ∷ [])))

autonomousCanonicalGraphSearch :
  String ->
  List (List String)
autonomousCanonicalGraphSearch source =
  autonomousGraphSearchFromRoot canonicalGraphRoot (parseDotEdges source)

autonomousCanonicalGraphSearchCount :
  String ->
  Nat
autonomousCanonicalGraphSearchCount source =
  length (autonomousCanonicalGraphSearch source)

autonomousCanonicalGraphReport : String -> String
autonomousCanonicalGraphReport source =
  let edges = parseDotEdges source
      plans = autonomousCanonicalGraphSearch source
  in
  "theorem-graph-edges="
    ++ show (length edges)
    ++ " autonomous-a-star-chains="
    ++ show (length plans)


autonomousGraphSearchRegression : Bool
autonomousGraphSearchRegression =
  let
    edges =
      ("A" , "B") ∷
      ("B" , "C") ∷
      []
    laws = graphLawsFromEdges edges
    plans = autonomousGraphSearchFromRoot "A" edges
  in
  case plans of λ where
    [] -> False
    (plan ∷ _) -> graphValidPlan plan laws

semanticGraphLaw :
  Extractor.SemanticLaw ->
  GraphLaw
semanticGraphLaw law =
  graphLaw
    (Extractor.semanticLawId law)
    (Extractor.semanticLawDependencies law)

semanticGraphLaws :
  List Extractor.SemanticLaw ->
  List GraphLaw
semanticGraphLaws [] = []
semanticGraphLaws (law ∷ laws) =
  semanticGraphLaw law ∷ semanticGraphLaws laws

semanticLawForName :
  String ->
  List Extractor.SemanticLaw ->
  Maybe Extractor.SemanticLaw
semanticLawForName _ [] = Nothing
semanticLawForName requested (law ∷ laws) =
  if Extractor.semanticLawName law == requested then
    Just law
  else
    semanticLawForName requested laws

graphAStarHeuristic :
  List GraphLaw ->
  GraphNode ->
  Nat
graphAStarHeuristic laws node =
  case graphLast (graphNodePlan node) of λ where
    Nothing -> zero
    Just terminal ->
      case graphLawForName terminal laws of λ where
        Nothing -> zero
        Just law ->
          if graphLawDependencies law == [] then
            zero
          else
            suc zero

graphAStarScore :
  List GraphLaw ->
  GraphNode ->
  Nat
graphAStarScore laws node =
  length (graphNodePlan node) + graphAStarHeuristic laws node

graphAStarInsert :
  List GraphLaw ->
  GraphNode ->
  List GraphNode ->
  List GraphNode
graphAStarInsert laws node [] =
  node ∷ []
graphAStarInsert laws node (head ∷ tail) =
  if graphAStarScore laws node < graphAStarScore laws head then
    node ∷ head ∷ tail
  else
    head ∷ graphAStarInsert laws node tail

graphAStarInsertAll :
  List GraphLaw ->
  List GraphNode ->
  List GraphNode ->
  List GraphNode
graphAStarInsertAll laws [] frontier = frontier
graphAStarInsertAll laws (node ∷ nodes) frontier =
  graphAStarInsertAll
    laws
    nodes
    (graphAStarInsert laws node frontier)

graphAStarFirstWithFuel :
  Nat ->
  List GraphLaw ->
  List GraphNode ->
  Maybe (List String)
graphAStarFirstWithFuel zero laws frontier =
  Nothing
graphAStarFirstWithFuel (suc fuel) laws [] =
  Nothing
graphAStarFirstWithFuel (suc fuel) laws (node ∷ frontier) =
  if graphMaximalDependencyChain
       (graphNodePlan node)
       laws then
    Just (graphNodePlan node)
  else
    graphAStarFirstWithFuel
      fuel
      laws
      (graphAStarInsertAll
        laws
        (graphExpandNode node laws)
        frontier)

graphAStarFirst :
  List GraphLaw ->
  GraphNode ->
  Maybe (List String)
graphAStarFirst laws seed =
  graphAStarFirstWithFuel
    (suc (factorial (length laws)))
    laws
    (seed ∷ [])

requiredTheoremNames : List String
requiredTheoremNames =
  "CanonicalAQLoopTheorem" ∷
  "CanonicalFullLearnerConnectedScanConjugacyTheorem" ∷
  "S4PlusS5RecurrentScanTheorem" ∷
  "CanonicalQMunchausenL2SharedNegationPolarityTheorem" ∷
  "CanonicalExactCompositionTuringCompletenessContract" ∷
  "CanonicalEndogenousMinimaxBellmanShapleyUAPTheorem" ∷
  "CanonicalPolymorphicSparsemaxCompositionTheorem" ∷
  "OffPolicyFunctionApproximationStabilityBoundary" ∷
  "canonicalLearnerBairdSevenStar" ∷
  "CanonicalExactRNNLMTheorem" ∷
  "CanonicalGlobalTokenLMCompositionTheorem" ∷
  "CanonicalIntegerHaarScaledOrthogonalityTheorem" ∷
  "NatRingSolverNormalizationTheorem" ∷
  "IntegerRingSolverNormalizationTheorem" ∷
  "ListMonoidSolverNormalizationTheorem" ∷
  "CanonicalAlgebraicTacticBackendTheorem" ∷
  "CanonicalSafeTacticNormalizationTheorem" ∷
  "inverse-csearchable" ∷
  "CanonicalIntegerLayerNormEGraphAStarInfiniteHorizonStabilityTheorem" ∷
  "AStarPlanMonoidTheorem" ∷
  "CanonicalTokenArbitraryLengthGenerationTheorem" ∷
  "CanonicalAStarCostGuidanceTheorem" ∷
  "CanonicalEndogenousEGraphAStarTransportClosureTheorem" ∷
  "CanonicalFiniteCycleExclusionIsomorphismTheorem" ∷
  "CanonicalOperatorCompositionTheorem" ∷
  "CanonicalF4GlobalOptimizerStabilityTheorem" ∷
  "CanonicalPureNonOrangeBypassCompletionTheorem" ∷
  "ExactContractComputabilityBoundaryTheorem" ∷
  "StateIsomorphism" ∷
  "ExactTwoCounterConfiguration" ∷
  "ExactTwoCounterMachine" ∷
  "nashEveryFiniteGameViaBrouwer" ∷
  "brouwerMixedNashFixedPointBridge" ∷
  "finiteMixedNash-brouwer-egraph-astar-proof" ∷
  "finiteMixedNash-egraph-astar-convergence" ∷
  "finiteMixedNash-egraph-astar-eventualStationarity" ∷
  "finiteMixedNash-egraph-astar-proof" ∷
  "finiteMixedNash-cycle-transport" ∷
  "finiteMixedNash-from-GRU-tail" ∷
  "finiteMixedNash-brouwer-gru-egraph-astar-distribution-proof" ∷
  "finiteMixedNash-brouwer-gru-egraph-astar-distribution-proof-nash" ∷
  "finiteMixedNash-brouwer-gru-egraph-astar-distribution-fixed" ∷
  "canonicalFullLearner-no-finite-rank-stability" ∷
  "CanonicalHardSparsityDegeneracyTheorem" ∷
  "ActionWeights" ∷
  "actionSupportCount" ∷
  "actionWeightSum" ∷
  "actionWeightSquareSum" ∷
  "generalTsallis2Denominator" ∷
  "generalTsallis2Numerator" ∷
  "generalTsallis2NearSparsity" ∷
  "generalTsallis2NearSparsity-zero" ∷
  "generalTsallis2NearSparsity-definition" ∷
  "fractionEquivalent" ∷
  "tsallis2Near-oneHot" ∷
  "generalSupportSparsity" ∷
  "generalSupportSparsity-definition" ∷
  []

requiredSubcompositionNames : List String
requiredSubcompositionNames =
  "CanonicalStationarySubcompositionTheorem" ∷ []

requiredNames : List String
requiredNames =
  requiredTheoremNames ++ requiredSubcompositionNames

requiredPlanForName :
  String ->
  List Extractor.SemanticLaw ->
  Maybe (List String)
requiredPlanForName requested semanticLaws =
  case semanticLawForName requested semanticLaws of λ where
    Nothing -> Nothing
    Just law ->
      let graphLaws = semanticGraphLaws semanticLaws
      in
      graphAStarFirst
        graphLaws
        (graphNode (Extractor.semanticLawId law ∷ []))

requiredPlanIsValid :
  List Extractor.SemanticLaw ->
  List String ->
  Bool
requiredPlanIsValid semanticLaws plan =
  graphValidPlan plan (semanticGraphLaws semanticLaws)

requiredPlans :
  List String ->
  List Extractor.SemanticLaw ->
  List (String × List String)
requiredPlans [] _ = []
requiredPlans (name ∷ names) semanticLaws =
  case requiredPlanForName name semanticLaws of λ where
    Nothing ->
      requiredPlans names semanticLaws
    Just plan ->
      if requiredPlanIsValid semanticLaws plan then
        (name , plan) ∷ requiredPlans names semanticLaws
      else
        requiredPlans names semanticLaws

requiredPlanCount :
  List String ->
  List Extractor.SemanticLaw ->
  Nat
requiredPlanCount names semanticLaws =
  length (requiredPlans names semanticLaws)

requiredPlanComplete :
  List String ->
  List Extractor.SemanticLaw ->
  Bool
requiredPlanComplete names semanticLaws =
  requiredPlanCount names semanticLaws == length names

requiredPlanReport :
  List String ->
  List Extractor.SemanticLaw ->
  String
requiredPlanReport names semanticLaws =
  "required-plan-count="
    ++ show (requiredPlanCount names semanticLaws)
    ++ " required-plan-total="
    ++ show (length names)
    ++ " required-plan-regression="
    ++ show (requiredPlanComplete names semanticLaws)

semanticLawExtractionReport :
  List Extractor.SemanticLaw ->
  String
semanticLawExtractionReport laws =
  "semantic-laws="
    ++ show (length laws)
    ++ " nonreflexive="
    ++ show (Extractor.countNonreflexive laws)
    ++ " composite="
    ++ show (Extractor.countComposite laws)

semanticSearchExecutableReport :
  List Extractor.SemanticLaw ->
  String
semanticSearchExecutableReport laws =
  requiredPlanReport requiredNames laws
    ++ " egraph-regression="
    ++ show symbolicEGraphRegression
    ++ " egraph-associativity-regression="
    ++ show eGraphAssociativityRegression

main : IO ⊤
main = do
  source <- readFile "build/agda2hs-semantic-search/theorems-monolith.dot"
  semanticLaws <-
    Extractor.readSemanticLaws
      "build/agda2hs-semantic-search/.semantic-source-files"
  putStrLn semanticSearchReport
  putStrLn (autonomousCanonicalGraphReport source)
  putStrLn ("autonomous-regression=" ++ show autonomousGraphSearchRegression)
  putStrLn ("canonical-plan=" ++ show canonicalPlan)
  putStrLn (semanticLawExtractionReport semanticLaws)
  putStrLn (requiredPlanReport requiredNames semanticLaws)
  putStrLn (semanticSearchExecutableReport semanticLaws)

{-# COMPILE AGDA2HS main #-}

{-# COMPILE AGDA2HS Capability #-}
{-# COMPILE AGDA2HS SemanticLaw #-}
{-# COMPILE AGDA2HS GraphLaw #-}
{-# COMPILE AGDA2HS GraphNode #-}
{-# COMPILE AGDA2HS autonomousGraphSearch #-}
{-# COMPILE AGDA2HS autonomousGraphSearchRegression #-}
{-# COMPILE AGDA2HS autonomousGraphSearchCount #-}
{-# COMPILE AGDA2HS autonomousGraphSearchReport #-}
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
{-# COMPILE AGDA2HS canonicalGraphRoot #-}
{-# COMPILE AGDA2HS parseDotEdges #-}
{-# COMPILE AGDA2HS autonomousGraphSearchFromRoot #-}
{-# COMPILE AGDA2HS autonomousCanonicalGraphSearch #-}
{-# COMPILE AGDA2HS autonomousCanonicalGraphSearchCount #-}
{-# COMPILE AGDA2HS autonomousCanonicalGraphReport #-}
{-# COMPILE AGDA2HS semanticGraphLaw #-}
{-# COMPILE AGDA2HS semanticGraphLaws #-}
{-# COMPILE AGDA2HS requiredTheoremNames #-}
{-# COMPILE AGDA2HS requiredSubcompositionNames #-}
{-# COMPILE AGDA2HS requiredNames #-}
{-# COMPILE AGDA2HS requiredPlanForName #-}
{-# COMPILE AGDA2HS requiredPlans #-}
{-# COMPILE AGDA2HS requiredPlanCount #-}
{-# COMPILE AGDA2HS requiredPlanComplete #-}
{-# COMPILE AGDA2HS requiredPlanReport #-}
{-# COMPILE AGDA2HS semanticLawExtractionReport #-}
{-# COMPILE AGDA2HS semanticSearchExecutableReport #-}