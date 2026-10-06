-- KLA paper extraction surface.
--
-- The precision recurrence is represented in homogeneous coordinates:
--   λₜ = ((1 + pₜ φₜ) λₜ₋₁ + aₜ² φₜ) / (pₜ λₜ₋₁ + aₜ²)
-- so the nonlinear scalar update is carried by a 2×2 Möbius matrix.
--
-- The paper then obtains temporal parallelism from associative matrix
-- composition / prefix scan.  The mean information-form recurrence is
-- represented separately as an affine update.

module FullCoupled.KalmanLinearAttention where



-- BEGIN MIRTH-SYNC CANONICAL COMMAND
-- "$AGDA_COMMAND" -i .
-- END MIRTH-SYNC CANONICAL COMMAND

record KLAPair : Set where
  constructor klaPair
  field
    first second : Int
open KLAPair public

record KLAMobius : Set where
  constructor klaMobius
  field
    alpha beta gamma delta : Int
open KLAMobius public

klaMobiusApply : KLAMobius → KLAPair → KLAPair
klaMobiusApply m (klaPair x y) =
  klaPair
    (alpha m *Int x +Int beta m *Int y)
    (gamma m *Int x +Int delta m *Int y)

klaMobiusCompose : KLAMobius → KLAMobius → KLAMobius
klaMobiusCompose l r =
  klaMobius
    (alpha l *Int alpha r +Int beta l *Int gamma r)
    (alpha l *Int beta r +Int beta l *Int delta r)
    (gamma l *Int alpha r +Int delta l *Int gamma r)
    (gamma l *Int beta r +Int delta l *Int delta r)

klaPrecisionMatrix : Int → Int → Int → KLAMobius
klaPrecisionMatrix p a phi =
  klaMobius
    (+ 1 +Int p *Int phi)
    (a *Int a *Int phi)
    p
    (a *Int a)

record KLAAffine : Set where
  constructor klaAffine
  field
    forget gain : Int
open KLAAffine public

klaAffineApply : KLAAffine → Int → Int
klaAffineApply f eta =
  forget f *Int eta +Int gain f

-- ηₜ = fₜ ηₜ₋₁ + kₜ Λᵥᵗ vₜ is represented as an affine map.
klaMeanAffine : Int → Int → Int → KLAAffine
klaMeanAffine forgetFactor key valuePrecisionTimesValue =
  klaAffine
    forgetFactor
    (key *Int valuePrecisionTimesValue)

data KLAConcept : Set where
  information-form
  precision-update
  mobius-transform
  matrix-composition
  affine-mean-update
  parallel-prefix-scan : KLAConcept

record KLAGraphEdge : Set where
  constructor klaEdge
  field
    from to : KLAConcept
open KLAGraphEdge public

klaGraph : List KLAGraphEdge
klaGraph =
    klaEdge information-form precision-update
  ∷ klaEdge precision-update mobius-transform
  ∷ klaEdge mobius-transform matrix-composition
  ∷ klaEdge matrix-composition parallel-prefix-scan
  ∷ klaEdge information-form affine-mean-update
  ∷ klaEdge affine-mean-update parallel-prefix-scan
  ∷ []

data KLABool : Set where
  kla-yes kla-no : KLABool

klaConceptEq : KLAConcept → KLAConcept → KLABool
klaConceptEq information-form information-form = kla-yes
klaConceptEq precision-update precision-update = kla-yes
klaConceptEq mobius-transform mobius-transform = kla-yes
klaConceptEq matrix-composition matrix-composition = kla-yes
klaConceptEq affine-mean-update affine-mean-update = kla-yes
klaConceptEq parallel-prefix-scan parallel-prefix-scan = kla-yes
klaConceptEq _ _ = kla-no

klaEdgeTargets : KLAConcept → List KLAGraphEdge → List KLAConcept
klaEdgeTargets _ [] = []
klaEdgeTargets source (e ∷ es) with klaConceptEq source (from e)
... | kla-yes = to e ∷ klaEdgeTargets source es
... | kla-no = klaEdgeTargets source es

record KLAPlan : Set where
  constructor klaPlan
  field
    concepts : List KLAConcept
    cost : Nat
open KLAPlan public

record KLANode : Set where
  constructor klaNode
  field
    current : KLAConcept
    reversedPath : List KLAConcept
    costSoFar : Nat
open KLANode public

klaHeuristic : KLAConcept → KLAConcept → Nat
klaHeuristic current goal with klaConceptEq current goal
... | kla-yes = zero
... | kla-no = suc zero

klaNodeScore : KLAConcept → KLANode → Nat
klaNodeScore goal n =
  costSoFar n + klaHeuristic (current n) goal

klaNatLE : Nat → Nat → KLABool
klaNatLE zero _ = kla-yes
klaNatLE (suc m) zero = kla-no
klaNatLE (suc m) (suc n) = klaNatLE m n

klaInsertByScore :
  KLAConcept →
  KLANode →
  List KLANode →
  List KLANode
klaInsertByScore goal n [] = n ∷ []
klaInsertByScore goal n (h ∷ hs) with klaNatLE (klaNodeScore goal n) (klaNodeScore goal h)
... | kla-yes = n ∷ h ∷ hs
... | kla-no = h ∷ klaInsertByScore goal n hs

klaReverse : {A : Set} → List A → List A
klaReverse [] = []
klaReverse (x ∷ xs) = klaReverse xs ++ x ∷ []

klaExpand :
  KLAConcept →
  KLANode →
  List KLAGraphEdge →
  List KLANode
klaExpand goal node graph =
  klaExpandTargets
    goal
    node
    (klaEdgeTargets (current node) graph)

klaExpandTargets :
  KLAConcept →
  KLANode →
  List KLAConcept →
  List KLANode
klaExpandTargets goal node [] = []
klaExpandTargets goal node (target ∷ targets) =
  klaNode
    target
    (target ∷ reversedPath node)
    (suc (costSoFar node))
  ∷
  klaExpandTargets goal node targets

klaAStarFuel :
  Nat →
  KLAConcept →
  List KLAGraphEdge →
  List KLANode →
  Maybe KLANode
klaAStarFuel zero goal graph frontier = Nothing
klaAStarFuel (suc fuel) goal graph [] = Nothing
klaAStarFuel (suc fuel) goal graph (node ∷ rest) with klaConceptEq (current node) goal
... | kla-yes = Just node
... | kla-no =
    klaAStarFuel
      fuel
      goal
      graph
      (klaInsertChildren goal (klaExpand goal node graph) rest)

klaInsertChildren :
  KLAConcept →
  List KLANode →
  List KLANode →
  List KLANode
klaInsertChildren goal [] frontier = frontier
klaInsertChildren goal (n ∷ ns) frontier =
  klaInsertChildren
    goal
    ns
    (klaInsertByScore goal n frontier)

klaAStar : KLAConcept → KLAConcept → KLAPlan
klaAStar start goal =
  case
    klaAStarFuel
      (suc (suc (suc (suc (suc (suc zero))))))
      goal
      klaGraph
      (klaNode start (start ∷ []) zero ∷ [])
  of λ where
    Nothing → klaPlan [] zero
    Just node →
      klaPlan
        (klaReverse (reversedPath node))
        (costSoFar node)

klaMobiusPrefixPlan : KLAPlan
klaMobiusPrefixPlan =
  klaAStar information-form matrix-composition

klaMeanPrefixPlan : KLAPlan
klaMeanPrefixPlan =
  klaAStar information-form parallel-prefix-scan

klaMobiusPath : List KLAConcept
klaMobiusPath = concepts klaMobiusPrefixPlan

klaMeanPath : List KLAConcept
klaMeanPath = concepts klaMeanPrefixPlan
