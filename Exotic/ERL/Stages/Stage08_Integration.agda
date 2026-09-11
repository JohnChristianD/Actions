{-# OPTIONS --safe #-}
module Exotic.ERL.Stages.Stage08_Integration where

open import Agda.Builtin.Nat using (Nat; _+_)
open import Agda.Builtin.Equality using (_≡_; refl)

import Exotic.ERL.Stages.Stage03_LinearLearner as LL
import Exotic.ERL.Stages.Stage04_QProjection as QP
import Exotic.ERL.Stages.Stage05_Representation as RP
import Exotic.ERL.Stages.Stage06_CoupledLearner as CL
import Exotic.ERL.Stages.Stage07_OuterFinite as OF

data OuterMethod : Set where
  openES : OuterMethod

record Stage08State : Set₁ where
  constructor stage08
  field
    learner : LL.LinearState
    representation : RP.Representation Nat Nat
    qBound : Nat
    archive : OF.Archive
    method : OuterMethod

criticUpdate : Stage08State → LL.LinearState
criticUpdate s = LL.criticStep (Stage08State.learner s)

coupledState : Stage08State → CL.CoupledState
coupledState s = CL.coupled
  (LL.LinearState.theta (criticUpdate s))
  (LL.LinearState.phi (criticUpdate s))
  (Stage08State.qBound s)

candidate : Stage08State → Nat
candidate s =
  QP.qProject
    (CL.CoupledState.critic (coupledState s))
    (RP.applyRepresentation (Stage08State.representation s) 0)

outerStep : Stage08State → Stage08State
outerStep s = stage08
  (criticUpdate s)
  (Stage08State.representation s)
  (Stage08State.qBound s)
  (OF.insert (candidate s) (Stage08State.archive s))
  (Stage08State.method s)

representationBoundary : ∀ s →
  RP.applyRepresentation (Stage08State.representation s) 0 ≡
  RP.Representation.activation (Stage08State.representation s)
    (RP.Representation.affine (Stage08State.representation s) 0)
representationBoundary s = refl

criticBoundary : ∀ s →
  LL.LinearState.phi (criticUpdate s) ≡
  LL.LinearState.phi (LL.criticStep (Stage08State.learner s))
criticBoundary s = refl

qProjectionBoundary : ∀ s →
  QP.qProject
    (QP.qProject (candidate s) (Stage08State.qBound s))
    (Stage08State.qBound s)
  ≡ QP.qProject (candidate s) (Stage08State.qBound s)
qProjectionBoundary s = QP.qProjectionIdempotent _ _

coupledL2Boundary : ∀ s →
  CL.CoupledState.l2 (CL.coupledStep (coupledState s)) ≡
  CL.CoupledState.l2 (coupledState s)
coupledL2Boundary s = CL.coupledStepSameL2 _

outerBoundary : ∀ s →
  OF.Archive.best (OF.insert (candidate s) (Stage08State.archive s)) ≡
  OF.maxNat (candidate s) (OF.Archive.best (Stage08State.archive s))
outerBoundary s = OF.insertShape _ _

methodPreserved : ∀ s →
  Stage08State.method (outerStep s) ≡ Stage08State.method s
methodPreserved s = refl

stage08Composition : ∀ s →
  OF.Archive.best (Stage08State.archive (outerStep s)) ≡
  OF.maxNat (candidate s) (OF.Archive.best (Stage08State.archive s))
stage08Composition s = OF.insertShape _ _
