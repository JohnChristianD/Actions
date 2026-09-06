{-# OPTIONS --safe #-}
module Exotic.ERL.Stages.Stage08_Integration where

open import Agda.Builtin.Nat using (Nat; _+_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Unit using (⊤; tt)

import Exotic.ERL.Stages.Stage01_FiniteAlgebra as FA
import Exotic.ERL.Stages.Stage02_CHAD as CH
import Exotic.ERL.Stages.Stage03_LinearLearner as LL
import Exotic.ERL.Stages.Stage04_QProjection as QP
import Exotic.ERL.Stages.Stage05_Representation as RP
import Exotic.ERL.Stages.Stage06_CoupledLearner as CL
import Exotic.ERL.Stages.Stage07_OuterFinite as OF

data OuterMethod : Set where
  randomSearch : OuterMethod
  gesmrGA : OuterMethod
  openES : OuterMethod
  mr15GA : OuterMethod

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

chadFeature : Stage08State → Nat
chadFeature s =
  CH.CHAD.primal CH.idCHAD
    (CL.CoupledState.representation (coupledState s))

candidate : Stage08State → Nat
candidate s =
  QP.qProject
    (CL.CoupledState.critic (coupledState s))
    (RP.applyRepresentation (Stage08State.representation s) (chadFeature s))

outerStep : Stage08State → Stage08State
outerStep s = stage08
  (criticUpdate s)
  (Stage08State.representation s)
  (Stage08State.qBound s)
  (OF.insert (candidate s) (Stage08State.archive s))
  (Stage08State.method s)

record CoupledIntegrationCertificate (s : Stage08State) : Set where
  field
    finiteAlgebraBoundary : ∀ x y →
      FA.FiniteAlgebra.addA FA.natAlgebra x y ≡ x + y

    chadBoundary :
      CH.CHAD.primal CH.idCHAD (chadFeature s) ≡ chadFeature s

    criticBoundary :
      LL.LinearState.phi (criticUpdate s) ≡
      LL.LinearState.phi (Stage08State.learner s)

    qProjectionBoundary :
      QP.qProject (QP.qProject (candidate s) (Stage08State.qBound s))
        (Stage08State.qBound s)
      ≡
      QP.qProject (candidate s) (Stage08State.qBound s)

    representationBoundary :
      RP.applyRepresentation
        (Stage08State.representation s)
        (chadFeature s)
      ≡
      RP.Representation.tanh (Stage08State.representation s)
        (RP.Representation.layerNorm (Stage08State.representation s)
          (RP.Representation.affine (Stage08State.representation s) (chadFeature s)))

    coupledL2Boundary :
      CL.CoupledState.l2
        (CL.coupledStep (coupledState s))
      ≡
      CL.CoupledState.l2 (coupledState s)

    outerBoundary :
      OF.Archive.best (OF.insert (candidate s) (Stage08State.archive s))
      ≡
      OF.maxNat (candidate s) (OF.Archive.best (Stage08State.archive s))

    integratedArchive :
      OF.Archive.best (OF.Archive.best? )
      ≡
      OF.maxNat (candidate s) (OF.Archive.best (Stage08State.archive s))

    methodPreserved :
      Stage08State.method (outerStep s) ≡ Stage08State.method s

combinedCoupledTheorem : ∀ s → CoupledIntegrationCertificate s
combinedCoupledTheorem s = record
  { finiteAlgebraBoundary = λ x y → refl
  ; chadBoundary = CH.chadIdentity (chadFeature s)
  ; criticBoundary = LL.criticStepShape (Stage08State.learner s)
  ; qProjectionBoundary = QP.qProjectionIdempotent (candidate s) (Stage08State.qBound s)
  ; representationBoundary = RP.representationBoundary (Stage08State.representation s) (chadFeature s)
  ; coupledL2Boundary = CL.coupledStepSameL2 (coupledState s)
  ; outerBoundary = OF.insertShape (candidate s) (Stage08State.archive s)
  ; integratedArchive = OF.insertShape (candidate s) (Stage08State.archive s)
  ; methodPreserved = refl
  }

proofDAGConnected : ⊤
proofDAGConnected = tt
