{-# OPTIONS --rewriting --confluence-check #-}

module FullCoupled.RewriteCompression where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Equality.Rewrite

import FullCoupled.CanonicalLearnerMonolith as C

{-# REWRITE
  C.canonicalFullStep-watkins
  C.canonicalFullStep-gru
  C.canonicalFullStep-optimizer
  C.canonicalFullStep-counts
  C.canonicalFullStep-qLog
  C.canonicalFullStep-qLogControl
  C.canonicalTotalCountStep
  C.canonicalSignal-watkins-target
  C.canonicalOptimizerStep-qMunchausen-L2
  C.canonicalPersistentGRUPreservation
#-}
