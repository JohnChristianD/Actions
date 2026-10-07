module FullCoupled.AgdaGraphShort where

import FullCoupled.CanonicalLearnerMonolith as C
import FullCoupled.TheoremsMonolith as T

LearnerState = C.CanonicalFullLearnerState
LearnerKernel = C.CanonicalFullLearnerKernel

step = C.canonicalFullStep
policy = C.canonicalPolicy
affine = C.applyMonoidAffine
lstm = C.runMonoidLSTMCell
planAssoc = T.aStar-plan-append-associative
