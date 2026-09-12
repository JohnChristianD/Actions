{-# OPTIONS --safe #-}

module Candidate where

data CandidateKind : Set where
  identityLaw finiteStepLaw projectionLaw : CandidateKind

data CandidateSize : Set where
  size1 size2 size3 : CandidateSize

size : CandidateKind → CandidateSize
size identityLaw = size1
size finiteStepLaw = size2
size projectionLaw = size3
