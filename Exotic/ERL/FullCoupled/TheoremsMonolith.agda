{-# OPTIONS --safe #-}

------------------------------------------------------------------------
-- Single logical theorem source for the canonical learner.
--
-- The theorem surface is physically partitioned into dependency-ordered
-- Agda modules so CI can check each proof block on a bounded runner.
-- This facade re-exports the complete canonical theorem namespace.
------------------------------------------------------------------------

module Exotic.ERL.FullCoupled.TheoremsMonolith where

open import Exotic.ERL.FullCoupled.TheoremsMonolith.Part4 public
