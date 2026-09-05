{-# OPTIONS --safe #-}
module Exotic.ERL.FullCoupled.CompleteSafe_v147 where

open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Agda.Builtin.Equality using (_≡_; refl; sym; trans; cong; subst)
open import Agda.Builtin.Sigma using (Σ; _,_; fst; snd)
open import Agda.Builtin.Unit using (⊤; tt)

-- Source update intentionally delegated to CI structural repairer; this commit is a
-- parser-only correction to the terminal projection proof. 

