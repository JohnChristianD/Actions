{-# OPTIONS --safe #-}
module CI.KernelTrigger where

open import Agda.Builtin.Equality using (_≡_; refl)

auditTrigger : 1 ≡ 1
auditTrigger = refl
