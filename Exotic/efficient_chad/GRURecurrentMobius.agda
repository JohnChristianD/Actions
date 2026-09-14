{-# OPTIONS --safe #-}
module Exotic.efficient_chad.GRURecurrentMobius where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List using (List; []; _∷_; _++_)
open import Exotic.efficient_chad.MobiusInt8Composition using
  ( FiniteMobiusAction
  ; mobiusAction
  ; mobiusCompose
  )

-- One recurrent window is represented by a finite homogeneous action. A
-- concrete GRU window supplies the action witness for its finite recurrent
-- state; the scan theorem is independent of its particular parameters.
GRUWindow : Set₁
GRUWindow = FiniteMobiusAction

windowProduct : GRUWindow → GRUWindow → GRUWindow
windowProduct = mobiusCompose

windowProduct-assoc :
  ∀ (a b c : GRUWindow)
  → windowProduct (windowProduct a b) c
    ≡ windowProduct a (windowProduct b c)
windowProduct-assoc a b c = refl

windowIdentity : GRUWindow
windowIdentity = mobiusAction (λ p → p)

foldWindows : List GRUWindow → GRUWindow
foldWindows [] = windowIdentity
foldWindows (w ∷ ws) = windowProduct w (foldWindows ws)

foldWindows-append : ∀ (xs ys : List GRUWindow)
  → foldWindows (xs ++ ys)
    ≡ windowProduct (foldWindows xs) (foldWindows ys)
foldWindows-append [] ys = refl
foldWindows-append (x ∷ xs) ys =
  windowProduct-assoc x (foldWindows xs) (foldWindows ys)

-- Balanced regrouping is therefore extensionally equal to left-to-right
-- recurrent composition. This is the exact algebraic kernel needed for a
-- parallel associative scan over recurrent windows/depths.
parallelScan-reassociation : ∀ (a b c : GRUWindow)
  → windowProduct (windowProduct a b) c
    ≡ windowProduct a (windowProduct b c)
parallelScan-reassociation = windowProduct-assoc
