module Agda2HsSurface where

open import Haskell.Prelude

Entry = Int × List String

double : Int → Int
double x = x + x

{-# COMPILE AGDA2HS Entry #-}
{-# COMPILE AGDA2HS double #-}
