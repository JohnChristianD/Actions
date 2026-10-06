module FullCoupled.KalmanLinearAttentionTest where

-- BEGIN MIRTH-SYNC COMMON IMPORTS
-- Merged external import surface; internal FullCoupled imports remain module-local.
import Prelude.Int.Properties as IntegerProperties
open import Addition
open import Agda.Builtin.Reflection as Builtin
open import Agda.Builtin.Sigma hiding (_,_)
open import Agda.Primitive as Level
open import Cantor
open import Rationals.Addition
open import Rationals.Multiplication
open import Rationals.Negation
open import Rationals.Order
open import Rationals.Type
open import Equality
open import Haskell.Prelude hiding (String; ⊥)
open import Haskell.Prelude.Nat.Properties using (add-assoc; add-suc-r; ≤-antisym; ≤-trans; n<1+n)
open import InfinitePigeon.Addition
open import InfinitePigeon.Cantor
open import InfinitePigeon.Equality
open import InfinitePigeon.Finite
open import InfinitePigeon.InfinitePigeon
open import InfinitePigeon.JK-LogicalFacts
open import InfinitePigeon.JK-Monads
open import InfinitePigeon.Logic
open import InfinitePigeon.LogicalFacts
open import InfinitePigeon.Naturals
open import InfinitePigeon.Order
open import InfinitePigeon.Two
open import Iterative.Multisets 𝓤
open import Iterative.Multisets-Addendum ua 𝓤
open import Iterative.Sets ua 𝓤
open import JK-LogicalFacts
open import JK-Monads
open import K-AC-N
open import Logic
open import LogicalFacts
open import MLTT.Athenian
open import MLTT.Spartan hiding (J)
open import MonadOnTypes.Definition
open import MonadOnTypes.J
open import MonadOnTypes.JK R
open import MonadOnTypes.K
open import Naturals
open import Naturals.Exponentiation
open import Naturals.Properties
open import Notation.CanonicalMap
open import Notation.Order
open import Order
open import Prelude
open import Prelude.Char as Char
open import Prelude.Nat.Properties using (add-assoc; add-suc-r; ≤-antisym; ≤-trans; n<1+n)
open import Two
open import UF.Base
open import UF.ClassicalLogic
open import UF.FunExt
open import UF.Powerset
open import UF.PropTrunc
open import UF.Size
open import UF.Subsingletons
open import UF.Subsingletons-FunExt
open import UF.UA-FunExt
open import W.Type
-- END MIRTH-SYNC COMMON IMPORTS

-- BEGIN MIRTH-SYNC CANONICAL COMMAND
-- "$AGDA_COMMAND" -i .
-- END MIRTH-SYNC CANONICAL COMMAND

open import FullCoupled.KalmanLinearAttention using
  ( KLAConcept
  ; KLAPlan
  ; KLAMobius
  ; KLAAffine
  ; concepts
  ; cost
  ; klaMobiusPrefixPlan
  ; klaMeanPrefixPlan
  ; klaMobiusPath
  ; klaMeanPath
  ; klaPrecisionMatrix
  ; klaMeanAffine
  )

test-mobius-plan : KLAPlan
test-mobius-plan = klaMobiusPrefixPlan

test-mean-plan : KLAPlan
test-mean-plan = klaMeanPrefixPlan

test-mobius-cost : cost klaMobiusPrefixPlan ≡ suc (suc (suc zero))
test-mobius-cost = refl

test-mean-cost : cost klaMeanPrefixPlan ≡ suc (suc zero)
test-mean-cost = refl

test-mobius-path : List KLAConcept
test-mobius-path = klaMobiusPath

test-mean-path : List KLAConcept
test-mean-path = klaMeanPath

test-precision-matrix : KLAMobius
test-precision-matrix = klaPrecisionMatrix (+ 2) (+ 3) (+ 5)

test-mean-affine : KLAAffine
test-mean-affine = klaMeanAffine (+ 2) (+ 3) (+ 7)
