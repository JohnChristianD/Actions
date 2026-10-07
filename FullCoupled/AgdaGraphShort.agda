module FullCoupled.AgdaGraphShort where


-- BEGIN MIRTH-SYNC CANONICAL COMMAND
-- "$AGDA_COMMAND" -i .
-- END MIRTH-SYNC CANONICAL COMMAND


-- BEGIN MIRTH-SYNC COMMON IMPORTS
-- Merged external import surface; internal FullCoupled imports remain module-local.
open import Agda.Builtin.Reflection as Builtin
open import Haskell.Law.Num.Def using (IsLawfulNum)
open import Haskell.Law.Num.Int using (iLawfulNumInt)
open import Haskell.Prelude hiding (String; ⊥)
open import Haskell.Prelude.Nat.Properties using (add-assoc; add-suc-r; ≤-antisym; ≤-trans; n<1+n)
open import InfinitePigeon.FinitePigeon
open import MLTT.Spartan hiding (J)
open import Naturals
open import Naturals.Exponentiation
open import Naturals.Division
open import Naturals.Properties
open import Notation.Order
open import Order
open import Rationals.Addition
open import Rationals.Multiplication
open import Rationals.Negation
open import Rationals.Order
open import Rationals.Type
open import UF.Base
open import UF.FunExt
open import UF.PropTrunc
open import UF.Size
open import UF.Subsingletons
open import UF.Subsingletons-FunExt
open import UF.UA-FunExt
-- END MIRTH-SYNC COMMON IMPORTS


import FullCoupled.CanonicalLearnerMonolith as C
import FullCoupled.TheoremsMonolith as T

LearnerState = C.CanonicalFullLearnerState
LearnerKernel = C.CanonicalFullLearnerKernel

step = C.canonicalFullStep
policy = C.canonicalPolicy
affine = C.applyMonoidAffine
lstm = C.runMonoidLSTMCell
planAssoc = T.aStar-plan-append-associative
