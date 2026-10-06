-- BEGIN MIRTH-SYNC GLOBAL OPTIONS
{-# OPTIONS
  --lossy-unification
  --backtracking-instance-search
  --experimental-lazy-instances
  --confluence-check
  --syntactic-equality
  --polarity
  --auto-inline
  --guarded
  --exact-split
  --no-infer-absurd-clauses
  --keep-covering-clauses
  --no-projection-like
  --erasure
#-}
-- END MIRTH-SYNC GLOBAL OPTIONS


------------------------------------------------------------------------
-- Vendored from iwilare/formal-methods (HoareLogic.agda), MIT-licensed upstream.
-- Namespaced locally so theorem-specific imports cannot collide with the
-- existing FullCoupled proof surface.
------------------------------------------------------------------------

module FullCoupled.FormalMethods.HoareLogic where

-- BEGIN MIRTH-SYNC COMMON IMPORTS
-- Merged external import surface; internal FullCoupled imports remain module-local.
import Games.FiniteHistoryDependent
import Games.Main                -- uses Haskell features as postulates
import Prelude.Int.Properties as IntegerProperties
import SyntheticHomotopyTheory.Circle.FundamentalGroup -- depends on the above
import SyntheticHomotopyTheory.Circle.WithRewriting    -- uses --rewriting
import TWA.Thesis.Chapter6.Main  -- uses Haskell features as postulates
import Unsafe.CantorCompact      -- uses CountableTychonoff
import Unsafe.CoNat-Equiv        -- uses Coinductive records
import Unsafe.CountableTychonoff -- uses TERMINATING
import Unsafe.Haskell            -- uses Haskell features as postulates
import Unsafe.Type-in-Type-False -- uses --type-in-type
open import Addition
open import Agda.Builtin.Float renaming (primFloatPlus to _+ᵣ_; primFloatLess to _≤?ᵣ_)
open import Agda.Builtin.Nat renaming (primFloatPlus to _+ᵣ_; primFloatLess to _≤?ᵣ_)
open import Agda.Builtin.Reflection as Builtin
open import Agda.Builtin.Sigma hiding (_,_)
open import Agda.Primitive as Level
open import Cantor
open import Control.Monad.State using (State)
open import Equality
open import Games.TypeTrees
open import Haskell.Prelude
open import Haskell.Prelude hiding (String; ⊥)
open import Haskell.Prelude.Char as Char
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
open import MLTT.Fin
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
open import Dyadics.Addition
open import Dyadics.Negation
open import Dyadics.Multiplication
open import Dyadics.Order
open import Dyadics.Type
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


open import FullCoupled.FormalMethods.IMP
open import FullCoupled.FormalMethods.OperationalSemantics

assn : ∀{l} → Set (suc l)
assn {a} = state → Set a

data ⊢[_]_[_] {l} : assn {l} → com → assn {l} → Set (suc l) where
  Skip : ∀{P}
     → ⊢[ P ] SKIP [ P ]
  Loc : ∀{Q a x}
     → ⊢[ (λ s → Q (s [ x ::= aval a s ])) ] (x ::= a) [ Q ]
  Comp : ∀{P Q R c₁ c₂}
     → ⊢[ P ] c₁ [ Q ]
     → ⊢[ Q ] c₂ [ R ]
     → ⊢[ P ] c₁ :: c₂ [ R ]
  If : ∀{P b c₁ Q c₂}
     → ⊢[ (λ s → P s × bval b s ≡ true)  ] c₁ [ Q ]
     → ⊢[ (λ s → P s × bval b s ≡ false) ] c₂ [ Q ]
     → ⊢[ P ] (IF b THEN c₁ ELSE c₂) [ Q ]
  While : ∀{P b c}
     → ⊢[ (λ s → P s × bval b s ≡ true) ] c [ P ]
     → ⊢[ P ] (WHILE b DO c) [ (λ s → P s × bval b s ≡ false) ]
  Conseq : ∀{P Q P′ Q′ : assn} {c}
     → (∀ s → P′ s → P s)
     → ⊢[ P  ] c [ Q  ]
     → (∀ s → Q s → Q′ s)
     → ⊢[ P′ ] c [ Q′ ]

⊨[_]_[_] : assn → com → assn → Set
⊨[ P ] c [ Q ] = ∀{s t} → P s → ⦅ c , s ⦆⇒ t → Q t

soundness : ∀{P Q : assn} {c}
          → ⊢[ P ] c [ Q ]
          → ⊨[ P ] c [ Q ]
soundness Skip p Skip = p
soundness Loc p Loc = p
soundness (Comp r r₁) p (Comp z z₁) = soundness r₁ (soundness r p z) z₁
soundness (If r r₁) p (IfTrue x s) = soundness r (p , x) s
soundness (If r r₁) p (IfFalse x s) = soundness r₁ (p , x) s
soundness (While r) p (WhileFalse x₁) = p , x₁
soundness (While r) p (WhileTrue x₁ s s₁) = soundness (While r) (soundness r (p , x₁) s) s₁
soundness (Conseq x₁ r x₂) {s₁} {t} p s = x₂ t (soundness r (x₁ s₁ p) s)

wp : ∀{l} → com → assn {l} → assn {l}
wp c Q s = ∀ t → ⦅ c , s ⦆⇒ t → Q t

validity-wp : ∀{P Q : assn} {c}
      → ⊨[ P ] c [ Q ]
      → (∀ s → P s → wp c Q s)
validity-wp = λ z s z₁ t → z z₁

validity-wp-converse : ∀{P Q : assn} {c}
      → (∀ s → P s → wp c Q s)
      → ⊨[ P ] c [ Q ]
validity-wp-converse = (λ z {s} {t} z₁ → z s z₁ t)

wp-hoare : ∀ c {l} {Q : assn {l}}
  → ⊢[ wp c Q ] c [ Q ]
wp-hoare SKIP = Conseq (λ s z → z s Skip) Skip (λ s z → z)
wp-hoare (x ::= a) = Conseq (λ s wpe → wpe (s [ x ::= aval a s ]) Loc) Loc (λ s r → r)
wp-hoare (c :: c₁) = Comp (Conseq (λ s z x x₁ x₂ x₃ → z x₂ (Comp x₁ x₃)) (wp-hoare c) (λ s z → z)) (wp-hoare c₁)
wp-hoare (IF x THEN c ELSE c₁) = If (Conseq (λ s z x x₁ → proj₁ z x (IfTrue (proj₂ z) x₁)) (wp-hoare c) (λ s z → z))
                                    (Conseq (λ s z x x₁ → proj₁ z x (IfFalse (proj₂ z) x₁)) (wp-hoare c₁) (λ s z → z))
wp-hoare (WHILE b DO c) =
  Conseq (λ s x → x)
         (While (Conseq (λ s z x x₁ x₂ x₃ → proj₁ z x₂ (WhileTrue (proj₂ z) x₁ x₃))
                        (wp-hoare c)
                        (λ s z → z)))
         (λ s z → proj₁ z s (WhileFalse (proj₂ z)))

completeness : ∀ c {P Q : assn}
  → ⊨[ P ] c [ Q ]
  → ⊢[ P ] c [ Q ]
completeness c cc = Conseq (validity-wp cc) (wp-hoare c) (λ r x → x)
