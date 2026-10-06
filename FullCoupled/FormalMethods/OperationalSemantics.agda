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
-- Vendored from iwilare/formal-methods (OperationalSemantics.agda), MIT-licensed upstream.
-- Namespaced locally so theorem-specific imports cannot collide with the
-- existing FullCoupled proof surface.
------------------------------------------------------------------------

module FullCoupled.FormalMethods.OperationalSemantics where

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
open import DyadicsInductive.Dyadics
open import DyadicsInductive.DyadicOrder
open import DyadicsInductive.DyadicOrder-PropTrunc
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


contradiction : ∀ {a} {A : Set a} → A → (A → ⊥) → ⊥
contradiction p np = np p


open import FullCoupled.FormalMethods.IMP

data ⦅_,_⦆⇒_ : com → state → state → Set where
  Skip : ∀{s} → ⦅ SKIP , s ⦆⇒ s
  Loc : ∀{x a s}
      → ⦅ x ::= a , s ⦆⇒ (s [ x ::= aval a s ])
  Comp : ∀{c₁ c₂ s₁ s₂ s₃}
       → ⦅ c₁ , s₁ ⦆⇒ s₂
       → ⦅ c₂ , s₂ ⦆⇒ s₃
       → ⦅ c₁ :: c₂ , s₁ ⦆⇒ s₃
  IfTrue : ∀{c₁ c₂ b s t}
         → bval b s ≡ true
         → ⦅ c₁ , s ⦆⇒ t
         → ⦅ IF b THEN c₁ ELSE c₂ , s ⦆⇒ t
  IfFalse : ∀{c₁ c₂ b s t}
          → bval b s ≡ false
          → ⦅ c₂ , s ⦆⇒ t
          → ⦅ IF b THEN c₁ ELSE c₂ , s ⦆⇒ t
  WhileFalse : ∀{c b s}
             → bval b s ≡ false
             → ⦅ WHILE b DO c , s ⦆⇒ s
  WhileTrue  : ∀{c b s₁ s₂ s₃}
             → bval b s₁ ≡ true
             → ⦅ c , s₁ ⦆⇒ s₂
             → ⦅ WHILE b DO c , s₂ ⦆⇒ s₃
             → ⦅ WHILE b DO c , s₁ ⦆⇒ s₃

true≢false : ¬ (true ≡ false)
true≢false = λ ()
        
deterministic : ∀{c s t t′}
              → ⦅ c , s ⦆⇒ t
              → ⦅ c , s ⦆⇒ t′
              → t ≡ t′
deterministic Skip Skip = refl
deterministic Loc Loc = refl
deterministic (Comp r₁ r₂)  (Comp r₁′ r₂′) rewrite deterministic r₁ r₁′ = deterministic r₂ r₂′
deterministic (IfTrue v r)  (IfTrue  v′ r′) = deterministic r r′
deterministic (IfTrue v r)  (IfFalse v′ r′) rewrite v  = contradiction v′ true≢false
deterministic (IfFalse v r) (IfTrue  v′ r′) rewrite v′ = contradiction v true≢false
deterministic (IfFalse v r) (IfFalse v′ r′) = deterministic r r′
deterministic (WhileFalse v) (WhileFalse x₁) = refl
deterministic (WhileFalse v) (WhileTrue x₁ r₁ r₂) rewrite x₁ = contradiction v  true≢false
deterministic (WhileTrue v r₁ r₂) (WhileFalse v′) rewrite v  = contradiction v′ true≢false
deterministic (WhileTrue v r₁ r₂) (WhileTrue v′ r₁′ r₂′) rewrite deterministic r₁ r₁′ = deterministic r₂ r₂′

lemma2-3-5 : ∀{s t}
           → ¬ ( ⦅ WHILE (Bc true) DO SKIP , s ⦆⇒ t )
lemma2-3-5 (WhileTrue x Skip (WhileTrue v r₁ r₂)) = lemma2-3-5 r₂

infixl 19 _∼_
_∼_ : com → com → Set
c ∼ c′ = ∀{s t} → ⦅ c , s  ⦆⇒ t ⇔ ⦅ c′ , s ⦆⇒ t

lemma2-4-3 : ∀{b c} → (WHILE b DO c) ∼ (IF b THEN (c :: (WHILE b DO c)) ELSE SKIP)
lemma2-4-3 = equivalence (λ { (WhileFalse x) → IfFalse x Skip ; (WhileTrue x r r₁) → IfTrue x (Comp r r₁) })
                         (λ { (IfTrue x (Comp r r₁)) → WhileTrue x r r₁ ; (IfFalse x Skip) → WhileFalse x })

data ⦅_,_⦆→⦅_,_⦆ : com → state → com → state → Set where
  Loc : ∀{x a s}
      → ⦅ x ::= a , s ⦆→⦅ SKIP , s [ x ::= aval a s ] ⦆
  Comp₁ : ∀{c s}
        → ⦅ SKIP :: c , s ⦆→⦅ c , s ⦆
  Comp₂ : ∀{c₁ c₁′ c₂ s s′}
        → ⦅ c₁       , s ⦆→⦅ c₁′       , s′ ⦆
        → ⦅ c₁ :: c₂ , s ⦆→⦅ c₁′ :: c₂ , s′ ⦆
  IfTrue  : ∀{b s c₁ c₂}
          → bval b s ≡ true
          → ⦅ IF b THEN c₁ ELSE c₂ , s ⦆→⦅ c₁ , s ⦆
  IfFalse : ∀{b s c₁ c₂}
          → bval b s ≡ false
          → ⦅ IF b THEN c₁ ELSE c₂ , s ⦆→⦅ c₂ , s ⦆           
  While : ∀{b s c}
        → ⦅ WHILE b DO c , s ⦆→⦅ IF b THEN (c :: (WHILE b DO c)) ELSE SKIP , s ⦆

infix  3 ⦅_,_⦆∎
infixr 2 ⦅_,_⦆→⟨_⟩_ ⦅_,_⦆→*⟨_⟩_

data  ⦅_,_⦆→*⦅_,_⦆ : com → state → com → state → Set where
  ⦅_,_⦆∎ : ∀ c s → ⦅ c , s ⦆→*⦅ c , s ⦆
  ⦅_,_⦆→⟨_⟩_ : ∀ c s {c′ c″ s′ s″}
            → ⦅ c  , s  ⦆→⦅  c′ , s′ ⦆
            → ⦅ c′ , s′ ⦆→*⦅ c″ , s″ ⦆
            → ⦅ c  , s  ⦆→*⦅ c″ , s″ ⦆

⦅_,_⦆→*⟨_⟩_ : ∀ c s {c′ c″ s′ s″}
           → ⦅ c  , s  ⦆→*⦅ c′ , s′ ⦆
           → ⦅ c′ , s′ ⦆→*⦅ c″ , s″ ⦆
           → ⦅ c  , s  ⦆→*⦅ c″ , s″ ⦆
⦅ c , s ⦆→*⟨ ⦅ _ , _ ⦆∎ ⟩        b = b
⦅ c , s ⦆→*⟨ ⦅ _ , _ ⦆→⟨ x ⟩ r ⟩ b = ⦅ _ , _ ⦆→⟨ x ⟩ ⦅ _ , _ ⦆→*⟨ r ⟩ b

lemma2-5-6 : ∀{c₁ c₁′ c₂ s s′}
      → ⦅ c₁ , s       ⦆→*⦅ c₁′       ,  s′ ⦆
      → ⦅ c₁ :: c₂ , s ⦆→*⦅ c₁′ :: c₂ ,  s′ ⦆
lemma2-5-6  ⦅ _ , _ ⦆∎         = ⦅ _ , _ ⦆∎
lemma2-5-6 (⦅ _ , _ ⦆→⟨ x ⟩ r) = ⦅ _ , _ ⦆→⟨ Comp₂ x ⟩ lemma2-5-6 r

big-small : ∀{c s t}
          → ⦅ c , s ⦆⇒ t
          → ⦅ c , s ⦆→*⦅ SKIP , t ⦆
big-small (Skip {s}) =
  ⦅ SKIP , s ⦆∎
big-small (Loc {x}{s}{a}) =
  ⦅ x ::= s , a                    ⦆→⟨ Loc ⟩
  ⦅ SKIP    , a [ x ::= aval s a ] ⦆∎
big-small (Comp {c₁}{c₂}{s}{s′}{t} r₁ r₂) =
  ⦅ c₁   :: c₂ , s  ⦆→*⟨ lemma2-5-6 (big-small r₁) ⟩
  ⦅ SKIP :: c₂ , s′ ⦆→⟨  Comp₁ ⟩
  ⦅ c₂         , s′ ⦆→*⟨ big-small r₂ ⟩
  ⦅ SKIP       , t  ⦆∎
big-small (IfTrue {c₁}{c₂}{b}{s}{t} v r₁) =
  ⦅ IF b THEN c₁ ELSE c₂ , s ⦆→⟨ IfTrue v ⟩
  ⦅ c₁                   , s ⦆→*⟨ big-small r₁ ⟩
  ⦅ SKIP                 , t ⦆∎
big-small (IfFalse {c₁}{c₂}{b}{s}{t} v r₂) =
  ⦅ IF b THEN c₁ ELSE c₂ , s ⦆→⟨ IfFalse v ⟩
  ⦅ c₂                   , s ⦆→*⟨ big-small r₂ ⟩
  ⦅ SKIP                 , t ⦆∎
big-small (WhileFalse {c}{b}{s} v) =
  ⦅ WHILE b DO c                            , s ⦆→⟨ While ⟩
  ⦅ IF b THEN c :: (WHILE b DO c) ELSE SKIP , s ⦆→⟨ IfFalse v ⟩
  ⦅ SKIP                                    , s ⦆∎
big-small (WhileTrue {c}{b}{s}{s′}{t} v r₁ r₂) = 
  ⦅ WHILE b DO c                            , s  ⦆→⟨ While ⟩
  ⦅ IF b THEN c :: (WHILE b DO c) ELSE SKIP , s  ⦆→⟨ IfTrue v ⟩
  ⦅ c :: (WHILE b DO c)                     , s  ⦆→*⟨ lemma2-5-6 (big-small r₁) ⟩
  ⦅ SKIP :: (WHILE b DO c)                  , s′ ⦆→⟨ Comp₁ ⟩
  ⦅ WHILE b DO c                            , s′ ⦆→*⟨ big-small r₂ ⟩
  ⦅ SKIP                                    , t  ⦆∎

lemma2-5-8 : ∀{c s c′ s′ t}
           → ⦅ c  , s  ⦆→⦅ c′ , s′ ⦆ → ⦅ c′ , s′ ⦆⇒ t
           → ⦅ c  , s  ⦆⇒ t
lemma2-5-8 Loc Skip = Loc
lemma2-5-8 Comp₁ r₁ = Comp Skip r₁
lemma2-5-8 (Comp₂ x) (Comp r₁ r₂) = Comp (lemma2-5-8 x r₁) r₂
lemma2-5-8 (IfTrue x) r₁ = IfTrue x r₁
lemma2-5-8 (IfFalse x) r₁ = IfFalse x r₁
lemma2-5-8 While (IfTrue x (Comp r₁ r₂)) = WhileTrue x r₁ r₂
lemma2-5-8 While (IfFalse x Skip) = WhileFalse x

small-big : ∀{c s t}
          → ⦅ c , s ⦆→*⦅ SKIP , t ⦆
          → ⦅ c , s ⦆⇒ t          
small-big ⦅ SKIP , s ⦆∎ = Skip
small-big (⦅ c , s ⦆→⟨ x ⟩ r) = lemma2-5-8 x (small-big r)
