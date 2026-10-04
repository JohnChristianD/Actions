------------------------------------------------------------------------
-- Vendored from iwilare/formal-methods (OperationalSemantics.agda), MIT-licensed upstream.
-- Namespaced locally so theorem-specific imports cannot collide with the
-- existing FullCoupled proof surface.
------------------------------------------------------------------------

module FullCoupled.FormalMethods.OperationalSemantics where

-- BEGIN MIRTH-SYNC COMMON IMPORTS
-- Mirth-generated contract: this exact block is shared by every tracked .agda source.
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; cong; cong₂; subst; trans)
open import Agda.Builtin.Nat using (Nat; zero; suc)

-- Solver-associated Base modules.
open import Data.Bool.Base hiding (_≤_; _<_)
open import Data.Nat.Base hiding (_≤_; _<_; _>_; _≥_)
open import Data.Integer.Base hiding (_≤_; _<_; _>_; _≥_; suc; neg; sign; _+_; _*_)
open import Data.List.Base using (List; []; _∷_; _++_; map; length)
open import Data.Product.Base
open import Data.Sum.Base
open import Data.Maybe.Base

-- Solver front ends.
import Data.Bool.Solver as BoolSolver
open import Data.Nat.Solver using (module +-*-Solver)
import Data.Integer.Solver as IntegerSolver
open import Data.List.Relation.Binary.Sublist.Heterogeneous as HeterogeneousSublistBase
import Data.List.Relation.Binary.Sublist.Heterogeneous.Solver as HeterogeneousSublistSolver
import Data.List.Relation.Binary.Sublist.DecSetoid.Solver as DecSetoidSublistSolver
import Data.List.Relation.Binary.Sublist.DecPropositional.Solver as DecPropositionalSublistSolver
import Function.Related.TypeIsomorphisms.Solver as TypeIsomorphismsSolver
open import Data.Nat.Tactic.RingSolver as NatRingSolver using (solve-∀)
open import Data.Integer.Tactic.RingSolver as IntegerRingSolver using (solve-∀)
open import Tactic.RingSolver as RingSolver using (solve-∀)
open import Tactic.RingSolver.Core.AlmostCommutativeRing as RingCore
open import Tactic.RingSolver.Core.Expression as RingExpression
open import Tactic.RingSolver.Core.NatSet as RingNatSet
open import Tactic.RingSolver.Core.Polynomial.Base as RingPolynomialBase
open import Tactic.MonoidSolver as MonoidSolver using (solve)

-- Existing shared semantics and container imports.
open import Data.Nat using (NonZero; _∸_; _<_; _≤_; _<ᵇ_; _/_; z≤n; s≤s)
open import Data.Nat.Properties using (+-identityʳ; +-suc; ≤-antisym; ≤-decTotalOrder)
open import Data.Integer using (ℤ; +_; -_; -[1+_]; _≤?_) renaming (_+_ to _+ℤ_; _*_ to _*ℤ_)
import Data.Integer.Properties as IntegerProperties
open import Level using (0ℓ)
open import Data.List.Sort as Sort
open import Relation.Binary.Bundles using (DecTotalOrder)
open import Relation.Binary.Construct.On as On
import Relation.Binary.Construct.Flip.EqAndOrd as Flip
open import Data.Product.Relation.Binary.Lex.NonStrict as Lex
open import Data.Nat.DivMod using (m%n<n; m<n⇒m%n≡m)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Empty using (⊥)
open import Data.Unit using (⊤; tt)
open import Relation.Nullary using (¬_)
open import Effect.Monad using (RawMonad)
open import Effect.Monad.State using (State; RawMonadState)
open import Data.Nat.Induction using (Acc; acc; <-wellFounded)
open import Data.Nat.Properties using (≤-refl; ≤-trans; n<1+n)
open import Data.Integer using () renaming (_≤_ to _≤ℤ_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)
open import Algebra.Bundles using (Monoid)
open import Data.List.Properties using (++-monoid)
import Data.List.Effectful as ListEffectful
import Data.List.Base as ListBase
-- END MIRTH-SYNC COMMON IMPORTS


open import Data.Nat    using (ℕ; _+_; _≤?_)
open import Data.Bool   using (Bool; true; false; not; _∧_)
open import Data.String using (String; _≟_)
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym)
open import Function.Equivalence using (_⇔_; equivalence)

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
