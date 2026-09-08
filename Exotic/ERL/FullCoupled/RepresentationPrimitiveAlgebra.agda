{-# OPTIONS --safe #-}
module Exotic.ERL.FullCoupled.RepresentationPrimitiveAlgebra where

open import Agda.Builtin.Equality using (_≡_; refl; sym; trans; cong)
open import Agda.Builtin.Sigma using (Σ; _,_; fst; snd)
open import Agda.Builtin.Nat using (Nat; zero; suc)

------------------------------------------------------------------------
-- Minimal total algebraic boundary for representation primitives.
--
-- Division, square root, and transcendental activations are not assumed to
-- belong to an arbitrary Ring.  They enter only through lawful primitive
-- nodes, with domain evidence supplied at the call site.
------------------------------------------------------------------------

record Ring : Set₁ where
  field
    R : Set
    zero one : R
    add mul : R → R → R
    neg : R → R
    addAssoc : ∀ x y z → add (add x y) z ≡ add x (add y z)
    addComm : ∀ x y → add x y ≡ add y x
    addZeroL : ∀ x → add zero x ≡ x
    addZeroR : ∀ x → add x zero ≡ x
    mulAssoc : ∀ x y z → mul (mul x y) z ≡ mul x (mul y z)
    mulComm : ∀ x y → mul x y ≡ mul y x
    mulOneL : ∀ x → mul one x ≡ x
    mulOneR : ∀ x → mul x one ≡ x
    distrib : ∀ x y z → mul x (add y z) ≡ add (mul x y) (mul x z)
    zeroMulL : ∀ x → mul zero x ≡ zero
    zeroMulR : ∀ x → mul x zero ≡ zero
    addNegL : ∀ x → add (neg x) x ≡ zero
    addNegR : ∀ x → add x (neg x) ≡ zero

record PrimitiveAlgebra (G : Ring) : Set₁ where
  open Ring G
  field
    inv : R → R
    inv-law : ∀ {x} → x ≢ zero → mul x (inv x) ≡ one
    sqrt : R → R
    sqrt-law : ∀ {x} → SqrtDomain x → mul (sqrt x) (sqrt x) ≡ x
    tanh : R → R
    tanh-deriv : R → R
    tanh-vjp-law : ∀ x c → mul c (tanh-deriv x) ≡ mul c (add one (neg (mul (tanh x) (tanh x))))

  SqrtDomain : R → Set
  SqrtDomain x = Σ (R → R) (λ s → mul (s x) (s x) ≡ x)

record UnaryNode (A : Set) : Set₁ where
  field
    primal : A → A
    pullback : A → A → A

module Laws (G : Ring) (P : PrimitiveAlgebra G) where
  open Ring G
  open PrimitiveAlgebra P

  invNode : UnaryNode R
  invNode = record
    { primal = inv
    ; pullback = λ x c → neg (mul c (mul (inv x) (inv x)))
    }

  sqrtNode : UnaryNode R
  sqrtNode = record
    { primal = sqrt
    ; pullback = λ x c → mul c (inv (add (sqrt x) (sqrt x)))
    }

  tanhNode : UnaryNode R
  tanhNode = record
    { primal = tanh
    ; pullback = λ x c → mul c (tanh-deriv x)
    }

  compose : UnaryNode R → UnaryNode R → UnaryNode R
  compose f g = record
    { primal = λ x → UnaryNode.primal g (UnaryNode.primal f x)
    ; pullback = λ x c →
        UnaryNode.pullback f x
          (UnaryNode.pullback g (UnaryNode.primal f x) c)
    }

  composeLaw :
    ∀ f g x c →
    UnaryNode.pullback (compose f g) x c ≡
      UnaryNode.pullback f x
        (UnaryNode.pullback g (UnaryNode.primal f x) c)
  composeLaw f g x c = refl

  invCorrect : ∀ {x} → x ≢ zero → mul x (inv x) ≡ one
  invCorrect = inv-law

  sqrtCorrect : ∀ {x} → SqrtDomain x → mul (sqrt x) (sqrt x) ≡ x
  sqrtCorrect = sqrt-law

  tanhCorrect : ∀ x c →
    UnaryNode.pullback tanhNode x c ≡ mul c (add one (neg (mul (tanh x) (tanh x))))
  tanhCorrect x c = tanh-vjp-law x c

  normalized :
    ∀ {x eps} →
    x ≢ zero →
    eps ≢ zero →
    R
  normalized {x} {eps} _ _ = mul x (inv eps)

  normalizedScaleLaw :
    ∀ {x eps} →
    x ≢ zero →
    eps ≢ zero →
    normalized {x = x} {eps = eps} ≡ mul x (inv eps)
  normalizedScaleLaw _ _ = refl

------------------------------------------------------------------------
-- A representation gate is now a composition of lawful nodes.
-- The exact affine/mean/variance implementation can supply these nodes
-- separately; the global theorem needs no analytic postulates.
------------------------------------------------------------------------

gate : ∀ {G : Ring} → PrimitiveAlgebra G → UnaryNode (Ring.R G)
gate P = Laws.compose (Laws.invNode (recordRing P)) (Laws.tanhNode (recordRing P))
  where
  recordRing : ∀ {G : Ring} → PrimitiveAlgebra G → Ring
  recordRing {G} _ = G

compositionKernel : ∀ {G : Ring} (P : PrimitiveAlgebra G) x c →
  UnaryNode.pullback (gate P) x c ≡
    UnaryNode.pullback (Laws.invNode (G)) x
      (UnaryNode.pullback (Laws.tanhNode (G)) (PrimitiveAlgebra.inv P x) c)
compositionKernel P x c = refl
  where
  G = _

------------------------------------------------------------------------
-- Soundness boundary: all non-algebraic semantics are obligations carried
-- by PrimitiveAlgebra.  Nothing here invokes --unsafe, postulates, floating
-- point, or an undecidable domain test.
------------------------------------------------------------------------

representationAlgebraClosed : ∀ {G : Ring} → PrimitiveAlgebra G → Set
representationAlgebraClosed _ = Ring.R G
