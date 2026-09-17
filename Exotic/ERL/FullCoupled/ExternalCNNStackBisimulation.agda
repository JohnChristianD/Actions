{-# OPTIONS --safe #-}
module Exotic.ERL.FullCoupled.ExternalCNNStackBisimulation where

open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)

record CNNStack (X Y : Set) (RX : X → X → Set) (RY : Y → Y → Set) : Set where
  constructor cnnStack
  field
    map : X → Y
    preserve : ∀ {x y} → RX x y → RY (map x) (map y)
open CNNStack public

identityStack : ∀ {X : Set} (R : X → X → Set) → CNNStack X X R R
identityStack R = cnnStack (λ x → x) (λ e → e)

composeStack :
  ∀ {X Y Z : Set}
  {RX : X → X → Set} {RY : Y → Y → Set} {RZ : Z → Z → Set} →
  CNNStack X Y RX RY → CNNStack Y Z RY RZ → CNNStack X Z RX RZ
composeStack A B =
  cnnStack
    (λ x → map B (map A x))
    (λ e → preserve B (preserve A e))

stackMap : ∀ {X : Set} {R : X → X → Set} → Nat → CNNStack X X R R → X → X
stackMap zero S x = x
stackMap (suc n) S x = stackMap n S (map S x)

stackPreserves :
  ∀ {X : Set} {R : X → X → Set}
  (n : Nat) (S : CNNStack X X R R) {x y : X} →
  R x y →
  R (stackMap n S x) (stackMap n S y)
stackPreserves zero S e = e
stackPreserves (suc n) S e = stackPreserves n S (preserve S e)

record TransitionSystem (X S : Set) : Set where
  constructor transitionSystem
  field
    relation : X → X → Set
    observe : X → S
    next : S → S
open TransitionSystem public

record CNNTransitionWitness (X S : Set) : Set where
  constructor cnnTransitionWitness
  field
    system : TransitionSystem X S
    representation : CNNStack X X (relation system) (relation system)
open CNNTransitionWitness public

cnn-stack-transition-preserves :
  ∀ {X S : Set} (W : CNNTransitionWitness X S) (n : Nat)
  {x y : X} →
  relation (system W) x y →
  relation (system W) (stackMap n (representation W) x)
                         (stackMap n (representation W) y)
cnn-stack-transition-preserves W n e = stackPreserves n (representation W) e

record TransitionAdapter (X H S : Set) : Set where
  constructor transitionAdapter
  field
    encode : X → H
    input : H → S
    next : S → S
open TransitionAdapter public

cnn-stack-lift :
  ∀ {X H S : Set}
  (A : TransitionAdapter X H S)
  (C : CNNStack X X (λ x y → encode A x ≡ encode A y)
                       (λ x y → encode A x ≡ encode A y)) →
  X → S
cnn-stack-lift A C x = next A (input A (encode A (map C x)))

cnn-stack-lift-factor :
  ∀ {X H S : Set}
  (A : TransitionAdapter X H S)
  (C : CNNStack X X (λ x y → encode A x ≡ encode A y)
                       (λ x y → encode A x ≡ encode A y)) x →
  cnn-stack-lift A C x ≡ next A (input A (encode A (map C x)))
cnn-stack-lift-factor A C x = refl
