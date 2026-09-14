{-# OPTIONS --safe #-}
module Exotic.ERL.FullCoupled.DPGBellmanHaarComposition where

open import Agda.Builtin.Equality using (_≡_; refl; cong)
open import Data.Fin using (Fin; zero; suc; toℕ)
open import Data.Nat using (ℕ; _+_; _*_; _≤?_; _∸_)
open import Data.Product using (_×_; _,_)
open import Relation.Nullary using (yes; no)
open import Exotic.efficient_chad.Int8 using
  ( Int8
  ; code
  ; int8OfNat
  ; int8Add
  ; int8Mul
  ; zero8
  ; one8
  )
open import Exotic.ERL.FullCoupled.FiniteHaarSparsemaxRoPE using
  ( Int8Pair
  ; frontEnd
  ; frontEndToGRU
  )
open import Exotic.ERL.FullCoupled.Int8DPG using
  ( SharedDPGBand
  ; sharedActor
  ; sharedCritic
  )

------------------------------------------------------------------------
-- Finite ordered Q semantics.
--
-- Int8 itself is a finite carrier with modular arithmetic, so it is not
-- used as an ordered Bellman-value space here. The Bellman layer uses Nat
-- values and a two-action finite action set; this keeps max-Q semantics
-- honest while the Int8 layer remains the finite controller carrier.
------------------------------------------------------------------------

State : Set
State = Fin 2

Action : Set
Action = Fin 2

Q : Set₁
Q = State → Action → ℕ

max2 : ℕ → ℕ → ℕ
max2 x y with x ≤? y
... | yes p = y
... | no p = x

maxQ : Q → State → ℕ
maxQ q s = max2 (q s zero) (q s (suc zero))

GreedyPolicy : Set
GreedyPolicy = State → Action

IsGreedy : GreedyPolicy → Q → Set
IsGreedy π q = ∀ s → q s (π s) ≡ maxQ q s

------------------------------------------------------------------------
-- Q-argmax bootstrapping and the DPG connection.
--
-- The discount operation is kept abstract. For a real discounted MDP it is
-- instantiated by multiplication by gamma with 0 <= gamma < 1 in an ordered
-- value space; that analytic contraction theorem is deliberately not encoded
-- in modular Int8 arithmetic.
------------------------------------------------------------------------

Discount : Set
Discount = ℕ → ℕ

discountedBoot : ℕ → Discount → ℕ → ℕ
discountedBoot reward δ qValue = reward + δ qValue

maxQBootstrap :
  ℕ → Discount → Q → State → ℕ
maxQBootstrap reward δ q s = discountedBoot reward δ (maxQ q s)

greedyPolicyBootstrap :
  ℕ → Discount → Q → GreedyPolicy → State → ℕ
greedyPolicyBootstrap reward δ q π s =
  discountedBoot reward δ (q s (π s))

DPG-maxQ-bootstrap-equivalence :
  ∀ (reward : ℕ) (δ : Discount) (q : Q)
    (π : GreedyPolicy) →
  IsGreedy π q →
  ∀ s →
  greedyPolicyBootstrap reward δ q π s
  ≡ maxQBootstrap reward δ q s
DPG-maxQ-bootstrap-equivalence reward δ q π greedy s =
  cong (discountedBoot reward δ) (greedy s)

------------------------------------------------------------------------
-- A deterministic actor is not automatically greedy. The equality above
-- therefore has a real optimization premise rather than smuggling argmax
-- behavior into the critic type.
------------------------------------------------------------------------

DPG-actor-is-greedy-is-an-extra-assumption :
  ∀ (π : GreedyPolicy) (q : Q) → IsGreedy π q → IsGreedy π q
DPG-actor-is-greedy-is-an-extra-assumption π q h = h

------------------------------------------------------------------------
-- Unnormalized integer Haar/Hadamard coefficients.
--
-- H = [[1,1],[1,-1]] has orthogonal columns with squared norm 2. Thus it is
-- orthogonal-but-not-orthonormal: no 1/sqrt(2) factor is needed, and no
-- non-dyadic normalization is introduced.
------------------------------------------------------------------------

negOne8 : Int8
negOne8 = int8OfNat 255

two8 : Int8
two8 = int8OfNat 2

neg8 : Int8 → Int8
neg8 x = int8OfNat (256 ∸ toℕ (code x))

haarInt8 : Int8Pair → Int8Pair
haarInt8 (x , y) =
  ( int8Add x y
  , int8Add x (neg8 y)
  )

haarColumnLeft : Int8 × Int8
haarColumnLeft = one8 , one8

haarColumnRight : Int8 × Int8
haarColumnRight = one8 , negOne8

dot8 : (Int8 × Int8) → (Int8 × Int8) → Int8
dot8 (a , b) (c , d) = int8Add (int8Mul a c) (int8Mul b d)

haar-columns-orthogonal :
  dot8 haarColumnLeft haarColumnRight ≡ zero8
haar-columns-orthogonal = refl

haar-column-left-norm :
  dot8 haarColumnLeft haarColumnLeft ≡ two8
haar-column-left-norm = refl

haar-column-right-norm :
  dot8 haarColumnRight haarColumnRight ≡ two8
haar-column-right-norm = refl

------------------------------------------------------------------------
-- Composition after the integer Haar front-end.
------------------------------------------------------------------------

record NewComposedBand : Set₁ where
  constructor newComposedBand
  field
    band : SharedDPGBand

open NewComposedBand public

newActorOutput : NewComposedBand → Int8Pair → Int8
newActorOutput b p = sharedActor (band b) (frontEndToGRU p)

newCriticOutput : NewComposedBand → Int8Pair → Int8
newCriticOutput b p = sharedCritic (band b) (frontEndToGRU p)

newCompositionLaw :
  ∀ (b : NewComposedBand) (p : Int8Pair) →
  (newActorOutput b p , newCriticOutput b p)
  ≡
  ( sharedActor (band b) (frontEndToGRU p)
  , sharedCritic (band b) (frontEndToGRU p) )
newCompositionLaw b p = refl

------------------------------------------------------------------------
-- The front-end and the actor/critic are a common prefix followed by two
-- heads. The factorization is exact in the finite carrier.
------------------------------------------------------------------------

commonPrefixThenHeads :
  SharedDPGBand → Int8Pair → Int8 × Int8
commonPrefixThenHeads b p =
  sharedActor b (frontEndToGRU p) ,
  sharedCritic b (frontEndToGRU p)

commonPrefix-factorization :
  ∀ (b : SharedDPGBand) (p : Int8Pair) →
  commonPrefixThenHeads b p
  ≡
  ( sharedActor b (frontEndToGRU p)
  , sharedCritic b (frontEndToGRU p) )
commonPrefix-factorization b p = refl
