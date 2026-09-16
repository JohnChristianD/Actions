{-# OPTIONS --safe #-}

module Exotic.ERL.FullCoupled.CanonicalGamePorts where

open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; cong)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)
open import Data.Nat using (_∸_; _≤_; z≤n; s≤s)
open import Data.Fin using (Fin; fromℕ<; toℕ)
open import Data.Fin.Properties using (toℕ-fromℕ<; toℕ<n)
open import Data.Nat.DivMod using (m%n<n; m<n⇒m%n≡m)
open import Data.Product using (_×_; _,_)
open import Data.Empty using (⊥)

record Int8 : Set where
  constructor int8
  field code : Fin 256
open Int8 public

int8OfNat : Nat → Int8
int8OfNat n = int8 (fromℕ< (m%n<n n 256))

zero8 : Int8
zero8 = int8OfNat 0

one8 : Int8
one8 = int8OfNat 1

add8 : Int8 → Int8 → Int8
add8 x y = int8OfNat (toℕ (code x) + toℕ (code y))

record StepResult (S : Set) : Set where
  constructor stepResult
  field observation : Int8
        state : S
        reward : Int8
        done : BoolLike

data BoolLike : Set where
  yes no : BoolLike

record PortAction4 : Set where
  constructor portAction4
  field action4 : Fin 4
open PortAction4 public

data KnapsackAction : Set where
  skipTake : KnapsackAction
  takeTake : KnapsackAction

record KnapsackState : Set where
  constructor knapsackState
  field index capacity value : Nat

knapsackWeights : Fin 8 → Nat
knapsackWeights i = toℕ i + 1

knapsackValues : Fin 8 → Nat
knapsackValues i = (toℕ i + 1) * 2

knapsackStep : KnapsackAction → KnapsackState → StepResult KnapsackState
knapsackStep a (knapsackState i c v) with a
... | skipTake = stepResult (int8OfNat i) (knapsackState i c v) zero8 no
... | takeTake with i <ᵇ 8
...   | false = stepResult (int8OfNat i) (knapsackState i c v) zero8 yes
...   | true with knapsackWeights i ≤ c
...     | false = stepResult (int8OfNat i) (knapsackState i c v) zero8 no
...     | true = stepResult (int8OfNat i) (knapsackState (suc i) (c ∸ knapsackWeights i) (v + knapsackValues i)) (int8OfNat (knapsackValues i)) no

record MazeState : Set where
  constructor mazeState
  field row col goalRow goalCol time : Nat

mazeOpen : Nat → Nat → BoolLike
mazeOpen r c with r ≤ 9
... | false = no
... | true with c ≤ 9
...   | false = no
...   | true = yes

mazeMove : Fin 4 → Nat × Nat → Nat × Nat
mazeMove a (r , c) with toℕ a
... | zero = r ∸ 1 , c
... | suc zero = r , suc c
... | suc (suc zero) = suc r , c
... | _ = r , c ∸ 1

mazeStep : Fin 4 → MazeState → StepResult MazeState
mazeStep a (mazeState r c gr gc t) with mazeMove a (r , c)
... | nr , nc with mazeOpen nr nc
...   | no = stepResult (int8OfNat (r + c)) (mazeState r c gr gc (suc t)) zero8 no
...   | yes with nr ≡ gr
...     | refl with nc ≡ gc
...       | refl = stepResult (int8OfNat (nr + nc)) (mazeState nr nc gr gc (suc t)) (int8OfNat 1) yes
...       | _ = stepResult (int8OfNat (nr + nc)) (mazeState nr nc gr gc (suc t)) zero8 no
...     | _ = stepResult (int8OfNat (nr + nc)) (mazeState nr nc gr gc (suc t)) zero8 no

record LBFState : Set where
  constructor lbfState
  field a1r a1c a2r a2c foodR foodC foodLevel time : Nat

lbfStep : Fin 6 → LBFState → StepResult LBFState
lbfStep a (lbfState r1 c1 r2 c2 fr fc fl t) with toℕ a
... | zero = stepResult (int8OfNat r1) (lbfState (r1 ∸ 1) c1 (r2 ∸ 1) c2 fr fc fl (suc t)) zero8 no
... | suc zero = stepResult (int8OfNat c1) (lbfState r1 (suc c1) r2 (suc c2) fr fc fl (suc t)) zero8 no
... | suc (suc zero) = stepResult (int8OfNat r1) (lbfState (suc r1) c1 (suc r2) c2 fr fc fl (suc t)) zero8 no
... | suc (suc (suc zero)) = stepResult (int8OfNat c1) (lbfState r1 (c1 ∸ 1) r2 (c2 ∸ 1) fr fc fl (suc t)) zero8 no
... | suc (suc (suc (suc zero))) = stepResult (int8OfNat fr) (lbfState r1 c1 r2 c2 fr fc zero fl (suc t)) (int8OfNat fl) no
... | _ with r1 ≡ fr
...   | refl with c1 ≡ fc
...     | refl = stepResult (int8OfNat fl) (lbfState r1 c1 r2 c2 fr fc zero (suc t)) (int8OfNat fl) no
...     | _ = stepResult (int8OfNat fl) (lbfState r1 c1 r2 c2 fr fc fl (suc t)) zero8 no
...   | _ = stepResult (int8OfNat fl) (lbfState r1 c1 r2 c2 fr fc fl (suc t)) zero8 no

record MetaMazeState : Set where
  constructor metaMazeState
  field row col goalRow goalCol time : Nat

metaMazeStep : Fin 4 → MetaMazeState → StepResult MetaMazeState
metaMazeStep = mazeStep′ where
  mazeStep′ : Fin 4 → MetaMazeState → StepResult MetaMazeState
  mazeStep′ a (metaMazeState r c gr gc t) with mazeMove a (r , c)
  ... | nr , nc with mazeOpen nr nc
  ...   | no = stepResult (int8OfNat (r + c)) (metaMazeState r c gr gc (suc t)) zero8 no
  ...   | yes with nr ≡ gr
  ...     | refl with nc ≡ gc
  ...       | refl = stepResult (int8OfNat (nr + nc)) (metaMazeState nr nc gr gc (suc t)) (int8OfNat 10) yes
  ...       | _ = stepResult (int8OfNat (nr + nc)) (metaMazeState nr nc gr gc (suc t)) zero8 no
  ...     | _ = stepResult (int8OfNat (nr + nc)) (metaMazeState nr nc gr gc (suc t)) zero8 no

fourRoomsStep : Fin 4 → MazeState → StepResult MazeState
fourRoomsStep = mazeStep

record PongState : Set where
  constructor pongState
  field p1 p2 ballR ballC velR velC time : Nat

pongStep : Fin 3 → PongState → StepResult PongState
pongStep a (pongState p1 p2 br bc vr vc t) =
  let np1 = ifMove (toℕ a) p1
      np2 = np1
      nbr = br + vr
      nbc = bc + vc
  in stepResult (int8OfNat (nbr + nbc)) (pongState np1 np2 nbr nbc vr vc (suc t)) one8 no
  where
    ifMove : Nat → Nat → Nat
    ifMove zero p = p
    ifMove (suc zero) p = p ∸ 1
    ifMove _ p = suc p

record MemoryChainState : Set where
  constructor memoryChainState
  field memory query time : Nat

memoryChainStep : Fin 2 → MemoryChainState → StepResult MemoryChainState
memoryChainStep a (memoryChainState m q t) with t ≤ 5
... | true = stepResult (int8OfNat m) (memoryChainState m q (suc t)) zero8 no
... | false with toℕ a ≡ q
...   | refl = stepResult (int8OfNat m) (memoryChainState m q (suc t)) (int8OfNat 1) no
...   | _ = stepResult (int8OfNat m) (memoryChainState m q (suc t)) zero8 no

record DiscountingChainState : Set where
  constructor discountingChainState
  field rewardTime time : Nat

discountingChainStep : Fin 5 → DiscountingChainState → StepResult DiscountingChainState
discountingChainStep a (discountingChainState rt t) with t ≡ rt
... | refl = stepResult (int8OfNat rt) (discountingChainState rt (suc t)) (int8OfNat (toℕ a + 1)) no
... | _ = stepResult (int8OfNat rt) (discountingChainState rt (suc t)) zero8 no

record CartPoleQuantizedState : Set where
  constructor cartPoleQuantizedState
  field position velocity angle angularVelocity time : Nat

cartPoleQuantizedStep : Fin 2 → CartPoleQuantizedState → StepResult CartPoleQuantizedState
cartPoleQuantizedStep a (cartPoleQuantizedState p v ang av t) with toℕ a
... | zero = stepResult (int8OfNat p) (cartPoleQuantizedState (p ∸ 1) v ang av (suc t)) zero8 no
... | _ = stepResult (int8OfNat p) (cartPoleQuantizedState (suc p) v ang av (suc t)) zero8 no

record BernoulliBanditState : Set where
  constructor bernoulliBanditState
  field best lastAction lastReward time : Nat

bernoulliBanditStep : Fin 2 → BernoulliBanditState → StepResult BernoulliBanditState
bernoulliBanditStep a (bernoulliBanditState best la lr t) with toℕ a ≡ best
... | refl = stepResult (int8OfNat best) (bernoulliBanditState best (toℕ a) 1 (suc t)) one8 no
... | _ = stepResult (int8OfNat best) (bernoulliBanditState best (toℕ a) 0 (suc t)) zero8 no

record RockSampleState : Set where
  constructor rockSampleState
  field row col rockGood time : Nat

rockSampleStep : Fin 6 → RockSampleState → StepResult RockSampleState
rockSampleStep a (rockSampleState r c g t) with toℕ a
... | zero = stepResult (int8OfNat r) (rockSampleState (r ∸ 1) c g (suc t)) zero8 no
... | suc zero = stepResult (int8OfNat c) (rockSampleState r (suc c) g (suc t)) zero8 no
... | suc (suc zero) = stepResult (int8OfNat r) (rockSampleState (suc r) c g (suc t)) zero8 no
... | suc (suc (suc zero)) = stepResult (int8OfNat c) (rockSampleState r (c ∸ 1) g (suc t)) zero8 no
... | suc (suc (suc (suc zero))) with r ≡ 3
...   | refl = stepResult (int8OfNat c) (rockSampleState r c 0 (suc t)) (ifNat g) no
...   | _ = stepResult (int8OfNat c) (rockSampleState r c g (suc t)) zero8 no
... | _ = stepResult (int8OfNat g) (rockSampleState r c g (suc t)) zero8 no
  where
    ifNat : Nat → Int8
    ifNat zero = zero8
    ifNat _ = one8

jumanjiKnapsackPort : KnapsackState → Set
jumanjiKnapsackPort s = StepResult KnapsackState

jumanjiMazePort : MazeState → Set
jumanjiMazePort s = StepResult MazeState

jumanjiLBFPort : LBFState → Set
jumanjiLBFPort s = StepResult LBFState

gymnaxMetaMazePort : MetaMazeState → Set
gymnaxMetaMazePort s = StepResult MetaMazeState

gymnaxFourRoomsPort : MazeState → Set
gymnaxFourRoomsPort s = StepResult MazeState

gymnaxPongPort : PongState → Set
gymnaxPongPort s = StepResult PongState

memoryChainPort : MemoryChainState → Set
memoryChainPort s = StepResult MemoryChainState

discountingChainPort : DiscountingChainState → Set
discountingChainPort s = StepResult DiscountingChainState

cartPolePort : CartPoleQuantizedState → Set
cartPolePort s = StepResult CartPoleQuantizedState

bernoulliBanditPort : BernoulliBanditState → Set
bernoulliBanditPort s = StepResult BernoulliBanditState

rockSamplePort : RockSampleState → Set
rockSamplePort s = StepResult RockSampleState

-- The finite execution layer deliberately fixes stochastic/continuous sources to
-- explicit finite deterministic projections. This preserves action, transition,
-- reward and termination shapes without importing probability or real analysis.
