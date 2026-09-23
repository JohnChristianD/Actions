{-# OPTIONS --safe #-}

module Exotic.ERL.FullCoupled.CanonicalGamePorts where

open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)
open import Data.Nat using (_∸_; _≤_; z≤n; s≤s)
open import Data.Integer using (ℤ; +_)
open import Data.Product using (_×_; _,_)
open import Data.Empty using (⊥)

data BoolLike : Set where
  yes no : BoolLike

record Int8 : Set where
  constructor int8
  field code : ℤ
open Int8 public

int8OfNat : Nat → Int8
int8OfNat n = int8 (+ n)

zero8 : Int8
zero8 = int8OfNat 0

one8 : Int8
one8 = int8OfNat 1

record StepResult (S : Set) : Set where
  constructor stepResult
  field observation : Int8
        state : S
        reward : Int8
        done : BoolLike
open StepResult public

natEq : Nat → Nat → BoolLike
natEq zero zero = yes
natEq zero (suc n) = no
natEq (suc m) zero = no
natEq (suc m) (suc n) = natEq m n

leBool : Nat → Nat → BoolLike
leBool zero _ = yes
leBool (suc _) zero = no
leBool (suc m) (suc n) = leBool m n

record KnapsackState : Set where
  constructor knapsackState
  field index capacity value : Nat

data KnapsackAction : Set where
  chooseItem0 chooseItem1 : KnapsackAction

knapsackWeight0 : Nat
knapsackWeight0 = 1

knapsackWeight1 : Nat
knapsackWeight1 = 2

knapsackValue0 : Nat
knapsackValue0 = 2

knapsackValue1 : Nat
knapsackValue1 = 4

knapsackStep : KnapsackAction → KnapsackState → StepResult KnapsackState
knapsackStep chooseItem0 (knapsackState i c v) with leBool knapsackWeight0 c
... | no = stepResult (int8OfNat i) (knapsackState i c v) zero8 yes
... | yes = stepResult (int8OfNat 0) (knapsackState (suc i) (c ∸ knapsackWeight0) (v + knapsackValue0)) (int8OfNat knapsackValue0) no
knapsackStep chooseItem1 (knapsackState i c v) with leBool knapsackWeight1 c
... | no = stepResult (int8OfNat i) (knapsackState i c v) zero8 yes
... | yes = stepResult (int8OfNat 1) (knapsackState (suc i) (c ∸ knapsackWeight1) (v + knapsackValue1)) (int8OfNat knapsackValue1) no

record MazeState : Set where
  constructor mazeState
  field row col goalRow goalCol time : Nat

mazeMove : Nat → Nat × Nat → Nat × Nat
mazeMove a (r , c) with a
... | zero = r ∸ 1 , c
... | suc zero = r , suc c
... | suc (suc zero) = suc r , c
... | _ = r , c ∸ 1

mazeOpen : Nat → Nat → BoolLike
mazeOpen r c with leBool r 4
... | no = no
... | yes with leBool c 4
...   | no = no
...   | yes = yes

mazeStep : Nat → MazeState → StepResult MazeState
mazeStep a (mazeState r c gr gc t) with mazeMove a (r , c)
... | nr , nc with mazeOpen nr nc
...   | no = stepResult (int8OfNat (r + c)) (mazeState r c gr gc (suc t)) zero8 no
...   | yes with natEq nr gr
...     | yes with natEq nc gc
...       | yes = stepResult (int8OfNat (nr + nc)) (mazeState nr nc gr gc (suc t)) one8 yes
...       | no = stepResult (int8OfNat (nr + nc)) (mazeState nr nc gr gc (suc t)) zero8 no
...     | no = stepResult (int8OfNat (nr + nc)) (mazeState nr nc gr gc (suc t)) zero8 no

-- Jumanji ToyGenerator's fixed 5x5 connectivity layout.
toyMazeOpen : Nat → Nat → BoolLike
toyMazeOpen zero c = orBool (between 0 0 c) (between 2 4 c)
toyMazeOpen (suc zero) c = orBool (between 0 0 c) (between 2 2 c)
toyMazeOpen (suc (suc zero)) c = orBool (between 0 0 c) (between 2 4 c)
toyMazeOpen (suc (suc (suc zero))) c = between 0 2 c
toyMazeOpen (suc (suc (suc (suc zero)))) c = between 0 4 c
toyMazeOpen _ _ = no
  where
    between : Nat → Nat → Nat → BoolLike
    between lo hi x with leBool lo x
    ... | no = no
    ... | yes with leBool x hi
    ...   | no = no
    ...   | yes = yes

    orBool : BoolLike → BoolLike → BoolLike
    orBool yes _ = yes
    orBool _ yes = yes
    orBool _ _ = no

record LBFState : Set where
  constructor lbfState
  field a1r a1c a2r a2c foodR foodC foodLevel time : Nat

lbfStep : Nat → LBFState → StepResult LBFState
lbfStep a (lbfState r1 c1 r2 c2 fr fc fl t) with a
... | zero = stepResult (int8OfNat r1) (lbfState (r1 ∸ 1) c1 (r2 ∸ 1) c2 fr fc fl (suc t)) zero8 no
... | suc zero = stepResult (int8OfNat c1) (lbfState r1 (suc c1) r2 (suc c2) fr fc fl (suc t)) zero8 no
... | suc (suc zero) = stepResult (int8OfNat r1) (lbfState (suc r1) c1 (suc r2) c2 fr fc fl (suc t)) zero8 no
... | suc (suc (suc zero)) = stepResult (int8OfNat c1) (lbfState r1 (c1 ∸ 1) r2 (c2 ∸ 1) fr fc fl (suc t)) zero8 no
... | suc (suc (suc (suc zero))) with natEq r1 fr
...   | yes with natEq c1 fc
...     | yes = stepResult (int8OfNat fl) (lbfState r1 c1 r2 c2 fr fc 0 (suc t)) (int8OfNat fl) no
...     | no = stepResult (int8OfNat fl) (lbfState r1 c1 r2 c2 fr fc fl (suc t)) zero8 no
...   | no = stepResult (int8OfNat fl) (lbfState r1 c1 r2 c2 fr fc fl (suc t)) zero8 no
... | _ = stepResult (int8OfNat fl) (lbfState r1 c1 r2 c2 fr fc fl (suc t)) zero8 no

record MetaMazeState : Set where
  constructor metaMazeState
  field row col goalRow goalCol time : Nat

metaMazeStep : Nat → MetaMazeState → StepResult MetaMazeState
metaMazeStep a (metaMazeState r c gr gc t) with mazeMove a (r , c)
... | nr , nc with mazeOpen nr nc
...   | no = stepResult (int8OfNat (r + c)) (metaMazeState r c gr gc (suc t)) zero8 no
...   | yes with natEq nr gr
...     | yes with natEq nc gc
...       | yes = stepResult (int8OfNat (nr + nc)) (metaMazeState nr nc gr gc (suc t)) (int8OfNat 10) yes
...       | no = stepResult (int8OfNat (nr + nc)) (metaMazeState nr nc gr gc (suc t)) zero8 no
...     | no = stepResult (int8OfNat (nr + nc)) (metaMazeState nr nc gr gc (suc t)) zero8 no

fourRoomsStep : Nat → MazeState → StepResult MazeState
fourRoomsStep = mazeStep

record PongState : Set where
  constructor pongState
  field p1 p2 ballR ballC velR velC time : Nat

pongStep : Nat → PongState → StepResult PongState
pongStep a (pongState p1 p2 br bc vr vc t) with a
... | zero = stepResult (int8OfNat (br + bc)) (pongState p1 p2 (br + vr) (bc + vc) vr vc (suc t)) one8 no
... | suc zero = stepResult (int8OfNat (br + bc)) (pongState (p1 ∸ 1) p2 (br + vr) (bc + vc) vr vc (suc t)) one8 no
... | _ = stepResult (int8OfNat (br + bc)) (pongState (suc p1) p2 (br + vr) (bc + vc) vr vc (suc t)) one8 no

record MemoryChainState : Set where
  constructor memoryChainState
  field memory query time : Nat

memoryChainStep : Nat → MemoryChainState → StepResult MemoryChainState
memoryChainStep a (memoryChainState m q t) with leBool t 5
... | yes with natEq (a) q
...   | yes = stepResult (int8OfNat m) (memoryChainState m q (suc t)) zero8 no
...   | no = stepResult (int8OfNat m) (memoryChainState m q (suc t)) zero8 no
... | no with natEq (a) q
...   | yes = stepResult (int8OfNat m) (memoryChainState m q (suc t)) one8 no
...   | no = stepResult (int8OfNat m) (memoryChainState m q (suc t)) zero8 no

record DiscountingChainState : Set where
  constructor discountingChainState
  field rewardTime time : Nat

discountingChainStep : Nat → DiscountingChainState → StepResult DiscountingChainState
discountingChainStep a (discountingChainState rt t) with natEq t rt
... | yes = stepResult (int8OfNat rt) (discountingChainState rt (suc t)) (int8OfNat (a + 1)) no
... | no = stepResult (int8OfNat rt) (discountingChainState rt (suc t)) zero8 no

record CartPoleQuantizedState : Set where
  constructor cartPoleQuantizedState
  field position velocity angle angularVelocity time : Nat

cartPoleQuantizedStep : Nat → CartPoleQuantizedState → StepResult CartPoleQuantizedState
cartPoleQuantizedStep a (cartPoleQuantizedState p v ang av t) with a
... | zero = stepResult (int8OfNat p) (cartPoleQuantizedState (p ∸ 1) v ang av (suc t)) zero8 no
... | _ = stepResult (int8OfNat p) (cartPoleQuantizedState (suc p) v ang av (suc t)) zero8 no

record BernoulliBanditState : Set where
  constructor bernoulliBanditState
  field best lastAction lastReward time : Nat

bernoulliBanditStep : Nat → BernoulliBanditState → StepResult BernoulliBanditState
bernoulliBanditStep a (bernoulliBanditState best la lr t) with natEq (a) best
... | yes = stepResult (int8OfNat best) (bernoulliBanditState best (a) 1 (suc t)) one8 no
... | no = stepResult (int8OfNat best) (bernoulliBanditState best (a) 0 (suc t)) zero8 no

record RockSampleState : Set where
  constructor rockSampleState
  field row col rockGood time : Nat

rockSampleStep : Nat → RockSampleState → StepResult RockSampleState
rockSampleStep a (rockSampleState r c g t) with a
... | zero = stepResult (int8OfNat r) (rockSampleState (r ∸ 1) c g (suc t)) zero8 no
... | suc zero = stepResult (int8OfNat c) (rockSampleState r (suc c) g (suc t)) zero8 no
... | suc (suc zero) = stepResult (int8OfNat r) (rockSampleState (suc r) c g (suc t)) zero8 no
... | suc (suc (suc zero)) = stepResult (int8OfNat c) (rockSampleState r (c ∸ 1) g (suc t)) zero8 no
... | suc (suc (suc (suc zero))) with natEq r 3
...   | yes with natEq g 1
...     | yes = stepResult (int8OfNat c) (rockSampleState r c 0 (suc t)) one8 no
...     | no = stepResult (int8OfNat c) (rockSampleState r c 0 (suc t)) (int8OfNat 255) no
...   | no = stepResult (int8OfNat g) (rockSampleState r c g (suc t)) zero8 no
... | _ = stepResult (int8OfNat g) (rockSampleState r c g (suc t)) zero8 no

jumanjiKnapsackPort : Set
jumanjiKnapsackPort = KnapsackState

jumanjiMazeV0Port : Set
jumanjiMazeV0Port = MazeState

jumanjiLevelBasedForagingV0Port : Set
jumanjiLevelBasedForagingV0Port = LBFState

gymnaxMetaMazePort : Set
gymnaxMetaMazePort = MetaMazeState

gymnaxFourRoomsPort : Set
gymnaxFourRoomsPort = MazeState

gymnaxPongMiscPort : Set
gymnaxPongMiscPort = PongState

gymnaxMemoryChainBsuitePort : Set
gymnaxMemoryChainBsuitePort = MemoryChainState

gymnaxDiscountingChainBsuitePort : Set
gymnaxDiscountingChainBsuitePort = DiscountingChainState

gymnaxCartPolePort : Set
gymnaxCartPolePort = CartPoleQuantizedState

gymnaxBernoulliBanditMiscPort : Set
gymnaxBernoulliBanditMiscPort = BernoulliBanditState

pobaxRockSamplePort : Set
pobaxRockSamplePort = RockSampleState
