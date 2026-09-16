{-# OPTIONS --safe #-}

module Exotic.ERL.FullCoupled.CanonicalEndToEndFaithfulBench_test where

open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Exotic.ERL.FullCoupled.CanonicalEndToEndFaithfulBench2

check-cartpole-regret : metricRegret cartPoleMetrics ≡ 500
check-cartpole-regret = refl
check-cartpole-success : metricSuccess cartPoleMetrics ≡ 1
check-cartpole-success = refl

check-bandit0-regret : metricRegret banditBest0Metrics ≡ 2
check-bandit0-regret = refl
check-bandit0-success : metricSuccess banditBest0Metrics ≡ 0
check-bandit0-success = refl
check-bandit1-regret : metricRegret banditBest1Metrics ≡ 2
check-bandit1-regret = refl
check-bandit1-success : metricSuccess banditBest1Metrics ≡ 0
check-bandit1-success = refl

check-knapsack-regret : metricRegret knapsackMetrics ≡ 2
check-knapsack-regret = refl
check-knapsack-success : metricSuccess knapsackMetrics ≡ 0
check-knapsack-success = refl

check-maze-regret : metricRegret mazeV0Metrics ≡ 1
check-maze-regret = refl
check-maze-success : metricSuccess mazeV0Metrics ≡ 0
check-maze-success = refl
check-metaMaze-regret : metricRegret metaMazeMetrics ≡ 10
check-metaMaze-regret = refl
check-metaMaze-success : metricSuccess metaMazeMetrics ≡ 0
check-metaMaze-success = refl
check-fourRooms-regret : metricRegret fourRoomsMetrics ≡ 1
check-fourRooms-regret = refl
check-fourRooms-success : metricSuccess fourRoomsMetrics ≡ 0
check-fourRooms-success = refl

check-lbf-regret : metricRegret levelBasedForagingMetrics ≡ 1
check-lbf-regret = refl
check-lbf-success : metricSuccess levelBasedForagingMetrics ≡ 0
check-lbf-success = refl
check-pong-regret : metricRegret pongMetrics ≡ 0
check-pong-regret = refl
check-pong-success : metricSuccess pongMetrics ≡ 1
check-pong-success = refl

check-memory-regret : metricRegret memoryChainMetrics ≡ 0
check-memory-regret = refl
check-memory-success : metricSuccess memoryChainMetrics ≡ 1
check-memory-success = refl
check-discounting-regret : metricRegret discountingChainMetrics ≡ 1
check-discounting-regret = refl
check-discounting-success : metricSuccess discountingChainMetrics ≡ 1
check-discounting-success = refl

check-rock-regret : metricRegret rockSampleMetrics ≡ 1
check-rock-regret = refl
check-rock-success : metricSuccess rockSampleMetrics ≡ 0
check-rock-success = refl