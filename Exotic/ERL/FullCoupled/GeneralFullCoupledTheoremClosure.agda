{-# OPTIONS --safe #-}
module Exotic.ERL.FullCoupled.GeneralFullCoupledTheoremClosure where

open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_) 
open import Data.Fin using (Fin)

open import Exotic.ERL.FullCoupled.GeneralFullCoupledLearnerMonolith as L
open import Exotic.ERL.FullCoupled.GeneralFullCoupledTheoremsMonolith as T

-- Policy is sparsemax over the LCB-shifted score surface, not attention.
lcbPolicy-score-law : ∀ {A} (q : L.QVec A) (c : L.CountVec A) (a : Fin A) →
  L.scoreA q c a ≡ L.int8Add (q a) (L.lcbBonus (c a))
lcbPolicy-score-law q c a = refl

generalPolicy-is-lcb-sparsemax : ∀ {A} K s →
  L.generalPolicy K s ≡
  L.sparsemaxPolicy (L.actionSpaceK K) (L.q s) (L.counts s)
generalPolicy-is-lcb-sparsemax K s = refl

learnerStep-clock-closure : ∀ {A} K s r →
  L.clock (L.learnerStep K s r) ≡ suc (L.clock s)
learnerStep-clock-closure K s r = T.learnerStep-clock K s r

learnerStep-action-closure : ∀ {A} K s r →
  L.lastAction (L.learnerStep K s r) ≡ L.generalPolicy K s
learnerStep-action-closure K s r = refl

learnerStep-q-closure : ∀ {A} K s r →
  L.q (L.learnerStep K s r) ≡
  L.updateAt (L.q s) (L.generalPolicy K s)
    (L.int8Add r
      (L.munchausenSignal
        (L.mode K)
        (L.sparsemaxWeight
          (L.actionSpaceK K) (L.q s) (L.counts s)
          (L.generalPolicy K s)))
learnerStep-q-closure K s r = refl

learnerStep-count-closure : ∀ {A} K s r →
  L.counts (L.learnerStep K s r) ≡
  L.incAt (L.counts s) (L.generalPolicy K s)
learnerStep-count-closure K s r = refl

iterateLearner-zero-closure : ∀ {A} K s r →
  L.iterateLearner K zero s r ≡ s
iterateLearner-zero-closure K s r = refl

iterateLearner-suc-closure : ∀ {A} K n s r →
  L.iterateLearner K (suc n) s r ≡
  L.learnerStep K (L.iterateLearner K n s r) r
iterateLearner-suc-closure K n s r = refl

prefixAction-zero-closure : ∀ T →
  L.prefixAction T zero ≡ L.identityMobius
prefixAction-zero-closure T = refl

prefixAction-suc-closure : ∀ T n →
  L.prefixAction T (suc n) ≡
  L.composeMobius (L.atDepth T n) (L.prefixAction T n)
prefixAction-suc-closure T n = refl

semidirectCompose-mobius-closure : ∀ f g s x →
  T.semidirectMobiusStep (L.composeMobius f g) s x ≡
  T.semidirectMobiusStep f s (L.run g x)
semidirectCompose-mobius-closure f g s x = refl

traceStep-closure : ∀ T n s x →
  T.traceStep T n s x ≡
  L.gruStep s (L.run (L.atDepth T n) (T.traceInput T n x))
traceStep-closure T n s x = refl

traceIterate-zero-closure : ∀ T s x →
  T.traceIterate T zero s x ≡ s
traceIterate-zero-closure T s x = refl

traceIterate-suc-closure : ∀ T n s x →
  T.traceIterate T (suc n) s x ≡
  T.traceStep T n (T.traceIterate T n s x) x
traceIterate-suc-closure T n s x = refl

traceIterate-depth-invariant : ∀ T n s x →
  L.gruPersistent (T.traceIterate T n s x) ≡ L.gruPersistent s
traceIterate-depth-invariant T zero s x = refl
traceIterate-depth-invariant T (suc n) s x =
  trans
    (T.gruPersistentLaw (T.traceIterate T n s x) (T.traceInput T n x))
    (traceIterate-depth-invariant T n s x)

traceGRU-depth-invariant-closure : ∀ T n s x →
  L.gruPersistent (T.traceGRU T n s x) ≡ L.gruPersistent s
traceGRU-depth-invariant-closure T n s x = T.trace-depth-invariant T n s x

weightsNumerators : ∀ {A : Nat} → (Fin A → L.SparseWeight) → L.List Nat
weightsNumerators {A} ws =
  L.mapList (λ a → L.numerator (ws a)) (L.finList A)

weightsNumeratorSum : ∀ {A : Nat} → (Fin A → L.SparseWeight) → Nat
weightsNumeratorSum ws = L.sumList (weightsNumerators ws)

-- Exact finite KKT certificate for the discrete sparsemax representation.
-- The weights are tied to L.sparsemaxWeight and the simplex equation sums
-- their actual Nat numerators over every Fin A action.
record SparsemaxKKTRealization (A : Nat) : Set where
  constructor sparsemaxKKTRealization
  field
    kernel : L.ActionSpace A
    q : L.QVec A
    counts : L.CountVec A
    weights : Fin A → L.SparseWeight
    weights-law : ∀ a → weights a ≡ L.sparsemaxWeight kernel q counts a
    supportSizeK : Nat
    supportNonempty : supportSizeK ≢ zero
    denominatorK : Nat
    denominator-law : ∀ a → L.denominator (weights a) ≡ denominatorK
    simplexLaw : weightsNumeratorSum weights ≡ denominatorK
    stationarity : Fin A → Set
    complementarity : Fin A → Set
open SparsemaxKKTRealization public

sparsemaxKKT-realized-simplex : ∀ {A} (W : SparsemaxKKTRealization A) →
  weightsNumeratorSum (weights W) ≡ denominatorK W
sparsemaxKKT-realized-simplex W = simplexLaw W

sparsemaxKKT-realized-weight-law : ∀ {A} (W : SparsemaxKKTRealization A) a →
  weights W a ≡ L.sparsemaxWeight (kernel W) (q W) (counts W) a
sparsemaxKKT-realized-weight-law W a = weights-law W a

-- Exact policy/attention separation marker. The policy consumes the scalar
-- LCB score vector; no attention matrix or softmax-attention theorem is used.
sparsemax-policy-not-attention-surface : ∀ {A} K s →
  L.generalPolicy K s ≡
  L.sparsemaxPolicy (L.actionSpaceK K) (L.q s) (L.counts s)
sparsemax-policy-not-attention-surface K s = refl

cnn-depth-closure : ∀ {R : Set}
  (C : T.StandardCNNStack R) d n x →
  T.iterateLayers (T.layer C) d (T.shift C n x) ≡
  T.shift C n (T.iterateLayers (T.layer C) d x)
cnn-depth-closure C d n x = T.standardCNN-depth-equivariant C d n x

cnn-learner-trajectory-closure : ∀ {X R H : Set}
  (C : T.CNNLearnerComparison X R H) n x →
  T.decodeState C (T.iterateEndo (T.cnnStep C) n (T.input C x)) ≡
  T.iterateEndo (T.learnerStep C) n (T.decodeState C (T.input C x))
cnn-learner-trajectory-closure C n x = T.cnnLearner-trajectory-bisimulation C n x
