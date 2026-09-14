{-# OPTIONS --safe #-}
module Exotic.ERL.Exploration.ExplorationTheoremSchema where

open import Agda.Builtin.Equality using (_≡_; refl)

infix 4 _—→_

data Reach {S : Set} (_—→_ : S → S → Set) : S → S → Set where
  here : ∀ {s} → Reach _—→_ s s
  there : ∀ {s t u} → s —→ t → Reach _—→_ t u → Reach _—→_ s u

Irreducible : ∀ {S : Set} → (S → S → Set) → Set
Irreducible _—→_ = ∀ s t → Reach _—→_ s t

SelfLoop : ∀ {S : Set} → (S → S → Set) → Set
SelfLoop _—→_ = ∀ s → s —→ s

record PeriodOne {S : Set} (_—→_ : S → S → Set) : Set where
  constructor periodOne
  field
    irreducible : Irreducible _—→_
    selfLoop : SelfLoop _—→_

-- In this finite theorem ledger, aperiodicity is certified by irreducibility
-- together with a reachable one-step return. No limit or statistical theorem
-- is used.
Aperiodic : ∀ {S : Set} → (S → S → Set) → Set
Aperiodic _—→_ = PeriodOne _—→_

periodOne-from-components : ∀ {S : Set} {_—→_ : S → S → Set}
  → Irreducible _—→_
  → SelfLoop _—→_
  → PeriodOne _—→_
periodOne-from-components r l = periodOne r l

a-periodic-from-components : ∀ {S : Set} {_—→_ : S → S → Set}
  → Irreducible _—→_
  → SelfLoop _—→_
  → Aperiodic _—→_
a-periodic-from-components = periodOne-from-components

same-state-reachable : ∀ {S : Set} {_—→_ : S → S → Set} (s : S)
  → Reach _—→_ s s
same-state-reachable s = here

reach-transitive : ∀ {S : Set} {_—→_ : S → S → Set}
  {s t u : S}
  → Reach _—→_ s t
  → Reach _—→_ t u
  → Reach _—→_ s u
reach-transitive here q = q
reach-transitive (there p r) q = there p (reach-transitive r q)

selfLoop-is-return : ∀ {S : Set} {_—→_ : S → S → Set}
  → SelfLoop _—→_
  → ∀ s → Reach _—→_ s s
selfLoop-is-return loop s = there (loop s) here
