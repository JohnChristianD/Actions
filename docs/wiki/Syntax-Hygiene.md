# Agda Syntax and Namespace Hygiene

The current theorem monolith has repeatedly crossed namespace boundaries between stdlib relations, generic records, and learner-specific fields. The repository now uses these preemptive rules.

## 1. Never export generic relation names when a stdlib relation is already in scope

Do not publicly expose a theorem-local field named `_≤_`.

Use a qualified semantic name such as `carrier≤` or `midpoint≤`.

This prevents a local record field from clashing with `Data.Nat._≤_` and other imported order structures.

## 2. Do not export imported learner names through unrelated records

The learner module already exports `learnerStep`.

A theorem witness record must therefore use a distinct field such as `transitionStep`, not another public `learnerStep` field.

The namespace collision was eliminated in the current source.

## 3. Prefer qualified module aliases

Core canonical modules use `L` for the general learner and `C` for the canonical coupled learner.

The theorem monolith uses `T` for its own reusable theorem definitions where needed.

Keep these aliases stable and avoid broad `open ... public` imports for modules with large field surfaces.

## 4. Type binders that are likely to generate metas

Use explicit binders for recurrent carrier values, for example `(r : L.Int8)` and `(s : CanonicalCoupledState A)`.

Do this especially in theorem records, anonymous lambdas, and fields whose names overlap with imported definitions.

## 5. Replace anonymous `with` lambdas in record constructors with named helpers

A branch proof should have a named type and a named definition, such as `prBranchFunction` and `prBranch-sound`.

Then the record constructor receives the named proof. This avoids Agda parser failures caused by embedding a `with` expression directly inside a constructor argument.

## 6. Bind implicit function parameters when the proof body uses them

The present blocker at line 592 is a scope error in `finiteSionSandwich`: the result type quantifies an implicit `payoff`, but the defining equation uses `payoff` without binding it on the left-hand side.

The collision-safe pattern is to bind the implicit argument in the definition head, for example `finiteSionSandwich {payoff = payoff} W = ...`.

## 7. Reserve short generic names

Avoid public field names `Carrier`, `step`, `update`, `choose`, `run`, `decode`, and `_≤_` when a module already imports or exports similarly generic names.

Use semantic prefixes or module qualification instead.

## 8. Keep canonical and legacy semantics visibly separate

Do not reuse the legacy `F4State` name in canonical modules. The canonical state is `CanonicalF4State` and the canonical parameters are `CanonicalF4Params`.

This prevents the canonical global βθ term from being confused with the legacy `l2Global` field.
