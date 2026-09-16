# Mobius, Walsh-Hadamard, input-driven GRU, and pessimistic monolith

> Agentic implementation plan. Agda `--safe` is the acceptance oracle; Haskell is the automation language for theorem discovery and redundancy auditing.

**Goal:** Make the canonical deterministic learner actor-free and theorem-first while replacing the recurrent nonlinear boundary with an exact finite-rational Mobius ratio `x / (1 - x)`, replacing smooth sign-like surfaces with finite hard sign, replacing the old unnormalised transform with an exactly dyadic-normalized Walsh-Hadamard basis at dimension `4^k`, making recurrent parameter coordinates state-independent while keeping the update input-driven, making the q-log scale endogenous, and consolidating pruning automation.

**Canonical architecture:** Watkins is the only learned Q/action-selection source. Learned sparsemax attention is representation state, not an actor. The action-selection policy is derived from Watkins Q plus deterministic LCB/count correction and fixed-temperature sparsemax. The recurrent path consumes the action-selection signal through the normalized Walsh boundary and the finite Mobius recurrent carrier.

## Global constraints

- No independently learned actor parameterization.
- Learned sparsemax attention must remain representation/attention state.
- `canonicalPolicy` must be invariant under replacement of learned attention state.
- Recurrent parameter coordinates remain unchanged by the recurrent step.
- The recurrent output remains a function of the current input.
- `x / (1 - x)` is represented over an exact finite-rational boundary rather than being approximated by modular `Int8` arithmetic.
- The singular input `x = 1` receives an explicit total finite boundary, and the non-singular rational law is separately proved.
- Walsh-Hadamard dimension is a power of four so normalization is dyadic.
- Maximum pessimism is defined relative to the signed Q7 semantic order, not by raw modular code zero.
- Identity initialization is explicit only where the carrier actually has an identity element.
- Pessimistic initialization alone must never be presented as a no-cycle theorem.
- A no-cycle theorem requires a discharged Lyapunov/order witness or another exact invariant for the concrete update.
- Mobius associativity is the associativity of `MobiusGroup.composeAction`, not of Walsh-Hadamard multiplication.
- Negative q-log shaping stays finite and deterministic; its endogenous control must be a proved total state function.
- No automation pruning rule may ban the q-log algorithm name by text.
- New helper automation is Haskell or declarative Guix/Nix, not Python or Bash source scripts.

## Work completed by this plan

### Mobius recurrent carrier

`Exotic/ERL/FullCoupled/MobiusRational.agda` defines an exact numerator/denominator carrier and proves `mobiusRatio8-law` away from the explicit singularity boundary.

`Exotic/ERL/FullCoupled/DyadicGRU.agda` uses that carrier for the hidden coordinate, defines identity recurrent parameter initialization, proves persistent parameter coordinates, and preserves explicit input dependence.

### Hard sign

`CanonicalSparsemaxLearnerV2.agda` defines `HardSign8`, `hardSignCode`, and `hardSign8` as a total finite three-way sign surface with explicit zero behavior.

### Orthonormal Walsh-Hadamard

`Exotic/ERL/FullCoupled/FrozenOrthonormalWalshGRU.agda` defines the dimension-four basis `H₄ / 2`, records the exact raw Gram identities `H₄ H₄ᵀ = 4I`, and uses the fixed dyadic factor `1/2` to obtain the orthonormal basis. The learner lifts the two action coordinates into four dimensions before the transform.

### Pessimistic critic

The signed Q7 carrier interprets code `128` as semantic `-128`, the least admissible Q7 value. The critic therefore exposes `maxPessimisticCritic` with both Q coordinates at code `128`.

### Endogenous q-log scale

`endogenousNegativeScale8` derives the signed shaping coefficient from the current canonical policy surface, and `canonicalQLogControlStep` updates the scale as part of `canonicalFullStep`.

### Attention/actor separation

`canonicalPolicy-attention-invariant` proves that changing learned sparsemax attention state does not change action selection. Learned attention is therefore formally representation state, not a second actor.

### Composition theorem family

The Haskell generator now reports independent theorem families for the canonical monolith, finite Mobius boundary, Walsh boundary, recurrent boundary, and Mobius composition/persistence boundary.

## Remaining acceptance gate

The branch must pass:

1. the Haskell theorem-scope guard;
2. the Haskell redundancy audit;
3. `agda --safe` on Int8, Mobius rational boundary, recurrent boundary, Walsh boundary, Watkins critic, canonical monolith, canonical regression, count-memory theorem, and Mobius composition;
4. generated theorem-status compilation.

The generated report may say `Proven` only when the named proof terms exist and their corresponding Agda source modules compile under `--safe`.

## Strongest justified theorem claims

The current refactor provides stronger algebraic boundaries for attention/policy separation, exact finite-rational Mobius evaluation, persistent input-driven recurrent coordinates, dyadic normalized Walsh orthogonality, endogenous q-log control, and maximal semantic pessimistic initialization.

A stronger unconditional whole-learner finite-cycle theorem is not justified merely by those ingredients. The formal route remains a concrete strict-decrease witness for the actual `canonicalFullStep`, followed by `noNontrivialFiniteCycle`. Initialization and Mobius associativity do not substitute for that witness.

## Tsallis-2 note

The literature identifies sparsemax as the alpha-2 member of the alpha-entmax/Tsallis-regularized family. Formalizing its variational or entropy-optimality characterization could add a new theorem boundary. It does not by itself strengthen the learner's Mobius, Walsh, persistence, or finite-cycle composition theorems, so the computational kernel remains the exact sparsemax map until that additional theorem is discharged.
