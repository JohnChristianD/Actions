# MARL-facing laws, Hodge-Maxwell composition, and the F4 growth ray

This note restores the semantic explanation that the topology should make visible. The phrase “three MARL laws” is a grouping of the existing exact learner laws, not a claim that MARL literature names these three propositions as a standard canonical trio.

## The three exact learner laws

The first law is recurrent scan composition. The canonical GRU transition is exposed as a recurrent network, and prefix scans compose through the existing recurrent-prefix correctness and split laws. In the theorem layer this is consumed by `canonical-recurrent-prefix-monoid-homomorphism` and `canonical-recurrent-scan-conjugacy-theorem`. Operationally: processing a prefix and then its continuation is extensionally the same as processing the concatenated input stream.

The second law is the optimizer step law. `canonicalF4RecurrentNetwork-step-law` identifies the F4 recurrent component with the actual `f4ThetaStep` applied to the current optimizer state and signal. This is not a generic theorem about every optimizer; it is a definitional characterization of this F4/L2 update.

The third law is NormPair inertness. `canonicalNormPairRecurrentNetwork-step-law` states that the NormPair component of the recurrent factor is unchanged by its step. Together with the full learner's `canonicalFullStep-norm` and policy invariance, this makes NormPair a dynamically inert factor for the current policy/transition semantics.

These three laws compose with the learner's endogenous signal rather than sitting beside it. The full learner computes a Watkins target from reward, q-log bias, critic information, and endogenous feedback; the same signal drives the GRU and F4 update. `canonical-gruf4-norm-watkins-prefix-composition-theorem` packages the resulting GRU × F4 × NormPair × Watkins prefix composition.

## Hodge-Maxwell composition

The Hodge-Maxwell branch is a representation layer over the same transition semantics. `ConnectedContinuousHodgeMaxwellGRURepresentationTheorem` supplies the continuous Hodge-Maxwell/GRU representation surface, while `ConnectedHodgeMaxwellGRUF4WatkinsEGraphCompositionTheorem` joins it to the exact F4/Watkins learner through explicit inverse/representation and step-conjugacy data.

That means the composition claim is semantic: the Hodge-Maxwell state representation is required to commute with the learner transition. It is not “GRU theorem + Maxwell theorem = physics theorem” by proximity. The actual encode/decode, conjugacy, continuity, and coupling interfaces are what make the edge meaningful.

The downstream `ConnectedGRUHodgeMaxwellTsallisWalrasianPOMDPCompositionTheorem` is broader still. Its existence in the theorem surface does not turn the Hodge-Maxwell representation into an unconditional economic-equilibrium existence theorem; the economic relation and its required witnesses remain explicit.

## What the linear F4 ray means

`f4-unit-forcing-linear-growth` proves an exact forcing response along the F4 theta coordinate: under the specified unit forcing, the relevant integer-valued optimizer coordinate grows linearly with the horizon. `f4-unit-forcing-no-upper-bound` turns that ray into the corresponding impossibility of an unconditional infinite-horizon upper bound.

The important interpretation is narrower than “the optimizer diverges.” The theorem identifies a particular forcing regime in which the implemented update accumulates a persistent increment. It therefore demonstrates that the current F4 quantity is not unconditionally bounded over arbitrary horizons.

This mechanism is not unique to F4 as a general optimizer phenomenon. Any update of the schematic form

  x_(t+1) = x_t + c

with persistent nonzero c has x_t = x_0 + t c, hence linear drift. Gradient descent on a constant nonzero gradient is the simplest analogue. What is specific here is the exact discrete F4/L2 definition, the chosen integer substrate, and the theorem's machine-checked forcing ray. The result is therefore an exact property of this optimizer implementation, not a novelty claim that only F4 can exhibit linear growth.

## Topological consequence

The ray and the factor theorem should be read together:

  exact learner laws
    -> recurrent/optimizer/factor composition
    -> F4 stability + NormPair factorization
    -> exact linear forcing ray
    -/-> convergence
    -/-> fixed point
    -/-> market clearing
    -/-> supporting price
    -/-> Walrasian existence

The negative edges are part of the result: the exact learner-side structure is characterized without silently importing the economic assumptions needed for existence or convergence.

## Evidence stack

Agda is the proof authority. The Mercury JSON output is machine evidence for extracted laws and dependency discovery. Mermaid is the human-readable topology projection. TSV/CSV are not canonical graph representations, and SQLite/NoSQL are not warranted for the current deterministic, repository-local dependency workload.

A CSV file used for an unrelated replication archive is not part of this graph-format decision and should not be removed merely because CSV is unnecessary for topology.


## Four-physics-law continuation graph

The four physics-facing laws are now graphed as a separate frontier from the already-closed learner composition:

  Law I exact representation witness
      + Law II Hodge-Maxwell representation
      + Law III exact representation / variational interface
      + Law IV canonical GRU statistical representation
      + explicit physics → learner interface witness
      -> Four-Law one-step commuting square
      -> Four-Law iterate conjugacy
      -> Four-Law exact prefix / horizon conjugacy
      -> Four-Law end-to-end representation closure

The arrows in this continuation are deliberately marked [FRONTIER]. The graph records the dependency shape, not a proof claim. In particular, Law I and Law III still require their explicit inverse representation witnesses, and the physics → learner transition witness must be supplied before the one-step square can be promoted to an Agda theorem.

The existing ConnectedContinuousHodgeMaxwellGRUF4WatkinsExactPrefixHorizonRegretConjugacyEGraphCompositionTheorem is a distinct, already-present Hodge-Maxwell/learner endpoint. The new four-law frontier is stricter: it asks for the Law I + Law II + Law III + Law IV interface to be assembled into one prefix/horizon transport theorem.

The intended induction is the standard commuting-step lift:

  encode (PhysicsStep s) ≡ LearnerStep (encode s)

  ⇒ encode (iterate PhysicsStep n s)
       ≡ iterate LearnerStep n (encode s)

and, for recurrent input prefixes, the corresponding concatenation/prefix transport law. This remains a representation/conjugacy result; it does not imply convergence, fixed-point existence, market clearing, supporting prices, or Walrasian existence without independent economic hypotheses.


### Current frontier decomposition

The one-step square is now decomposed into three explicit proof obligations:

1. **Law I inverse representation witness** — enough encode/decode structure to establish the exact Law-I representation boundary.
2. **Law III inverse representation witness** — enough encode/decode structure for the variational/virtual-work layer.
3. **Physics → learner transition witness** — an extensional commuting law connecting the physical transition to the canonical learner step.

Only after all three are present does the graph promote:

  one-step square → iterate conjugacy → exact prefix/horizon conjugacy.

This decomposition is intentionally stronger than merely connecting the four law labels: each edge must eventually correspond to proof-relevant data on the Agda surface.


### Conjugacy-kernel continuation

The repository already contains a generic proof-relevant GlobalConjugacyEquivalence record with both state/feature reconstruction and forward/backward dynamics equations. The four-law frontier therefore does not need a new abstract notion of conjugacy: the remaining work is to instantiate this existing kernel with the Law-I/Law-III physics witnesses and the physics-to-learner interface.

The refined dependency chain is:

  GlobalConjugacyEquivalence
      + Law-I inverse witness
      + Law-III inverse witness
      + physics-to-learner witness
      + Law-II Hodge-Maxwell conjugacy
      + Law-IV GRU step closure
      -> four-law commuting square
      -> n-step iterate conjugacy
      -> prefix concatenation transport
      -> exact prefix/horizon conjugacy
      -> end-to-end representation closure.

This is materially stronger than the previous one-step-only frontier because the induction kernel and the prefix-monoid transport stage are now explicit. The existing iterateCanonical definition and recurrent-prefix append lemmas provide the corresponding learner-side induction shape, while CanonicalLearnerHodgeMaxwellCompositionTheorem already supplies an explicit learner-to-solution inverse pair and one-step conjugacy seam.

No new Agda theorem is claimed by this graph update; the frontier remains conditional until the missing physics witnesses are instantiated and typechecked.
