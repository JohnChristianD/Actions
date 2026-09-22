# GRU automata/sign-optimizer graph research

## Scope

Research boundary for the connected graph candidate
`CanonicalEndogenousAutomataSignOptimizerAffineGRUExpressivityTopologyNeighborhoodConjugacyCandidate`.

## Findings

- Jordan, Sokol, and Park, *Gated recurrent units viewed through the lens of continuous time dynamical systems*, report stable limit cycles, multistability, and homoclinic bifurcations in GRU dynamics. This supports treating GRU expressivity as a dynamical-systems question, while not proving the repository's discrete conjugacy theorem.
  Primary source: https://doi.org/10.3389/FNCOM.2021.678158

- Marzen, Crutchfield, and collaborators, *Probabilistic Deterministic Finite Automata and Recurrent Networks, Revisited*, study RNN/finite-automaton relationships and note that recurrent architectures can represent finite-state behavior, while predictive performance can remain below the exact automaton optimum under finite data.
  Primary source: https://doi.org/10.3390/e24010090

- Peng, Schwartz, Thomson, and Smith, *Rational Recurrences*, formally connect recurrent hidden-state updates with weighted finite-state automata through rational recurrences.
  Primary source: https://aclanthology.org/D18-1152/

- Dhayalkar, *Symbolic Feedforward Networks for Probabilistic Finite Automata: Exact Simulation and Learnability*, gives a recent constructive neural simulation result for probabilistic finite automata and connects exact state propagation with differentiable neural computation.
  Primary source: https://doi.org/10.48550/arXiv.2509.10034

## Repository consequence

These sources support the graph direction of combining recurrent dynamics with finite-state structure. They do not establish the repository-specific sign-optimizer-affine witness, exact GRU conjugacy, neighborhood separation, topology compatibility, inclusion, or baseline nonrepresentability obligations. Those remain Agda promotion gates.

## Knowledge delta

Added a documented research boundary for the new pre-graphed automata/sign-optimizer-affine candidate. No theorem was promoted from candidate status on literature evidence alone.
