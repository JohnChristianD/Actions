# Algebraic proof: nonlinear sequence storage and generation

## Claim

Let A be the token algebra, P the finite position algebra, R the representation algebra, and let

  phi : A x P -> R
  psi : R -> A x P

satisfy psi (phi (a,p)) = (a,p). Let x : P -> A be the sequence and define h(p) = phi (x(p),p). Let succ : P -> P be successor on nonterminal positions. Suppose a recurrent transition T on R satisfies T(h(p)) = h(succ(p)).

Then the generator initialized at h(p0) and iterated by T emits x(p) at every reachable position p.

## Proof

Decoder correctness gives

  out(h(p)) = proj1(psi(h(p)))
             = proj1(psi(phi(x(p),p)))
             = proj1(x(p),p)
             = x(p).

The transition equation gives h(p) -> T(h(p)) = h(succ(p)). By induction, T^k(h(p0)) = h(succ^k(p0)). Applying out gives out(T^k(h(p0))) = x(succ^k(p0)). Thus finite-sequence storage and generation are exact.

## Nonlinear condition

No linearity assumption on phi is used. Add the independent condition that phi is not affine on A x P. The exact-storage and exact-generation conclusion still follows from injectivity, a decoder left inverse, and successor-transition compatibility. Hence the algebraic theorem isolates what must be proved about a nonlinear representation rather than assuming linear-subspace encoding.

## Connected graph

SequenceStorage -> NonlinearRepresentationInjectivity -> DecoderLeftInverse -> SuccessorTransitionCompatibility -> FiniteOrbitConjugacy -> ExactSequenceGeneration.

The automata/sign-optimizer-affine GRU candidate attaches through FiniteAutomatonTransition -> SignOptimizerAffinePreservation -> GRUSuccessorConjugacy -> NeighborhoodSeparation -> TopologyCompatibility. Promotion remains gated by Agda witnesses for every edge.

## Source boundary

Csordas, Potts, Manning, and Geiger, Recurrent Neural Networks Learn to Store and Generate Sequences using Non-Linear Representations, 2024, DOI 10.48550/arXiv.2408.10920.

The paper supplies evidence for magnitude-based nonlinear representations in trained gated RNNs. It does not itself establish the repository-specific connected theorem; exact promotion remains an Agda --safe obligation.
