# CHAD source manifest

Mathematical authority: Agda 2.8.0 `--safe` in this repository.

## Original CHAD

The original paper is **CHAD: Combinatory Homomorphic Automatic Differentiation** (Matthijs Vákár, 2021 preprint; TOPLAS 2022, DOI 10.1145/3527634). Its central result is a compositional, type-respecting source transformation for forward- and reverse-mode AD, with correctness established by a logical-relations argument.

## Efficient CHAD

**Efficient CHAD** (Tom Smeding and Matthijs Vákár, POPL/PACMPL 2024, DOI 10.1145/3632878; arXiv:2307.05738) optimizes CHAD using sparse vectors, state-passing style, defunctionalization/closure conversion, and controlled mutable accumulation, and contains an Agda complexity formalization.

The upstream Efficient-CHAD Agda repository is an external reference. The canonical theorem surface here remains finite, dyadic, and Int8-based; upstream Float/Real material is not imported as a mathematical oracle.

## In-scope port

The repository proves finite CHAD composition and finite recurrent reassociation locally. Those are the portable algebraic obligations needed for the dyadic GRU/Möbius composition. Full semantic equivalence to the original CHAD or Efficient CHAD implementations is not claimed unless an explicit finite `--safe` refinement proof is present.
