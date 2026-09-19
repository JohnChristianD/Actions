# Canonical Learner Semantics

Last audited: 2026-09-19 against \`main\` at \`d48e5cf6e3671f268440135f1acc32eeafb3d510\`.

## 1. Finite Int8 carrier

\`CanonicalLearnerMonolith.agda\` defines:

\`\`\`
record Int8 : Set where
  constructor int8
  field code : Fin 256
\`\`\`

The primitive arithmetic functions are \`int8OfNat\`, \`int8Add\`, \`int8Mul\`, \`int8Neg\`, and \`int8Sub\`. They operate through the finite \`Fin 256\` code and do not import a generic ring structure.

The repository proves concrete carrier lemmas such as \`int8Roundtrip\`, while deliberately avoiding a claim that the carrier is a generic abstract ring.

## 2. Critic, LCB, and sparsemax

The canonical policy surface consists of:

- \`CriticState\`
- \`LCBCountState\`
- \`LCBCountKernel\`
- \`ActionScore\`
- \`Sparsemax2Pair\`
- \`fixedTemperatureSparsemax\`

The fixed sparsemax temperature is the Int8 value 16.

The policy is:

\`\`\`
canonicalPolicy K s =
  fixedTemperatureSparsemax
    (lcbScore (lcbKernel K) (lcbCounts s) (critic (watkins s)))
\`\`\`

Attention state, NormPair, and optimizer state are separate from policy selection. The theorem monolith proves policy invariance under replacement of each of those state components through \`LearnerReplacement\`.

## 3. Finite Q-log control

\`FiniteRational\` is a concrete sign/numerator/denominator record.

The learner defines:

- \`finiteQLog8\`
- \`negativeFiniteQLog8\`
- \`qLog2Bias8\`
- \`SignedQLogControl\`

The canonical Q-log step is the negative finite Q-log of the selected policy weight. The Q-log bias then contributes directly to the canonical Watkins target.

This is a finite exact representation surface. It is not a generic real logarithm implementation.

## 4. Learned sparsemax attention and Walsh phase

\`LearnedSparsemaxAttention\` contains two Int8 parameters.

The exact attention path is:

\`\`\`
learnedSparsemaxAttentionWeights
  -> liftAttention
  -> walshHadamardApply
  -> phase4 / walshRademacherRope4
  -> walshRademacherRopeReadout
\`\`\`

The Walsh layer is a finite width-4 construction. The source proves the concrete Int8 Gram/orthogonality law through \`H4GramLaw\`.

\`Phase4\` has four constructors and \`phase4\` repeats modulo four. The rotary analogue is a finite signed-permutation layer, not a numerical sine/cosine RoPE implementation.

## 5. GRU and persistent quotient

\`GRUState\` contains:

- hidden state;
- \`GRUMatrices\`;
- \`GRUNoise\`;
- \`GlobalControl\`.

\`gruStep\` updates the hidden coordinate while the parameter-like coordinates are preserved.

The source proves:

- \`persistent-preservation\`
- \`gruParameterPersistence\`
- \`GRUEquivalent\` reflexivity
- \`gruStep-respects-equivalence\`
- \`gruActionAssociativity\`
- \`gruInputActionAssociativity\`

\`GRUAction\` is explicit endomorphism composition. The source does not register a standard-library \`Monoid\` instance.

## 6. F4/L2 optimizer

\`F4IntUState\` contains:

\`\`\`
thetaQ rTheta eQ rE rL : Int8
\`\`\`

\`F4IntUKernel\` contains \`globalL2 : Int8\`.

The optimizer transition is \`f4ThetaStep\`. Its parameter law is \`f4ParameterInvariant\`.

The canonical optimizer consumes \`canonicalSignal\`, which is definitionally equal to \`canonicalWatkinsTarget\`. The current source therefore gives an explicit q-Munchausen/L2 signal path without introducing a separate actor implementation.

## 7. NormPair

\`NormPair\` contains two Int8 fields:

\`\`\`
l1
path
\`\`\`

with:

\`\`\`
normPairWeight  = l1 + path
normPairWeightPlusOne = 1 + normPairWeight
\`\`\`

The canonical full step preserves \`NormPair\`, hence also preserves \`normPairWeightPlusOne\).

## 8. Full learner state and transition

\`FullLearnerState\` has nine components:

1. \`clock : Nat\`
2. \`watkins : WatkinsState\`
3. \`attention : LearnedSparsemaxAttention\`
4. \`gru : GRUState\`
5. \`optimizer : F4IntUState\`
6. \`norm : NormPair\`
7. \`lcbCounts : LCBCountState\`
8. \`qLogControl : SignedQLogControl\`
9. \`qLogValue : FiniteRational\`

\`canonicalFullStep\` performs:

\`\`\`
clock        := suc clock
watkins      := canonicalWatkinsStep
attention    := canonicalAttentionStep
gru          := canonicalGRUStep
optimizer    := canonicalOptimizerStep
norm         := norm
lcbCounts    := canonicalCountStep
qLogControl  := canonicalQLogControlStep
qLogValue    := canonicalQLogStep
\`\`\`

The exact projection laws are named \`canonicalFullStep-clock\`, \`canonicalFullStep-watkins\`, \`canonicalFullStep-attention\`, \`canonicalFullStep-gru\`, \`canonicalFullStep-optimizer\`, \`canonicalFullStep-norm\`, \`canonicalFullStep-counts\`, \`canonicalFullStep-qLog\`, and \`canonicalFullStep-qLogControl\`.

The transition has no fixed point because the clock advances. The same clock law yields aperiodicity and exclusion of nontrivial finite cycles for the canonical iteration.

## 9. Endogenous feedback

The canonical endogenous feedback is:

\`\`\`
canonicalEndogenousFeedback K s =
    canonicalAttentionMix K s
  + canonicalGRUFeedback s
  + canonicalF4L2Feedback K s
  + canonicalQLogControlFeedback s
  + canonicalQLogValueFeedback s
\`\`\`

The canonical Watkins target is:

\`\`\`
reward
+ qLogBias
+ discounted max critic
+ endogenous feedback
\`\`\`

The source makes this exact by definition, and \`canonicalWatkinsTarget-law\` exposes the decomposition propositionally.

## 10. Recurrent scan abstraction

The learner monolith defines:

- \`RecurrentNetwork State Input\`
- \`canonicalGRURecurrentNetwork\`
- \`Endomorphism\`
- \`recurrentPrefixState\`
- \`recurrentPrefixEndomorphism\`
- \`recurrentPrefix-correct\`
- \`recurrentPrefix-split\`

The split law is for arbitrary natural prefix lengths. It is an algebraic decomposition of the executable recurrence, not a second neural-network implementation.

The same source proves \`int8-no-countably-unbounded-injective\`, which gives the finite-state obstruction to injectively encoding an unbounded natural clock in \`Int8\`.

## 11. Finite closed-loop ports

\`CanonicalGamePorts.agda\` defines exact finite \`StepResult\` carriers and port transitions.

\`CanonicalFaithfulGameVariants.agda\` defines exact Toy Maze and FourRooms openness predicates.

\`CanonicalClosedLoopBench.agda\` defines \`ClosedLoopSpec\`, \`ClosedLoopRun\`, and \`ClosedLoopMetrics\`, then runs explicit finite learner/environment loops.

The result is exact finite formal composition. It is not an external simulator equivalence theorem.

## 12. Generalized benchmark boundary

\`GeneralFullCoupledLearnerMonolith.agda\` is separate from the canonical learner. It generalizes action cardinality through a parameter \`A\`, defines \`QVec A\`, \`CountVec A\`, sorting over \`Fin A\`, and a sparsemax policy over that generalized surface.

\`GeneralClosedLoopBenchV2.agda\` consumes that generalized learner with benchmark-specific environments and ablations.

This generalized surface should not be read back into the canonical theorem source as though it were the same learner.
