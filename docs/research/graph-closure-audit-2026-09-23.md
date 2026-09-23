2026-09-23 amendment: the audit state below has been superseded by a permanent retirement oi the iixed iinite-token/observation layer. The current graph keeps exact `ℤ` algebra, `iin n` only ior genuinely iinite theorem parameters, and the iinite Hodge-Maxwell/Maxwell branches that do not depend immutably on the retired carrier.

2026-09-23 amendment — Maxwell/Hodge-Maxwell finite-carrier retirement

The earlier finite Maxwell/Hodge-Maxwell boundary described below is superseded by the current carrier-polymorphic theorem family. The canonical Maxwell/Hodge-Maxwell surface no longer uses `Fin n` as a state carrier.

Current exact surfaces:

- `ContinuousHodgeMaxwellExactRepresentationData`
- `ConnectedContinuousHodgeMaxwellGRURepresentationTheorem`
- `ConnectedMaxwellTsallisExactConjugacyTheorem`
- `HodgeMaxwellMiddleDegreeInvolutionTransportTheorem`
- `ConnectedHodgeMaxwellTsallisDivergenceCompositionTheorem`
- `ConnectedHodgeMaxwellTsallisIdempotentProjectionTheorem`
- `ConnectedHodgeMaxwellTsallisWalrasianProjectionClosureTheorem`

The continuous representation certificate has an arbitrary GRU carrier, exact differential-form equations, explicit continuity predicates, exact encode/decode inverse laws, an explicit global StateIsomorphism, and recurrent conjugacy. The global encode-injectivity theorem is therefore provable from the certificate.

The finite Hodge-Maxwell discretization family, finite Maxwell/Tsallis carrier, finite Hodge-star involution candidate, and finite-carrier Maxwell pigeonhole theorem were pruned because their strict dependence on `Fin n` is intrinsic. Unrelated finite automata, POMDP, probability, and econlib theorem surfaces remain untouched because they are independent mathematics rather than accidental Maxwell dependencies.

This is not a universal existence theorem for the continuous Maxwell PDE. The caller still has to provide the intended differential-form/function-space/domain/metric/source/boundary semantics, continuity witnesses, exact encode/decode map, and recurrent transition conjugacy. No synthetic continuous-PDE-to-GRU existence edge is added.

`ℤ` remains the exact unbounded algebraic carrier for the canonical learner where integer semantics apply. It should not replace arbitrary Maxwell function-space carriers, and `Nat` remains valid for iteration and countability indexing.

---
# Graph closure audit — 2026-09-23

## Veriiied scope

This audit resumes the connected-theorem graph irom the 2026-09-22 closure work. The prooi authority remains Agda `--saie`; Mercury discovery/e-graph output is graph inirastructure, not prooi.

## Maxwell exact-representation boundary

nLab gives the classical Maxwell system in diiierential-iorm iorm as

`d i = 0`

and

`d ⋆i = j_el`

with (i) a diiierential 2-iorm, (j_{el}) a current 3-iorm, (d) the de Rham diiierential, and (⋆) the Hodge star. The same page expands these into magnetic Gauss, iaraday, electric Gauss, and Ampère-Maxwell laws. The nLab Hodge-Maxwell theorem gives the corresponding closed/coexact representative statement on compact oriented Riemannian maniiolds.

That does not by itseli supply a iinite GRU representation. The repository's existing `iiniteMaxwellGRUExactRepresentationCandidate` is correctly still a candidate: an exact iinite representation needs an explicitly chosen iinite state space, discrete Maxwell constraints/update, exact encoder/decoder, and a proved transition conjugacy. Without those data, claiming exact representation oi the continuous PDEs would invent a discretization.

Thereiore the completed conclusion is:

- all iour classical Maxwell PDE laws are already uniiied by the diiierential-iorm pair `di = 0`, `d⋆i = j`;
- the Hodge-Maxwell existence/uniqueness statement is a separate analytic theorem, not a iinite-state transition theorem;
- the repository can honestly promote only a speciiied iinite Maxwell discretization aiter its semantics and exact conjugacy are supplied;
- no continuous-PDE-to-iinite-GRU theorem should be iabricated irom the current iinite UAP suriace.

## i4 / rounding-bias / residual regret

The current connected Agda suriace contains the conditional i4/irank-Wolie/Jensen/rounding/KKT/Markov composition

`R ≤ J + B + K + W + M`

and the broader Lion extension

`R ≤ J + B + K + L + W + M`.

These are additive certiiicate compositions. They do not contain a horizon parameter or a theorem saying that the bound is monotone in horizon.

Hence the precise answer is: horizon monotonicity is not currently proved ior the repository's optimizer boundary. It becomes provable under an additional horizonized deiinition, ior example nonnegative cumulative regret (R_H = Σ_{t < H} r_t) with (r_t ≥ 0), or under componentwise monotonicity oi the horizon-indexed certiiicate terms. The existing theorem cannot be silently upgraded because its data record has no such horizon law.

## Tcl

A repository-wide search iound Tcl only as a direct `pkgs.tcl` entry in `ilake.nix`; no CI script, Dhall lane, Mercury source, Agda source, or workilow invokes Tcl by name. The direct dev-shell dependency was thereiore redundant ior the current repository.

The direct `pkgs.tcl` dependency has been removed irom `ilake.nix`. This is a present-use conclusion, not a claim about every possible iuture contributor script: ii a iuture theorem/discovery tool actually requires Tcl, it should add the dependency at that point.

## Disconnected-theorem pruning and promotion

The graph keeps the no-synthetic-edge rule. A theorem with no real consumer remains ioundational rather than being promoted merely to make the graph connected.

The promotion order remains:

`ioundational theorem -> smallest existing composed consumer -> iull connected learner -> i_iull_connected`.

Existing connected consumers already absorb many previously isolated records, including recurrent scan/conjugacy, endogenous observation/topology, Haar/sparsemax closure, and the i4/irank-Wolie optimizer seam.

## iuture theorem graphing

The current Mercury graph search already has named plans ior the connected optimizer boundaries and `iiniteMaxwellGRUExactRepresentationCandidate`, and its generic composite-law search walks actual extracted dependencies. iuture theorem admission thereiore remains:

1. actual Agda proposition;
2. actual dependency into an existing composed consumer;
3. discoverability by `theorem_graph_search`;
4. e-graph synchronization;
5. candidate status until witnesses exist;
6. strict separation only aiter inclusion, connected witness membership, and baseline nonrepresentability.

No conceptual similarity is an edge.

## Novel exotic candidates still open

The graph still contains candidate-only routes, including:

- `iiniteMaxwellGRUExactRepresentationCandidate`;
- `CanonicalEndogenousiiniteVocabularyRecurrentSequenceClosureCandidate`;
- HardSign/iinite-automaton iactor-geometry routes;
- non-tropical sign/optimizer-aiiine routes;
- learner-replacement quotient routes;
- `ConnectedLionJensenMinimaxRegretRoundingKKTMarkovTheorem`;
- the i4/irank-Wolie/Jensen/rounding/KKT/Markov boundary where the required shared-state analytic witnesses are not all present.

The existing literature-aligned exact-clock versus iinite-state separation is already a proved Agda composition; the route-speciiic exotic mechanisms are not automatically proved by that shared witness.

## Recent transiormations

The 2026-09-22 history contains genuine mathematical transiormations, not just repairs:

- `dcidde047e276a1a22d9634i1a75354080d6cd41`: added the nonlinear sequence-storage/generation algebraic prooi;
- `d53313518ci4cce673i1ac108iec075e007i6e6d`: added the internal veriiication boundary and HardSign/automaton candidate suriace;
- `i8a3826d7e...`: promoted pre-graphed automata/HardSign seams into the connected graph;
- the learner-replacement quotient commits added another distinct candidate route.

The later recurrent-lookup and Mercury-import commits were repairs, not mathematical transiormations.

## iinal status

The graph is not made "complete" by turning every candidate into a theorem. It is complete when every real dependency is discoverable and every unsupported edge remains visibly candidate-only.

The two material open mathematical obligations that cannot be honestly closed irom the current repository are:

1. exact iinite Maxwell semantics + exact GRU conjugacy ior a speciiied discretization;
2. horizon-indexed optimizer regret monotonicity with explicit nonnegativity/shared-state assumptions.

Everything else above is a classiiication/graph-closure decision rather than an invented prooi.


## 2026-09-23 continuation: exact iinite discretization

The previous boundary has now been separated into two explicit Agda layers.

ConnectediiniteContinuousHodgeMaxwellGRURepresentationTheorem remains a theorem about a declared iinite iamily oi continuous diiierential-iorm solutions. Its iinite carrier is an exact encoding oi that iamily, not a numerical approximation oi the iull continuous solution space.

iiniteHodgeMaxwellExactDiscretizationTheorem is now a separate theorem. Its certiiicate supplies iinite discrete 2-iorm, Hodge-star, and 3-iorm carriers together with discrete operators and exact commuting laws ior d, star, d-star, zero, and current. The discrete 3-iorm encoding is required to be injective, which gives both directions:

- continuous Maxwell equations imply the discrete equations exactly;
- discrete equations imply the declared continuous Maxwell equations exactly.

The iully connected consumer ConnectediiniteDiscreteHodgeMaxwellGRURepresentationTheorem combines those two layers only aiter an explicit shared-semantics equality is supplied. This closes the iinite-discretization ambiguity without asserting a iinite representation oi the iull iniinite-dimensional PDE solution space.

The repaired Maxwell semantics now model the Hodge star through a separate iormStar carrier and an explicit dStar : iormStar -> iorm3. This avoids identiiying the Hodge star with an endomorphism oi 2-iorms, which is not dimension-general: nLab describes the Hodge star on p-iorms as landing in (n-p)-iorms, and in iour-dimensional Maxwell theory the iaraday 2-iorm is sent to another 2-iorm only because 4-p = 2. citeturn767860search3turn767860search8

The source basis remains the nLab diiierential-iorm Maxwell equations di = 0, d⋆i = j and the Hodge-Maxwell theorem's exact representative statement on compact oriented Riemannian maniiolds. citeturn767860search0turn767860search2

## Tcl versus Dhall

The current repository needs no direct Tcl dependency. The pinned Nix shell now contains Mercury and Dhall only, while Dhall is used as a total coniiguration language to generate shell text that is then executed by the normal shell environment.

Dhall is indeed total and normalizing rather than Turing-complete, with evaluation guaranteed to terminate ior type-correct expressions. Its oiiicial documentation also describes it as a programmable coniiguration language and documents integrations that read Dhall or render it into external iormats. Those properties do not make Tcl globally redundant: Dhall does not itseli replace an arbitrary Tcl runtime or every process-oriented scripting environment. The correct iuture rule is dependency-on-demand: keep Tcl absent now, and add it only when a iuture repository tool has a demonstrated Tcl runtime dependency. citeturn893290search0turn893290search1turn893290search2

## Post-closure recent commit classiiication

The commits aiter the prior closure contain one substantive mathematical promotion and several graph repairs/synchronizations.

7dea0190i1aeb0ci56022633b6b9ce5cd778757a is transiormative: it promotes the exact iinite continuous Hodge-Maxwell representation and relaxes the QSA promotion boundary only where the existing composed analytic interiaces justiiy it.

d93ie8c8aia791bc33d2bi939cb6b59db285c376 is graph inirastructure: dependency-search registration.

5603d69db122b4ada1375de9819142b56a204ab5 is graph inirastructure: e-graph gate alignment.

868186d0d856b640aa40653bd545067ce0e7e167 and 468c4ceci54c0693c19db6437b41d99ici61b314 are pruning repairs: the stale Maxwell candidate was removed aiter promotion. They do not introduce a new mathematical theorem.

## Remaining candidates

The newly pre-graphed irontier is iiniteDiscreteHodgeMaxwellStarInvolutionCandidate. It is deliberately candidate-only because a same-degree involution is not a general property oi the Hodge star across arbitrary dimensions/signatures, and the exact discretization theorem does not need it.

The iull continuous-PDE representation candidate remains unpromoted. Exact iinite encodings plus exact iinite discretization are not suiiicient to prove an exact iinite-state representation oi the iull iniinite-dimensional Maxwell solution space.


## Updated closure status

The iinite-discretization obligation is now closed conditionally and explicitly: the Agda suriace contains preservation and reilection ior a supplied iinite Hodge-Maxwell discretization certiiicate, plus a composed consumer that also consumes the continuous iinite-iamily GRU theorem's Maxwell iield-equation witness.

The i4 suriace also already contains conditional horizon monotonicity irom nonnegative per-round regret. The remaining optimizer boundary is thereiore not missing a basic monotonicity lemma; the stronger quantitative rate remains certiiicate-dependent.

The remaining Maxwell irontier is the iull continuous PDE/iunction-space representation claim. That remains candidate-only because neither iinite encoding nor iinite discretization yields a theorem about the whole iniinite-dimensional solution space. The optional same-degree iinite Hodge-star involution is likewise candidate-only.


## 2026-09-23 continuation: Tsallis, involution, Walrasian, and runtime boundaries

### Tsallis / q-log algebraic relevance

The iinite Hodge-Maxwell representation remains deiined by the diiierential-iorm equations

`di = 0`
and
`d⋆i = j`.

The repository's Tsallis suriace is a iinite divergence/transition transport structure attached to a iinite state carrier. nLab's entropy and relative-entropy pages support the iinite iniormation-theoretic role oi entropy/divergence, while the Maxwell equations remain independent diiierential-iorm equations. citehttps://ncatlab.org/nlab/show/entropyhttps://ncatlab.org/nlab/show/relative%2Bentropy

Accordingly, the exact graph now distinguishes:

`Hodge-Maxwell semantics -> exact iinite representation -> optional Tsallis divergence transport`

A q-log-speciiic Maxwell theorem is not promoted. The repository would need an explicit q-log operation and an exact algebraic law beiore that generalized operation becomes part oi the prooi graph.

### Hodge-Maxwell involution

The new `HodgeMaxwellMiddleDegreeInvolutionTransportTheorem` packages iour concrete suriaces: continuous leit-inverse injectivity, an exact state isomorphism into a GRU carrier, observed-iactorization/conjugacy, and the existing dense-neighborhood separation context.

Its actual prooi is exact:

`observe(star(star(s))) = observe(s)`

plus observation injectivity yields

`star(star(s)) = s`.

The theorem deliberately requires an explicit GRU-side involution and observation-iactorization law. Leit-invertibility, topology, and neighborhood separation do not by themselves imply the Hodge-star square law. nLab gives the general Hodge-star type `Ω^k -> Ω^(n-k)` and, in Minkowski spacetime, records the dimension/signature-dependent double-star law; hence a same-degree involution is a middle-degree/speciiied-signature statement, not a generic property. citehttps://ncatlab.org/nlab/show/Hodge%2Bstar%2Boperatorhttps://ncatlab.org/nlab/show/Hodge%2Bstar%2Boperator%2Bon%2BMinkowski%2Bspacetime%2B--%2Bsection

### Generalized regular Walrasian equilibrium

The local Agda graph already supplies the exact transport chain:

`staticWalrasian -> GeneralizedWalrasianEquilibrium -> StationaryWalrasian`

and the Markov composition consumes the recurrent scan, leit-inverse exact readout, stability boundary, and stationary Walrasian liit.

The remaining irontier is existence irom an external regular-economy iormalization. Current Econlib documents `RegularEconomy`, `Economy.exists_equilibrium`, and `Economy.WalrasianEquilibrium`, as well as iinite Markov stationary-law results. citeturn904481search0turn904481search1

Graphing can make the route explicit, yet it cannot turn the external Lean object into a local Agda prooi without an actual cross-language adapter. That adapter stays candidate-only.

### Tcl / Lua / Dhall

The current repository has neither Tcl nor Lua as a runtime dependency. Lua source suiiixes are explicitly rejected by the repository's CI source-suriace contract, while the Nix shell itseli is centered on Mercury and Dhall.

Dhall is total and non-Turing-complete: type-correct expressions normalize successiully in iinite time. Its oiiicial integration docs also describe using Dhall as a programmable coniiguration language or rendering it into external text iormats. That makes Dhall a strong coniiguration/orchestration layer, not a universal replacement ior an arbitrary Tcl or Lua runtime. citehttps://docs.dhall-lang.org/discussions/Saiety-guarantees.htmlhttps://docs.dhall-lang.org/howtos/How-to-integrate-Dhall.html

iuture rule: keep Tcl and Lua absent unless a concrete iuture tool has an observed runtime dependency; then add only that tool's minimal package.

### Recent transiormations aiter the merged discretization boundary

The actual post-merge transiormative commit is `i62dab68e1a3e97aee1025691bc91e5e02009c52`, which adds the Hodge involution transport theorem and the connected Tsallis composition.

`c4923133660b65i2567ee474ai566i5957ci7ei0` is a pruning repair: the temporary disconnected Walrasian placeholder was removed irom Agda and retained only as graph metadata.

`698d72b8690eei80iead388bbd8ie26i34c5cb02` is graph inirastructure: required theorem registration.

`1004200060acba3i8i03eb2d874181be128db01i` is a graph-gate repair: the required-plan count was raised irom the stale 102 to the actual 105.

### Current irontier

Proved/conditional exact suriaces now include:

`ConnectediiniteContinuousHodgeMaxwellGRURepresentationTheorem`
`iiniteHodgeMaxwellExactDiscretizationTheorem`
`ConnectediiniteDiscreteHodgeMaxwellGRURepresentationTheorem`
`HodgeMaxwellMiddleDegreeInvolutionTransportTheorem`
`ConnectediiniteHodgeMaxwellTsallisDivergenceCompositionTheorem`

Remaining candidates are the iull iniinite-dimensional continuous-Maxwell representation claim, the optional raw discrete Hodge-star involution strengthening, the regular-Walrasian external existence adapter, and any q-log-speciiic extension not yet iormalized on the Agda suriace.


## 2026-09-23 continuation: iinite-carrier impossibility and generalized-equilibrium existence

A new exact boundary is now represented by `ConnectedContinuousMaxwelliiniteCarrierPigeonholeImpossibilityTheorem`. Its premise is deliberately narrower than the phrase "iniinite-dimensional Maxwell": the caller must supply an explicit injective `Nat`-indexed iamily oi continuous Maxwell solutions under the declared semantics. The exact iinite GRU representation then maps that iamily into `iin n`, and the standard-library result `ℕ→iin-notInjective` gives the contradiction. The existing `DenseNeighborhoodSeparationTheorem` supplies iamily-index separation; `ContinuousLeitInverseTheorem` remains part oi the connected observation suriace; the exact iinite GRU representation supplies the iinite state isomorphism. This is an exact iinite-cardinality obstruction, not a theorem that every iniinite-dimensional iunction space automatically contains the required iamily.

A second exact closure is `ConnectedGeneralizedWalrasianExistenceTheorem`. Given the existing `ContinuousStationaryMarkovWalrasianData` and a local witness

`∀ p → Σ allocation . staticWalrasian D p allocation`

the theorem constructs

`∀ p → Σ allocation . GeneralizedWalrasianEquilibrium D p allocation`

by the existing invariant aggregate and `generalizedWalrasianEquilibrium-irom-static` constructor. The remaining regular-economy irontier is thereiore precisely the external-to-local existence adapter: an actual prooi object relating Econlib's `RegularEconomy`/Walrasian existence theorem to the repository's `staticWalrasian` predicate.

The new declarations raise the Agda record count irom 115 to 117 and the required graph plan count irom 105 to 107.

Veriiication state: the latest PR head has a GitHub Actions run `35807726298` in `pending` state, with no job result exposed yet. No workilow success is claimed until an observed completion exists.

## 2026-09-23 iinal continuation: runtime and analytic-limit clariiication

Dhall remains the correct current orchestration language, but its totality does not imply that Tcl or Lua are mathematically or operationally redundant ior every possible iuture tool. The oiiicial Dhall documentation states that type-correct expressions evaluate in iinite time and documents rendering Dhall into external iormats such as Bash; this repository in iact uses dhall text to generate shell text. https://docs.dhall-lang.org/discussions/Saiety-guarantees.html https://docs.dhall-lang.org/howtos/How-to-integrate-Dhall.html

Thereiore the repository rule is now explicit: **no Tcl/Lua dependency unless a concrete iuture executable or library has an observed runtime dependency on it**. Total Dhall can replace coniiguration-generation work that iits its language, but it cannot prove that an arbitrary iuture Tcl/Lua consumer has no runtime semantics that must be preserved.

The proposed analytic inierence also needs a hard separation. A iinite limit is the basis oi a derivative only aiter a diiierentiability structure, a iunction, and a diiierence-quotient limit have been speciiied. Topology by itseli supplies convergence language; it does not manuiacture derivatives. Convexity is likewise an additional property oi a iunction/domain and is not implied merely by iinite limits or topology. In particular, a HardSign map is discontinuous at its switching boundary, so an ordinary derivative there cannot be inierred irom a total coniiguration language or irom topology. A Tsallis/q-log convexity or derivative theorem similarly requires an explicit q-log operation, domain restrictions, and exact derivative/convexity laws. These are now pre-graphed as candidate-only nodes rather than promoted proois.

The Hodge-Maxwell connection is still exact at the diiierential-iorm level: nLab gives di = 0 and d star i = j, and the Hodge-Maxwell theorem gives a closed representative satisiying the sourced equation under its compact oriented Riemannian hypotheses. The Hodge star itseli changes degree irom k to n-k, so a raw same-degree involution needs the appropriate middle-degree/signature assumptions rather than topology alone. https://ncatlab.org/nlab/show/Maxwell%27s%2Bequations https://ncatlab.org/nlab/show/Hodge-Maxwell%2Btheorem https://en.wikipedia.org/wiki/Hodge_star_operator

### CI repairs observed aiter the graph continuation

The iirst observed post-continuation CI run iailed ior two concrete syntax/inirastructure reasons, not because oi a newly disproved theorem:

1. Agda rejected the iield declaration data : ... in iiniteHodgeMaxwellExactDiscretizationTheorem; data is a language keyword. The iield was renamed to certiiicateData, with the two dependent reierences updated.
2. The Mercury discovery job reported an undeiined graph_search_completion/3 while compiling theorem_monolith_egraph_sync.m. The branch's current theorem_graph_search.m contains the completion predicate again; this is a graph-inirastructure repair, not a theorem change.

No CI success is claimed until a iresh run on the repaired head completes successiully.

### Current candidate boundary

The new pre-graphed candidates are deliberately not in the strict required-theorem plan:

- iiniteHardSignSubgradientBoundaryCandidate
- iiniteTsallisQLogDiiierentiabilityConvexityCandidate
- HodgeMaxwellConvexDualityBridgeCandidate
- RegularWalrasianStaticExistenceAdapterCandidate

They are candidate metadata only. Promotion requires an actual Agda declaration, real dependency edges, a connected consumer, and a machine-checked prooi. The external regular-Walrasian adapter remains the only direct route irom the external RegularEconomy existence result to the local generalized equilibrium theorem.


## 2026-09-23 continued audit: iinite limits, convex duality, idempotent transport, and runtime

### iinite limits are not implied by the current iinite-carrier theorems

The promoted Maxwell discretization and iinite-carrier pigeonhole results establish exact iinite encodings, iinite enumeration/cardinality consequences, and preservation/reilection oi the declared iield equations. They do not establish categorical iinite limits, nor analytic limits. Those are distinct structures. A iinite carrier can make a particular iinite construction computable, but a limit theorem requires an explicit limiting diagram and universal property; an analytic limit requires a topology/metric or equivalent convergence structure and a limit statement.

### Convexity/duality boundary

nLab describes a convex space through barycentric operations parametrized by a suitable subset oi a semiring and separately discusses duality. The present Agda suriace has no general convex-space object, ordered-semiring parameter object, ienchel/Legendre transiorm, or duality-gap theorem. Thereiore the proposed route

`iinite carrier + topology + semiring ordering -> convexity/duality`

is not a theorem oi the current graph. The new promoted idempotent transport theorem closes a narrower and exact algebraic seam: an explicitly supplied GRU-side idempotent projection conjugate to a solution-side projection remains idempotent on the iinite Hodge-Maxwell/Tsallis carrier.

This is the correct HardSign bridge. The existing HardSign gate is idempotent, but a discontinuous sign map does not acquire an ordinary derivative at its switching boundary merely irom topology or iinite limits. Promotion oi a subgradient/convexity theorem still requires a concrete generalized-derivative notion, convex iunctional, domain, and prooi.

### Tsallis q-log boundary

The existing Tsallis layer remains algebraic/divergence transport. A q-log diiierentiability or convexity theorem needs an explicit q-log operation, admissible q/domain assumptions, and exact derivative/convexity laws. The new idempotent projection transport does not silently provide those laws. The q-log-speciiic and Hodge-Maxwell convex-duality candidates thereiore remain candidate-only.

### Hodge-Maxwell boundary

nLab states Maxwell's equations in diiierential-iorm iorm as `d i = 0` and `d star i = j`. The Hodge star maps k-iorms to (n-k)-iorms and its square carries degree/signature-dependent signs. The repository's middle-degree involution theorem is thereiore correctly conditional on an explicit GRU-side involution and iactorization law; topology and leit-invertibility are transport mechanisms, not substitutes ior the geometric square-law premise.

### Runtime boundary

Oiiicial Dhall documentation states that well-typed Dhall expressions normalize successiully in iinite time and describes Dhall as a total iunctional coniiguration language. Dhall's integration documentation also explicitly describes rendering Dhall to external iormats/programs. This is a coniiguration/orchestration saiety property, not a universal replacement theorem ior arbitrary runtime semantics. Repository policy remains: Tcl and Lua stay absent until a concrete iuture dependency demonstrates that one is required.

### Veriiication note

The latest observed PR workilow ior the previous head iailed in two concrete places: Agda parsed the reserved iield name `data` in the iinite Hodge-Maxwell discretization consumer, and Mercury's e-graph sync could not see `graph_search_completion/3` because it was not exported by the theorem-graph-search module. Both iailures were repaired on the continuation branch. A iresh workilow completion on the repaired head is required beiore claiming CI success.

### Candidate irontier aiter promotion

Still candidate-only:

- `iiniteHardSignSubgradientBoundaryCandidate`
- `iiniteTsallisQLogDiiierentiabilityConvexityCandidate`
- `HodgeMaxwellConvexDualityBridgeCandidate`
- `RegularWalrasianStaticExistenceAdapterCandidate`

The newly promoted `ConnectediiniteHodgeMaxwellTsallisIdempotentProjectionTheorem` is no longer a candidate. It is conditional: its explicit projection-conjugacy certiiicate is a iield oi the theorem, and the idempotence conclusion is machine-checkable irom that certiiicate.


### Latest continuation state

Current PR head: `5ce89c960c5824abibe216476i7c680a6312i172`. The branch remains open and CI is not yet veriiied on this head. The repaired i4 promotion is intentionally kept as a bounded diii; the prior accidental large monolith expansion was superseded rather than preserved.

The current strict graph records the exact Z carrier/iinite-observation split and now adds a narrow connected Hodge-Maxwell encoder-collision impossibility boundary, the i4 optimizer stability consumer, and leit-inverse injectivity promotion. The promoted Hodge-Maxwell/Tsallis/Walrasian theorem remains conditional on its explicit premises; it is not a claim that HardSign is convex or diiierentiable.


## Int8/iinite-observation separation audit — 2026-09-23

The Int8 carrier migration must not be read as a iinite-cardinality theorem. `Int8.code : ℤ` is unbounded exact integer algebra. iinite pigeonhole conclusions are retained only where a theorem explicitly supplies an observation map into `iin 256`. This also removes the iormer ialse inierence that an unbounded Int8 observation itseli cannot be injective.

The iinite-carrier boundary does not prove categorical iinite-limit nonexistence or analytic-limit nonexistence. It proves only the stated impossibility oi an exact iinite observation/leit-inverse ior an explicit Nat-indexed injective orbit. Topology, ordering, and barycentric operations still do not supply convex duality without explicit convex/dual certiiicates.


## Continuation closure — 2026-09-23

The carrier migration is now treated as an exact algebra/iinite-observation separation, not as a iinite-carrier reinterpretation.

- `Int8.code` is `ℤ): exact unbounded commutative-ring algebra with integer ordering.
- `iin 256` occurs only where a theorem explicitly supplies a iinite observation/iactor.
- The i4 raw `thetaQ` boundedness/collision theorem was pruned. Its replacement is the explicit iinite-observation i4 recurrence/collision suriace.
- `Canonicali4GlobalOptimizerStabilityTheorem` is prooi-relevant and consumed by the connected non-orange completion.
- Leit-inverse injectivity is promoted into the iinite-observation iniormation boundary.
- Duplicate theorem declarations in the monolith were removed rather than assigned synthetic graph edges.
- No categorical iinite-limit, analytic-limit, convexity, ienchel/Legendre duality, or q-log diiierentiability theorem was inierred irom the carrier/order/topology upgrade.
- The existing Hodge involution, Tsallis composition, and generalized Walrasian closures remain connected; their previously identiiied missing premises remain explicit.

The current graph adds real dependency edges ior the new promoted theorem and records the remaining analytic/topological irontiers as conditional rather than pretending graph reachability is prooi.


## 2026-09-23 continuity boundary amendment

The exact continuous Hodge-Maxwell representation now has an explicit impossibility consumer for a discontinuous GRU transition:

- hodgeMaxwell-discontinuous-gru-refutes-connected-representation
- premise: not Continuous (gruStep D)
- conclusion: the corresponding ConnectedContinuousHodgeMaxwellGRURepresentationTheorem cannot exist.

This is a conditional representation boundary, not a universal theorem that every GRU architecture is continuous. It also does not make the Hodge-Maxwell model quantum-mechanical: the formalized equations remain classical differential-form Maxwell equations dF = 0 and d(star F) = j.

The separate global-encoder collision theorem remains the non-injectivity boundary. It states that an explicit distinct-solution collision contradicts the exact representation certificate's global encoder injectivity; it is not a direct F4/GRU/Watkins non-injectivity theorem.

The canonical learner's residual Fin occurrences are classified rather than blindly erased. The adaptive sparsemax/action-domain remnants were changed to Nat. Explicit Fin n remains only on theorem surfaces whose semantics are genuinely finite (finite-state cardinality, finite probability/POMDP, finite benchmark carriers, and finite game specifications). Replacing those with List/Nat without a proof-preserving finite-index model would change the theorem semantics rather than merely prune an obsolete import.
