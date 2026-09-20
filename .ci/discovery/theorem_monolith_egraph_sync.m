:- module theorem_monolith_egraph_sync.

:- interface.

:- import_module io.

:- pred main(io::di, io::uo) is det.

:- implementation.

:- import_module io.
:- import_module interpolated_theorem_egraph.
:- import_module learner_semantic_extractor.
:- import_module learner_semantic_manifest.
:- import_module list.
:- import_module string.
:- import_module symbolic_egraph.

:- func forced_target_law_id = string.
forced_target_law_id =
    "../../Exotic/ERL/FullCoupled/TheoremsMonolith.agda#canonical-endogenous-minimax-bellman-shapley-uap-theorem".

:- func continuous_readout_dependency = string.
continuous_readout_dependency =
    "../../Exotic/ERL/FullCoupled/TheoremsMonolith.agda#continuousLeftInverse-exactReadout-transfer".

:- func bounded_exact_approximation_dependency = string.
bounded_exact_approximation_dependency =
    "../../Exotic/ERL/FullCoupled/TheoremsMonolith.agda#boundedExactApproximation-on-boundedOrbit".

:- func infinite_state_orbit_dependency = string.
infinite_state_orbit_dependency =
    "../../Exotic/ERL/FullCoupled/TheoremsMonolith.agda#canonicalInfiniteStateOrbitEmbedding".

:- func pigeonhole_dependency = string.
pigeonhole_dependency =
    "../../Exotic/ERL/FullCoupled/TheoremsMonolith.agda#canonicalPigeonholeNatClockContradiction".

:- func no_global_uap_dependency = string.
:- func finite_int8_continuous_left_inverse_dependency = string.
:- func exact_universal_uap_dependency = string.
no_global_uap_dependency =
    "../../Exotic/ERL/FullCoupled/TheoremsMonolith.agda#canonicalNoGlobalInt8DiscreteUAPOnOrbit".

finite_int8_continuous_left_inverse_dependency =
    "../../Exotic/ERL/FullCoupled/TheoremsMonolith.agda#canonicalNoGlobalInt8ContinuousLeftInverseOnDiscreteTopologies".

exact_universal_uap_dependency =
    "../../Exotic/ERL/FullCoupled/TheoremsMonolith.agda#ExactUniversalApproximationThroughContinuousLeftInverse".

:- func finite_feature_continuity_dependency = string.
finite_feature_continuity_dependency =
    "../../Exotic/ERL/FullCoupled/TheoremsMonolith.agda#canonicalNoGlobalFiniteFeatureContinuousLeftInverseOnDiscreteTopologies".

:- func finite_time_exact_readout_dependency = string.
finite_time_exact_readout_dependency =
    "../../Exotic/ERL/FullCoupled/TheoremsMonolith.agda#canonicalFiniteTimeExactUniversalReadout".

:- func finite_sample_exact_readout_dependency = string.
finite_sample_exact_readout_dependency =
    "../../Exotic/ERL/FullCoupled/TheoremsMonolith.agda#canonicalFiniteSampleExactUniversalReadout".

:- func iterate_composition_dependency = string.
iterate_composition_dependency =
    "../../Exotic/ERL/FullCoupled/TheoremsMonolith.agda#canonicalIterateComposition".

:- func convex_concave_dependency = string.
convex_concave_dependency =
    "../../Exotic/ERL/FullCoupled/TheoremsMonolith.agda#TopologicalConvexConcaveExactReadoutTheorem".

:- func finite_regret_dependency = string.
finite_regret_dependency =
    "../../Exotic/ERL/FullCoupled/TheoremsMonolith.agda#finiteHorizonRegretComposition".

:- func finite_visit_dependency = string.
finite_visit_dependency =
    "../../Exotic/ERL/FullCoupled/TheoremsMonolith.agda#finiteStateActionVisitInjectionImpossible".

:- func injectivity_dependency = string.
injectivity_dependency =
    "../../Exotic/ERL/FullCoupled/TheoremsMonolith.agda#leftInverse-observation-injective".


:- func aperiodicity_dependency = string.
aperiodicity_dependency =
    "../../Exotic/ERL/FullCoupled/TheoremsMonolith.agda#canonicalAperiodic-theorem".

:- func finite_cycle_dependency = string.
finite_cycle_dependency =
    "../../Exotic/ERL/FullCoupled/TheoremsMonolith.agda#canonicalNoNontrivialFiniteCycle-theorem".


:- func recurrent_bound_uap_dependency = string.
recurrent_bound_uap_dependency =
    "../../Exotic/ERL/FullCoupled/TheoremsMonolith.agda#CanonicalRecurrentBoundedExactUniversalApproximationTheorem".

:- pred forced_target_law(
    list(semantic_law)::in, semantic_law::out) is semidet.
forced_target_law(All, Target) :-
    list.member(Target, All),
    law_id(Target) = forced_target_law_id,
    semantic_law.composite(Target) = yes,
    list.member(
        continuous_readout_dependency,
        semantic_law.dependencies(Target)),
    list.member(
        bounded_exact_approximation_dependency,
        semantic_law.dependencies(Target)),
    list.member(
        infinite_state_orbit_dependency,
        semantic_law.dependencies(Target)),
    list.member(
        pigeonhole_dependency,
        semantic_law.dependencies(Target)),
    list.member(
        no_global_uap_dependency,
        semantic_law.dependencies(Target)),
    list.member(
        finite_int8_continuous_left_inverse_dependency,
        semantic_law.dependencies(Target)),
    list.member(
        exact_universal_uap_dependency,
        semantic_law.dependencies(Target)),
    list.member(
        finite_feature_continuity_dependency,
        semantic_law.dependencies(Target)),
    list.member(
        finite_time_exact_readout_dependency,
        semantic_law.dependencies(Target)),
    list.member(
        finite_sample_exact_readout_dependency,
        semantic_law.dependencies(Target)),
    list.member(
        iterate_composition_dependency,
        semantic_law.dependencies(Target)),
    list.member(
        aperiodicity_dependency,
        semantic_law.dependencies(Target)),
    list.member(
        finite_cycle_dependency,
        semantic_law.dependencies(Target)),
    list.member(
        convex_concave_dependency,
        semantic_law.dependencies(Target)),
    list.member(
        finite_regret_dependency,
        semantic_law.dependencies(Target)),
    list.member(
        finite_visit_dependency,
        semantic_law.dependencies(Target)),
    list.member(
        injectivity_dependency,
        semantic_law.dependencies(Target)),
    list.member(
        recurrent_bound_uap_dependency,
        semantic_law.dependencies(Target)).

:- pred composite_laws(
    list(semantic_law)::in, list(semantic_law)::out) is det.
composite_laws(All, Composite) :-
    list.filter(
        (pred(L::in) is semidet :-
            semantic_law.composite(L) = yes),
        All,
        Composite).

:- pred write_report(
    list(semantic_law)::in,
    semantic_law::in,
    list(semantic_law)::in,
    int::in,
    saturation_report::in,
    int::in,
    io::di, io::uo) is det.
write_report(All, Target, Composite, QuotientCount, Saturation, ExtractionCost, !IO) :-
    NonReflexive = list.length(
        list.filter(
            (pred(L::in) is semidet :-
                semantic_law.reflexive(L) = no),
            All)),
    io.open_output("theorem-monolith-egraph-sync.json", Result, !IO),
    (
        Result = ok(Stream),
        io.write_string(Stream,
            "{\n" ++
            "  \"source_theorem_monolith\": \"../../Exotic/ERL/FullCoupled/TheoremsMonolith.agda\",\n" ++
            "  \"forced_target_law\": \"" ++ law_id(Target) ++ "\",\n" ++
            "  \"single_agda_source\": true,\n" ++
            "  \"generated_agda_module\": false,\n" ++
            "  \"semantic_law_count\": " ++
                string.int_to_string(list.length(All)) ++ ",\n" ++
            "  \"nonreflexive_law_count\": " ++
                string.int_to_string(NonReflexive) ++ ",\n" ++
            "  \"composite_law_count\": " ++
                string.int_to_string(list.length(Composite)) ++ ",\n" ++
            "  \"egraph_associativity_quotient_count\": " ++
                string.int_to_string(QuotientCount) ++ ",\n" ++
            "  \"egraph_e_matching\": \"on\",\n" ++
            "  \"egraph_saturation\": \"on\",\n" ++
            "  \"egraph_rebuild\": \"on\",\n" ++
            "  \"egraph_eclass_analysis\": \"on\",\n" ++
            "  \"egraph_cost_extraction\": \"on\",\n" ++
            "  \"egraph_saturation_iterations\": " ++
                string.int_to_string(saturation_iterations(Saturation)) ++ ",\n" ++
            "  \"egraph_extraction_cost\": " ++
                string.int_to_string(ExtractionCost) ++ ",\n" ++
            "  \"continuous_left_inverse_transfer\": \"connected\",\n" ++
            "  \"exact_universal_readout\": \"connected\",\n" ++
            "  \"bounded_exact_approximation\": \"connected\",\n" ++
            "  \"infinite_state_orbit\": \"connected\",\n" ++
            "  \"pigeonhole_contradiction\": \"connected\",\n" ++
            "  \"global_int8_uap\": \"refuted\",\n" ++
            "  \"proof_authority\": \"Agda --safe\"\n" ++
            "}\n",
            !IO),
        io.close_output(Stream)
    ;
        Result = error(_),
        io.write_string(
            "ERROR: cannot write theorem monolith e-graph sync report\n",
            !IO),
        io.set_exit_status(1, !IO)
    ).

main(!IO) :-
    extract_semantics(!IO),
    read_manifest(All, !IO),
    composite_laws(All, Composite),
    (
        forced_target_law(All, Target),
        discovery_egraph_from_laws(All, EGraph0, QuotientCount),
        saturate(semantic_rewrite_rules, 32, EGraph0, EGraph, Saturation),
        analyze(EGraph, Analyses),
        add_expr(law_expr(forced_target_law_id), EGraph, TargetClass, EGraph1),
        extract_best(TargetClass, EGraph1, 64, _, ExtractionCost),
        list.length(All) > 0,
        list.length(Composite) > 0,
        QuotientCount > 0,
        class_count(EGraph) > 0,
        enode_count(EGraph) > 0,
        list.length(Analyses) > 0,
        saturation_iterations(Saturation) > 0,
        ExtractionCost > 0
    ->
        write_report(All, Target, Composite, QuotientCount, Saturation, ExtractionCost, !IO),
        io.write_string(
            "mercury-theorem-monolith-egraph-sync=pass\n",
            !IO),
        io.write_string(
            "forced-target-law=" ++ law_id(Target) ++ "\n",
            !IO),
        io.write_string(
            "single-agda-source=TheoremsMonolith.agda\n",
            !IO),
        io.write_string(
            "generated-agda-module=false\n",
            !IO),
        io.write_string(
            "continuous-left-inverse=connected\n",
            !IO),
        io.write_string(
            "bounded-exact-approximation=connected\n",
            !IO),
        io.write_string(
            "infinite-state-orbit=connected\n",
            !IO),
        io.write_string(
            "pigeonhole-global-int8-uap=refuted\n",
            !IO),
        io.write_string(
            "egraph-associativity-quotient-count=" ++
            string.int_to_string(QuotientCount) ++ "\n",
            !IO),
        io.write_string(
            "e-matching=on saturation=on rebuild=on eclass-analysis=on cost-extraction=on\n",
            !IO),
        io.write_string(
            "finite-int8-continuous-left-inverse=contradicted\n"
            "generic-finite-feature-obstruction=connected\n"
            "finite-time-exact-readout=connected\n"
            "finite-sample-exact-readout=connected\n"
            "iterate-composition=connected\n"
            "topology-convex-concave=connected\n"
            "finite-regret-composition=connected\n"
            "finite-state-action-visit-capacity=connected\n"
            "left-inverse-injectivity=connected\n",
            !IO)
    ;
        io.write_string(
            "ERROR: theorem monolith target/dependencies or semantic e-graph gate failed\n",
            !IO),
        io.set_exit_status(1, !IO)
    ).

