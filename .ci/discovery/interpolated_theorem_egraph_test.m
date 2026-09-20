:- module interpolated_theorem_egraph_test.

:- interface.

:- import_module io.

:- pred main(io::di, io::uo) is det.

:- implementation.

:- import_module io.
:- import_module symbolic_egraph.
:- import_module interpolated_theorem_egraph.
:- import_module learner_semantic_manifest.
:- import_module list.

main(!IO) :-
    read_manifest(Laws, !IO),
    discovery_egraph_from_laws(Laws, E0, QuotientCount),
    saturate(semantic_rewrite_rules, 32, E0, E, Saturation),
    analyze(E, Analyses),
    add_expr(app("semantic-law", [atom(forced_target_id)]), E, TargetClass, E1),
    extract_best(TargetClass, E1, 64, _, ExtractionCost),
    CompositeCount = list.length(
        list.filter(
            (pred(L::in) is semidet :-
                semantic_law.composite(L) = yes),
            Laws)),
    ExactUAPId = "../../Exotic/ERL/FullCoupled/TheoremsMonolith.agda#ExactUniversalApproximationThroughContinuousLeftInverse",
    ContinuousBoundaryId = "../../Exotic/ERL/FullCoupled/TheoremsMonolith.agda#canonicalNoGlobalInt8ContinuousLeftInverseOnDiscreteTopologies",
    InjectivityId = "../../Exotic/ERL/FullCoupled/TheoremsMonolith.agda#leftInverse-observation-injective",
    FiniteFeatureId = "../../Exotic/ERL/FullCoupled/TheoremsMonolith.agda#canonicalNoGlobalFiniteFeatureContinuousLeftInverseOnDiscreteTopologies",
    FiniteTimeId = "../../Exotic/ERL/FullCoupled/TheoremsMonolith.agda#canonicalFiniteTimeExactUniversalReadout",
    FiniteSampleId = "../../Exotic/ERL/FullCoupled/TheoremsMonolith.agda#canonicalFiniteSampleExactUniversalReadout",
    IterateCompositionId = "../../Exotic/ERL/FullCoupled/TheoremsMonolith.agda#canonicalIterateComposition",
    MixingPrefixCompositionId = "../../Exotic/ERL/FullCoupled/TheoremsMonolith.agda#CanonicalHadamardAttentionRopePrefixCompositionTheorem",
    AperiodicityId = "../../Exotic/ERL/FullCoupled/TheoremsMonolith.agda#canonicalAperiodic-theorem",
    FiniteCycleId = "../../Exotic/ERL/FullCoupled/TheoremsMonolith.agda#canonicalNoNontrivialFiniteCycle-theorem",
    VisitId = "../../Exotic/ERL/FullCoupled/TheoremsMonolith.agda#finiteStateActionVisitInjectionImpossible",
    EmergentExactOrbitId = "../../Exotic/ERL/FullCoupled/TheoremsMonolith.agda#CanonicalFiniteExactOrbitUAPCompositionTheorem",
    NonReflexive = list.length(
        list.filter(
            (pred(L::in) is semidet :-
                semantic_law.reflexive(L) = no),
            Laws)),
    (
        list.filter(
            (pred(L::in) is semidet :-
                semantic_law.source(L) =
                    "../../Exotic/ERL/FullCoupled/TheoremsMonolith.agda"),
            Laws) = Laws,
        CompositeCount > 0,
        NonReflexive >= CompositeCount,
        QuotientCount > 0,
        class_count(E) > 0,
        enode_count(E) > 0,
        class_count(E) < enode_count(E),
        list.length(Analyses) > 0,
        saturation_iterations(Saturation) > 0,
        ExtractionCost > 0,
        list.member(ExactUAPLaw, Laws),
        law_id(ExactUAPLaw) = ExactUAPId,
        list.member(ContinuousBoundaryLaw, Laws),
        law_id(ContinuousBoundaryLaw) = ContinuousBoundaryId,
        list.member(InjectivityLaw, Laws),
        law_id(InjectivityLaw) = InjectivityId,
        list.member(FiniteFeatureLaw, Laws),
        law_id(FiniteFeatureLaw) = FiniteFeatureId,
        list.member(FiniteTimeLaw, Laws),
        law_id(FiniteTimeLaw) = FiniteTimeId,
        list.member(FiniteSampleLaw, Laws),
        law_id(FiniteSampleLaw) = FiniteSampleId,
        list.member(IterateCompositionLaw, Laws),
        law_id(IterateCompositionLaw) = IterateCompositionId,
        list.member(MixingPrefixCompositionLaw, Laws),
        law_id(MixingPrefixCompositionLaw) = MixingPrefixCompositionId,
        list.member(AperiodicityLaw, Laws),
        law_id(AperiodicityLaw) = AperiodicityId,
        list.member(FiniteCycleLaw, Laws),
        law_id(FiniteCycleLaw) = FiniteCycleId,
        list.member(VisitLaw, Laws),
        law_id(VisitLaw) = VisitId,
        list.member(EmergentExactOrbitLaw, Laws),
        law_id(EmergentExactOrbitLaw) = EmergentExactOrbitId,
        e_match(
            papp("proof-compose", [
                pvar("A"),
                papp("proof-compose", [pvar("B"), pvar("C")])
            ]),
            TargetClass,
            E1,
            _)
    ->
        io.write_string(
            "theorem-semantic-egraph-regression=pass "
            "source=manifest "
            "quotient=proof-compose-associativity "
            "e-matching=on saturation=on rebuild=on "
            "eclass-analysis=on cost-extraction=on "
            "dynamic=on\n",
            !IO)
    ;
        io.write_string(
            "ERROR: theorem semantic e-graph regression failed\n",
            !IO),
        io.set_exit_status(1, !IO)
    ).
