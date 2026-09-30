:- module prune_redundant_components.

:- interface.

:- import_module io.

:- pred main(io::di, io::uo) is det.

:- implementation.

:- import_module list.

:- func retired_paths = list(string).
retired_paths = [
    "Exotic/ERL/Exploration/MR15Reachability.agda",
    "Exotic/ERL/Exploration/OpenESDyadic.agda",
    "Exotic/FullCoupled/NoisyNetCoupled.agda",
    "Exotic/FullCoupled/SparsemaxFlatDyadicBehavior.agda",
    "Exotic/FullCoupled/SparsemaxFlatDyadicBehavior_test.agda",
    "Exotic/FullCoupled/SparsemaxFlatDyadicSeparation.agda",
    "Exotic/FullCoupled/SparsemaxFlatDyadicSeparation_test.agda",
    "Exotic/FullCoupled/SharedActorCritic.agda",
    "Exotic/FullCoupled/SparsemaxActorVsCriticTheorem.agda",
    "Exotic/FullCoupled/SparsemaxActorVsCriticTheorem_test.agda",
    "Exotic/FullCoupled/SignReLUSemidirectCycleComposition.agda",
    "Exotic/FullCoupled/SignReLUSemidirectCycleComposition_test.agda",
    "Exotic/FullCoupled/ConnectedGRUSemidirectQSA.agda",
    "Exotic/FullCoupled/EGraphSemanticTransport.agda",
    "Exotic/FullCoupled/FourLawClosureWitnesses.agda",
    "Exotic/FullCoupled/FourLawClosureImpossibility.agda",
    "Exotic/FullCoupled/GRUStatisticalInjectivity.agda",
    "Exotic/FullCoupled/CommonsComposition.agda",
    "Exotic/FullCoupled/GRUFractalInjectiveComposition.agda",
    "Exotic/FullCoupled/GRUFractalInjectiveCompositionCanonical.agda",
    "Exotic/FullCoupled/GRUFractalDomainAdapters.agda",
    "Exotic/FullCoupled/GRUFractalLimitClosure.agda",
    "Exotic/FullCoupled/GRUFractalEGraphAStarLimitComposition.agda",
    "Exotic/FullCoupled/GRUFractalLimitDecoderSurvival.agda",
    "Exotic/FullCoupled/GRUFractalLimitConvergenceAdapter.agda",
    "Exotic/FullCoupled/GRUFractalLimitConvergenceImpossibility.agda",
    "Exotic/FullCoupled/ZPFStatisticalRepresentation.agda",
    "Exotic/FullCoupled/TsallisStatisticalRepresentation.agda",
    "Exotic/FullCoupled/RepositorySemanticEGraphClosure.agda",
    "Exotic/FullCoupled/FrozenOrthogonalAttentionGRU.agda",
    "Exotic/FullCoupled/Int8SparsemaxLiteral.agda",
    "Exotic/econlib/RockPaperScissors.agda",
    "Exotic/econlib/RockPaperScissors_test.agda"
].

:- pred audit_path(string::in, io::di, io::uo) is det.
audit_path(Path, !IO) :-
    io.read_named_file_as_string(Path, Result, !IO),
    (
        Result = error(_),
        io.write_string("absent=" ++ Path ++ "\n", !IO)
    ;
        Result = ok(_),
        io.write_string("ERROR: retired component still exists: " ++ Path ++ "\n", !IO),
        io.set_exit_status(1, !IO)
    ).

main(!IO) :-
    io.set_exit_status(0, !IO),
    io.write_string(
        "canonical=Exotic/FullCoupled/CanonicalLearnerMonolith.agda\n",
        !IO),
    list.foldl(audit_path, retired_paths, !IO),
    io.get_exit_status(Status, !IO),
    (
        Status = 0,
        io.write_string("canonical-component-audit=clean\n", !IO),
        io.write_string("retirement-policy=fail-if-reintroduced\n", !IO)
    ;
        true
    ).
