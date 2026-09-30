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
    "FullCoupled/NoisyNetCoupled.agda",
    "FullCoupled/SparsemaxFlatDyadicBehavior.agda",
    "FullCoupled/SparsemaxFlatDyadicBehavior_test.agda",
    "FullCoupled/SparsemaxFlatDyadicSeparation.agda",
    "FullCoupled/SparsemaxFlatDyadicSeparation_test.agda",
    "FullCoupled/SharedActorCritic.agda",
    "FullCoupled/SparsemaxActorVsCriticTheorem.agda",
    "FullCoupled/SparsemaxActorVsCriticTheorem_test.agda",
    "FullCoupled/SignReLUSemidirectCycleComposition.agda",
    "FullCoupled/SignReLUSemidirectCycleComposition_test.agda",
    "FullCoupled/ConnectedGRUSemidirectQSA.agda",
    "FullCoupled/EGraphSemanticTransport.agda",
    "FullCoupled/FourLawClosureWitnesses.agda",
    "FullCoupled/FourLawClosureImpossibility.agda",
    "FullCoupled/GRUStatisticalInjectivity.agda",
    "FullCoupled/CommonsComposition.agda",
    "FullCoupled/GRUFractalInjectiveComposition.agda",
    "FullCoupled/GRUFractalInjectiveCompositionCanonical.agda",
    "FullCoupled/GRUFractalDomainAdapters.agda",
    "FullCoupled/GRUFractalLimitClosure.agda",
    "FullCoupled/GRUFractalEGraphAStarLimitComposition.agda",
    "FullCoupled/GRUFractalLimitDecoderSurvival.agda",
    "FullCoupled/GRUFractalLimitConvergenceAdapter.agda",
    "FullCoupled/GRUFractalLimitConvergenceImpossibility.agda",
    "FullCoupled/ZPFStatisticalRepresentation.agda",
    "FullCoupled/TsallisStatisticalRepresentation.agda",
    "FullCoupled/RepositorySemanticEGraphClosure.agda",
    "FullCoupled/FrozenOrthogonalAttentionGRU.agda",
    "FullCoupled/Int8SparsemaxLiteral.agda",
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
        "canonical=FullCoupled/CanonicalLearnerMonolith.agda\n",
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
