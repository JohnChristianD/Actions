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
    "Exotic/ERL/FullCoupled/NoisyNetCoupled.agda",
    "Exotic/ERL/FullCoupled/SparsemaxFlatDyadicBehavior.agda",
    "Exotic/ERL/FullCoupled/SparsemaxFlatDyadicBehavior_test.agda",
    "Exotic/ERL/FullCoupled/SparsemaxFlatDyadicSeparation.agda",
    "Exotic/ERL/FullCoupled/SparsemaxFlatDyadicSeparation_test.agda",
    "Exotic/ERL/FullCoupled/SharedActorCritic.agda",
    "Exotic/ERL/FullCoupled/SparsemaxActorVsCriticTheorem.agda",
    "Exotic/ERL/FullCoupled/SparsemaxActorVsCriticTheorem_test.agda",
    "Exotic/ERL/FullCoupled/SignReLUSemidirectCycleComposition.agda",
    "Exotic/ERL/FullCoupled/SignReLUSemidirectCycleComposition_test.agda",
    "Exotic/ERL/FullCoupled/ConnectedGRUSemidirectQSA.agda",
    "Exotic/ERL/FullCoupled/EGraphSemanticTransport.agda",
    "Exotic/ERL/FullCoupled/FourLawClosureWitnesses.agda",
    "Exotic/ERL/FullCoupled/FourLawClosureImpossibility.agda",
    "Exotic/ERL/FullCoupled/GRUStatisticalInjectivity.agda",
    "Exotic/ERL/FullCoupled/CommonsComposition.agda",
    "Exotic/ERL/FullCoupled/GRUFractalInjectiveComposition.agda",
    "Exotic/ERL/FullCoupled/GRUFractalInjectiveCompositionCanonical.agda",
    "Exotic/ERL/FullCoupled/GRUFractalDomainAdapters.agda",
    "Exotic/ERL/FullCoupled/GRUFractalLimitClosure.agda",
    "Exotic/ERL/FullCoupled/GRUFractalEGraphAStarLimitComposition.agda",
    "Exotic/ERL/FullCoupled/GRUFractalLimitDecoderSurvival.agda",
    "Exotic/ERL/FullCoupled/GRUFractalLimitConvergenceAdapter.agda",
    "Exotic/ERL/FullCoupled/GRUFractalLimitConvergenceImpossibility.agda",
    "Exotic/ERL/FullCoupled/ZPFStatisticalRepresentation.agda",
    "Exotic/ERL/FullCoupled/TsallisStatisticalRepresentation.agda",
    "Exotic/ERL/FullCoupled/RepositorySemanticEGraphClosure.agda",
    "Exotic/ERL/FullCoupled/FrozenOrthogonalAttentionGRU.agda",
    "Exotic/ERL/FullCoupled/Int8SparsemaxLiteral.agda",
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
        "canonical=Exotic/ERL/FullCoupled/CanonicalLearnerMonolith.agda\n",
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
