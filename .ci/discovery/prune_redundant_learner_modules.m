:- module prune_redundant_learner_modules.

:- interface.

:- import_module io.

:- pred main(io::di, io::uo) is det.

:- implementation.

:- import_module list, string.

:- func candidate_paths = list(string).
candidate_paths = [
    "Exotic/ERL/FullCoupled/CanonicalSparsemaxLearnerV2.agda",
    "Exotic/ERL/FullCoupled/CanonicalSparsemaxLearnerV2_test.agda",
    "Exotic/ERL/FullCoupled/DyadicGRU.agda",
    "Exotic/ERL/FullCoupled/FrozenOrthonormalWalshGRU.agda",
    "Exotic/ERL/FullCoupled/Int8StabilityComposition.agda",
    "Exotic/ERL/FullCoupled/FiniteSemidirectComposition.agda",
    "Exotic/ERL/FullCoupled/CountMemoryCycleTheorem.agda",
    "Exotic/ERL/FullCoupled/CountMemoryCycleTheorem_test.agda",
    "Exotic/ERL/FullCoupled/AllSafeCombined.agda",
    "Exotic/ERL/FullCoupled/AllSafeCombined_test.agda",
    "Exotic/ERL/FullCoupled/DeterministicQSA.agda",
    "Exotic/ERL/FullCoupled/DeterministicQSA_test.agda"
].

:- pred audit(string::in, io::di, io::uo) is det.
audit(Path, !IO) :-
    io.read_named_file_as_string(Path, Result, !IO),
    (
        Result = error(_),
        io.write_string("absent=" ++ Path ++ "\n", !IO)
    ;
        Result = ok(Source),
        io.write_string("present=" ++ Path ++ "\n", !IO),
        (
            string.sub_string_search(Source, "import", _)
        ->
            io.write_string("candidate-import-surface=present\n", !IO)
        ;
            io.write_string("candidate-import-surface=absent\n", !IO)
        ),
        io.set_exit_status(1, !IO)
    ).

main(!IO) :-
    io.set_exit_status(0, !IO),
    io.write_string(
        "canonical=Exotic/ERL/FullCoupled/CanonicalLearnerMonolith.agda\n",
        !IO),
    io.write_string("prune-mode=dry-run; shell=none\n", !IO),
    list.foldl(audit, candidate_paths, !IO),
    io.get_exit_status(Status, !IO),
    (
        Status = 0,
        io.write_string("mercury-prune-audit=complete\n", !IO)
    ;
        true
    ).
