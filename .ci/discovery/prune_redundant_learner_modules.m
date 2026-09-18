:- module prune_redundant_learner_modules.

:- interface.

:- import_module io.

:- pred main(io::di, io::uo) is det.

:- implementation.

:- import_module list.

:- func candidate_pairs = list({string, string}).
candidate_pairs = [
    {"Exotic/ERL/FullCoupled/CanonicalSparsemaxLearnerV2.agda",
        "Exotic.ERL.FullCoupled.CanonicalSparsemaxLearnerV2"},
    {"Exotic/ERL/FullCoupled/CanonicalSparsemaxLearnerV2_test.agda",
        "Exotic.ERL.FullCoupled.CanonicalSparsemaxLearnerV2_test"},
    {"Exotic/ERL/FullCoupled/DyadicGRU.agda",
        "Exotic.ERL.FullCoupled.DyadicGRU"},
    {"Exotic/ERL/FullCoupled/FrozenOrthonormalWalshGRU.agda",
        "Exotic.ERL.FullCoupled.FrozenOrthonormalWalshGRU"},
    {"Exotic/ERL/FullCoupled/Int8StabilityComposition.agda",
        "Exotic.ERL.FullCoupled.Int8StabilityComposition"},
    {"Exotic/ERL/FullCoupled/FiniteSemidirectComposition.agda",
        "Exotic.ERL.FullCoupled.FiniteSemidirectComposition"},
    {"Exotic/ERL/FullCoupled/CountMemoryCycleTheorem.agda",
        "Exotic.ERL.FullCoupled.CountMemoryCycleTheorem"},
    {"Exotic/ERL/FullCoupled/CountMemoryCycleTheorem_test.agda",
        "Exotic.ERL.FullCoupled.CountMemoryCycleTheorem_test"},
    {"Exotic/ERL/FullCoupled/AllSafeCombined.agda",
        "Exotic.ERL.FullCoupled.AllSafeCombined"},
    {"Exotic/ERL/FullCoupled/AllSafeCombined_test.agda",
        "Exotic.ERL.FullCoupled.AllSafeCombined_test"},
    {"Exotic/ERL/FullCoupled/DeterministicQSA.agda",
        "Exotic.ERL.FullCoupled.DeterministicQSA"},
    {"Exotic/ERL/FullCoupled/DeterministicQSA_test.agda",
        "Exotic.ERL.FullCoupled.DeterministicQSA_test"}
].

:- pred audit({string, string}::in, io::di, io::uo) is det.
audit({Path, Module}, !IO) :-
    io.write_string("candidate=" ++ Path ++ ", module=" ++ Module ++ "\n", !IO),
    Command =
        "if test -e '" ++ Path ++ "'; then " ++
        "if git grep -n -I -- 'import " ++ Module ++ "' -- '*.agda' >/dev/null 2>&1; " ++
        "then echo users-present; else echo prunable-zero-import-users; fi; " ++
        "else echo absent; fi",
    io.call_system(Command, _, !IO).

main(!IO) :-
    io.write_string("canonical=Exotic/ERL/FullCoupled/CanonicalLearnerMonolith.agda\n", !IO),
    io.write_string("prune-mode=dry-run\n", !IO),
    list.foldl(audit, candidate_pairs, !IO),
    io.write_string("mercury-prune-audit=complete\n", !IO).
