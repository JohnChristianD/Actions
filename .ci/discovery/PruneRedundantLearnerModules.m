:- module prune_redundant_learner_modules.

:- interface.

:- import_module io.

:- pred main(io::di, io::uo) is det.

:- implementation.

:- import_module list.
:- import_module string.

:- func candidates = list(string).
candidates = [
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

:- func module_name(string) = string.
module_name(Path) = string.replace_all(
    string.replace_all(
        string.substring(Path, 0, string.length(Path) - 5),
        "/", "."),
    "-", "_").

:- pred check_candidate(string::in, io::di, io::uo) is det.
check_candidate(Path, !IO) :-
    Module = module_name(Path),
    Command =
        "if test -e " ++ quote(Path) ++ "; then " ++
        "echo candidate=" ++ quote(Path) ++ ",module=" ++ quote(Module) ++ "; " ++
        "if git grep -n -I -- \"import " ++ Module ++ "\" -- '*.agda' >/dev/null 2>&1; " ++
        "then echo users-present; " ++
        "else echo prunable-zero-import-users; fi; " ++
        "fi",
    io.call_system(Command, _, !IO).

:- func quote(string) = string.
quote(S) = "\"" ++ S ++ "\"".

main(!IO) :-
    io.write_string("canonical=Exotic/ERL/FullCoupled/CanonicalLearnerMonolith.agda\n", !IO),
    io.write_string("prune-mode=dry-run\n", !IO),
    list.foldl(check_candidate, candidates, !IO),
    io.write_string(
        "pass --apply semantics remain intentionally guarded by repository policy\n",
        !IO
    ).

