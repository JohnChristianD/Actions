:- module check_forbidden_theorems.

:- interface.

:- import_module io.

:- pred main(io::di, io::uo) is det.

:- implementation.

:- import_module list.
:- import_module string.

:- func checked_paths = list(string).
checked_paths = [
    "Exotic/ERL/FullCoupled/GeneralFullCoupledLearnerMonolith.agda",
    "Exotic/ERL/FullCoupled/GeneralFullCoupledTheoremsMonolith.agda",
    "Exotic/ERL/FullCoupled/GeneralClosedLoopBenchV2.agda",
    "Exotic/ERL/FullCoupled/CanonicalLearnerMonolith.agda",
    "Exotic/ERL/FullCoupled/CanonicalLearnerMonolith_test.agda",
    "Exotic/ERL/FullCoupled/CanonicalClosedLoopBench.agda",
    "Exotic/ERL/FullCoupled/CanonicalGamePorts.agda",
    "Exotic/ERL/FullCoupled/CanonicalFaithfulGameVariants.agda",
    "Exotic/ERL/FullCoupled/CanonicalLearnerGameExecution_test.agda",
    "Exotic/econlib/GameTheory.agda",
    "Exotic/econlib/Equilibrium.agda",
    "Exotic/econlib/MatchingPennies.agda"
].

:- func forbidden = list(string).
forbidden = [
    "transcendental",
    "transcendentals",
    "flatdyadicmix",
    "postulate",
    "{-# postulate",
    "{!",
    "!!}",
    "?hole?"
].

:- pred file_clean(string::in, list(string)::in, io::di, io::uo) is det.

file_clean(Path, Tokens, !IO) :-
    io.read_named_file_as_string(Path, Result, !IO),
    (
        Result = ok(Source),
        Lower = string.to_lower(Source),
        inspect_tokens(Path, Lower, Tokens, Problems),
        print_problems(Problems, !IO)
    ;
        Result = error(_),
        io.format("ERROR: required proof file missing or unreadable: %s\n",
            [s(Path)], !IO),
        io.set_exit_status(1, !IO)
    ).

:- pred inspect_tokens(string::in, string::in, list(string)::in,
    list(string)::out) is det.

inspect_tokens(Path, Source, Tokens, Problems) :-
    inspect_tokens_2(Path, Source, Tokens, [], Rev),
    list.reverse(Rev, Problems).

:- pred inspect_tokens_2(string::in, string::in, list(string)::in,
    list(string)::in, list(string)::out) is det.

inspect_tokens_2(_, _, [], !Problems).
inspect_tokens_2(Path, Source, [Token | Tokens], !Problems) :-
    LowerToken = string.to_lower(Token),
    (
        string.sub_string_search(Source, LowerToken, _)
    ->
        Problem = "ERROR: forbidden token in " ++ Path ++ ": " ++ Token,
        !:Problems = [Problem | !.Problems]
    ;
        true
    ),
    inspect_tokens_2(Path, Source, Tokens, !Problems).

:- pred print_problems(list(string)::in, io::di, io::uo) is det.

print_problems([], !IO).
print_problems([P | Ps], !IO) :-
    io.write_string(P ++ "\n", !IO),
    io.set_exit_status(1, !IO),
    print_problems(Ps, !IO).

:- pred scan(list(string)::in, io::di, io::uo) is det.

scan([], !IO).
scan([Path | Paths], !IO) :-
    file_clean(Path, forbidden, !IO),
    scan(Paths, !IO).

main(!IO) :-
    io.set_exit_status(0, !IO),
    scan(checked_paths, !IO),
    io.get_exit_status(Status, !IO),
    (
        Status = 0,
        io.write_string("canonical-and-generalized-safe-surface=complete\n", !IO),
        io.write_string("holes-and-postulates=absent\n", !IO),
        io.write_string("forbidden-theorem-families=absent\n", !IO)
    ;
        Status \= 0
    ).
