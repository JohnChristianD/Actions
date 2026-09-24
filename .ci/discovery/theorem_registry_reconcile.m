:- module theorem_registry_reconcile.

:- interface.

:- import_module io.

:- pred main(io::di, io::uo) is det.

:- implementation.

:- import_module bool.
:- import_module list.
:- import_module learner_semantic_extractor.
:- import_module string.

:- type mode
    ---> check
    ;    prune.

:- type registry_result
    ---> registry_result(
        found :: bool,
        changed :: bool,
        stale :: list(string)
    ).

:- func actions_ci_path = string.
actions_ci_path = "../actions_ci.dhall".

:- func graph_search_path = string.
graph_search_path = "theorem_graph_search.m".

:- pred live_name(string::in, list(semantic_law)::in) is semidet.
live_name(Name, [Law | Laws]) :-
    (
        law_name(Law) = Name
    ->
        true
    ;
        live_name(Name, Laws)
    ).

live_name(_, []) :-
    fail.

:- pred add_stale(string::in, list(string)::in, list(string)::out) is det.
add_stale(Name, Acc, Out) :-
    (
        list.member(Name, Acc)
    ->
        Out = Acc
    ;
        Out = [Name | Acc]
    ).

:- pred write_lines(io.text_output_stream::in, list(string)::in,
    io::di, io::uo) is det.

write_lines(_, [], !IO).
write_lines(Stream, [Line | Lines], !IO) :-
    io.write_string(Stream, Line, !IO),
    io.write_string(Stream, "\n", !IO),
    write_lines(Stream, Lines, !IO).

:- pred read_lines(string::in, list(string)::out,
    io::di, io::uo) is semidet.

read_lines(Path, Lines, !IO) :-
    io.read_named_file_as_lines(Path, Result, !IO),
    (
        Result = ok(Lines)
    ;
        Result = error(_),
        fail
    ).

:- pred write_file(string::in, list(string)::in,
    io::di, io::uo) is det.

write_file(Path, Lines, !IO) :-
    io.open_output(Path, Result, !IO),
    (
        Result = ok(Stream),
        write_lines(Stream, Lines, !IO),
        io.close_output(Stream, !IO)
    ;
        Result = error(_),
        io.write_string(
            "ERROR: cannot write " ++ Path ++ "\n",
            !IO),
        io.set_exit_status(1, !IO)
    ).

:- pred parse_quoted_symbol(string::in, string::out) is semidet.
parse_quoted_symbol(Line, Name) :-
    Parts = string.split_at_string("\\"", string.strip(Line)),
    Parts = [_, Candidate | _],
    Candidate \= "",
    Name = Candidate.

:- pred filter_actions_lines(
    list(string)::in,
    list(semantic_law)::in,
    bool::in,
    list(string)::in,
    int::in,
    int::out,
    list(string)::in,
    list(string)::out,
    list(string)::out,
    bool::in,
    bool::out) is det.

filter_actions_lines([], _, InRequired, Acc, Stale0, Stale, StaleNames0,
    StaleNames, Out, Found0, Found) :-
    (
        InRequired = yes,
        io.write_string(
            "ERROR: unterminated required registry in actions_ci.dhall\n",
            !IO),
        io.set_exit_status(1, !IO)
    ;
        true
    ),
    Stale = Stale0,
    StaleNames = StaleNames0,
    list.reverse(Acc, Out),
    Found = Found0.

filter_actions_lines([Line | Lines], Live, InRequired0, Acc0,
    Stale0, Stale, StaleNames0, StaleNames, Out, Found0, Found) :-
    Trimmed = string.strip(Line),
    (
        InRequired0 = no,
        Trimmed = "required='"
    ->
        filter_actions_lines(
            Lines, Live, yes, [Line | Acc0],
            Stale0, Stale, StaleNames0, StaleNames,
            Out, yes, Found)
    ;
        InRequired0 = yes,
        Trimmed = "'"
    ->
        filter_actions_lines(
            Lines, Live, no, [Line | Acc0],
            Stale0, Stale, StaleNames0, StaleNames,
            Out, Found0, Found)
    ;
        InRequired0 = yes,
        Trimmed \= "",
        live_name(Trimmed, Live)
    ->
        filter_actions_lines(
            Lines, Live, yes, [Line | Acc0],
            Stale0, Stale, StaleNames0, StaleNames,
            Out, Found0, Found)
    ;
        InRequired0 = yes,
        Trimmed \= ""
    ->
        add_stale(Trimmed, StaleNames0, StaleNames1),
        filter_actions_lines(
            Lines, Live, yes, Acc0,
            Stale0 + 1, Stale, StaleNames1, StaleNames,
            Out, Found0, Found)
    ;
        filter_actions_lines(
            Lines, Live, InRequired0, [Line | Acc0],
            Stale0, Stale, StaleNames0, StaleNames,
            Out, Found0, Found)
    ).

:- pred graph_state_transition(
    string::in, string::out) is semidet.

graph_state_transition(
    "graph_required_theorems = [", "theorems").
graph_state_transition(
    "graph_required_subcompositions = [", "subcompositions").

:- pred filter_graph_lines(
    list(string)::in,
    list(semantic_law)::in,
    string::in,
    list(string)::in,
    int::in,
    int::out,
    list(string)::in,
    list(string)::out,
    list(string)::out,
    bool::in,
    bool::out) is det.

filter_graph_lines([], _, State, Acc, Stale0, Stale, StaleNames0,
    StaleNames, Out, Found0, Found) :-
    (
        State \= "outside"
    ->
        io.write_string(
            "ERROR: unterminated graph registry in theorem_graph_search.m\n",
            !IO),
        io.set_exit_status(1, !IO)
    ;
        true
    ),
    Stale = Stale0,
    StaleNames = StaleNames0,
    list.reverse(Acc, Out),
    Found = Found0.

filter_graph_lines([Line | Lines], Live, State0, Acc0,
    Stale0, Stale, StaleNames0, StaleNames, Out, Found0, Found) :-
    Trimmed = string.strip(Line),
    (
        State0 = "outside",
        graph_state_transition(Trimmed, NewState)
    ->
        filter_graph_lines(
            Lines, Live, NewState, [Line | Acc0],
            Stale0, Stale, StaleNames0, StaleNames,
            Out, yes, Found)
    ;
        State0 \= "outside",
        Trimmed = "]."
    ->
        filter_graph_lines(
            Lines, Live, "outside", [Line | Acc0],
            Stale0, Stale, StaleNames0, StaleNames,
            Out, Found0, Found)
    ;
        State0 \= "outside",
        parse_quoted_symbol(Trimmed, Name),
        live_name(Name, Live)
    ->
        filter_graph_lines(
            Lines, Live, State0, [Line | Acc0],
            Stale0, Stale, StaleNames0, StaleNames,
            Out, Found0, Found)
    ;
        State0 \= "outside",
        parse_quoted_symbol(Trimmed, Name)
    ->
        add_stale(Name, StaleNames0, StaleNames1),
        filter_graph_lines(
            Lines, Live, State0, Acc0,
            Stale0 + 1, Stale, StaleNames1, StaleNames,
            Out, Found0, Found)
    ;
        filter_graph_lines(
            Lines, Live, State0, [Line | Acc0],
            Stale0, Stale, StaleNames0, StaleNames,
            Out, Found0, Found)
    ).

:- pred reconcile_actions(
    list(semantic_law)::in,
    mode::in,
    io::di, io::uo,
    registry_result::out) is det.

reconcile_actions(Live, Mode, !IO, Result) :-
    (
        read_lines(actions_ci_path, Lines0, !IO)
    ->
        filter_actions_lines(
            Lines0, Live, no, [], 0, StaleCount,
            [], StaleRev, Lines1, no, Found),
        list.reverse(StaleRev, Stale),
        (
            StaleCount > 0,
            Mode = prune
        ->
            write_file(actions_ci_path, Lines1, !IO),
            Changed = yes
        ;
            Changed = no
        ),
        (
            Found = yes
        ->
            true
        ;
            io.write_string(
                "ERROR: required registry not found in actions_ci.dhall\n",
                !IO),
            io.set_exit_status(1, !IO)
        ),
        Result = registry_result(Found, Changed, Stale)
    ;
        io.write_string(
            "ERROR: cannot read actions_ci.dhall\n",
            !IO),
        io.set_exit_status(1, !IO),
        Result = registry_result(no, no, [])
    ).

:- pred reconcile_graph(
    list(semantic_law)::in,
    mode::in,
    io::di, io::uo,
    registry_result::out) is det.

reconcile_graph(Live, Mode, !IO, Result) :-
    (
        read_lines(graph_search_path, Lines0, !IO)
    ->
        filter_graph_lines(
            Lines0, Live, "outside", [], 0, StaleCount,
            [], StaleRev, Lines1, no, Found),
        list.reverse(StaleRev, Stale),
        (
            StaleCount > 0,
            Mode = prune
        ->
            write_file(graph_search_path, Lines1, !IO),
            Changed = yes
        ;
            Changed = no
        ),
        (
            Found = yes
        ->
            true
        ;
            io.write_string(
                "ERROR: graph registry blocks not found in theorem_graph_search.m\n",
                !IO),
            io.set_exit_status(1, !IO)
        ),
        Result = registry_result(Found, Changed, Stale)
    ;
        io.write_string(
            "ERROR: cannot read theorem_graph_search.m\n",
            !IO),
        io.set_exit_status(1, !IO),
        Result = registry_result(no, no, [])
    ).

:- pred print_stale(string::in, list(string)::in, io::di, io::uo) is det.
print_stale(_, [], !IO).
print_stale(Source, [Name | Names], !IO) :-
    io.write_string(
        "stale registry entry: " ++ Source ++ " :: " ++ Name ++ "\n",
        !IO),
    print_stale(Source, Names, !IO).

:- pred resolve_mode(list(string)::in, mode::out, io::di, io::uo) is det.
resolve_mode(Args, Mode, !IO) :-
    (
        Args = ["--check"]
    ->
        Mode = check
    ;
        Args = ["--prune"]
    ->
        Mode = prune
    ;
        io.write_string(
            "usage: theorem_registry_reconcile --check|--prune\n",
            !IO),
        io.set_exit_status(1, !IO),
        Mode = check
    ).

:- pred print_result(string::in, registry_result::in,
    io::di, io::uo) is det.
print_result(Name, Result, !IO) :-
    registry_result(_, Changed, Stale) = Result,
    io.write_string(
        Name ++ " changed=" ++
        (if Changed = yes then "true" else "false") ++
        " stale-count=" ++
        string.int_to_string(list.length(Stale)) ++ "\n",
        !IO),
    print_stale(Name, Stale, !IO).

main(!IO) :-
    io.set_exit_status(0, !IO),
    io.command_line_arguments(Args, !IO),
    resolve_mode(Args, Mode, !IO),
    read_semantic_laws(Live, !IO),
    reconcile_actions(Live, Mode, !IO, ActionsResult),
    reconcile_graph(Live, Mode, !IO, GraphResult),
    (
        Mode = prune
    ->
        read_semantic_laws(LiveAfter, !IO),
        reconcile_actions(LiveAfter, check, !IO, ActionsCheck),
        reconcile_graph(LiveAfter, check, !IO, GraphCheck),
        print_result("actions_ci.dhall", ActionsResult, !IO),
        print_result("theorem_graph_search.m", GraphResult, !IO),
        print_result("actions_ci.dhall[post-prune-check]", ActionsCheck, !IO),
        print_result("theorem_graph_search.m[post-prune-check]", GraphCheck, !IO),
        require_clean(ActionsCheck, GraphCheck, !IO)
    ;
        print_result("actions_ci.dhall", ActionsResult, !IO),
        print_result("theorem_graph_search.m", GraphResult, !IO),
        require_clean(ActionsResult, GraphResult, !IO)
    ).

:- pred require_clean(
    registry_result::in,
    registry_result::in,
    io::di, io::uo) is det.

require_clean(Actions, Graph, !IO) :-
    (
        list.length(registry_result.stale(Actions)) = 0,
        list.length(registry_result.stale(Graph)) = 0
    ->
        true
    ;
        io.write_string(
            "ERROR: stale machine-owned theorem registry metadata remains\n",
            !IO),
        io.set_exit_status(1, !IO)
    ).
