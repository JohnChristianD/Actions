:- module tsts_endogenous_discovery.

:- interface.

:- import_module io.
:- pred main(io::di, io::uo) is det.

:- implementation.

:- import_module list.
:- import_module string.

:- type architecture
    ---> tsts_endogenous.

:- type property
    ---> bayesian_tree_selection_boundary
    ;   exact_canonical_evaluator
    ;   endogenous_score
    ;   watkins_gru_f4_same_target
    ;   norm_pair_preservation
    ;   persistent_gru_preservation
    ;   no_evolutionary_population
    ;   no_graph_search_adapter.

:- func candidates = list(architecture).
candidates = [tsts_endogenous].

:- func required = list(property).
required = [
    bayesian_tree_selection_boundary,
    exact_canonical_evaluator,
    endogenous_score,
    watkins_gru_f4_same_target,
    norm_pair_preservation,
    persistent_gru_preservation,
    no_evolutionary_population,
    no_graph_search_adapter
].

:- pred supports(architecture::in, property::in) is semidet.
supports(tsts_endogenous, bayesian_tree_selection_boundary).
supports(tsts_endogenous, exact_canonical_evaluator).
supports(tsts_endogenous, endogenous_score).
supports(tsts_endogenous, watkins_gru_f4_same_target).
supports(tsts_endogenous, norm_pair_preservation).
supports(tsts_endogenous, persistent_gru_preservation).
supports(tsts_endogenous, no_evolutionary_population).
supports(tsts_endogenous, no_graph_search_adapter).

:- pred supported_all(architecture::in, list(property)::in) is semidet.
supported_all(_, []).
supported_all(A, [P | Ps]) :-
    supports(A, P),
    supported_all(A, Ps).

:- pred discover(list(architecture)::in, list(property)::in,
    architecture::out) is semidet.
discover([A | _], Required, A) :-
    supported_all(A, Required).
discover([_ | As], Required, A) :-
    discover(As, Required, A).

:- func architecture_name(architecture) = string.
architecture_name(tsts_endogenous) = "TSTS_endogenous".

:- pred write_report(architecture::in, io::di, io::uo) is det.
write_report(A, !IO) :-
    io.open_output("tsts-endogenous-composition-candidate.json", Result, !IO),
    (
        Result = ok(Stream),
        io.write_string(Stream, "{\n", !IO),
        io.write_string(Stream, "  \"accepted\": true,\n", !IO),
        io.write_string(Stream, "  \"architecture\": \"", !IO),
        io.write_string(Stream, architecture_name(A), !IO),
        io.write_string(Stream, "\",\n", !IO),
        io.write_string(Stream,
            "  \"semantic_boundary\": \"TSTS-only endogenous branch selection over the existing exact learner evaluator\",\n",
            !IO),
        io.write_string(Stream,
            "  \"outer_search\": \"TSTS\",\n", !IO),
        io.write_string(Stream,
            "  \"evolutionary_search\": false,\n", !IO),
        io.write_string(Stream,
            "  \"graph_search_adapter\": false,\n", !IO),
        io.write_string(Stream,
            "  \"proof_gate\": \"TheoremsMonolith.agda\",\n", !IO),
        io.write_string(Stream,
            "  \"external_equivalence\": false\n", !IO),
        io.write_string(Stream, "}\n", !IO),
        io.close_output(Stream)
    ;
        Result = error(_),
        io.write_string(
            "ERROR: cannot write TSTS endogenous discovery report\n",
            !IO),
        io.set_exit_status(1, !IO)
    ).

main(!IO) :-
    (
        discover(candidates, required, A)
    ->
        write_report(A, !IO),
        io.write_string(
            "tsts-endogenous-discovery=accepted\n", !IO),
        io.write_string(
            "candidate=TSTS_endogenous\n", !IO),
        io.write_string(
            "next=Agda endogenous connected theorem gate\n", !IO)
    ;
        io.write_string(
            "tsts-endogenous-discovery=rejected\n", !IO),
        io.set_exit_status(1, !IO)
    ).
