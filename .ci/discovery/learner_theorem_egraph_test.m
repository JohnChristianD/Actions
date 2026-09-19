:- module learner_theorem_egraph_test.

:- interface.

:- import_module io.

:- pred main(io::di, io::uo) is det.

:- implementation.

:- import_module io.
:- import_module learner_theorem_egraph.
:- import_module list.

main(!IO) :-
    Raw = raw_terms,
    E = discovery_egraph,
    extract_minimal(E, Raw, Minimal),
    RawCount = list.length(Raw),
    MinimalCount = list.length(Minimal),
    (
        RawCount = 8,
        MinimalCount = 4
    ->
        io.write_string(
            "theorem-egraph-regression=pass raw=8 minimal=4 saturation=enabled\n",
            !IO)
    ;
        io.write_string(
            "ERROR: theorem e-graph regression failed\n",
            !IO),
        io.set_exit_status(1, !IO)
    ).
