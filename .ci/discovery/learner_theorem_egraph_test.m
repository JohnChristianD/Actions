:- module learner_theorem_egraph_test.

:- interface.

:- import_module io.

:- pred main(io::di, io::uo) is det.

:- implementation.

:- import_module learner_theorem_egraph.
:- import_module eqvclass.
:- import_module io.
:- import_module list.

main(!IO) :-
    Raw = raw_terms,
    E = discovery_egraph,
    quotient_terms(E, Raw, [], Quotient),
    RawCount = list.length(Raw),
    QuotientCount = list.length(Quotient),
    (
        RawCount = 8,
        QuotientCount = 4
    ->
        io.write_string(
            "theorem-egraph-regression=pass raw=8 quotient=4\n",
            !IO)
    ;
        io.write_string(
            "ERROR: theorem e-graph regression failed\n",
            !IO),
        io.set_exit_status(1, !IO)
    ).
