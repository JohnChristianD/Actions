:- module theorem_surface_sync.

:- interface.
:- import_module io.
:- pred main(io::di, io::uo) is det.

:- implementation.

:- import_module learner_semantic_extractor.
:- import_module list.
:- import_module string.

:- pred write_quoted_names(
    io.text_output_stream::in,
    list(semantic_law)::in,
    io::di, io::uo) is det.

write_quoted_names(_, [], !IO).
write_quoted_names(Stream, [Law | Laws], !IO) :-
    io.write_string(Stream, "    \"", !IO),
    io.write_string(Stream, law_name(Law), !IO),
    io.write_string(Stream, "\"", !IO),
    (
        Laws = []
    ->
        true
    ;
        io.write_string(Stream, ",", !IO)
    ),
    io.write_string(Stream, "\n", !IO),
    write_quoted_names(Stream, Laws, !IO).

:- pred write_report(
    list(semantic_law)::in,
    io::di, io::uo) is det.

write_report(Laws, !IO) :-
    io.open_output("theorem-surface.dhall", Result, !IO),
    (
        Result = ok(Stream),
        io.write_string(Stream, "{\n", !IO),
        io.write_string(
            Stream,
            "  sourceTheoremMonolith = \"../../../Exotic/ERL/FullCoupled/TheoremsMonolith.agda\",\n",
            !IO),
        io.write_string(Stream, "  proofAuthority = \"Agda --safe\",\n", !IO),
        io.write_string(Stream, "  semanticLawCount = ", !IO),
        io.write_string(Stream, string.int_to_string(list.length(Laws)), !IO),
        io.write_string(Stream, ",\n", !IO),
        io.write_string(Stream, "  semanticLawNames = [\n", !IO),
        write_quoted_names(Stream, Laws, !IO),
        io.write_string(Stream, "  ]\n", !IO),
        io.write_string(Stream, "}\n", !IO),
        io.close_output(Stream, !IO)
    ;
        Result = error(_),
        io.write_string(
            "ERROR: cannot write theorem surface contract\n",
            !IO),
        io.set_exit_status(1, !IO)
    ).

main(!IO) :-
    read_semantic_laws(Laws, !IO),
    (
        list.length(Laws) > 0
    ->
        write_report(Laws, !IO),
        io.write_string(
            "mercury-theorem-surface-sync=pass\n",
            !IO),
        io.write_string(
            "semantic-law-count=" ++
            string.int_to_string(list.length(Laws)) ++ "\n",
            !IO)
    ;
        io.write_string(
            "ERROR: canonical Agda theorem surface is empty\n",
            !IO),
        io.set_exit_status(1, !IO)
    ).
