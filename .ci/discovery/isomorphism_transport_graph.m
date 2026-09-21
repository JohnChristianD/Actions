:- module isomorphism_transport_graph.

:- interface.
:- import_module io.
:- pred main(io::di, io::uo) is det.

:- implementation.
:- import_module learner_semantic_extractor.
:- import_module list.
:- import_module string.

:- type transport_kind
    ---> invariant_equality
    ;   invariant_impossibility.

:- pred contains(string::in, string::in) is semidet.
contains(Text, Needle) :-
    string.sub_string_search(Text, Needle, _).

:- pred conclusion_fragment(string::in, string::out) is det.
conclusion_fragment(Signature, Conclusion) :-
    Parts = string.split_at_string("→", Signature),
    (
        list.reverse(Parts, [Last | _])
    ->
        Conclusion = string.strip(Last)
    ;
        Conclusion = string.strip(Signature)
    ).

:- pred transport_kind_for(
    string::in, transport_kind::out) is semidet.
transport_kind_for(Conclusion, invariant_impossibility) :-
    contains(Conclusion, "≢").
transport_kind_for(Conclusion, invariant_equality) :-
    contains(Conclusion, "≡").

:- func kind_text(transport_kind) = string.
kind_text(invariant_equality) = "INVARIANT_EQUALITY".
kind_text(invariant_impossibility) = "INVARIANT_IMPOSSIBILITY".

:- pred transportable_law(semantic_law::in) is semidet.
transportable_law(Law) :-
    conclusion_fragment(law_signature(Law), Conclusion),
    transport_kind_for(Conclusion, _).

:- pred write_entries(
    io.text_output_stream::in,
    list(semantic_law)::in,
    io::di, io::uo) is det.
write_entries(_, [], !IO).
write_entries(Stream, [Law | Laws], !IO) :-
    conclusion_fragment(law_signature(Law), Conclusion),
    (
        transport_kind_for(Conclusion, Kind)
    ->
        io.write_string(Stream, "    {\"id\":\"", !IO),
        io.write_string(Stream, law_id(Law), !IO),
        io.write_string(Stream, "\",\"counterpart\":\"", !IO),
        io.write_string(Stream, kind_text(Kind), !IO),
        io.write_string(Stream,
            "\",\"transport_kernel\":\"Agda::isomorphism", !IO),
        (
            Kind = invariant_equality
        ->
            io.write_string(Stream, "EqualityTransport", !IO)
        ;
            io.write_string(Stream, "DisequalityTransport", !IO)
        ),
        io.write_string(Stream, "\"}", !IO),
        (
            Laws = []
        ->
            true
        ;
            io.write_string(Stream, ",", !IO)
        ),
        io.write_string(Stream, "\n", !IO)
    ;
        true
    ),
    write_entries(Stream, Laws, !IO).

:- pred count_transportable(
    list(semantic_law)::in, int::out) is det.
count_transportable([], 0).
count_transportable([Law | Laws], Count) :-
    count_transportable(Laws, Tail),
    conclusion_fragment(law_signature(Law), Conclusion),
    (
        transport_kind_for(Conclusion, _)
    ->
        Count = Tail + 1
    ;
        Count = Tail
    ).

main(!IO) :-
    read_semantic_laws(Laws, !IO),
    TransportableLaws = list.filter(transportable_law, Laws),
    count_transportable(Laws, Transportable),
    Direct = list.length(Laws) - Transportable,
    (
        Transportable > 0,
        list.length(Laws) > 0
    ->
        io.open_output(
            ".ci/discovery/isomorphism-transport-graph.json",
            Result,
            !IO),
        (
            Result = ok(Stream),
            io.write_string(Stream, "{\n", !IO),
            io.write_string(Stream,
                "  \"rule\": \"ISOMORPHISM_TRANSPORT_CLOSURE\",\n",
                !IO),
            io.write_string(Stream,
                "  \"orange_statuses_allowed\": false,\n", !IO),
            io.write_string(Stream,
                "  \"proof_authority\": \"Agda --safe\",\n", !IO),
            io.write_string(Stream,
                "  \"direct_theorem_status\": \"DIRECT_THEOREM\",\n",
                !IO),
            io.write_string(Stream,
                "  \"eligible_counterparts\": [\"INVARIANT_EQUALITY\",\"INVARIANT_IMPOSSIBILITY\"],\n",
                !IO),
            io.write_string(Stream,
                "  \"transport_kernel\": [\"Agda::isomorphismEqualityTransport\",\"Agda::isomorphismDisequalityTransport\",\"Agda::isomorphismIterateConjugacy\",\"Agda::isomorphismNoFiniteCycleTransport\"],\n",
                !IO),
            io.write_string(Stream,
                "  \"semantic_law_count\": ", !IO),
            io.write_string(Stream, string.int_to_string(list.length(Laws)), !IO),
            io.write_string(Stream, ",\n", !IO),
            io.write_string(Stream,
                "  \"transportable_law_count\": ", !IO),
            io.write_string(Stream, string.int_to_string(Transportable), !IO),
            io.write_string(Stream, ",\n", !IO),
            io.write_string(Stream,
                "  \"direct_law_count\": ", !IO),
            io.write_string(Stream, string.int_to_string(Direct), !IO),
            io.write_string(Stream, ",\n", !IO),
            io.write_string(Stream,
                "  \"collapse_semantics\": \"same theorem fact, quotienting representation by exact state isomorphism when an equality/disequality conclusion has the required transport shape\",\n",
                !IO),
            io.write_string(Stream,
                "  \"entries\": [\n", !IO),
            write_entries(Stream, TransportableLaws, !IO),
            io.write_string(Stream,
                "  ],\n", !IO),
            io.write_string(Stream,
                "  \"non_transportable_semantics\": \"DIRECT_THEOREM; no vague status\"\n",
                !IO),
            io.write_string(Stream, "}\n", !IO),
            io.close_output(Stream, !IO)
        ;
            io.write_string(
                "ERROR: cannot write isomorphism transport graph report\n",
                !IO),
            io.set_exit_status(1, !IO)
        ),
        io.write_string("isomorphism-transport-graph=pass\n", !IO),
        io.write_string("transportable-law-count=", !IO),
        io.write_string(string.int_to_string(Transportable), !IO),
        io.write_string("\n", !IO)
    ;
        io.write_string(
            "ERROR: isomorphism transport closure requires at least one exact equality/disequality theorem and a non-empty semantic law set\n",
            !IO),
        io.set_exit_status(1, !IO)
    ).
