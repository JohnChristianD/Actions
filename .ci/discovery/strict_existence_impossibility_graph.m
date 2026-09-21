:- module strict_existence_impossibility_graph.

:- interface.
:- import_module io.
:- pred main(io::di, io::uo) is det.

:- implementation.
:- import_module learner_semantic_extractor.
:- import_module theorem_graph_search.
:- import_module list.
:- import_module string.

:- type strict_class
    ---> existence
    ;   impossibility.

:- type strict_target
    ---> strict_target(
        law :: semantic_law,
        classification :: strict_class,
        evidence :: string
    ).

:- pred contains(string::in, string::in) is semidet.
contains(Text, Needle) :-
    string.sub_string_search(Text, Needle, _).

:- pred classify_existence(semantic_law::in, string::out) is semidet.
classify_existence(Law, Evidence) :-
    Signature = law_signature(Law),
    (
        contains(Signature, "Nonempty"),
        Evidence = "signature:Nonempty"
    ;
        contains(Signature, "Exists"),
        Evidence = "signature:Exists"
    ;
        contains(Signature, "∃"),
        Evidence = "signature:∃"
    ).

:- pred classify_impossibility(semantic_law::in, string::out) is semidet.
classify_impossibility(Law, Evidence) :-
    Signature = law_signature(Law),
    (
        contains(Signature, "⊥"),
        Evidence = "signature:⊥"
    ;
        contains(Signature, "¬"),
        Evidence = "signature:¬"
    ).

:- pred classify(semantic_law::in, strict_class::out, string::out) is semidet.
classify(Law, Class, Evidence) :-
    (
        classify_existence(Law, ExistenceEvidence),
        not classify_impossibility(Law, _)
    ->
        Class = existence,
        Evidence = ExistenceEvidence
    ;
        classify_impossibility(Law, ImpossibilityEvidence),
        not classify_existence(Law, _)
    ->
        Class = impossibility,
        Evidence = ImpossibilityEvidence
    ).

:- pred classify_targets(list(semantic_law)::in,
    list(strict_target)::out) is det.
classify_targets([], []).
classify_targets([Law | Laws], Targets) :-
    classify_targets(Laws, Tail),
    (
        classify(Law, Class, Evidence)
    ->
        Targets = [strict_target(Law, Class, Evidence) | Tail]
    ;
        Targets = Tail
    ).

:- func class_text(strict_class) = string.
class_text(existence) = "EXISTENCE".
class_text(impossibility) = "IMPOSSIBILITY".

:- pred write_targets(
    io.text_output_stream::in,
    list(strict_target)::in,
    io::di, io::uo) is det.
write_targets(_, [], !IO).
write_targets(Stream, [Target | Targets], !IO) :-
    Target = strict_target(Law, Class, Evidence),
    io.write_string(Stream, "    {"id":"", !IO),
    io.write_string(Stream, law_id(Law), !IO),
    io.write_string(Stream, "","classification":"", !IO),
    io.write_string(Stream, class_text(Class), !IO),
    io.write_string(Stream, "","evidence":"", !IO),
    io.write_string(Stream, Evidence, !IO),
    io.write_string(Stream, ""}", !IO),
    (
        Targets = []
    ->
        true
    ;
        io.write_string(Stream, ",", !IO)
    ),
    io.write_string(Stream, "\n", !IO),
    write_targets(Stream, Targets, !IO).

:- pred strict_plans(
    list(semantic_law)::in,
    list(list(string))::out) is det.
strict_plans(Laws, Plans) :-
    classify_targets(Laws, Targets),
    strict_target_laws(Targets, StrictLaws),
    StrictIds = list.map(
        (func(Law) = law_id(Law)),
        StrictLaws),
    search_emergent_compositions_from_seed_ids(
        Laws,
        StrictIds,
        Plans).

:- pred strict_target_laws(
    list(strict_target)::in,
    list(semantic_law)::out) is det.
strict_target_laws([], []).
strict_target_laws([strict_target(Law, _, _) | Targets], [Law | Laws]) :-
    strict_target_laws(Targets, Laws).

:- pred all_plans_begin_with_strict_target(
    list(list(string))::in,
    list(strict_target)::in) is semidet.
all_plans_begin_with_strict_target([], _).
all_plans_begin_with_strict_target([Plan | Plans], Targets) :-
    Plan = [Head | _],
    list.member(strict_target(Law, _, _), Targets),
    law_id(Law) = Head,
    all_plans_begin_with_strict_target(Plans, Targets).

:- pred has_vague_status_text(list(strict_target)::in) is semidet.
has_vague_status_text(Targets) :-
    list.member(Target, Targets),
    Target = strict_target(Law, _, _),
    Name = law_name(Law),
    (
        contains(Name, "frontier")
    ;
        contains(Name, "unknown")
    ;
        contains(Name, "adapter")
    ).

main(!IO) :-
    read_semantic_laws(Laws, !IO),
    classify_targets(Laws, Targets),
    strict_target_laws(Targets, StrictLaws),
    StrictIds = list.map(
        (func(Law) = law_id(Law)),
        StrictLaws),
    search_emergent_compositions_from_seed_ids(
        Laws,
        StrictIds,
        Plans),
    (
        list.length(Targets) > 0,
        list.length(Plans) > 0,
        all_plans_begin_with_strict_target(Plans, Targets),
        not has_vague_status_text(Targets)
    ->
        io.open_output(".ci/discovery/strict-existence-impossibility-graph.json", Result, !IO),
        (
            Result = ok(Stream),
            io.write_string(Stream, "{\n", !IO),
            io.write_string(Stream,
                "  \"rule\": \"STRICT_EXISTENCE_OR_IMPOSSIBILITY_ONLY\",\n", !IO),
            io.write_string(Stream,
                "  \"orange_statuses_allowed\": false,\n", !IO),
            io.write_string(Stream, "  \"strict_target_count\": ", !IO),
            io.write_string(Stream, string.int_to_string(list.length(Targets)), !IO),
            io.write_string(Stream, ",\n", !IO),
            io.write_string(Stream, "  \"strict_plan_count\": ", !IO),
            io.write_string(Stream, string.int_to_string(list.length(Plans)), !IO),
            io.write_string(Stream, ",\n", !IO),
            io.write_string(Stream, "  \"targets\": [\n", !IO),
            write_targets(Stream, Targets, !IO),
            io.write_string(Stream, "  ],\n", !IO),
            io.write_string(Stream, "  \"graph_search\": \"A* cost-guided dependency paths over strict targets\",\n", !IO),
            io.write_string(Stream, "  \"terminal_statuses\": [\"EXISTENCE\",\"IMPOSSIBILITY\"]\n", !IO),
            io.write_string(Stream, "}\n", !IO),
            io.close_output(Stream, !IO),
            io.write_string("strict-existence-impossibility-graph=pass\n", !IO),
            io.write_string("strict-target-count=", !IO),
            io.write_string(string.int_to_string(list.length(Targets)), !IO),
            io.write_string("\nstrict-plan-count=", !IO),
            io.write_string(string.int_to_string(list.length(Plans)), !IO),
            io.write_string("\n")
        ;
            io.write_string(
                "ERROR: cannot write strict existence/impossibility graph report\n",
                !IO),
            io.set_exit_status(1, !IO)
        )
    ;
        io.write_string(
            "ERROR: strict graph requires at least one explicit EXISTENCE/IMPOSSIBILITY target and a valid A* plan; no vague status is admissible\n",
            !IO),
        io.set_exit_status(1, !IO)
    ).
