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

:- type signature_kind
    ---> existence_signature
    ;   impossibility_signature
    ;   equality_signature
    ;   equivalence_signature
    ;   order_signature
    ;   inclusion_signature
    ;   stationarity_signature
    ;   uniqueness_signature
    ;   convergence_signature
    ;   injectivity_signature
    ;   noninjectivity_signature
    ;   fixed_point_signature
    ;   decision_signature
    ;   subsingleton_signature
    ;   other_signature.

:- type strict_target
    ---> strict_target(
        law :: semantic_law,
        classification :: strict_class,
        kind :: signature_kind,
        evidence :: string
    ).

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

:- pred classify_existence(string::in, string::out) is semidet.
classify_existence(Conclusion, Evidence) :-
    (
        contains(Conclusion, "Nonempty"),
        Evidence = "conclusion:Nonempty"
    ;
        contains(Conclusion, "Exists"),
        Evidence = "conclusion:Exists"
    ;
        contains(Conclusion, "∃"),
        Evidence = "conclusion:∃"
    ;
        contains(Conclusion, "Σ"),
        Evidence = "conclusion:Σ"
    ).

:- pred classify_impossibility(string::in, string::out) is semidet.
classify_impossibility(Conclusion, Evidence) :-
    (
        contains(Conclusion, "⊥"),
        Evidence = "conclusion:⊥"
    ;
        contains(Conclusion, "¬"),
        Evidence = "conclusion:¬"
    ;
        contains(Conclusion, "≢"),
        Evidence = "conclusion:≢"
    ).

:- pred signature_kind_for(string::in, signature_kind::out) is det.
signature_kind_for(Conclusion, Kind) :-
    (
        classify_existence(Conclusion, _)
    ->
        Kind = existence_signature
    ;
        classify_impossibility(Conclusion, _)
    ->
        Kind = impossibility_signature
    ;
        contains(Conclusion, "≡")
    ->
        Kind = equality_signature
    ;
        contains(Conclusion, "↔")
    ->
        Kind = equivalence_signature
    ;
        contains(Conclusion, "⊆"),
        Kind = inclusion_signature
    ;
        contains(Conclusion, "⊂"),
        Kind = inclusion_signature
    ;
        contains(Conclusion, "⊇"),
        Kind = inclusion_signature
    ;
        contains(Conclusion, "⊃"),
        Kind = inclusion_signature
    ;
        contains(Conclusion, "IsStationary"),
        Kind = stationarity_signature
    ;
        contains(Conclusion, "Stationary"),
        Kind = stationarity_signature
    ;
        contains(Conclusion, "Unique"),
        Kind = uniqueness_signature
    ;
        contains(Conclusion, "unique"),
        Kind = uniqueness_signature
    ;
        contains(Conclusion, "Converges"),
        Kind = convergence_signature
    ;
        contains(Conclusion, "convergence"),
        Kind = convergence_signature
    ;
        contains(Conclusion, "geometric"),
        Kind = convergence_signature
    ;
        contains(Conclusion, "Injective"),
        Kind = injectivity_signature
    ;
        contains(Conclusion, "injective"),
        Kind = injectivity_signature
    ;
        contains(Conclusion, "NotInjective"),
        Kind = noninjectivity_signature
    ;
        contains(Conclusion, "non-injective"),
        Kind = noninjectivity_signature
    ;
        contains(Conclusion, "FixedPoint"),
        Kind = fixed_point_signature
    ;
        contains(Conclusion, "fixedPoint"),
        Kind = fixed_point_signature
    ;
        contains(Conclusion, "Decidable"),
        Kind = decision_signature
    ;
        contains(Conclusion, "Subsingleton"),
        Kind = subsingleton_signature
    ;
        contains(Conclusion, "≤"),
        Kind = order_signature
    ;
        contains(Conclusion, "≥"),
        Kind = order_signature
    ;
        Kind = other_signature
    ).

:- pred classify(semantic_law::in, strict_class::out,
    signature_kind::out, string::out) is semidet.
classify(Law, Class, Kind, Evidence) :-
    conclusion_fragment(law_signature(Law), Conclusion),
    Kind = signature_kind_for(Conclusion),
    (
        classify_existence(Conclusion, ExistenceEvidence),
        not classify_impossibility(Conclusion, _)
    ->
        Class = existence,
        Evidence = ExistenceEvidence
    ;
        classify_impossibility(Conclusion, ImpossibilityEvidence),
        not classify_existence(Conclusion, _)
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
        classify(Law, Class, Kind, Evidence)
    ->
        Targets = [strict_target(Law, Class, Kind, Evidence) | Tail]
    ;
        Targets = Tail
    ).

:- func kind_text(signature_kind) = string.
kind_text(existence_signature) = "EXISTENCE".
kind_text(impossibility_signature) = "IMPOSSIBILITY".
kind_text(equality_signature) = "EQUALITY".
kind_text(equivalence_signature) = "EQUIVALENCE".
kind_text(order_signature) = "ORDER".
kind_text(inclusion_signature) = "INCLUSION".
kind_text(stationarity_signature) = "STATIONARITY".
kind_text(uniqueness_signature) = "UNIQUENESS".
kind_text(convergence_signature) = "CONVERGENCE".
kind_text(injectivity_signature) = "INJECTIVITY".
kind_text(noninjectivity_signature) = "NONINJECTIVITY".
kind_text(fixed_point_signature) = "FIXED_POINT".
kind_text(decision_signature) = "DECISION".
kind_text(subsingleton_signature) = "SUBSINGLETON".
kind_text(other_signature) = "OTHER".

:- func class_text(strict_class) = string.
class_text(existence) = "EXISTENCE".
class_text(impossibility) = "IMPOSSIBILITY".

:- pred write_targets(io.text_output_stream::in,
    list(strict_target)::in, io::di, io::uo) is det.
write_targets(_, [], !IO).
write_targets(Stream, [Target | Targets], !IO) :-
    Target = strict_target(Law, Class, Kind, Evidence),
    io.write_string(Stream, "    {\"id\":\"", !IO),
    io.write_string(Stream, law_id(Law), !IO),
    io.write_string(Stream, "\",\"classification\":\"", !IO),
    io.write_string(Stream, class_text(Class), !IO),
    io.write_string(Stream, "\",\"signature_kind\":\"", !IO),
    io.write_string(Stream, kind_text(Kind), !IO),
    io.write_string(Stream, "\",\"evidence\":\"", !IO),
    io.write_string(Stream, Evidence, !IO),
    io.write_string(Stream, "\"}", !IO),
    (
        Targets = []
    ->
        true
    ;
        io.write_string(Stream, ",", !IO)
    ),
    io.write_string(Stream, "\n", !IO),
    write_targets(Stream, Targets, !IO).

:- pred strict_target_laws(list(strict_target)::in,
    list(semantic_law)::out) is det.
strict_target_laws([], []).
strict_target_laws(
    [strict_target(Law, _, _, _) | Targets], [Law | Laws]) :-
    strict_target_laws(Targets, Laws).

:- pred all_plans_begin_with_strict_target(
    list(list(string))::in, list(strict_target)::in) is semidet.
all_plans_begin_with_strict_target([], _).
all_plans_begin_with_strict_target([Plan | Plans], Targets) :-
    Plan = [Head | _],
    list.member(strict_target(Law, _, _, _), Targets),
    law_id(Law) = Head,
    all_plans_begin_with_strict_target(Plans, Targets).

:- pred has_vague_status_text(list(strict_target)::in) is semidet.
has_vague_status_text(Targets) :-
    list.member(Target, Targets),
    Target = strict_target(Law, _, _, _),
    Name = law_name(Law),
    (
        contains(Name, "frontier")
    ;
        contains(Name, "unknown")
    ;
        contains(Name, "adapter")
    ;
        contains(Name, "vague")
    ).

:- pred write_inventory(io.text_output_stream::in,
    list(semantic_law)::in, io::di, io::uo) is det.
write_inventory(_, [], !IO).
write_inventory(Stream, [Law | Laws], !IO) :-
    conclusion_fragment(law_signature(Law), Conclusion),
    Kind = signature_kind_for(Conclusion),
    io.write_string(Stream, "    {\"id\":\"", !IO),
    io.write_string(Stream, law_id(Law), !IO),
    io.write_string(Stream, "\",\"kind\":\"", !IO),
    io.write_string(Stream, kind_text(Kind), !IO),
    io.write_string(Stream, "\"}", !IO),
    (
        Laws = []
    ->
        true
    ;
        io.write_string(Stream, ",", !IO)
    ),
    io.write_string(Stream, "\n", !IO),
    write_inventory(Stream, Laws, !IO).

main(!IO) :-
    read_semantic_laws(Laws, !IO),
    classify_targets(Laws, Targets),
    strict_target_laws(Targets, StrictLaws),
    StrictIds = list.map(
        (func(Law) = law_id(Law)),
        StrictLaws),
    search_emergent_compositions_from_seed_ids(
        Laws, StrictIds, Plans),
    (
        list.length(Targets) > 0,
        list.length(Plans) > 0,
        all_plans_begin_with_strict_target(Plans, Targets),
        not has_vague_status_text(Targets)
    ->
        io.open_output(
            "strict-existence-impossibility-graph.json",
            Result,
            !IO),
        (
            Result = ok(Stream),
            io.write_string(Stream, "{\n", !IO),
            io.write_string(Stream,
                "  \"rule\": \"STRICT_EXISTENCE_OR_IMPOSSIBILITY_ONLY\",\n",
                !IO),
            io.write_string(Stream,
                "  \"orange_statuses_allowed\": false,\n", !IO),
            io.write_string(Stream, "  \"strict_target_count\": ", !IO),
            io.write_string(Stream,
                string.int_to_string(list.length(Targets)), !IO),
            io.write_string(Stream, ",\n", !IO),
            io.write_string(Stream, "  \"strict_plan_count\": ", !IO),
            io.write_string(Stream,
                string.int_to_string(list.length(Plans)), !IO),
            io.write_string(Stream, ",\n", !IO),
            io.write_string(Stream,
                "  \"signature_kinds\": [\"EXISTENCE\",\"IMPOSSIBILITY\",\"EQUALITY\",\"EQUIVALENCE\",\"ORDER\",\"INCLUSION\",\"STATIONARITY\",\"UNIQUENESS\",\"CONVERGENCE\",\"INJECTIVITY\",\"NONINJECTIVITY\",\"FIXED_POINT\",\"DECISION\",\"SUBSINGLETON\",\"OTHER\"],\n",
                !IO),
            io.write_string(Stream,
                "  \"targets\": [\n", !IO),
            write_targets(Stream, Targets, !IO),
            io.write_string(Stream,
                "  ],\n  \"graph_search\": \"A* cost-guided dependency paths over strict targets\",\n",
                !IO),
            io.write_string(Stream,
                "  \"terminal_statuses\": [\"EXISTENCE\",\"IMPOSSIBILITY\"]\n",
                !IO),
            io.write_string(Stream, "}\n", !IO),
            io.close_output(Stream, !IO)
        ;
            io.write_string(
                "ERROR: cannot write strict existence/impossibility graph report\n",
                !IO),
            io.set_exit_status(1, !IO)
        ),
        io.open_output(
            "signature-inventory.json",
            InventoryResult,
            !IO),
        (
            InventoryResult = ok(InventoryStream),
            io.write_string(InventoryStream, "{\n", !IO),
            io.write_string(InventoryStream,
                "  \"signature_inventory_rule\": \"EXACT_CONCLUSION_SHAPE\",\n",
                !IO),
            io.write_string(InventoryStream,
                "  \"signatures\": [\n", !IO),
            write_inventory(InventoryStream, Laws, !IO),
            io.write_string(InventoryStream, "  ]\n}\n", !IO),
            io.close_output(InventoryStream, !IO)
        ;
            io.write_string(
                "ERROR: cannot write signature inventory\n", !IO),
            io.set_exit_status(1, !IO)
        ),
        io.write_string("strict-existence-impossibility-graph=pass\n", !IO),
        io.write_string("strict-target-count=", !IO),
        io.write_string(string.int_to_string(list.length(Targets)), !IO),
        io.write_string("\n")
    ;
        io.write_string(
            "ERROR: strict graph requires explicit EXISTENCE/IMPOSSIBILITY conclusions and a valid A* plan; no vague status is admissible\n",
            !IO),
        io.set_exit_status(1, !IO)
    ).
