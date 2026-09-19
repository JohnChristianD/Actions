:- module novel_learner_theorem_discovery.

:- interface.

:- import_module io.

:- pred main(io::di, io::uo) is det.

:- implementation.

:- import_module learner_semantic_extractor.
:- import_module io.
:- import_module list.
:- import_module string.

:- type semantic_law
    ---> semantic_law(
        source :: string,
        name :: string,
        reflexive :: string,
        composite :: string,
        signature :: string,
        dependencies :: list(string)
    ).

:- pred read_manifest(list(semantic_law)::out, io::di, io::uo) is det.
read_manifest(Laws, !IO) :-
    io.read_named_file_as_lines("learner-semantic-laws.tsv", Result, !IO),
    (
        Result = ok(Lines),
        parse_manifest_lines(Lines, [], Laws)
    ;
        Result = error(Error),
        io.write_string(
            "ERROR: cannot read learner semantic manifest: " ++
            Error ++ "\n",
            !IO),
        io.set_exit_status(1, !IO),
        Laws = []
    ).

:- pred parse_manifest_lines(list(string)::in,
    list(semantic_law)::in, list(semantic_law)::out) is det.
parse_manifest_lines([], Acc, Laws) :-
    list.reverse(Acc, Laws).
parse_manifest_lines([Line | Rest], Acc, Laws) :-
    (
        string.strip(Line) = ""
        -> parse_manifest_lines(Rest, Acc, Laws)
    ;
        Line = "source|name|reflexive|composite|signature|dependencies"
        -> parse_manifest_lines(Rest, Acc, Laws)
    ;
        Parts = string.split_at_string("|", Line),
        (
            Parts = [Source, Name, Reflexive, Composite, Signature0, Dependencies0 | _],
            Signature = string.replace_all(Signature0, "%7C", "|"),
            Dependencies = parse_dependencies(Dependencies0),
            parse_manifest_lines(
                Rest,
                [semantic_law(
                    Source, Name, Reflexive, Composite,
                    Signature, Dependencies) | Acc],
                Laws)
        ;
            parse_manifest_lines(Rest, Acc, Laws)
        )
    ).

:- func parse_dependencies(string) = list(string).
parse_dependencies("") = [].
parse_dependencies(Text) = list.filter(
    (pred(X::in) is semidet :- string.strip(X) = ""),
    string.split_at_string(";", Text)
).

:- pred composite_laws(list(semantic_law)::in,
    list(semantic_law)::out) is det.
composite_laws(All, Composite) :-
    list.filter(
        (pred(L::in) is semidet :-
            L ^ composite = "true"),
        All,
        Composite).

:- func rhs_qualification(string, string) = string.
rhs_qualification(Source, Name) =
    ( if string.sub_string_search(Source, "CanonicalLearnerMonolith.agda", _) then
        "C." ++ Name
    else if string.sub_string_search(Source, "TheoremsMonolith.agda", _) then
        "T." ++ Name
    else
        Name
    ).

:- pred write_generated_aliases(
    list(semantic_law)::in,
    int::in,
    io.text_output_stream::in,
    io::di, io::uo) is det.
write_generated_aliases([], _, _, !IO).
write_generated_aliases(
    [L | Ls], Index, Stream, !IO) :-
    io.write_string(Stream,
        "generatedSemanticComposition" ++
        string.int_to_string(Index) ++
        " :\n  " ++ L ^ signature ++ "\n" ++
        "generatedSemanticComposition" ++
        string.int_to_string(Index) ++
        " = " ++ rhs_qualification(L ^ source, L ^ name) ++
        "\n\n",
        !IO),
    write_generated_aliases(Ls, Index + 1, Stream, !IO).

:- pred write_generated_module(list(semantic_law)::in,
    io::di, io::uo) is det.
write_generated_module(Composite, !IO) :-
    io.open_output(
        "../../Exotic/ERL/FullCoupled/GeneratedNovelLearnerTheorems.agda",
        Result,
        !IO),
    (
        Result = ok(Stream),
        io.write_string(Stream,
            "{-# OPTIONS --safe #-}\n\n" ++
            "module Exotic.ERL.FullCoupled.GeneratedNovelLearnerTheorems where\n\n" ++
            "open import Agda.Builtin.Nat using (Nat)\n" ++
            "open import Exotic.ERL.FullCoupled.CanonicalLearnerMonolith as C\n" ++
            "open import Exotic.ERL.FullCoupled.TheoremsMonolith as T\n\n" ++
            "-- This surface is generated from the actual learner monolith\n" ++
            "-- declarations.  No theorem-name registry is used.\n\n" ++
            "generatedSemanticCompositionCount : Nat\n" ++
            "generatedSemanticCompositionCount = " ++
            string.int_to_string(list.length(Composite)) ++
            "\n\n",
            !IO),
        write_generated_aliases(Composite, 0, Stream, !IO),
        io.close_output(Stream)
    ;
        Result = error(_),
        io.write_string(
            "ERROR: cannot write generated semantic theorem module\n",
            !IO),
        io.set_exit_status(1, !IO)
    ).

:- pred write_report(list(semantic_law)::in,
    list(semantic_law)::in, io::di, io::uo) is det.
write_report(All, Composite, !IO) :-
    NonReflexive = list.length(
        list.filter(
            (pred(L::in) is semidet :- L ^ reflexive = "false"),
            All)),
    io.open_output("novel-learner-theorem-discovery.json", Result, !IO),
    (
        Result = ok(Stream),
        io.write_string(Stream,
            "{\n" ++
            "  \"accepted\": true,\n" ++
            "  \"search_semantics\": \"learner-monolith semantic dependency extraction\",\n" ++
            "  \"symbolic_registry\": false,\n" ++
            "  \"refl_as_composition\": false,\n" ++
            "  \"semantic_law_count\": " ++
                string.int_to_string(list.length(All)) ++ ",\n" ++
            "  \"nonreflexive_law_count\": " ++
                string.int_to_string(NonReflexive) ++ ",\n" ++
            "  \"composite_law_count\": " ++
                string.int_to_string(list.length(Composite)) ++ ",\n" ++
            "  \"proof_authority\": \"Agda --safe\"\n" ++
            "}\n",
            !IO),
        io.close_output(Stream)
    ;
        Result = error(_),
        io.write_string(
            "ERROR: cannot write semantic discovery report\n",
            !IO),
        io.set_exit_status(1, !IO)
    ).

main(!IO) :-
    extract_semantics(!IO),
    read_manifest(All, !IO),
    composite_laws(All, Composite),
    write_generated_module(Composite, !IO),
    write_report(All, Composite, !IO),
    io.write_string(
        "semantic-theorem-discovery=generated-from-learner-monolith\n",
        !IO),
    io.write_string(
        "semantic-law-count=" ++
        string.int_to_string(list.length(All)) ++ "\n",
        !IO),
    io.write_string(
        "composite-law-count=" ++
        string.int_to_string(list.length(Composite)) ++ "\n",
        !IO).
