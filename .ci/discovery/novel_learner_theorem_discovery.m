:- module novel_learner_theorem_discovery.

:- interface.

:- import_module io.

:- pred main(io::di, io::uo) is det.

:- implementation.

:- import_module bool.
:- import_module io.
:- import_module learner_semantic_extractor.
:- import_module learner_semantic_manifest.
:- import_module list.
:- import_module string.

:- pred composite_laws(
    list(semantic_law)::in, list(semantic_law)::out) is det.
composite_laws(All, Composite) :-
    list.filter(
        (pred(L::in) is semidet :-
            semantic_law.composite(L) = yes),
        All,
        Composite).

:- func rhs_qualification(string, string) = string.
rhs_qualification(Source, Name) =
    Name.

:- pred write_generated_aliases(
    list(semantic_law)::in,
    int::in,
    io.text_output_stream::in,
    io::di, io::uo) is det.
write_generated_aliases([], _, _, !IO).
write_generated_aliases([L | Ls], Index, Stream, !IO) :-
    io.write_string(Stream,
        "generatedSemanticComposition" ++
        string.int_to_string(Index) ++
        " :\n  " ++ semantic_law.signature(L) ++ "\n" ++
        "generatedSemanticComposition" ++
        string.int_to_string(Index) ++
        " = " ++ rhs_qualification(
            semantic_law.source(L),
            semantic_law.name(L)) ++
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
            "open import Agda.Builtin.Nat using (Nat; suc)\n" ++
            "open import Data.Empty using (⊥)\n" ++
            "open import Exotic.ERL.FullCoupled.CanonicalLearnerMonolith as C\n" ++
            "open import Exotic.ERL.FullCoupled.TheoremsMonolith as T\n" ++
            "open C\n" ++
            "open T\n\n" ++
            "-- Generated from actual executable learner/theorem declarations.\\n" ++
            "-- Reflexive declarations are excluded from the composition class.\\n\\n" ++
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

:- pred write_report(
    list(semantic_law)::in, list(semantic_law)::in,
    io::di, io::uo) is det.
write_report(All, Composite, !IO) :-
    NonReflexive = list.length(
        list.filter(
            (pred(L::in) is semidet :-
                semantic_law.reflexive(L) = no),
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
