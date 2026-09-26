:- module learner_semantic_extractor.

:- interface.

:- import_module bool.
:- import_module io.
:- import_module list.

:- type semantic_law
    ---> semantic_law(
        source :: string,
        name :: string,
        reflexive :: bool,
        composite :: bool,
        signature :: string,
        dependencies :: list(string)
    ).

:- pred extract_semantics(io::di, io::uo) is det.
:- pred read_semantic_laws(list(semantic_law)::out, io::di, io::uo) is det.
:- func law_id(semantic_law) = string.
:- func law_source(semantic_law) = string.
:- func law_name(semantic_law) = string.
:- func law_signature(semantic_law) = string.
:- func law_dependencies(semantic_law) = list(string).
:- pred is_reflexive(semantic_law::in) is semidet.
:- pred is_composite(semantic_law::in) is semidet.

:- implementation.

 :- import_module char.
:- import_module int.
:- import_module string.

:- type semantic_decl
    ---> semantic_decl(
        source_file :: string,
        name :: string,
        signature :: string,
        body :: string
    ).

:- type scan_state
    ---> idle
    ;   signature_state(
            string,
            list(string)
        )
    ;   body_state(
            string,
            list(string),
            list(string)
        ).

:- func concat_strings(list(string)) = string.
concat_strings(Parts) = string.join_list("", Parts).

:- func source_files = list(string).
source_files = [
    "../../Exotic/ERL/FullCoupled/TheoremsMonolith.agda",
    "../../Exotic/ERL/FullCoupled/GRUFractalLimitConvergenceAdapter.agda",
    "../../Exotic/ERL/FullCoupled/GRUFractalLimitClosure.agda",
    "../../Exotic/ERL/FullCoupled/GRUFractalLimitDecoderSurvival.agda",
    "../../Exotic/ERL/FullCoupled/GRUFractalEGraphAStarLimitComposition.agda"
].

:- func syntax_heads = list(string).
syntax_heads = [
    "module", "open", "import", "data", "record", "field", "constructor",
    "private", "mutual", "variable", "infix", "infixl", "infixr", "postulate",
    "instance", "macro"
].

:- pred first_word(string::in, string::out) is semidet.
first_word(Line, Word) :-
    Words = string.words(string.strip(Line)),
    Words = [Word | _].

:- pred top_level_line(string::in) is semidet.
top_level_line(Line) :-
    ( if string.first_char(Line, C, _) then
        not char.is_whitespace(C)
    else
        fail
    ).

:- pred syntax_head(string::in) is semidet.
syntax_head(Word) :-
    list.member(Word, syntax_heads).

:- pred top_level_header(string::in, string::out, string::out) is semidet.
top_level_header(Line, Name, SignatureFragment) :-
    top_level_line(Line),
    first_word(Line, Name),
    not syntax_head(Name),
    Name \= "--",
    string.sub_string_search(Line, ":", _),
    Parts = string.split_at_string(":", Line),
    Parts = [_, After | _],
    SignatureFragment = string.strip(After).

:- pred top_level_record_header(
    string::in, string::out, string::out) is semidet.
top_level_record_header(Line, Name, SignatureFragment) :-
    top_level_line(Line),
    first_word(Line, "record"),
    Words = string.words(string.strip(Line)),
    Words = ["record", Name | _],
    string.sub_string_search(Line, ":", _),
    Parts = string.split_at_string(":", Line),
    Parts = [_, After | _],
    SignatureFragment = string.strip(After).

:- pred top_level_declaration_header(
    string::in, string::out) is semidet.
top_level_declaration_header(Line, Name) :-
    top_level_line(Line),
    first_word(Line, Name),
    Name \= "--",
    string.sub_string_search(Line, ":", _).

:- pred body_clause(string::in, string::in, string::out) is semidet.
body_clause(Name, Line, Body) :-
    top_level_line(Line),
    first_word(Line, LineName),
    LineName = Name,
    string.sub_string_search(Line, "=", _),
    Parts = string.split_at_string("=", Line),
    Parts = [_, Rhs | Rest],
    Body = string.strip(
        string.join_list("=", [Rhs | Rest])).

:- pred semantic_reflexive(semantic_decl::in) is semidet.
semantic_reflexive(semantic_decl(_, _, _, Body)) :-
    string.strip(Body) = "refl".

:- pred identifier_char(char::in) is semidet.
identifier_char(C) :-
    char.is_alpha(C)
    ;
    char.is_digit(C)
    ;
    C = '_'
    ;
    char.to_int(C) = 45.

:- pred occurrence_boundary(string::in, string::in, int::in) is semidet.
occurrence_boundary(Text, Name, Position) :-
    Length = string.length(Name),
    End = Position + Length,
    (
        Position = 0
    ;
        Position > 0,
        string.index(Text, Position - 1, Before),
        not identifier_char(Before)
    ),
    (
        End >= string.length(Text)
    ;
        End < string.length(Text),
        string.index(Text, End, After),
        not identifier_char(After)
    ).

:- pred contains_identifier(string::in, string::in) is semidet.
contains_identifier(Text, Name) :-
    string.sub_string_search(Text, Name, Position),
    occurrence_boundary(Text, Name, Position).

:- pred semantic_signature(semantic_decl::in) is semidet.
semantic_signature(semantic_decl(_, Name, Signature, _)) :-
    Name \= "",
    Signature \= "".

:- pred parse_lines(string::in, list(string)::in,
    list(semantic_decl)::out) is det.
parse_lines(Source, Lines, Decls) :-
    scan_lines(Source, Lines, idle, [], Rev),
    list.reverse(Rev, Decls).

:- pred scan_lines(string::in, list(string)::in, scan_state::in,
    list(semantic_decl)::in, list(semantic_decl)::out) is det.
scan_lines(Source, [], State, Acc, Out) :-
    finalize_state(Source, State, Acc, Out).
scan_lines(Source, [Line | Rest], State0, Acc0, Out) :-
    (
        State0 = idle,
        (
            if top_level_record_header(Line, RecordName, RecordFragment)
            then
                scan_lines(Source, Rest,
                    signature_state(RecordName, [RecordFragment]), Acc0, Out)
            else if top_level_header(Line, Name, Fragment)
            then
                scan_lines(Source, Rest,
                    signature_state(Name, [Fragment]), Acc0, Out)
            else
                scan_lines(Source, Rest, idle, Acc0, Out)
        )
    ;
        State0 = signature_state(Name, SigRev),
        (
            if body_clause(Name, Line, Body)
            then
                scan_lines(Source, Rest,
                    body_state(Name, SigRev, [Body]), Acc0, Out)
            else if top_level_declaration_header(Line, NextName),
                    NextName \= Name
            then
                finalize_state(Source, State0, Acc0, Acc1),
                scan_lines(Source, [Line | Rest], idle, Acc1, Out)
            else
                scan_lines(Source, Rest,
                    signature_state(Name, [string.strip(Line) | SigRev]),
                    Acc0, Out)
        )
    ;
        State0 = body_state(Name, SigRev, BodyRev),
        (
            if top_level_declaration_header(Line, NextName),
               NextName \= Name
            then
                finalize_state(Source, State0, Acc0, Acc1),
                scan_lines(Source, [Line | Rest], idle, Acc1, Out)
            else
                scan_lines(Source, Rest,
                    body_state(Name, SigRev, [string.strip(Line) | BodyRev]),
                    Acc0, Out)
        )
    ).

:- pred finalize_state(string::in, scan_state::in,
    list(semantic_decl)::in, list(semantic_decl)::out) is det.
finalize_state(_, idle, Acc, Acc).
finalize_state(Source, signature_state(Name, SigRev), Acc, Out) :-
    Signature = string.join_list(" ", list.reverse(SigRev)),
    Out = [semantic_decl(Source, Name, Signature, "") | Acc].
finalize_state(Source, body_state(Name, SigRev, BodyRev), Acc, Out) :-
    Signature = string.join_list(" ", list.reverse(SigRev)),
    Body = string.join_list(" ", list.reverse(BodyRev)),
    Out = [semantic_decl(Source, Name, Signature, Body) | Acc].


:- pred theorem_monolith_is_safe(io::di, io::uo) is det.
theorem_monolith_is_safe(!IO) :-
    io.read_named_file_as_lines(
        "../../Exotic/ERL/FullCoupled/TheoremsMonolith.agda",
        ReadResult, !IO),
    (
        ReadResult = ok(Lines),
        (
            list.member("{-# OPTIONS --safe #-}", Lines)
        ->
            true
        ;
            io.write_string(
                "ERROR: canonical theorem monolith is not declared --safe\n",
                !IO),
            io.set_exit_status(1, !IO)
        )
    ;
        ReadResult = error(_),
        io.write_string(
            "ERROR: cannot read canonical theorem monolith\n", !IO),
        io.set_exit_status(1, !IO)
    ).

:- pred read_all_sources(list(string)::in, list(semantic_decl)::in,
    io.res(list(semantic_decl))::out, io::di, io::uo) is det.
read_all_sources([], Acc, ok(All), !IO) :-
    list.reverse(Acc, All).
read_all_sources([File | Files], Acc, Result, !IO) :-
    io.read_named_file_as_lines(File, ReadResult, !IO),
    (
        ReadResult = ok(Lines),
        parse_lines(
            File,
            Lines,
            Decls),
        read_all_sources(Files, Decls ++ Acc, Result, !IO)
    ;
        ReadResult = error(Error),
        Result = error(Error)
    ).

:- pred semantic_declarations(
    io.res(list(semantic_decl))::out, io::di, io::uo) is det.
semantic_declarations(Result, !IO) :-
    read_all_sources(source_files, [], Result, !IO).

:- pred dependency_names(semantic_decl::in, list(semantic_decl)::in,
    list(string)::out) is det.
dependency_names(
    semantic_decl(Source, Name, Signature, Body), All, Dependencies) :-
    DependencyText = concat_strings([Signature, " ", Body]),
    find_dependencies(Source, Name, DependencyText, All, [], Rev),
    list.reverse(Rev, Dependencies).

:- pred find_dependencies(string::in, string::in, string::in,
    list(semantic_decl)::in, list(string)::in, list(string)::out) is det.
find_dependencies(_, _, _, [], Acc, Acc).
find_dependencies(Source, Name, Body, [D | Ds], Acc0, Acc) :-
    D = semantic_decl(TargetSource, TargetName, _, _),
    (
        TargetName = Name
    ->
        Acc1 = Acc0
    ;
        (
            TargetSource = Source,
            contains_identifier(Body, TargetName)
        ->
            Acc1 = [concat_strings([TargetSource, "#", TargetName]) | Acc0]
        ;
            TargetSource \= Source,
            contains_identifier(Body, concat_strings([".", TargetName]))
        ->
            Acc1 = [concat_strings([TargetSource, "#", TargetName]) | Acc0]
        ;
            Acc1 = Acc0
        )
    ),
    find_dependencies(Source, Name, Body, Ds, Acc1, Acc).

:- pred semantic_laws_from_declarations(
    list(semantic_decl)::in,
    list(semantic_decl)::in,
    list(semantic_law)::out) is det.
semantic_laws_from_declarations(_, [], []).
semantic_laws_from_declarations(All, [D | Ds], [Law | Laws]) :-
    D = semantic_decl(Source, Name, Signature, _),
    (
        semantic_reflexive(D)
        -> Reflexive = yes
        ; Reflexive = no
    ),
    dependency_names(D, All, Dependencies),
    (
        list.length(Dependencies) >= 2,
        not semantic_reflexive(D)
        -> Composite = yes
        ; Composite = no
    ),
    Law = semantic_law(
        Source, Name, Reflexive, Composite, Signature, Dependencies),
    semantic_laws_from_declarations(All, Ds, Laws).

is_reflexive(semantic_law(_, _, yes, _, _, _)).
is_composite(semantic_law(_, _, _, yes, _, _)).

law_source(Law) = Law ^ source.
law_id(Law) = string.append(string.append(law_source(Law), "#"), law_name(Law)).
law_name(Law) = Law ^ name.
law_signature(Law) = Law ^ signature.
law_dependencies(Law) = Law ^ dependencies.

read_semantic_laws(Laws, !IO) :-
    theorem_monolith_is_safe(!IO),
    semantic_declarations(Result, !IO),
    (
        Result = ok(All),
        list.filter(semantic_signature, All, Decls),
        semantic_laws_from_declarations(All, Decls, Laws)
    ;
        Result = error(_),
        io.write_string(
            "ERROR: cannot read canonical theorem semantic declarations\n",
            !IO),
        io.set_exit_status(1, !IO),
        Laws = []
    ).

extract_semantics(!IO) :-
    read_semantic_laws(Laws, !IO),
    io.write_string(
        "theorem-monolith-semantic-extraction=in-memory\n", !IO),
    io.write_string(
        concat_strings([
            "semantic-law-count=",
            string.int_to_string(list.length(Laws)),
            "\n"
        ]),
        !IO),
    io.write_string(
        concat_strings([
            "nonreflexive-law-count=",
            string.int_to_string(
                list.length(
                    list.filter(
                        (pred(L::in) is semidet :- not is_reflexive(L)),
                        Laws))),
            "\n"
        ]),
        !IO),
    io.write_string(
        concat_strings([
            "composite-law-count=",
            string.int_to_string(
                list.length(
                    list.filter(
                        (pred(L::in) is semidet :- is_composite(L)),
                        Laws))),
            "\n"
        ]),
        !IO).

:- pred count_composite(list(semantic_decl)::in,
    list(semantic_decl)::in, int::out, int::out) is det.
count_composite([], _, 0, 0).
count_composite([D | Ds], All, Composite, NonReflexive) :-
    dependency_names(D, All, Dependencies),
    (
        semantic_reflexive(D)
        -> ThisNonReflexive = 0,
           ThisComposite = 0
        ;  ThisNonReflexive = 1,
           (
               list.length(Dependencies) >= 2
               -> ThisComposite = 1
               ;  ThisComposite = 0
           )
    ),
    count_composite(Ds, All, TailComposite, TailNonReflexive),
    Composite = ThisComposite + TailComposite,
    NonReflexive = ThisNonReflexive + TailNonReflexive.
