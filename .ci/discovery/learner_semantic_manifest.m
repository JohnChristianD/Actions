:- module learner_semantic_manifest.

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

:- pred read_manifest(list(semantic_law)::out, io::di, io::uo) is det.
:- func law_id(semantic_law) = string.
:- func law_source(semantic_law) = string.
:- func law_name(semantic_law) = string.
:- func law_signature(semantic_law) = string.
:- func law_dependencies(semantic_law) = list(string).
:- pred is_reflexive(semantic_law::in) is semidet.
:- pred is_composite(semantic_law::in) is semidet.

:- implementation.

:- import_module string.

:- pred parse_line(string::in, semantic_law::out) is semidet.
parse_line(Line, Law) :-
    Line \= "",
    Line \= "source|name|reflexive|composite|signature|dependencies",
    Parts = string.split_at_string("|", Line),
    Parts = [Source, Name, ReflexiveS, CompositeS, Signature0, DependenciesS | _],
    (
        ReflexiveS = "true" -> Reflexive = yes ; Reflexive = no
    ),
    (
        CompositeS = "true" -> Composite = yes ; Composite = no
    ),
    Signature = string.replace_all(Signature0, "%7C", "|"),
    parse_dependencies(DependenciesS, Dependencies),
    Law = semantic_law(
        Source, Name, Reflexive, Composite, Signature, Dependencies).

:- pred parse_dependencies(string::in, list(string)::out) is det.
parse_dependencies(Text, Dependencies) :-
    (
        Text = ""
    ->
        Dependencies = []
    ;
        parse_dependency_parts(
            string.split_at_string(";", Text),
            Dependencies)
    ).

:- pred parse_dependency_parts(list(string)::in, list(string)::out) is det.
parse_dependency_parts([], []).
parse_dependency_parts([X | Xs], Result) :-
    Y = string.strip(X),
    parse_dependency_parts(Xs, Tail),
    (
        Y = ""
    ->
        Result = Tail
    ;
        Result = [Y | Tail]
    ).

:- pred read_lines(list(string)::in, list(semantic_law)::in,
    list(semantic_law)::out) is det.
read_lines([], Acc, Laws) :-
    list.reverse(Acc, Laws).
read_lines([Line | Rest], Acc0, Laws) :-
    (
        if parse_line(string.strip(Line), Law) then
            read_lines(Rest, [Law | Acc0], Laws)
        else
            read_lines(Rest, Acc0, Laws)
    ).

read_manifest(Laws, !IO) :-
    io.read_named_file_as_lines("learner-semantic-laws.tsv", Result, !IO),
    (
        Result = ok(Lines),
        read_lines(Lines, [], Laws)
    ;
        Result = error(_),
        io.write_string(
            "ERROR: cannot read learner semantic manifest\n", !IO),
        io.set_exit_status(1, !IO),
        Laws = []
    ).

law_source(Law) = Law ^ source.

law_id(Law) = Id :-
    Source = law_source(Law),
    Name = law_name(Law),
    Prefix = string.append(Source, "#"),
    Id = string.append(Prefix, Name).

law_name(Law) = Law ^ name.

law_signature(Law) = Law ^ signature.

law_dependencies(Law) = Law ^ dependencies.

is_reflexive(Law) :-
    Law ^ reflexive = yes.

is_composite(Law) :-
    Law ^ composite = yes.
