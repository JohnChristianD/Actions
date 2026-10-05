:- module autonomous_inversion_search.

:- interface.

:- import_module io.

:- pred main(io::di, io::uo) is det.

:- implementation.

:- import_module int.
:- import_module list.
:- import_module string.

:- import_module learner_semantic_extractor.

% Mercury is doing discovery here: it searches a capability space rather than
% proving equality again. Agda remains the proof authority for any claimed
% theorem reached from a candidate composition.

:- type capability
    ---> inversion
    ;    exact_search
    ;    uniform_continuity.

:- type discovery_node
    ---> discovery_node(
        plan :: list(string),
        covered :: list(capability)
    ).

:- func all_capabilities = list(capability).
all_capabilities = [inversion, exact_search, uniform_continuity].

:- pred has_capability(
    capability::in,
    semantic_law::in) is semidet.

has_capability(inversion, Law) :-
    Name = string.to_lower(law_name(Law)),
    Signature = string.to_lower(law_signature(Law)),
    (
        string.sub_string_search(Name, "inverse", _)
    ;
        string.sub_string_search(Name, "invert", _)
    ;
        string.sub_string_search(Name, "injective", _)
    ;
        string.sub_string_search(Signature, "inverse", _)
    ;
        string.sub_string_search(Signature, "is-equiv", _)
    ).

has_capability(exact_search, Law) :-
    Name = string.to_lower(law_name(Law)),
    Signature = string.to_lower(law_signature(Law)),
    (
        string.sub_string_search(Name, "searchable", _)
    ;
        string.sub_string_search(Name, "search", _)
    ;
        string.sub_string_search(Signature, "csearchable", _)
    ;
        string.sub_string_search(Signature, "searchable", _)
    ;
        string.sub_string_search(Signature, "search", _)
    ).

has_capability(uniform_continuity, Law) :-
    Name = string.to_lower(law_name(Law)),
    Signature = string.to_lower(law_signature(Law)),
    (
        string.sub_string_search(Name, "ucontinuous", _)
    ;
        string.sub_string_search(Name, "continuity", _)
    ;
        string.sub_string_search(Name, "closeness", _)
    ;
        string.sub_string_search(Signature, "ucontinuous", _)
    ;
        string.sub_string_search(Signature, "continuity", _)
    ;
        string.sub_string_search(Signature, "closeness", _)
    ).

:- pred covered(
    capability::in,
    list(capability)::in) is semidet.
covered(C, [C0 | Cs]) :-
    (
        C = C0
    ;
        covered(C, Cs)
    ).
covered(_, []):-
    fail.

:- pred add_capability(
    capability::in,
    list(capability)::in,
    list(capability)::out) is det.
add_capability(C, Cs, Out) :-
    (
        covered(C, Cs)
    ->
        Out = Cs
    ;
        Out = [C | Cs]
    ).

:- pred all_required_covered(
    list(capability)::in,
    list(capability)::in) is semidet.
all_required_covered([], _).
all_required_covered([C | Cs], Covered) :-
    covered(C, Covered),
    all_required_covered(Cs, Covered).

:- pred discovery_source(
    semantic_law::in) is semidet.
discovery_source(Law) :-
    Source = law_source(Law),
    (
        string.sub_string_search(Source, "FullCoupled/CanonicalLearnerMonolith.agda", _)
    ;
        string.sub_string_search(Source, "FullCoupled/TheoremsMonolith.agda", _)
    ).

:- pred law_is_candidate(
    capability::in,
    semantic_law::in) is semidet.
law_is_candidate(C, Law) :-
    discovery_source(Law),
    not is_reflexive(Law),
    not is_record_field(Law),
    has_capability(C, Law),
    Name = law_name(Law),
    % Do not let the bridge prove itself as its own discovery candidate.
    not string.sub_string_search(
        string.to_lower(Name),
        "exact-search-inverse",
        _).

:- pred expand_capability(
    list(semantic_law)::in,
    capability::in,
    discovery_node::in,
    list(discovery_node)::out) is det.
expand_capability(Laws, C, discovery_node(Plan, Covered), Children) :-
    expand_capability_2(
        Laws, C, Plan, Covered, [], Reversed),
    list.reverse(Reversed, Children).

:- pred expand_capability_2(
    list(semantic_law)::in,
    capability::in,
    list(string)::in,
    list(capability)::in,
    list(discovery_node)::in,
    list(discovery_node)::out) is det.
expand_capability_2(
    [], _, _, _, Acc, Acc).
expand_capability_2(
    [Law | Laws],
    C,
    Plan,
    Covered,
    Acc0,
    Acc) :-
    (
        if law_is_candidate(C, Law),
           not list.member(law_id(Law), Plan)
        then
            add_capability(C, Covered, Covered1),
            Acc1 = [
                discovery_node(
                    [law_id(Law) | Plan],
                    Covered1) | Acc0]
        else
            Acc1 = Acc0
    ),
    expand_capability_2(
        Laws, C, Plan, Covered, Acc1, Acc).

:- func missing_count(
    list(capability),
    list(capability)) = int.
missing_count([], _) = 0.
missing_count([C | Cs], Covered) =
    (if covered(C, Covered) then 0 else 1)
    + missing_count(Cs, Covered).

:- func node_score(
    discovery_node) = int.
node_score(discovery_node(Plan, Covered)) =
    list.length(Plan)
    + missing_count(all_capabilities, Covered).

:- pred insert_astar(
    discovery_node::in,
    list(discovery_node)::in,
    list(discovery_node)::out) is det.
insert_astar(Node, [], [Node]).
insert_astar(Node, [Head | Tail], Out) :-
    (
        if node_score(Node) =< node_score(Head)
        then
            Out = [Node, Head | Tail]
        else
            insert_astar(Node, Tail, Tail0),
            Out = [Head | Tail0]
    ).

:- pred insert_children(
    list(discovery_node)::in,
    list(discovery_node)::in,
    list(discovery_node)::out) is det.
insert_children([], Frontier, Frontier).
insert_children([Node | Nodes], Frontier0, Frontier) :-
    insert_astar(Node, Frontier0, Frontier1),
    insert_children(Nodes, Frontier1, Frontier).

:- pred autonomous_astar(
    list(semantic_law)::in,
    list(discovery_node)::in,
    list(discovery_node)::in,
    list(discovery_node)::out) is det.
autonomous_astar(_, [], Results, Results).
autonomous_astar(Laws, [Node | Frontier], Results0, Results) :-
    Node = discovery_node(_, Covered),
    (
        if all_required_covered(all_capabilities, Covered)
        then
            autonomous_astar(
                Laws, Frontier,
                [Node | Results0], Results)
        else
            expand_next(Laws, Node, Children),
            insert_children(Children, Frontier, Frontier1),
            autonomous_astar(
                Laws, Frontier1,
                Results0, Results)
    ).

:- pred expand_next(
    list(semantic_law)::in,
    discovery_node::in,
    list(discovery_node)::out) is det.
expand_next(Laws, Node, Children) :-
    missing_capability(Laws, Node, C),
    expand_capability(Laws, C, Node, Children).

:- pred missing_capability(
    list(semantic_law)::in,
    discovery_node::in,
    capability::out) is semidet.
missing_capability(_, discovery_node(_, Covered), C) :-
    list.member(C, all_capabilities),
    not covered(C, Covered).

:- pred dedupe_results(
    list(discovery_node)::in,
    list(discovery_node)::out) is det.
dedupe_results(Results, Deduped) :-
    dedupe_results_2(Results, [], [], Deduped).

:- pred dedupe_results_2(
    list(discovery_node)::in,
    list(string)::in,
    list(discovery_node)::in,
    list(discovery_node)::out) is det.
dedupe_results_2([], _, Acc, Out) :-
    list.reverse(Acc, Out).
dedupe_results_2(
    [Node @ discovery_node(Plan, _) | Nodes],
    Seen,
    Acc0,
    Out) :-
    Key = string.join_list("|", Plan),
    (
        if list.member(Key, Seen)
        then
            dedupe_results_2(Nodes, Seen, Acc0, Out)
        else
            dedupe_results_2(
                Nodes,
                [Key | Seen],
                [Node | Acc0],
                Out)
    ).

:- pred write_plan_items(
    io.text_output_stream::in,
    list(discovery_node)::in,
    io::di,
    io::uo) is det.
write_plan_items(_, [], !IO).
write_plan_items(Stream, [discovery_node(Plan, _) | Nodes], !IO) :-
    io.write_string(
        Stream,
        "    " ++ string.join_list(" -> ", Plan) ++ "",
        !IO),
    (
        Nodes = []
    ->
        true
    ;
        io.write_string(Stream, ",", !IO)
    ),
    io.write_string(Stream, "\n", !IO),
    write_plan_items(Stream, Nodes, !IO).

:- pred write_report(
    list(semantic_law)::in,
    list(discovery_node)::in,
    io::di,
    io::uo) is det.
write_report(Laws, Results, !IO) :-
    io.open_output(
        "autonomous-inversion-search.dhall",
        OpenResult,
        !IO),
    (
        OpenResult = ok(Stream),
        io.write_string(Stream, "{\n", !IO),
        io.write_string(
            Stream,
            "  semanticLawCount = " ++
            string.int_to_string(list.length(Laws)) ++ ",\n",
            !IO),
        io.write_string(
            Stream,
            "  searchObjective = \"inversion + exact-search + uniform-continuity\",\n",
            !IO),
        io.write_string(
            Stream,
            "  discoveryMode = \"capability-space A*\",\n",
            !IO),
        io.write_string(
            Stream,
            "  proofAuthority = \"Agda --safe TWA proof terms\",\n",
            !IO),
        io.write_string(
            Stream,
            "  candidateCount = " ++
            string.int_to_string(list.length(Results)) ++ ",\n",
            !IO),
        io.write_string(
            Stream,
            "  candidates = [\n",
            !IO),
        write_plan_items(Stream, Results, !IO),
        io.write_string(Stream, "  ]\n", !IO),
        io.write_string(Stream, "}\n", !IO),
        io.close_output(Stream, !IO)
    ;
        OpenResult = error(_),
        io.write_string(
            "ERROR: cannot write autonomous inversion/search report\n",
            !IO),
        io.set_exit_status(1, !IO)
    ).

main(!IO) :-
    read_semantic_laws(Laws, !IO),
    Start = discovery_node([], []),
    autonomous_astar(Laws, [Start], [], Reversed),
    dedupe_results(Reversed, Results),
    (
        Results = []
    ->
        io.write_string(
            "ERROR: no inversion/exact-search/uniform-continuity composition discovered\n",
            !IO),
        io.set_exit_status(1, !IO)
    ;
        write_report(Laws, Results, !IO),
        io.write_string(
            "mercury-autonomous-inversion-search=pass\n",
            !IO)
    ).
