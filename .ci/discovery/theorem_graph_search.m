:- module theorem_graph_search.

:- interface.

:- import_module list.
:- import_module learner_semantic_extractor.

:- pred search_emergent_compositions(
    list(semantic_law)::in,
    list(list(string))::out) is det.

:- pred search_emergent_composition(
    list(semantic_law)::in,
    list(string)::out) is semidet.

:- implementation.

:- type graph_node
    ---> graph_node(
        plan :: list(string)
    ).

:- pred law_for_id(
    string::in, list(semantic_law)::in, semantic_law::out) is semidet.
law_for_id(_, [], _) :-
    fail.
law_for_id(Id, [Law | Laws], Result) :-
    (
        if law_id(Law) = Id then
            Result = Law
        else
            law_for_id(Id, Laws, Result)
    ).

:- pred seed_node(semantic_law::in, graph_node::out) is semidet.
seed_node(Law, Node) :-
    not is_reflexive(Law),
    Node = graph_node([law_id(Law)]).

:- pred seed_nodes(
    list(semantic_law)::in,
    list(graph_node)::out) is det.
seed_nodes([], []).
seed_nodes([Law | Laws], Nodes) :-
    seed_nodes(Laws, Tail),
    (
        if seed_node(Law, Node) then
            Nodes = [Node | Tail]
        else
            Nodes = Tail
    ).

:- pred expand_node(
    graph_node::in,
    list(semantic_law)::in,
    list(graph_node)::out) is det.
expand_node(Node, Laws, Children) :-
    Plan0 = Node ^ plan,
    Plan0 = [TerminalId | _],
    (
        if law_for_id(TerminalId, Laws, TerminalLaw) then
            expand_dependencies(
                law_dependencies(TerminalLaw),
                Plan0,
                [],
                Children)
        else
            Children = []
    ).

:- pred expand_dependencies(
    list(string)::in,
    list(string)::in,
    list(graph_node)::in,
    list(graph_node)::out) is det.
expand_dependencies([], _, Acc, Children) :-
    list.reverse(Acc, Children).
expand_dependencies([Dependency | Dependencies], Plan, Acc0, Children) :-
    (
        if list.member(Dependency, Plan) then
            expand_dependencies(Dependencies, Plan, Acc0, Children)
        else
            expand_dependencies(
                Dependencies,
                [Dependency | Plan],
                [graph_node([Dependency | Plan]) | Acc0],
                Children)
    ).

:- pred maximal_dependency_chain(
    graph_node::in,
    list(semantic_law)::in) is semidet.
maximal_dependency_chain(Node, Laws) :-
    expand_node(Node, Laws, []).

:- pred insert_children(
    list(graph_node)::in,
    list(graph_node)::in,
    list(graph_node)::out) is det.
insert_children([], Frontier, Frontier).
insert_children([Node | Nodes], Frontier0, Frontier) :-
    Frontier1 = [Node | Frontier0],
    insert_children(Nodes, Frontier1, Frontier).

:- pred graph_collect(
    list(semantic_law)::in,
    list(graph_node)::in,
    list(list(string))::in,
    list(list(string))::out) is det.
graph_collect(_, [], Results, Results).
graph_collect(Laws, [Node | Frontier], Results0, Results) :-
    (
        if maximal_dependency_chain(Node, Laws) then
            graph_collect(
                Laws, Frontier,
                [Node ^ plan | Results0], Results)
        else
            expand_node(Node, Laws, Children),
            insert_children(Children, Frontier, Frontier1),
            graph_collect(
                Laws, Frontier1, Results0, Results)
    ).

:- pred all_unique(list(string)::in) is semidet.
all_unique([]).
all_unique([X | Xs]) :-
    not list.member(X, Xs),
    all_unique(Xs).

:- pred valid_plan(
    list(string)::in, list(semantic_law)::in) is semidet.
valid_plan(Plan, Laws) :-
    Plan = [TerminalId | _],
    all_unique(Plan),
    valid_chain(Plan, Laws),
    law_for_id(TerminalId, Laws, _).

:- pred valid_chain(list(string)::in, list(semantic_law)::in) is semidet.
valid_chain([_], _).
valid_chain([Child, Parent | Rest], Laws) :-
    law_for_id(Parent, Laws, ParentLaw),
    list.member(Child, law_dependencies(ParentLaw)),
    valid_chain([Parent | Rest], Laws).

:- pred all_valid_plans(
    list(list(string))::in, list(semantic_law)::in) is semidet.
all_valid_plans([], _).
all_valid_plans([Plan | Plans], Laws) :-
    valid_plan(Plan, Laws),
    all_valid_plans(Plans, Laws).

search_emergent_compositions(Laws, Results) :-
    seed_nodes(Laws, Seeds),
    graph_collect(Laws, Seeds, [], Reversed),
    list.reverse(Reversed, Results),
    all_valid_plans(Results, Laws).

search_emergent_composition(Laws, Plan) :-
    seed_nodes(Laws, Seeds),
    graph_collect(Laws, Seeds, [], Results),
    list.member(Plan, Results).
