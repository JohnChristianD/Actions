:- module theorem_astar_search.

:- interface.

:- import_module io.
:- import_module list.
:- import_module learner_semantic_manifest.

:- pred :- pred search_det(
    list(semantic_law)::in,
    list(astar_node)::in,
    int::in,
    list(string)::out) is semidet.
search_det(Laws, [First | Rest], Expansions, Plan) :-
    pop_best_acc(Rest, First, [], Node, Frontier1),
    (
        if goal_node(Node, Laws) then
            Plan = plan(Node)
        else if cost(Node) < max_depth then
            expand_node(Node, Laws, Children),
            insert_children(Children, Frontier1, Frontier2),
            search_det(Laws, Frontier2, Expansions + 1, Plan)
        else
            fail
    ).

search_emergent_composition(Laws, Plan) :-
    seed_nodes(Laws, Seeds),
    search_det(Laws, Seeds, 0, Plan).
