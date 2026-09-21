:- module theorem_astar_search.

:- interface.

:- import_module io.
:- import_module list.
:- import_module learner_semantic_manifest.

:- pred search_emergent_compositions(
    list(semantic_law)::in,
    int::in,
    list(list(string))::out,
    io::di, io::uo) is det.

:- pred search_emergent_composition(
    list(semantic_law)::in,
    list(string)::out) is semidet.

:- implementation.

:- import_module int.

:- type astar_node
    ---> astar_node(
        seed :: string,
        plan :: list(string),
        cost :: int,
        heuristic :: int
    ).

:- func max_depth = int.
max_depth = 4.

:- func goal_depth = int.
goal_depth = 3.

:- pred all_unique(list(string)::in) is semidet.
all_unique([]).
all_unique([X | Xs]) :-
    not list.member(X, Xs),
    all_unique(Xs).

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

:- pred seed_node(semantic_law::in, astar_node::out) is semidet.
seed_node(Law, Node) :-
    not is_reflexive(Law),
    is_composite(Law),
    Id = law_id(Law),
    Node = astar_node(Id, [Id], 0, goal_depth - 1).

:- pred seed_nodes(
    list(semantic_law)::in,
    list(astar_node)::out) is det.
seed_nodes([], []).
seed_nodes([Law | Laws], Nodes) :-
    seed_nodes(Laws, Tail),
    (
        seed_node(Law, Node)
    ->
        Nodes = [Node | Tail]
    ;
        Nodes = Tail
    ).

:- func node_f(astar_node) = int.
node_f(Node) =
    cost(Node) + heuristic(Node).

:- pred node_before(astar_node::in, astar_node::in) is semidet.
node_before(A, B) :-
    FA = node_f(A),
    FB = node_f(B),
    (
        if FA < FB then
            true
        else if FA > FB then
            fail
        else
            HA = heuristic(A),
            HB = heuristic(B),
            (
                if HA < HB then
                    true
                else if HA > HB then
                    fail
                else
                    CA = cost(A),
                    CB = cost(B),
                    CA < CB
            )
    ).

:- pred frontier_insert(astar_node::in, list(astar_node)::in,
    list(astar_node)::out) is det.
frontier_insert(Node, [], [Node]).
frontier_insert(Node, [Head | Tail], Result) :-
    (
        node_before(Node, Head)
    ->
        Result = [Node, Head | Tail]
    ;
        frontier_insert(Node, Tail, TailResult),
        Result = [Head | TailResult]
    ).

:- pred pop_best(
    list(astar_node)::in,
    astar_node::out,
    list(astar_node)::out) is semidet.
pop_best([Best | Rest], BestOut, Remaining) :-
    pop_best_acc(Rest, Best, [], BestOut, Remaining).

:- pred pop_best_acc(
    list(astar_node)::in,
    astar_node::in,
    list(astar_node)::in,
    astar_node::out,
    list(astar_node)::out) is det.
pop_best_acc([], Best, Acc, Best, Remaining) :-
    list.reverse(Acc, Remaining).
pop_best_acc([Candidate | Rest], Best0, Acc0, Best, Remaining) :-
    (
        node_before(Candidate, Best0)
    ->
        pop_best_acc(Rest, Candidate, [Best0 | Acc0], Best, Remaining)
    ;
        pop_best_acc(Rest, Best0, [Candidate | Acc0], Best, Remaining)
    ).

:- pred missing_depth(astar_node::in, int::out) is det.
missing_depth(Node, Missing) :-
    Length = list.length(plan(Node)),
    (
        Length >= goal_depth
    ->
        Missing = 0
    ;
        Missing = goal_depth - Length
    ).

:- pred expand_node(
    astar_node::in,
    list(semantic_law)::in,
    list(astar_node)::out) is det.
expand_node(Node, Laws, Children) :-
    Plan = plan(Node),
    (
        if Plan = [TerminalId | _],
           law_for_id(TerminalId, Laws, TerminalLaw)
        then
            Dependencies = law_dependencies(TerminalLaw),
            expand_dependencies(Dependencies, Node, [], Children)
        else
            Children = []
    ).

:- pred expand_dependencies(
    list(string)::in,
    astar_node::in,
    list(astar_node)::in,
    list(astar_node)::out) is det.
expand_dependencies([], _, Acc, Children) :-
    list.reverse(Acc, Children).
expand_dependencies([Dependency | Dependencies], Node, Acc0, Children) :-
    Plan0 = plan(Node),
    (
        list.member(Dependency, Plan0)
    ->
        expand_dependencies(Dependencies, Node, Acc0, Children)
    ;
        NewPlan = [Dependency | Plan0],
        NewNode0 = astar_node(
            seed(Node),
            NewPlan,
            cost(Node) + 1,
            0),
        missing_depth(NewNode0, NewHeuristic),
        Child = astar_node(
            seed(Node),
            NewPlan,
            cost(Node) + 1,
            NewHeuristic),
        expand_dependencies(
            Dependencies, Node, [Child | Acc0], Children)
    ).

:- pred goal_node(
    astar_node::in,
    list(semantic_law)::in) is semidet.
goal_node(Node, Laws) :-
    Plan = plan(Node),
    list.length(Plan) >= goal_depth,
    all_unique(Plan),
    Plan = [TerminalId | _],
    SeedId = seed(Node),
    law_for_id(SeedId, Laws, SeedLaw),
    not list.member(TerminalId, law_dependencies(SeedLaw)).

:- pred insert_children(
    list(astar_node)::in,
    list(astar_node)::in,
    list(astar_node)::out) is det.
insert_children([], Frontier, Frontier).
insert_children([Node | Nodes], Frontier0, Frontier) :-
    frontier_insert(Node, Frontier0, Frontier1),
    insert_children(Nodes, Frontier1, Frontier).

:- pred astar_collect(
    list(semantic_law)::in,
    list(astar_node)::in,
    int::in,
    int::in,
    int::in,
    list(list(string))::in,
    list(list(string))::out,
    io::di, io::uo) is det.
astar_collect(Laws, Frontier0, Expansions, MaxExpansions, MaxResults,
    Results0, Results, !IO) :-
    (
        if Expansions >= MaxExpansions then
            Results = Results0
        else if list.length(Results0) >= MaxResults then
            Results = Results0
        else if Frontier0 = [] then
            Results = Results0
        else
            astar_collect_frontier(
                Laws, Frontier0, Expansions, MaxExpansions, MaxResults,
                Results0, Results, !IO)
    ).

:- pred astar_collect_frontier(
    list(semantic_law)::in,
    list(astar_node)::in,
    int::in,
    int::in,
    int::in,
    list(list(string))::in,
    list(list(string))::out,
    io::di, io::uo) is det.
astar_collect_frontier(
    _, [], _, _, _, Results, Results, !IO).
astar_collect_frontier(
    Laws, [First | Rest], Expansions, MaxExpansions, MaxResults,
    Results0, Results, !IO) :-
    pop_best_acc(Rest, First, [], Node, Frontier1),
    (
        if goal_node(Node, Laws) then
            Results1 = [plan(Node) | Results0],
            astar_collect(
                Laws, Frontier1, Expansions,
                MaxExpansions, MaxResults,
                Results1, Results, !IO)
        else if cost(Node) < max_depth then
            expand_node(Node, Laws, Children),
            insert_children(Children, Frontier1, Frontier2),
            astar_collect(
                Laws, Frontier2, Expansions + 1,
                MaxExpansions, MaxResults,
                Results0, Results, !IO)
        else
            astar_collect(
                Laws, Frontier1, Expansions + 1,
                MaxExpansions, MaxResults,
                Results0, Results, !IO)
    ).

search_emergent_compositions(Laws, MaxResults, Results, !IO) :-
    seed_nodes(Laws, Seeds),
    astar_collect(Laws, Seeds, 0, 1000, MaxResults, [], Reversed, !IO),
    list.reverse(Reversed, Results).

search_emergent_composition(Laws, Plan) :-
    search_emergent_compositions(Laws, 1, Results, !IO),
    Results = [Plan | _].

