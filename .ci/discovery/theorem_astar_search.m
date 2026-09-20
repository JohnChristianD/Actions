:- module theorem_astar_search.

:- interface.

:- import_module io.
:- import_module learner_semantic_manifest.

:- pred search_collision_compositions(
    list(semantic_law)::in,
    int::in,
    list(list(string))::out,
    io::di, io::uo) is det.

:- pred search_collision_composition(
    list(semantic_law)::in,
    list(string)::out) is semidet.

:- implementation.

:- import_module bool.
:- import_module int.
:- import_module list.
:- import_module string.

:- type astar_node
    ---> astar_node(
        astar_plan :: list(string),
        astar_mask :: int,
        astar_cost :: int,
        astar_heuristic :: int
    ).

:- func max_depth = int.
max_depth = 4.

:- func goal_mask = int.
goal_mask = 7.

:- func scan_bit = int.
scan_bit = 1.

:- func injectivity_bit = int.
injectivity_bit = 2.

:- func collision_bit = int.
collision_bit = 4.

:- pred has_term(string::in, string::in) is semidet.
has_term(Text, Term) :-
    string.sub_string_search(Text, Term, _).

:- pred is_scan_candidate(semantic_law::in) is semidet.
is_scan_candidate(Law) :-
    Signature = semantic_law.signature(Law),
    Name = semantic_law.name(Law),
    (
        has_term(Signature, "List")
    ;   has_term(Name, "prefix")
    ),
    (
        has_term(Signature, "Endomorphism")
    ;   has_term(Name, "scan")
    ;   has_term(Name, "prefix")
    ).

:- pred is_injectivity_candidate(semantic_law::in) is semidet.
is_injectivity_candidate(Law) :-
    Signature = semantic_law.signature(Law),
    Name = semantic_law.name(Law),
    has_term(Name, "inject")
    ;
    has_term(Name, "leftInverse")
    ;
    has_term(Signature, "leftInverse").

:- pred is_collision_candidate(semantic_law::in) is semidet.
is_collision_candidate(Law) :-
    Signature = semantic_law.signature(Law),
    Name = semantic_law.name(Law),
    (
        has_term(Name, "collision")
    ;
        has_term(Signature, "ObservationTaskFactorization")
    ;
        (
            has_term(Signature, "observe")
        ,
            has_term(Signature, "≢")
        )
    ).

:- pred candidate_bit(semantic_law::in, int::out) is semidet.
candidate_bit(Law, Bit) :-
    (
        is_collision_candidate(Law)
    ->
        Bit = collision_bit
    ;
        is_injectivity_candidate(Law)
    ->
        Bit = injectivity_bit
    ;
        is_scan_candidate(Law)
    ->
        Bit = scan_bit
    ).

:- pred candidate_law(semantic_law::in) is semidet.
candidate_law(Law) :-
    semantic_law.reflexive(Law) = no,
    candidate_bit(Law, _).

:- pred missing_class_count(int::in, int::out) is det.
missing_class_count(Mask, Missing) :-
    CountScan = (if (Mask / scan_bit) = 0 then 1 else 0),
    CountInjectivity = (if (Mask / injectivity_bit) = 0 then 1 else 0),
    CountCollision = (if (Mask / collision_bit) = 0 then 1 else 0),
    Missing = CountScan + CountInjectivity + CountCollision.

:- func initial_node = astar_node.
initial_node =
    astar_node([], 0, 0, 3).

:- func node_f(astar_node) = int.
node_f(Node) =
    astar_node.astar_cost(Node) + astar_node.astar_heuristic(Node).

:- pred node_before(astar_node::in, astar_node::in) is semidet.
node_before(A, B) :-
    FA = node_f(A),
    FB = node_f(B),
    (
        FA < FB
    ;
        FA = FB,
        astar_node.astar_heuristic(A) < astar_node.astar_heuristic(B)
    ;
        FA = FB,
        astar_node.astar_heuristic(A) = astar_node.astar_heuristic(B),
        astar_node.astar_cost(A) < astar_node.astar_cost(B)
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

:- pred find_bit_for_id(string::in, list(semantic_law)::in, int::out) is semidet.
find_bit_for_id(Id, [Law | Laws], Bit) :-
    (
        law_id(Law) = Id,
        candidate_bit(Law, Bit)
    ;
        find_bit_for_id(Id, Laws, Bit)
    ).

:- pred expand_node(astar_node::in, list(semantic_law)::in,
    list(astar_node)::out) is det.
expand_node(Node, Laws, Children) :-
    Plan = astar_node.astar_plan(Node),
    Cost = astar_node.astar_cost(Node),
    list.filter(
        (pred(Law::in) is semidet :-
            candidate_law(Law),
            Id = law_id(Law),
            not list.member(Id, Plan)
        ),
        Laws,
        Candidates),
    expand_candidates(Candidates, Node, [], Children).

:- pred expand_candidates(
    list(semantic_law)::in,
    astar_node::in,
    list(astar_node)::in,
    list(astar_node)::out) is det.
expand_candidates([], _, Acc, Children) :-
    list.reverse(Acc, Children).
expand_candidates([Law | Laws], Node, Acc0, Children) :-
    Id = law_id(Law),
    candidate_bit(Law, Bit),
    NewMask = astar_node.astar_mask(Node) / Bit,
    NewCost = astar_node.astar_cost(Node) + 1,
    missing_class_count(NewMask, NewHeuristic),
    NewPlan = [Id | astar_node.astar_plan(Node)],
    Child = astar_node(NewPlan, NewMask, NewCost, NewHeuristic),
    expand_candidates(Laws, Node, [Child | Acc0], Children).

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

:- pred collect_goals(
    int::in,
    int::in,
    list(string)::in,
    list(list(string))::in,
    list(list(string))::out,
    int::out,
    io::di, io::uo) is det.
collect_goals(_, _, _, Acc, Acc, 0, !IO).
collect_goals(Count, MaxResults, Plan, Acc0, Acc, Added, !IO) :-
    (
        Count =< 0
    ->
        Acc = Acc0,
        Added = 0
    ;
        MaxResults =< list.length(Acc0)
    ->
        Acc = Acc0,
        Added = 0
    ;
        Acc1 = [Plan | Acc0],
        Acc = Acc1,
        Added = 1
    ).

:- pred astar_loop(
    list(semantic_law)::in,
    list(astar_node)::in,
    int::in,
    int::in,
    int::in,
    list(list(string))::in,
    list(list(string))::out,
    io::di, io::uo) is det.
astar_loop(_, [], _, _, _, Results, Results, !IO).
astar_loop(_, _, Expansions, MaxExpansions, MaxResults, Results, Results, !IO) :-
    Expansions >= MaxExpansions,
    MaxResults >= list.length(Results).
astar_loop(Laws, Frontier0, Expansions, MaxExpansions, MaxResults,
    Results0, Results, !IO) :-
    Expansions < MaxExpansions,
    MaxResults > list.length(Results0),
    pop_best(Frontier0, Node, Frontier1),
    Mask = astar_node.astar_mask(Node),
    Plan = astar_node.astar_plan(Node),
    (
        Mask = goal_mask
    ->
        collect_goals(
            1,
            MaxResults,
            Plan,
            Results0,
            Results1,
            _,
            !IO),
        astar_loop(
            Laws,
            Frontier1,
            Expansions,
            MaxExpansions,
            MaxResults,
            Results1,
            Results,
            !IO)
    ;
        astar_node.astar_cost(Node) < max_depth
    ->
        expand_node(Node, Laws, Children),
        insert_children(Children, Frontier1, Frontier2),
        astar_loop(
            Laws,
            Frontier2,
            Expansions + 1,
            MaxExpansions,
            MaxResults,
            Results0,
            Results,
            !IO)
    ;
        astar_loop(
            Laws,
            Frontier1,
            Expansions + 1,
            MaxExpansions,
            MaxResults,
            Results0,
            Results,
            !IO)
    ).

:- pred insert_children(
    list(astar_node)::in,
    list(astar_node)::in,
    list(astar_node)::out) is det.
insert_children([], Frontier, Frontier).
insert_children([Node | Nodes], Frontier0, Frontier) :-
    frontier_insert(Node, Frontier0, Frontier1),
    insert_children(Nodes, Frontier1, Frontier).

search_collision_compositions(Laws, MaxResults, Results, !IO) :-
    list.filter(candidate_law, Laws, CandidateLaws),
    (
        CandidateLaws = []
    ->
        Results = []
    ;
        Frontier0 = [initial_node],
        astar_loop(
            CandidateLaws,
            Frontier0,
            0,
            500,
            MaxResults,
            [],
            ReversedResults,
            !IO),
        list.reverse(ReversedResults, Results)
    ).

search_collision_composition(Laws, Plan) :-
    list.filter(candidate_law, Laws, CandidateLaws),
    search_det(CandidateLaws, [initial_node], 0, Plan).

:- pred search_det(
    list(semantic_law)::in,
    list(astar_node)::in,
    int::in,
    list(string)::out) is semidet.
search_det(_, [], _, _) :-
    fail.
search_det(Laws, Frontier0, Expansions, Plan) :-
    Expansions < 500,
    pop_best(Frontier0, Node, Frontier1),
    (
        astar_node.astar_mask(Node) = goal_mask
    ->
        Plan = astar_node.astar_plan(Node)
    ;
        astar_node.astar_cost(Node) < max_depth,
        expand_node(Node, Laws, Children),
        insert_children(Children, Frontier1, Frontier2),
        search_det(Laws, Frontier2, Expansions + 1, Plan)
    ).

