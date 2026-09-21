:- module symbolic_egraph.

:- interface.

:- import_module bool.
:- import_module list.
:- import_module string.

:- type eclass_id
    ---> eclass_id(int).

:- type enode
    ---> enode(string, list(eclass_id)).

:- type expr
    ---> atom(string)
    ;   app(string, list(expr)).

:- type egraph.

:- func empty = egraph.

:- pred add_expr(expr::in, egraph::in, eclass_id::out, egraph::out) is det.
:- pred merge(eclass_id::in, eclass_id::in, egraph::in, egraph::out) is det.
:- pred equivalent(eclass_id::in, eclass_id::in, egraph::in) is semidet.
:- pred rebuild(egraph::in, egraph::out) is det.

:- type pattern
    ---> pvar(string)
    ;   papp(string, list(pattern)).

:- type rewrite_rule
    ---> rewrite_rule(string, pattern, pattern).

:- type substitution.

:- type class_analysis
    ---> class_analysis(
        analysis_class :: eclass_id,
        analysis_enode_count :: int,
        analysis_min_local_cost :: int).

:- type saturation_report
    ---> saturation_report(
        saturation_iterations :: int,
        saturation_rewrites :: int,
        saturation_changed :: bool).

:- pred e_match(
    pattern::in, eclass_id::in, egraph::in, substitution::out) is nondet.

:- pred saturate_until_stable(
    list(rewrite_rule)::in,
    egraph::in,
    egraph::out,
    saturation_report::out) is det.

:- pred analyze(egraph::in, list(class_analysis)::out) is det.

:- pred saturate_loop(
    list(rewrite_rule)::in, egraph::in, egraph::out,
    int::in, int::in, saturation_report::out) is det.
saturate_loop(Rules, E0, E, Iter0, RewriteTotal0, Report) :-
    root_classes(E0, Roots),
    saturate_pass(Rules, Roots, E0, E1, Rewrites),
    rebuild(E1, E2),
    Class0 = class_count(E0),
    Class2 = class_count(E2),
    Enode0 = enode_count(E0),
    Enode2 = enode_count(E2),
    Iter = Iter0 + 1,
    RewriteTotal = RewriteTotal0 + Rewrites,
    (
        if
            Rewrites = 0,
            Class0 = Class2,
            Enode0 = Enode2
        then
            E = E2,
            Report = saturation_report(Iter, RewriteTotal, no)
        else
            saturate_loop(
                Rules,
                E2,
                E,
                Iter,
                RewriteTotal,
                Report)
    ).

saturate_until_stable(Rules, E0, E, Report) :-
    saturate_loop(Rules, E0, E, 0, 0, Report).



:- pred extract_best(
    eclass_id::in, egraph::in, int::in, expr::out, int::out) is semidet.

:- func class_count(egraph) = int.
:- func enode_count(egraph) = int.

:- implementation.

:- import_module int.
:- import_module version_hash_table.
:- import_module map.
:- import_module maybe.
:- import_module solutions.
:- import_module require.

:- type binding
    ---> binding(enode, eclass_id).

:- type egraph
    ---> egraph(
        next_id :: int,
        parent :: map(int, int),
        hashcons :: version_hash_table(enode, eclass_id),
        bindings :: list(binding)
    ).

:- pred parent_set(
    map(int, int)::in, int::in, int::in, map(int, int)::out) is det.
parent_set(M, K, V, M2) :-
    map.set(K, V, M, M2).

:- pred enode_hash(enode::in, int::out) is det.
enode_hash(enode(Symbol, Children), Hash) :-
    string.hash(Symbol, Initial),
    hash_children(Children, Initial, Hash).

:- pred hash_children(list(eclass_id)::in, int::in, int::out) is det.
hash_children([], H, H).
hash_children([eclass_id(I) | Is], H0, H) :-
    H1 = H0 * 16777619 + I + 1,
    hash_children(Is, H1, H).

empty = E :-
    Hash = version_hash_table.init(enode_hash, 4, 0.75),
    E = egraph(0, map.init, Hash, []).

:- pred root(map(int, int)::in, eclass_id::in, eclass_id::out) is det.
root(Parent, Id, Root) :-
    IdI = id_int(Id),
    ( if map.search(Parent, IdI, P) then
        ( if P = IdI then
            Root = Id
        else
            root(Parent, eclass_id(P), Root)
        )
    else
        Root = Id
    ).

:- func id_int(eclass_id) = int.
id_int(eclass_id(I)) = I.

:- pred fresh_class(egraph::in, eclass_id::out, egraph::out) is det.
fresh_class(egraph(Next, Parent0, Hash, Bindings), Id,
        egraph(Next + 1, Parent, Hash, Bindings)) :-
    Id = eclass_id(Next),
    parent_set(Parent0, Next, Next, Parent).

:- pred canonical_children(egraph::in, list(eclass_id)::in,
    list(eclass_id)::out) is det.
canonical_children(_, [], []).
canonical_children(E, [C | Cs], [R | Rs]) :-
    root(parent(E), C, R),
    canonical_children(E, Cs, Rs).

:- pred hashcons_node(enode::in, egraph::in,
    eclass_id::out, egraph::out) is det.
hashcons_node(Node0, E0, Id, E) :-
    Node = canonical_node(E0, Node0),
    ( if version_hash_table.search(hashcons(E0), Node, Existing) then
        root(parent(E0), Existing, Id),
        E = E0
    else
        fresh_class(E0, Id0, E1),
        H1 = version_hash_table.set(hashcons(E1), Node, Id0),
        B1 = [binding(Node, Id0) | bindings(E1)],
        E = replace_hash(E1, H1, B1),
        Id = Id0
    ).

:- func canonical_node(egraph, enode) = enode.
canonical_node(E, enode(Symbol, Children)) =
    enode(Symbol, CanonicalChildren) :-
    canonical_children(E, Children, CanonicalChildren).

:- func replace_hash(egraph, version_hash_table(enode, eclass_id),
    list(binding)) = egraph.
replace_hash(egraph(N, P, _, _), H, B) = egraph(N, P, H, B).

add_expr(atom(Symbol), E0, Id, E) :-
    hashcons_node(enode(Symbol, []), E0, Id, E).
add_expr(app(Symbol, Children), E0, Id, E) :-
    add_exprs(Children, E0, ChildIds, E1),
    hashcons_node(enode(Symbol, ChildIds), E1, Id, E).

:- pred add_exprs(list(expr)::in, egraph::in,
    list(eclass_id)::out, egraph::out) is det.
add_exprs([], E, [], E).
add_exprs([X | Xs], E0, [Id | Ids], E) :-
    add_expr(X, E0, Id, E1),
    add_exprs(Xs, E1, Ids, E).

merge(A0, B0, E0, E) :-
    root(parent(E0), A0, A),
    root(parent(E0), B0, B),
    ( if A = B then
        E = E0
    else
        IdA = id_int(A),
        IdB = id_int(B),
        ( if IdA < IdB then
            parent_set(parent(E0), IdB, IdA, Parent)
        else
            parent_set(parent(E0), IdA, IdB, Parent)
        ),
        E1 = replace_parent(E0, Parent),
        rebuild(E1, E)
    ).

:- func replace_parent(egraph, map(int,int)) = egraph.
replace_parent(egraph(N, _, H, B), P) = egraph(N, P, H, B).

equivalent(A, B, E) :-
    root(parent(E), A, RA),
    root(parent(E), B, RB),
    RA = RB.

rebuild(E0, E) :-
    rebuild_pass(E0, E1, Changed),
    ( if Changed = yes then
        rebuild(E1, E)
    else
        E = E1
    ).

:- pred rebuild_pass(egraph::in, egraph::out, bool::out) is det.
rebuild_pass(E0, E, Changed) :-
    FreshHash = version_hash_table.init(enode_hash, 4, 0.75),
    rebuild_bindings(bindings(E0), E0, FreshHash, E1, no, Changed),
    E = E1.

:- pred rebuild_bindings(list(binding)::in, egraph::in,
    version_hash_table(enode,eclass_id)::in,
    egraph::out, bool::in, bool::out) is det.
rebuild_bindings([], E0, _, E0, Changed, Changed).
rebuild_bindings([binding(Node0, Id0) | Bs], E0, Hash0,
        E, Changed0, Changed) :-
    Node = canonical_node(E0, Node0),
    root(parent(E0), Id0, Root0),
    ( if version_hash_table.search(Hash0, Node, Existing0) then
        root(parent(E0), Existing0, Existing),
        ( if Root0 = Existing then
            rebuild_bindings(Bs, E0, Hash0, E, Changed0, Changed)
        else
            merge_roots(Root0, Existing, E0, E1),
            rebuild_bindings(Bs, E1, Hash0, E, yes, Changed)
        )
    else
        Hash1 = version_hash_table.set(Hash0, Node, Root0),
        E1 = replace_hash(E0, Hash1, bindings(E0)),
        rebuild_bindings(Bs, E1, Hash1, E, Changed0, Changed)
    ).

:- pred merge_roots(eclass_id::in, eclass_id::in,
    egraph::in, egraph::out) is det.
merge_roots(A, B, E0, E) :-
    IdA = id_int(A),
    IdB = id_int(B),
    ( if IdA < IdB then
        parent_set(parent(E0), IdB, IdA, P)
    else
        parent_set(parent(E0), IdA, IdB, P)
    ),
    E = replace_parent(E0, P).

class_count(E) = count_roots(bindings(E), parent(E), []).

:- func count_roots(list(binding), map(int,int), list(eclass_id))
    = int.
count_roots([], _, Seen) = list.length(Seen).
count_roots([binding(_, Id) | Bs], Parent, Seen0) =
    ( if member_root(Parent, Id, Seen0) then
        count_roots(Bs, Parent, Seen0)
    else
        count_roots(Bs, Parent, [Root | Seen0])
    ) :-
    root(Parent, Id, Root).

:- pred member_root(map(int,int)::in, eclass_id::in,
    list(eclass_id)::in) is semidet.
member_root(_, _, []) :-
    fail.
member_root(Parent, Id, [H | _]) :-
    root(Parent, Id, Root),
    Root = H.
member_root(Parent, Id, [_ | T]) :-
    member_root(Parent, Id, T).

enode_count(E) = list.length(bindings(E)).

:- type substitution_binding
    ---> substitution_binding(string, eclass_id).

:- type substitution
    ---> substitution(list(substitution_binding)).

:- pred lookup_binding(
    string::in, substitution::in, eclass_id::out) is semidet.
lookup_binding(Name, substitution(Bindings), Id) :-
    (
        Bindings = []
    ->
        fail
    ;
        Bindings = [substitution_binding(Name0, BoundId) | Rest],
        (
            Name = Name0
        ->
            Id = BoundId
        ;
            lookup_binding(Name, substitution(Rest), Id)
        )
    ).

:- pred bind_variable(
    string::in, eclass_id::in,
    substitution::in, substitution::out) is semidet.
bind_variable(Name, Id, Sub0, Sub) :-
    ( if lookup_binding(Name, Sub0, Existing) then
        Existing = Id,
        Sub = Sub0
    else
        Sub = substitution(
            [substitution_binding(Name, Id) | SubBindings]),
        Sub0 = substitution(SubBindings)
    ).

:- pred matching_enode(
    string::in, int::in, eclass_id::in, egraph::in,
    list(eclass_id)::out) is nondet.
matching_enode(Symbol, Arity, Class, E, Children) :-
    root(parent(E), Class, Root),
    list.member(binding(enode(Symbol0, Children0), Bound), bindings(E)),
    Symbol0 = Symbol,
    list.length(Children0, Arity),
    root(parent(E), Bound, BoundRoot),
    BoundRoot = Root,
    Children = Children0.

:- pred match_pattern(
    pattern::in, eclass_id::in, egraph::in,
    substitution::in, substitution::out) is nondet.
match_pattern(pvar(Name), Class, E, Sub0, Sub) :-
    root(parent(E), Class, Root),
    bind_variable(Name, Root, Sub0, Sub).
match_pattern(papp(Symbol, Patterns), Class, E, Sub0, Sub) :-
    list.length(Patterns, Arity),
    matching_enode(Symbol, Arity, Class, E, Children),
    match_pattern_children(Patterns, Children, E, Sub0, Sub).

:- pred match_pattern_children(
    list(pattern)::in, list(eclass_id)::in, egraph::in,
    substitution::in, substitution::out) is nondet.
match_pattern_children([], [], _, Sub, Sub).
match_pattern_children(
        [Pattern | Patterns], [Child | Children], E, Sub0, Sub) :-
    match_pattern(Pattern, Child, E, Sub0, Sub1),
    match_pattern_children(Patterns, Children, E, Sub1, Sub).
match_pattern_children(_, _, _, _, _) :-
    fail.

e_match(Pattern, Class, E, substitution(Bindings)) :-
    match_pattern(
        Pattern, Class, E, substitution([]), substitution(Bindings)).

:- pred instantiate_pattern(
    pattern::in, substitution::in, egraph::in,
    eclass_id::out, egraph::out) is semidet.
instantiate_pattern(pvar(Name), Sub, E, Id, E) :-
    lookup_binding(Name, Sub, Id).
instantiate_pattern(papp(Symbol, Patterns), Sub, E0, Id, E) :-
    instantiate_patterns(Patterns, Sub, E0, Children, E1),
    hashcons_node(enode(Symbol, Children), E1, Id, E).

:- pred instantiate_patterns(
    list(pattern)::in, substitution::in, egraph::in,
    list(eclass_id)::out, egraph::out) is semidet.
instantiate_patterns([], _, E, [], E).
instantiate_patterns([Pattern | Patterns], Sub, E0, [Id | Ids], E) :-
    instantiate_pattern(Pattern, Sub, E0, Id, E1),
    instantiate_patterns(Patterns, Sub, E1, Ids, E).

:- pred apply_match(
    rewrite_rule::in, eclass_id::in, substitution::in,
    egraph::in, egraph::out, int::out) is det.
apply_match(rewrite_rule(_, _, Rhs), Root, Sub, E0, E, Changed) :-
    ( if instantiate_pattern(Rhs, Sub, E0, RhsClass, E1) then
        root(parent(E1), Root, Root0),
        root(parent(E1), RhsClass, RhsRoot),
        (
            Root0 = RhsRoot
        ->
            E = E1,
            Changed = 0
        ;
            merge_roots(Root0, RhsRoot, E1, E2),
            E = E2,
            Changed = 1
        )
    else
        E = E0,
        Changed = 0
    ).

:- pred apply_rule_to_root(
    rewrite_rule::in, eclass_id::in, egraph::in,
    egraph::out, int::out) is det.
apply_rule_to_root(Rule, Root, E0, E, Changed) :-
    solutions(
        (pred(Sub::out) is nondet :-
            Rule = rewrite_rule(_, Lhs, _),
            e_match(Lhs, Root, E0, Sub)),
        Subs),
    apply_substitutions(Subs, Rule, Root, E0, E, 0, Changed).

:- pred apply_substitutions(
    list(substitution)::in, rewrite_rule::in, eclass_id::in,
    egraph::in, egraph::out, int::in, int::out) is det.
apply_substitutions([], _, _, E, E, Count, Count).
apply_substitutions([Sub | Subs], Rule, Root, E0, E, Count0, Count) :-
    apply_match(Rule, Root, Sub, E0, E1, Changed),
    apply_substitutions(Subs, Rule, Root, E1, E, Count0 + Changed, Count).

:- pred root_classes(
    egraph::in, list(eclass_id)::out) is det.
root_classes(E, Roots) :-
    root_classes_bindings(bindings(E), parent(E), [], Roots).

:- pred root_classes_bindings(
    list(binding)::in, map(int, int)::in,
    list(eclass_id)::in, list(eclass_id)::out) is det.
root_classes_bindings([], _, Acc, Roots) :-
    list.reverse(Acc, Roots).
root_classes_bindings([binding(_, Id) | Bs], Parent, Acc0, Roots) :-
    root(Parent, Id, Root),
    (
        list.member(Root, Acc0)
    ->
        Acc1 = Acc0
    ;
        Acc1 = [Root | Acc0]
    ),
    root_classes_bindings(Bs, Parent, Acc1, Roots).

:- pred saturate_pass(
    list(rewrite_rule)::in, list(eclass_id)::in,
    egraph::in, egraph::out, int::out) is det.
saturate_pass([], _, E, E, 0).
saturate_pass([Rule | Rules], Roots, E0, E, Count) :-
    apply_rules_to_roots(Rule, Roots, E0, E1, Count1),
    saturate_pass(Rules, Roots, E1, E, Count2),
    Count = Count1 + Count2.

:- pred apply_rules_to_roots(
    rewrite_rule::in, list(eclass_id)::in,
    egraph::in, egraph::out, int::out) is det.
apply_rules_to_roots(_, [], E, E, 0).
apply_rules_to_roots(Rule, [Root | Roots], E0, E, Count) :-
    apply_rule_to_root(Rule, Root, E0, E1, Count1),
    apply_rules_to_roots(Rule, Roots, E1, E, Count2),
    Count = Count1 + Count2.

:- pred local_cost(enode::in, int::out) is det.
local_cost(enode(Symbol, Children), Cost) :-
    Cost = 1 + string.length(Symbol) + list.length(Children).

:- pred analyze_bindings(
    list(binding)::in, map(int, int)::in,
    list(class_analysis)::in, list(class_analysis)::out) is det.
analyze_bindings([], _, Acc, Out) :-
    list.reverse(Acc, Out).
analyze_bindings([binding(Node, Id) | Bs], Parent, Acc0, Out) :-
    root(Parent, Id, Root),
    (
        if find_analysis(Root, Acc0, Existing) then
            Count = Existing ^ analysis_enode_count + 1,
            Cost0 = Existing ^ analysis_min_local_cost,
            local_cost(Node, Cost1),
            Cost = min(Cost0, Cost1),
            Updated = class_analysis(Root, Count, Cost),
            replace_analysis(Root, Updated, Acc0, Acc1)
        else
            local_cost(Node, Cost),
            Acc1 = [class_analysis(Root, 1, Cost) | Acc0]
    ),
    analyze_bindings(Bs, Parent, Acc1, Out).

:- pred find_analysis(
    eclass_id::in, list(class_analysis)::in,
    class_analysis::out) is semidet.
find_analysis(Root, Analyses, Result) :-
    (
        Analyses = []
    ->
        fail
    ;
        Analyses = [Head | Tail],
        (
            analysis_class(Head) = Root
        ->
            Result = Head
        ;
            find_analysis(Root, Tail, Result)
        )
    ).

:- pred replace_analysis(
    eclass_id::in, class_analysis::in,
    list(class_analysis)::in, list(class_analysis)::out) is det.
replace_analysis(_, _, [], []).
replace_analysis(Root, New, [A | As], Out) :-
    (
        analysis_class(A) = Root
    ->
        Out = [New | As]
    ;
        replace_analysis(Root, New, As, Tail),
        Out = [A | Tail]
    ).

analyze(E, Analyses) :-
    analyze_bindings(bindings(E), parent(E), [], Analyses).

:- pred extract_best_seen(
    eclass_id::in, egraph::in, int::in,
    list(eclass_id)::in, expr::out, int::out) is semidet.
extract_best_seen(Class, E, Depth, Seen, Expr, Cost) :-
    root(parent(E), Class, Root),
    Depth > 0,
    not list.member(Root, Seen),
    best_binding_for_root(
        bindings(E), Root, E, Depth, [Root | Seen], Expr, Cost).

:- pred best_binding_for_root(
    list(binding)::in, eclass_id::in, egraph::in, int::in,
    list(eclass_id)::in, expr::out, int::out) is semidet.
best_binding_for_root([], _, _, _, _, _, _) :-
    fail.
best_binding_for_root(
        [binding(Node, Bound) | Bs], Root, E, Depth, Seen,
        Expr, Cost) :-
    (
        root(parent(E), Bound, BoundRoot),
        BoundRoot = Root,
        Node = enode(Symbol, Children),
        extract_children(Children, E, Depth - 1, Seen, ChildExprs, ChildCost),
        Candidate = app(Symbol, ChildExprs),
        local_cost(Node, LocalCost),
        CandidateCost = LocalCost + ChildCost
    ->
        (
            if best_binding_for_root(
                    Bs, Root, E, Depth, Seen, OtherExpr, OtherCost)
            then
                (
                    CandidateCost =< OtherCost
                ->
                    Expr = Candidate,
                    Cost = CandidateCost
                ;
                    Expr = OtherExpr,
                    Cost = OtherCost
                )
            else
                Expr = Candidate,
                Cost = CandidateCost
        )
    ;
        best_binding_for_root(
            Bs, Root, E, Depth, Seen, Expr, Cost)
    ).

:- pred extract_children(
    list(eclass_id)::in, egraph::in, int::in,
    list(eclass_id)::in, list(expr)::out, int::out) is semidet.
extract_children([], _, _, _, [], 0).
extract_children([Child | Children], E, Depth, Seen, [Expr | Exprs], Cost) :-
    extract_best_seen(Child, E, Depth, Seen, Expr, Cost0),
    extract_children(Children, E, Depth, Seen, Exprs, Cost1),
    Cost = Cost0 + Cost1.

extract_best(Class, E, Depth, Expr, Cost) :-
    extract_best_seen(Class, E, Depth, [], Expr, Cost).
