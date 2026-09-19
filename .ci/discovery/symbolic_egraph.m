:- module symbolic_egraph.

:- interface.

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

:- func class_count(egraph) = int.
:- func enode_count(egraph) = int.

:- implementation.

:- import_module int.
:- import_module version_hash_table.
:- import_module map.
:- import_module maybe.

:- type binding
    ---> binding(enode, eclass_id).

:- type egraph
    ---> egraph(
        next_id :: int,
        parent :: map(int, int),
        hashcons :: version_hash_table(enode, eclass_id),
        bindings :: list(binding)
    ).

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
    map.set(Parent0, Next, Next, Parent).

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
            map.set(parent(E0), IdB, IdA, Parent)
        else
            map.set(parent(E0), IdA, IdB, Parent)
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
    ( if Changed then
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
        map.set(parent(E0), IdB, IdA, P)
    else
        map.set(parent(E0), IdA, IdB, P)
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
