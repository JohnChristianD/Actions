:- module clojure_involution_compat.

:- interface.

:- import_module io.

:- pred main(io::di, io::uo) is det.

:- implementation.

:- import_module list.

:- func seq_length(list(T)) = int.
seq_length([]) = 0.
seq_length([_ | Xs]) = 1 + seq_length(Xs).

:- func at(list(int), int) = int.
at([X | _], 0) = X.
at([_ | Xs], I) = at(Xs, I - 1).

:- func replace(int, int, list(int)) = list(int).
replace(0, X, [_ | Xs]) = [X | Xs].
replace(I, X, [Y | Ys]) = [Y | replace(I - 1, X, Ys)].

:- pred adjacent_swap(int::in, int::in, list(int)::in, list(int)::out) is semidet.
adjacent_swap(N, I, V, Out) :-
    I >= 0,
    I + 1 < N,
    I < seq_length(V),
    J = I + 1,
    Vi = at(V, I),
    Vj = at(V, J),
    Out = replace(J, Vi, replace(I, Vj, V)).

:- pred sign_flip(int::in, int::in, list(int)::in, list(int)::out) is semidet.
sign_flip(N, I, V, Out) :-
    I >= 0,
    I < N,
    I < seq_length(V),
    Out = replace(I, -at(V, I), V).

:- pred involution_swap(int::in, list(list(int))::in) is semidet.
involution_swap(_, []).
involution_swap(I, [V | Vs]) :-
    adjacent_swap(4, I, V, V1),
    adjacent_swap(4, I, V1, V2),
    V = V2,
    involution_swap(I, Vs).

:- pred involution_flip(int::in, list(list(int))::in) is semidet.
involution_flip(_, []).
involution_flip(I, [V | Vs]) :-
    sign_flip(4, I, V, V1),
    sign_flip(4, I, V1, V2),
    V = V2,
    involution_flip(I, Vs).

:- pred composed_basis(list(int)::in, list(int)::out) is semidet.
composed_basis(V, Out) :-
    sign_flip(4, 3, V, V1),
    adjacent_swap(4, 0, V1, V2),
    sign_flip(4, 3, V2, V3),
    adjacent_swap(4, 0, V3, Out).

main(!IO) :-
    Domain = [[0, 1, 2, 3], [3, 2, 1, 0], [-1, 4, 2, 8]],
    (
        involution_swap(0, Domain),
        involution_flip(3, Domain),
        composed_basis([0, 1, 2, 3], Basis),
        composed_basis(Basis, Basis2),
        Basis = Basis2
    ->
        io.write_string("mercury-involution-compat=pass\n", !IO)
    ;
        io.write_string("mercury-involution-compat=fail\n", !IO),
        io.set_exit_status(1, !IO)
    ).
