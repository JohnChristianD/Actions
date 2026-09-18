:- module mercury_oracle.

:- interface.

:- import_module io.

:- pred main(io::di, io::uo) is det.

:- implementation.

:- import_module integer.
:- import_module list.
:- import_module rational.
:- import_module string.

:- func sigmoid(rational.rational) = rational.rational.
sigmoid(Z) = (rational.rational(2) + Z) / rational.rational(4).

:- func tanh(rational.rational) = rational.rational.
tanh(Z) = (rational.rational(2) * Z) /
    (rational.rational(2) + Z * Z).

:- func lstm(rational.rational, rational.rational, rational.rational)
    = {rational.rational, rational.rational}.
lstm(X, H, C) = {H2, C2} :-
    Z = X + H,
    F = sigmoid(Z),
    I = sigmoid(Z),
    O = sigmoid(Z),
    G = tanh(Z),
    C2 = F * C + I * G,
    H2 = O * tanh(C2).

:- func q(int, int) = rational.rational.
q(N, D) = rational.rational(N, D).

:- func render(rational.rational) = string.
render(R) = Result :-
    N = integer.to_string(rational.numer(R)),
    D = rational.denom(R),
    ( if D = integer.one then
        Result = N
    else
        Result = N ++ "/" ++ integer.to_string(D)
    ).

:- pred emit(rational.rational::in, rational.rational::in,
    rational.rational::in, io::di, io::uo) is det.
emit(X, H, C, !IO) :-
    {LH, LC} = lstm(X, H, C),
    io.write_string(
        render(X) ++ "," ++
        render(H) ++ "," ++
        render(C) ++ "," ++
        render(LH) ++ "," ++
        render(LC) ++ "\n",
        !IO).

main(!IO) :-
    emit(q(1, 5), q(-1, 10), q(3, 10), !IO),
    emit(q(1, 1), q(1, 5), q(-2, 5), !IO),
    emit(q(-7, 10), q(1, 2), q(1, 10), !IO).
