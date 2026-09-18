:- module evosax_lion_discovery.

:- interface.

:- import_module io.

:- pred main(io::di, io::uo) is det.

:- implementation.

:- import_module int.
:- import_module list.
:- import_module string.

% Proof-friendly finite analogues of EvoSAX strategy families.
% This is a Mercury meta-search layer, not a JAX/Python port.
% Learner parameters, imports, and Agda semantics remain fixed by hand.
% The search space is a closed seven-slot A/Q program genome.

:- type strategy
    ---> random_search
    ;   hill_climbing
    ;   simple_es
    ;   open_es
    ;   pgpe
    ;   snes
    ;   cma_es.

:- type genome == list(int).

:- type candidate
    ---> candidate(
        genome_value :: genome,
        typed :: bool,
        canonical :: bool,
        complexity :: int,
        fitness :: int
    ).

:- func strategies = list(strategy).
strategies = [
    random_search,
    hill_climbing,
    simple_es,
    open_es,
    pgpe,
    snes,
    cma_es
].

:- func seed0 = int.
seed0 = 19.

:- func next_seed(int) = int.
next_seed(S) =
    ((S * 1103515) + 12345) rem 2147483647.

:- func bit(int) = int.
bit(S) = next_seed(S) rem 2.

:- func canonical = genome.
canonical = [0, 0, 0, 0, 0, 0, 0].

:- func baseline = genome.
baseline = [1, 1, 1, 1, 1, 1, 1].

:- pred flip_at(int::in, genome::in, genome::out) is semidet.
flip_at(0, [X | Xs], [Y | Xs]) :-
    Y = 1 - X.
flip_at(I, [X | Xs], [X | Ys]) :-
    I > 0,
    flip_at(I - 1, Xs, Ys).

:- pred random_genome(int::in, int::in, genome::out) is det.
random_genome(_, 0, []).
random_genome(Seed, N, [B | Bs]) :-
    N > 0,
    B = bit(Seed),
    random_genome(next_seed(Seed), N - 1, Bs).

:- func typed_genome(genome) = bool.
typed_genome(G) =
    (if length(G) = 7, all_binary(G) then yes else no).

:- pred all_binary(genome::in) is semidet.
all_binary([]).
all_binary([X | Xs]) :-
    ( X = 0 ; X = 1 ),
    all_binary(Xs).

:- func genome_distance(genome, genome) = int.
genome_distance([], []) = 0.
genome_distance([X | Xs], [Y | Ys]) =
    (if X = Y then 0 else 1) + genome_distance(Xs, Ys).
genome_distance(_, _) = 999.

:- func complexity(genome) = int.
complexity(G) = length(G) + genome_distance(G, canonical).

:- func fitness(genome) = int.
fitness(G) =
    (if typed_genome(G) = yes
     then 1000 - (100 * genome_distance(G, canonical)) - complexity(G)
     else -1000000).

:- func is_canonical(genome) = bool.
is_canonical(G) = (if G = canonical then yes else no).

:- func make_candidate(genome) = candidate.
make_candidate(G) =
    candidate(
        G,
        typed_genome(G),
        is_canonical(G),
        complexity(G),
        fitness(G)
    ).

:- func perturb(strategy, int, genome) = list(genome).
perturb(random_search, Seed, _) =
    [random_genome(Seed, 7)].
perturb(hill_climbing, _, G) =
    local_flips(G, 0, []).
perturb(simple_es, _, G) =
    local_flips(G, 0, []) ++ local_flips(G, 1, []).
perturb(open_es, Seed, G) =
    [centered_flip(G, Seed), centered_flip(G, next_seed(Seed))].
perturb(pgpe, Seed, G) =
    [centered_flip(G, Seed),
     centered_flip(G, next_seed(Seed)),
     centered_flip(G, next_seed(next_seed(Seed)))].
perturb(snes, Seed, G) =
    scaled_flips(G, Seed, 0, []).
perturb(cma_es, Seed, G) =
    diagonal_covariance_step(G, Seed, 0, []).

:- func local_flips(genome, int, list(genome)) = list(genome).
local_flips(G, I, Acc) =
    (if I >= length(G)
     then reverse(Acc)
     else
         (if flip_at(I, G, G1)
          then local_flips(G, I + 1, [G1 | Acc])
          else local_flips(G, I + 1, Acc))).

:- func centered_flip(genome, int) = genome.
centered_flip(G, Seed) =
    (if flip_at(next_seed(Seed) rem 7, G, G1)
     then G1
     else G).

:- func scaled_flips(genome, int, int, list(genome)) = list(genome).
scaled_flips(G, Seed, I, Acc) =
    (if I >= length(G)
     then reverse(Acc)
     else
         (if (Seed + I) rem 3 = 0, flip_at(I, G, G1)
          then scaled_flips(G, next_seed(Seed), I + 1, [G1 | Acc])
          else scaled_flips(G, next_seed(Seed), I + 1, Acc))).

:- func diagonal_covariance_step(genome, int, int, list(genome))
    = list(genome).
diagonal_covariance_step(G, Seed, I, Acc) =
    (if I >= length(G)
     then reverse(Acc)
     else
         (if (Seed + (I * I)) rem 2 = 0, flip_at(I, G, G1)
          then diagonal_covariance_step(
              G, next_seed(Seed), I + 1, [G1 | Acc])
          else diagonal_covariance_step(
              G, next_seed(Seed), I + 1, Acc))).

:- func simplify(candidate) = candidate.
simplify(C) = C.

:- func better(candidate, candidate) = candidate.
better(A, B) =
    (if candidate_fitness(A) >= candidate_fitness(B)
     then A
     else B).

:- func candidate_fitness(candidate) = int.
candidate_fitness(candidate(_, _, _, _, F)) = F.

:- func candidate_genome(candidate) = genome.
candidate_genome(candidate(G, _, _, _, _)) = G.

:- func candidate_canonical(candidate) = bool.
candidate_canonical(candidate(_, _, C, _, _)) = C.

:- func score_population(list(candidate)) = candidate.
score_population([C | Cs]) = list.foldl(better, Cs, C).
score_population([]) = make_candidate(baseline).

:- func evaluate(strategy, int, genome) = candidate.
evaluate(S, Seed, G) =
    score_population(list.map(make_candidate, perturb(S, Seed, G))).

:- func run_strategy(strategy, int, genome, int) = candidate.
run_strategy(S, Seed, G, Steps) =
    run_strategy_(S, Seed, G, Steps).

:- pred run_strategy_(strategy::in, int::in, genome::in, int::in,
    candidate::out) is det.
run_strategy_(_, _, G, 0, Result) :-
    Result = make_candidate(G).
run_strategy_(S, Seed, G, Steps, Result) :-
    Steps > 0,
    Current = make_candidate(G),
    Proposal = evaluate(S, Seed, G),
    Best = better(Current, Proposal),
    run_strategy_(
        S, next_seed(Seed), candidate_genome(Best), Steps - 1, Result).

:- func run_portfolio(genome, list(strategy), int) = candidate.
run_portfolio(G, Strategies, Seed) =
    run_portfolio_(G, Strategies, Seed).

:- pred run_portfolio_(genome::in, list(strategy)::in, int::in,
    candidate::out) is det.
run_portfolio_(G, [], _, Result) :-
    Result = make_candidate(G).
run_portfolio_(G, [S | Ss], Seed, Result) :-
    C0 = run_strategy(S, Seed, G, 8),
    C1 = simplify(C0),
    C2 = run_portfolio(candidate_genome(C1), Ss, next_seed(Seed)),
    Result = better(C1, C2).

:- func genome_string(genome) = string.
genome_string([]) = "".
genome_string([X]) = int_to_string(X).
genome_string([X | Xs]) =
    int_to_string(X) ++ "," ++ genome_string(Xs).

:- pred emit(candidate::in, io::di, io::uo) is det.
emit(C, !IO) :-
    io.write_string(
        "formal-meta-search=evosax-family-portfolio\n", !IO),
    io.write_string(
        "candidate-genome=" ++
        genome_string(candidate_genome(C)) ++ "\n", !IO),
    io.write_string(
        "candidate-fitness=" ++
        int_to_string(candidate_fitness(C)) ++ "\n", !IO),
    (
        candidate_canonical(C) = yes
    ->
        io.write_string(
            "candidate-status=canonical-program-found\n", !IO),
        io.write_string(
            "certificate-stage=Agda theorem/bench gate remains authoritative\n",
            !IO)
    ;
        io.write_string("candidate-status=proposal-only\n", !IO)
    ).

main(!IO) :-
    Result = run_portfolio(baseline, strategies, seed0),
    emit(Result, !IO).
