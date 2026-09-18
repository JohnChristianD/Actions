:- module jaxtar_aq_discovery.

:- interface.

:- import_module io.

:- pred main(io::di, io::uo) is det.

:- implementation.

:- import_module list.

:- type channel
    ---> critic
    ;   score_pair
    ;   sparse_pair
    ;   sparse_pair_rope
    ;   walsh4
    ;   recurrent_signal
    ;   shaped_reward
    ;   watkins_signal.

:- type op
    ---> lcb_score
    ;   sparsemax2
    ;   rope_quarter
    ;   wht4
    ;   project_left
    ;   qlog2_bias
    ;   watkins_q2.

:- func source(op) = channel.
source(lcb_score) = critic.
source(sparsemax2) = score_pair.
source(rope_quarter) = sparse_pair.
source(wht4) = sparse_pair_rope.
source(project_left) = walsh4.
source(qlog2_bias) = sparse_pair.
source(watkins_q2) = shaped_reward.

:- func target(op) = channel.
target(lcb_score) = score_pair.
target(sparsemax2) = sparse_pair.
target(rope_quarter) = sparse_pair_rope.
target(wht4) = walsh4.
target(project_left) = recurrent_signal.
target(qlog2_bias) = shaped_reward.
target(watkins_q2) = watkins_signal.

:- pred verify_path(channel::in, list(op)::in, channel::out) is semidet.
verify_path(Channel, [], Channel).
verify_path(Channel, [Op | Ops], Final) :-
    source(Op) = Channel,
    verify_path(target(Op), Ops, Final).

main(!IO) :-
    Policy = [lcb_score, sparsemax2],
    Attention = [rope_quarter, wht4, project_left],
    Target = [qlog2_bias, watkins_q2],
    verify_path(critic, Policy, score_pair),
    verify_path(sparse_pair, Attention, recurrent_signal),
    verify_path(sparse_pair, Target, watkins_signal),
    io.write_string("mercury-jaxtar-aq=typed-search-certificate\n", !IO),
    io.write_string("policy=LCB>sparsemax2\n", !IO),
    io.write_string("attention=learned-sparsemax>Walsh-Hadamard>Rademacher-phase>projection\n", !IO),
    io.write_string("target=negative-q2-Munchausen>Watkins\n", !IO),
    io.write_string("closed-loop-candidate=policy+attention+target\n", !IO).
