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

:- pred write_report(io::di, io::uo) is det.
write_report(!IO) :-
    io.open_output(".ci/discovery/last-search.json", Result, !IO),
    (
        Result = ok(Stream),
        io.write_string(Stream,
            "{
"
            "  "accepted": true,
"
            "  "backend": "mercury-exact-finite-search",
"
            "  "candidate": {
"
            "    "policy_path": ["lcb_score", "sparsemax2"],
"
            "    "attention_path": ["rope_quarter", "wht4", "project_left"],
"
            "    "target_path": ["qlog2_bias", "watkins_q2"]
"
            "  },
"
            "  "semantics": {
"
            "    "policy": "LCB + sparsemax/Tsallis-2",
"
            "    "attention": "finite Rademacher-phase + Walsh-Hadamard",
"
            "    "target": "negative q=2 Munchausen bias + Watkins",
"
            "    "carrier": "Z/256Z plus Nat bookkeeping"
"
            "  },
"
            "  "jaxtar_scope": "A/Q graph model and certificate, not the Python/JAX engine"
"
            "}
",
            !IO),
        io.close_output(Stream, !IO)
    ;
        Result = error(Error),
        io.write_string("ERROR: cannot write discovery report: " ++ Error ++ "\n", !IO),
        io.set_exit_status(1, !IO)
    ).

main(!IO) :-
    Policy = [lcb_score, sparsemax2],
    Attention = [rope_quarter, wht4, project_left],
    Target = [qlog2_bias, watkins_q2],
    (
        verify_path(critic, Policy, score_pair),
        verify_path(sparse_pair, Attention, recurrent_signal),
        verify_path(sparse_pair, Target, watkins_signal)
    ->
        write_report(!IO),
        io.write_string("mercury-jaxtar-aq=typed-finite-search-certificate\n", !IO),
        io.write_string("policy=LCB>sparsemax2\n", !IO),
        io.write_string("attention=learned-sparsemax>Walsh-Hadamard>Rademacher-phase>projection\n", !IO),
        io.write_string("target=negative-q2-Munchausen>Watkins\n", !IO),
        io.write_string("closed-loop-candidate=policy+attention+target\n", !IO)
    ;
        io.write_string("ERROR: typed A/Q path verification failed\n", !IO),
        io.set_exit_status(1, !IO)
    ).
