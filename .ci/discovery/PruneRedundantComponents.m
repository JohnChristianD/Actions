:- module prune_redundant_components.

:- interface.

:- import_module io.

:- pred main(io::di, io::uo) is det.

:- implementation.

main(!IO) :-
    Command =
        "set -eu; " ++
        "test -f Exotic/ERL/FullCoupled/CanonicalLearnerMonolith.agda; " ++
        "for p in " ++
        "Exotic/ERL/Exploration/MR15Reachability.agda " ++
        "Exotic/ERL/Exploration/OpenESDyadic.agda " ++
        "Exotic/ERL/FullCoupled/NoisyNetCoupled.agda " ++
        "Exotic/ERL/FullCoupled/SparsemaxFlatDyadicBehavior.agda " ++
        "Exotic/ERL/FullCoupled/SparsemaxFlatDyadicBehavior_test.agda " ++
        "Exotic/ERL/FullCoupled/SparsemaxFlatDyadicSeparation.agda " ++
        "Exotic/ERL/FullCoupled/SparsemaxFlatDyadicSeparation_test.agda " ++
        "Exotic/ERL/FullCoupled/SharedActorCritic.agda " ++
        "Exotic/ERL/FullCoupled/SparsemaxActorVsCriticTheorem.agda " ++
        "Exotic/ERL/FullCoupled/SparsemaxActorVsCriticTheorem_test.agda " ++
        "Exotic/ERL/FullCoupled/SignReLUSemidirectCycleComposition.agda " ++
        "Exotic/ERL/FullCoupled/SignReLUSemidirectCycleComposition_test.agda " ++
        "Exotic/ERL/FullCoupled/ConnectedGRUSemidirectQSA.agda " ++
        "Exotic/ERL/FullCoupled/FrozenOrthogonalAttentionGRU.agda " ++
        "Exotic/ERL/FullCoupled/Int8SparsemaxLiteral.agda " ++
        "Exotic/econlib/RockPaperScissors.agda " ++
        "Exotic/econlib/RockPaperScissors_test.agda; " ++
        "do test ! -e \"$p\"; done; " ++
        "for token in softsign haarApply haarRow0 haarRow1 helmertApply " ++
        "SharedActorCritic SparsemaxActorVsCriticTheorem; " ++
        "do if git grep -n -I -- \"$token\" -- '*.agda' >/dev/null 2>&1; " ++
        "then echo \"ERROR: legacy token active: $token\"; exit 1; fi; done; " ++
        "echo canonical-component-audit=clean; " ++
        "echo retirement-policy=report-only-until-owner-is-confirmed",
    io.call_system(Command, Result, !IO),
    (
        Result = ok(0)
    ->
        true
    ;
        io.set_exit_status(1, !IO)
    ).

