{ agdaModules =
    [ "FullCoupled.CanonicalLearnerMonolith"
    , "FullCoupled.TheoremsMonolith"
    ]
, graphGenerator = ".ci/mirth/agda_graph.mth"
, surfaceGenerator = ".ci/mirth/agda_to_elm.mth"
, elmManifest = ".ci/elm-application.dhall"
, theoremRoots =
    [ "BrouwerMixedNashExistence"
    , "nashEveryFiniteGameViaBrouwer"
    , "brouwerMixedNashFixedPointBridge"
    , "finiteMixedNash-brouwer-egraph-astar-proof"
    , "finiteMixedNash-egraph-astar-convergence"
    , "finiteMixedNash-egraph-astar-eventualStationarity"
    , "finiteMixedNash-cycle-transport"
    , "finiteMixedNash-from-GRU-tail"
    , "GRUInjectiveTailStabilityConvergenceIdentifiabilityTheorem"
    , "EGraphAStarFiniteRankConvergenceWitness"
    , "eGraphAStarConvergenceSemanticClosure"
    ]
}
