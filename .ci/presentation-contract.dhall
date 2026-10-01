{ agdaModules =
    [ "FullCoupled.CanonicalLearnerMonolith"
    , "FullCoupled.TheoremsMonolith"
    ]
, graphGenerator = ".ci/mirth/agda_graph.mth"
, surfaceGenerator = ".ci/mirth/agda_to_elm.mth"
, elmManifest = ".ci/elm-application.dhall"
}
