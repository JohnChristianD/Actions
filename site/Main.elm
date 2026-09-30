module Main exposing (main)

import Browser
import Html exposing (Html, a, code, h1, h2, li, main_, p, section, text, ul)
import Html.Attributes exposing (class, href, target, title)


type alias Model =
    {}


type Msg
    = NoOp


main : Program () Model Msg
main =
    Browser.sandbox
        { init = {}
        , update = \_ model -> model
        , view = view
        }


view : Model -> Html Msg
view _ =
    main_ [ class "repository" ]
        [ h1 [] [ text "Actions" ]
        , p []
            [ text "Mechanically checked canonical recurrent-learner proof system with explicit execution, automation, graph, economics, physics, and presentation boundaries." ]
        , section [] [ h2 [] [ text "Authority and tree" ]
            , p []
                [ text "Exactly two tracked Agda authority files remain. The active tree has no Exotic namespace; .github is the only retained platform-convention directory without an application child." ]
            , ul [] (List.map codeItem
                [ "FullCoupled/CanonicalLearnerMonolith.agda"
                , "FullCoupled/TheoremsMonolith.agda"
                ])
            , p []
                [ text "Agda proof terms are authoritative. Mercury, Dhall, Nix, Mirth, SMT, Vehicle, JAX, and Elm support verification, orchestration, execution, discovery, or presentation." ]
            ]
        , section [] [ h2 [] [ text "Canonical learner" ]
            , p []
                [ text "The learner monolith owns GRUState, FullLearnerState, optimizer/count/control state, sparse policy readout, canonicalFullStep, and iterateCanonical." ]
            , ul [] (List.map codeItem
                [ "gruStep"
                , "persistentGRU"
                , "persistent-preservation"
                , "integerLayerNormCenteredNumerators"
                , "integerLayerNormRadicand"
                , "scoreList / sortScores"
                , "topCodes / searchSupport / supportSize"
                , "sparsemaxWeight / selectPositive / sparsemaxPolicy"
                ])
            , p []
                [ text "The persistent matrix/noise/control GRU tail is invariant under each GRU step and is carried through full-learner iteration." ]
            ]
        , section [] [ h2 [] [ text "GRU left inverse and injectivity" ]
            , p []
                [ text "The canonical statistical observation stores the original GRUState and decodes by first projection." ]
            , ul [] (List.map codeItem
                [ "canonicalGRUStatisticalDecodeEncode"
                , "canonicalGRUStatisticalEncodeLeftInverse"
                , "leftInverse-implies-injective"
                , "canonicalGRUStatisticalEncodeInjective"
                , "CanonicalGRUStatisticalInjectivityTheorem"
                ])
            , p []
                [ text "This proves injectivity of the observation encoding. It does not assert injectivity of gruStep." ]
            ]
        , section [] [ h2 [] [ text "Tail stability and identifiability" ]
            , p []
                [ text "GRUInjectiveTailStabilityConvergenceIdentifiabilityTheorem consumes three explicit premises: injective encoding, exact state/feature step conjugacy, and an eventually fixed feature tail. It derives tail-fixed source state, eventual stationarity, and identifiability." ]
            ]
        , section [] [ h2 [] [ text "Canonical-learner Baird boundary" ]
            , p []
                [ text "Generic arbitrary-weight/arbitrary-update Baird records are pruned. The surviving boundary is indexed by the actual canonical learner kernel and actual learner state." ]
            , ul [] (List.map codeItem
                [ "CanonicalLearnerBairdSevenStarBoundary K s"
                , "canonicalLearnerBairdSevenStar"
                , "seven states / eight features"
                , "behavior 6/7 versus 1/7"
                , "solid target"
                , "zero reward / 99-100 discount"
                , "already-proved persistent-GRU iterate tail"
                , "explicit divergence witness"
                ])
            ]
        , section [] [ h2 [] [ text "Physics and economics" ]
            , p []
                [ text "Physics and economics remain in the theorem monolith. The active surface includes Hodge-Maxwell and four-law semantic interfaces, GRU/physics transport, production, demand/supply, aggregate excess demand, supporting-price and market-clearing witnesses, Walrasian interfaces, stationary/fixed-point closures, and economic composition." ]
            , p []
                [ text "Redundant wrapper endpoints were pruned without removing their underlying physics or economics. Generic GRU injectivity/convergence does not fabricate those domain correspondences." ]
            ]
        , section [] [ h2 [] [ text "PPAD boundary" ]
            , p []
                [ text "No PPAD-completeness theorem is claimed. A real result needs a concrete total polynomial-size search relation, PPAD membership, size bounds, and an explicit hardness reduction." ]
            ]
        , section [] [ h2 [] [ text "Data-structure choices" ]
            , ul [] (List.map codeItem
                [ "List = concrete finite ordered sequence"
                , "Monoid = algebraic laws on a carrier"
                , "Set = propositions, predicates, and relations"
                , "Monad = effect/state boundary"
                , "Dict = not justified by current theorem obligations"
                ])
            , p []
                [ text "A vector or Fin-indexed sequence becomes relevant only when length must be proof-relevant." ]
            ]
        , section [] [ h2 [] [ text "JAX execution mirror" ]
            , p []
                [ text "tools/jax_reference.py is JAX-only at the third-party import boundary. It uses JAX vmap, lax.scan, lax.associative_scan, jnp.lexsort, one-pass sparse-support prefix work, fixed-k lax.top_k, exact int64 arithmetic, and the concrete GRU hidden-state update." ]
            , ul [] (List.map codeItem
                [ "vmap_affine -> jaxVmapAffine"
                , "associative_prefix_sum -> jaxAssociativePrefixSum"
                , "recurrent_scan -> jaxRecurrentScan"
                , "lexicographic_score_order -> jaxLexicographicScoreOrder"
                , "sparse_support_size -> jaxSparseSupportSize"
                , "sparse_support_top_k -> jaxSparseSupportTopK"
                , "sparsemax_policy_index -> jaxSparsemaxPolicyIndex"
                , "integer_layernorm_centered_numerators -> jaxIntegerLayerNormCenteredNumerators"
                , "integer_layernorm_radicand -> jaxIntegerLayerNormRadicand"
                , "batched_integer_layernorm_radicand -> jaxBatchedIntegerLayerNormRadicand"
                , "signed_gate -> jaxSignedGate"
                , "gru_hidden_step -> jaxGRUHiddenStep"
                , "batched_gru_hidden_step -> jaxBatchedGRUHiddenStep"
                , "jitted_scan_sum -> jaxJittedScanSum"
                , "JAXExecutionMirrorReproof"
                ])
            , p []
                [ text "The Agda counterparts are finite typed computations and equality proofs. They do not claim that Agda has proved the Python interpreter or JAX compiler." ]
            ]
        , section [] [ h2 [] [ text "Python boundary" ]
            , p []
                [ text "Python is isolated to the dedicated JAX workflow because JAX is a Python package. The Nix shell and non-JAX CI helpers do not carry Python." ]
            ]
        , section [] [ h2 [] [ text "Mirth, C99, Nix, and Elm" ]
            , p []
                [ text "Mirth sources compile to C99 for fast-dirty synchronization and presentation generation. Nix composes the pinned environment; it is not described as a replacement for C99." ]
            , p []
                [ text "The Pages application is pure Elm. Mermaid is not a runtime dependency, and the Elm program does not execute Agda, JAX, Mirth, or Mercury." ]
            ]
        , section [] [ h2 [] [ text "CI contracts" ]
            , ul [] (List.map codeItem
                [ "exactly two tracked Agda monoliths"
                , "Agda 2.8.0 / stdlib 2.3"
                , "learner-to-theorem import direction"
                , "GRU left-inverse and injectivity surface"
                , "canonical-learner Baird boundary"
                , "physics/economics semantic surfaces"
                , "Mercury theorem registry and purity"
                , "Mirth import and ASCII synchronization"
                , "link-free Markdown outside Elm"
                , "pure Elm Pages compilation"
                , "pinned JAX execution and shape checks"
                , "pinned Nix composition"
                ])
            ]
        , section [] [ h2 [] [ text "Source navigation" ]
            , ul []
                [ linkItem "Canonical learner" "https://github.com/JohnChristianD/Actions/blob/main/FullCoupled/CanonicalLearnerMonolith.agda"
                , linkItem "Theorem monolith" "https://github.com/JohnChristianD/Actions/blob/main/FullCoupled/TheoremsMonolith.agda"
                , linkItem "JAX reference" "https://github.com/JohnChristianD/Actions/blob/main/tools/jax_reference.py"
                , linkItem "JAX workflow" "https://github.com/JohnChristianD/Actions/blob/main/.github/workflows/jax-reference.yml"
                , linkItem "CI contracts" "https://github.com/JohnChristianD/Actions/tree/main/.ci"
                , linkItem "Repository" "https://github.com/JohnChristianD/Actions"
                ]
            ]
        ]


codeItem : String -> Html Msg
codeItem value =
    li [] [ code [] [ text value ] ]


linkItem : String -> String -> Html Msg
linkItem label url =
    li [] [ a [ href url, target "_blank", title label ] [ text label ] ]
