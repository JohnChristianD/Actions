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
            [ text "Canonical recurrent-learner proof surface, explicit semantic boundaries, and a pure Elm presentation." ]
        , section [] [ h2 [] [ text "Authority" ]
            , p []
                [ text "Agda is the proof authority. Mercury discovers declaration and graph structure. Dhall defines CI contracts. Nix composes pinned environments. Mirth synchronizes generated checks. Elm only presents the repository." ]
            , ul [] (List.map codeItem
                [ "FullCoupled/CanonicalLearnerMonolith.agda"
                , "FullCoupled/TheoremsMonolith.agda"
                ])
            ]
        , section [] [ h2 [] [ text "Canonical learner" ]
            , p []
                [ text "The learner monolith defines the actual FullLearnerState, GRUState, optimizer/count/control state, canonicalFullStep, and iterateCanonical." ]
            , p []
                [ text "Persistent GRU matrix/noise/control state is preserved across each full-learner iterate. The count component advances by one, and the concrete learner therefore has no one-step fixed point." ]
            ]
        , section [] [ h2 [] [ text "GRU left inverse and injectivity" ]
            , p []
                [ text "The canonical statistical encoding contains the original GRUState. The first-projection decoder is a proved left inverse, and injectivity is derived from the general leftInverse-implies-injective theorem." ]
            , p []
                [ code [] [ text "canonicalGRUStatisticalDecodeEncode" ]
                , text " -> "
                , code [] [ text "leftInverse-implies-injective" ]
                , text " -> "
                , code [] [ text "canonicalGRUStatisticalEncodeInjective" ]
                ]
            , p []
                [ text "This proves encoding injectivity, not blanket injectivity of gruStep." ]
            ]
        , section [] [ h2 [] [ text "Generic convergence kernel" ]
            , p []
                [ text "The reusable convergence theorem consumes an injective encoding, exact feature/state step conjugacy, and an eventually fixed feature tail. It derives a tail-fixed source state, eventual stationarity, and identifiability." ]
            ]
        , section [] [ h2 [] [ text "Canonical-learner Baird boundary" ]
            , p []
                [ text "Generic Baird records are pruned. The surviving package is indexed by the actual canonical learner kernel and learner state." ]
            , ul [] (List.map codeItem
                [ "CanonicalLearnerBairdSevenStarBoundary"
                , "canonicalLearnerBairdSevenStar"
                , "seven states / eight features"
                , "behavior 6/7 versus 1/7"
                , "solid target policy"
                , "zero reward / gamma 0.99"
                ])
            , p []
                [ text "The package carries the already-proven persistent-GRU tail invariant. Its numerical divergence field remains an explicit witness." ]
            ]
        , section [] [ h2 [] [ text "Physics and economics" ]
            , p []
                [ text "The theorem monolith still contains Hodge-Maxwell and four-law semantic surfaces, GRU/physics transport, production, demand and supply, aggregate excess demand, supporting-price and market-clearing witnesses, Walrasian interfaces, and stationary/fixed-point closures." ]
            , p []
                [ text "Injectivity and convergence do not manufacture those correspondences; their transport and interpretation premises remain explicit." ]
            ]
        , section [] [ h2 [] [ text "PPAD and JAX" ]
            , p []
                [ text "No PPAD-completeness theorem is claimed. A valid result needs a search relation, polynomial encoding and size bounds, membership, totality, and an explicit hardness reduction." ]
            , p []
                [ text "The executable JAX mirror is deliberately finite and concrete rather than a claim about the whole JAX API." ]
            , ul [] (List.map codeItem
                [ "tools/jax_reference.py"
                , "jax.vmap"
                , "jax.lax.scan"
                , "jax.lax.associative_scan"
                , "jax.numpy.lexsort"
                , "jax.lax.top_k"
                , "integer LayerNorm / int64"
                , "concrete GRU hidden-state step"
                ])
            , p []
                [ text "The JAX workflow pins only the JAX package and validates the mirror through jax.jit and jax.eval_shape. Agda remains the proof authority." ]
            ]
        , section [] [ h2 [] [ text "Mirth, Elm, and CI" ]
            , p []
                [ text "Mirth synchronizes the exact common Agda import block and checks the presentation surface. The Elm program is pure and presentation-only. Mermaid is not a runtime dependency." ]
            , p []
                [ text "CI checks canonical Agda safety, theorem integration, import direction, the canonical Baird boundary, Mercury graph closure, Mirth synchronization, pure Elm compilation, Pages verification, and pinned Nix composition." ]
            ]
        , section [] [ h2 [] [ text "Source navigation" ]
            , ul []
                [ linkItem "Canonical learner" "https://github.com/JohnChristianD/Actions/blob/main/FullCoupled/CanonicalLearnerMonolith.agda"
                , linkItem "Theorem monolith" "https://github.com/JohnChristianD/Actions/blob/main/FullCoupled/TheoremsMonolith.agda"
                , linkItem "JAX reference" "https://github.com/JohnChristianD/Actions/blob/main/tools/jax_reference.py"
                , linkItem "JAX workflow" "https://github.com/JohnChristianD/Actions/blob/main/.github/workflows/jax-reference.yml"
                , linkItem "CI contracts" "https://github.com/JohnChristianD/Actions/tree/main/.ci"
                , linkItem "Repository root" "https://github.com/JohnChristianD/Actions"
                ]
            ]
        ]


codeItem : String -> Html Msg
codeItem value =
    li [] [ code [] [ text value ] ]


linkItem : String -> String -> Html Msg
linkItem label url =
    li [] [ a [ href url, target "_blank", title label ] [ text label ] ]
