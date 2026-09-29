module Main exposing (main)

import Browser
import Html exposing (Html, a, code, div, h1, h2, main_, p, pre, text)
import Html.Attributes exposing (class, href, target, title)


type alias Model =
    {}


type Msg
    = NoOp


main : Program () Model Msg
main =
    Browser.sandbox
        { init = \_ -> {}
        , update = \_ model -> model
        , view = view
        }


view : Model -> Html Msg
view _ =
    main_ []
        [ h1 [] [ text "Actions" ]
        , p []
            [ text "Pure Elm presentation surface for the repository proof and dependency topology." ]
        , div [ class "grid" ]
            [ panel "Proof authority"
                [ p []
                    [ text "Agda "
                    , code [] [ text "--safe" ]
                    , text " is the only semantic and proof authority."
                    ]
                , link "Canonical learner"
                    "https://github.com/JohnChristianD/Actions/blob/main/Exotic/ERL/FullCoupled/CanonicalLearnerMonolith.agda"
                , link "Theorem monolith"
                    "https://github.com/JohnChristianD/Actions/blob/main/Exotic/ERL/FullCoupled/TheoremsMonolith.agda"
                ]
            , panel "Discovery"
                [ p []
                    [ text "Mercury performs declaration extraction, dependency discovery, and graph processing." ]
                , link "Discovery sources"
                    "https://github.com/JohnChristianD/Actions/tree/main/.ci/discovery"
                ]
            , panel "Reproducibility"
                [ p []
                    [ text "Nix supplies the pinned environment used by local and GitHub Actions verification." ]
                , link "flake.nix"
                    "https://github.com/JohnChristianD/Actions/blob/main/flake.nix"
                ]
            , panel "Boundary"
                [ p []
                    [ text "The Elm program is presentation-only. It defines no learner semantics and no proof evidence." ]
                ]
            ]
        , h2 [] [ text "Topology" ]
        , pre []
            [ text """Agda --safe
   |
   v
proof authority
   |
   +--> Mercury discovery / dependency graph
   |
   +--> Nix reproducible execution
   |
   +--> GitHub Pages / pure Elm presentation""" ]
        ]


panel : String -> List (Html Msg) -> Html Msg
panel heading children =
    div [ class "panel" ]
        (h2 [] [ text heading ] :: children)


link : String -> String -> Html Msg
link label url =
    p [] [ a [ href url, target "_blank", title label ] [ text label ] ]
