module Main exposing (main)

import Browser
import Html exposing (Html, a, code, div, h1, h2, li, main_, p, pre, text, ul)
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
                    "https://github.com/JohnChristianD/Actions/blob/main/FullCoupled/CanonicalLearnerMonolith.agda"
                , link "Theorem monolith"
                    "https://github.com/JohnChristianD/Actions/blob/main/FullCoupled/TheoremsMonolith.agda"
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
                    [ text "Elm is presentation-only. It displays the fixed two-monolith inventory and defines no learner semantics or proof evidence." ]
                ]
            ]
        , h2 [] [ text "Agda modules" ]
        , ul [] (List.map moduleItem agdaModules)
        , h2 [] [ text "Topology" ]
        , pre []
            [ text """Agda --safe
     |
     +----> Mercury discovery / dependency graph
     |
     v
  Dhall presentation contract
     |
     v
  GitHub Pages / pure Elm presentation""" ]
        ]


panel : String -> List (Html Msg) -> Html Msg
panel heading children =
    div [ class "panel" ]
        (h2 [] [ text heading ] :: children)


moduleItem : String -> Html Msg
moduleItem value =
    li [] [ code [] [ text value ] ]


link : String -> String -> Html Msg
link label url =
    p [] [ a [ href url, target "_blank", title label ] [ text label ] ]


agdaModules : List String
agdaModules =
    [ "FullCoupled.CanonicalLearnerMonolith"
    , "FullCoupled.TheoremsMonolith"
    ]
