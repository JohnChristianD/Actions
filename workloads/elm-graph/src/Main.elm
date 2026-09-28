module Main exposing (main)


import Browser
import GeneratedGraph
import Graph exposing (Edge, Graph, Node)
import Html exposing (Html, div, h1, p, text)
import Html.Attributes as HtmlAttr
import Html.Events as HtmlEvents
import Svg
import Svg.Attributes as SvgAttr
import Svg.Events as SvgEvents


type alias Model =
    { graph : Graph
    , selected : Maybe String
    }


type Msg
    = Select String
    | ClearSelection


main : Program () Model Msg
main =
    Browser.sandbox
        { init =
            { graph = GeneratedGraph.graph
            , selected = Nothing
            }
        , update = update
        , view = view
        }


update : Msg -> Model -> Model
update msg model =
    case msg of
        Select nodeId ->
            { model | selected = Just nodeId }

        ClearSelection ->
            { model | selected = Nothing }


view : Model -> Html Msg
view model =
    let
        selectedNode =
            model.selected
                |> Maybe.andThen (findNode model.graph.nodes)
    in
    div
        [ HtmlAttr.style "font-family" "system-ui, sans-serif"
        , HtmlAttr.style "margin" "0"
        , HtmlAttr.style "padding" "24px"
        ]
        [ h1 [] [ text model.graph.title ]
        , p []
            [ text "Presentation-only graph view. Semantic meaning remains upstream." ]
        , Svg.svg
            [ SvgAttr.width "100%"
            , SvgAttr.viewBox "0 0 1200 700"
            , SvgAttr.attribute "role" "img"
            ]
            (List.map (viewEdge model.graph.nodes) model.graph.edges
                ++ List.map (viewNode model.selected) model.graph.nodes
            )
        , viewSelection selectedNode
        ]


viewEdge : List Node -> Edge -> Svg.Svg Msg
viewEdge nodes edge =
    case ( findNode nodes edge.source, findNode nodes edge.target ) of
        ( Just source, Just target ) ->
            Svg.g
                []
                [ Svg.line
                    [ SvgAttr.x1 (String.fromFloat source.x)
                    , SvgAttr.y1 (String.fromFloat source.y)
                    , SvgAttr.x2 (String.fromFloat target.x)
                    , SvgAttr.y2 (String.fromFloat target.y)
                    , SvgAttr.stroke "#94a3b8"
                    , SvgAttr.strokeWidth "2"
                    ]
                    []
                , Svg.text_
                    [ SvgAttr.x (String.fromFloat ((source.x + target.x) / 2))
                    , SvgAttr.y (String.fromFloat ((source.y + target.y) / 2 - 8))
                    , SvgAttr.fontSize "14"
                    , SvgAttr.textAnchor "middle"
                    , SvgAttr.fill "#475569"
                    ]
                    [ Svg.text edge.label ]
                ]

        _ ->
            Svg.g [] []


viewNode : Maybe String -> Node -> Svg.Svg Msg
viewNode selected node =
    let
        isSelected =
            selected == Just node.id

        radius =
            if isSelected then
                "16"
            else
                "12"

        strokeWidth =
            if isSelected then
                "4"
            else
                "2"
    in
    Svg.g
        [ SvgEvents.onClick (Select node.id) ]
        [ Svg.circle
            [ SvgAttr.cx (String.fromFloat node.x)
            , SvgAttr.cy (String.fromFloat node.y)
            , SvgAttr.r radius
            , SvgAttr.fill (statusFill node.status)
            , SvgAttr.stroke "#0f172a"
            , SvgAttr.strokeWidth strokeWidth
            ]
            []
        , Svg.text_
            [ SvgAttr.x (String.fromFloat node.x)
            , SvgAttr.y (String.fromFloat (node.y + 42))
            , SvgAttr.textAnchor "middle"
            , SvgAttr.fontSize "16"
            , SvgAttr.fill "#0f172a"
            ]
            [ Svg.text node.label ]
        , Svg.text_
            [ SvgAttr.x (String.fromFloat node.x)
            , SvgAttr.y (String.fromFloat (node.y + 60))
            , SvgAttr.textAnchor "middle"
            , SvgAttr.fontSize "12"
            , SvgAttr.fill "#64748b"
            ]
            [ Svg.text node.status ]
        ]


viewSelection : Maybe Node -> Html Msg
viewSelection selectedNode =
    case selectedNode of
        Nothing ->
            p [] [ text "Select a node for details." ]

        Just node ->
            div
                [ HtmlAttr.style "margin-top" "18px"
                , HtmlAttr.style "padding" "12px"
                , HtmlAttr.style "border" "1px solid #cbd5e1"
                ]
                [ p [] [ text ("Node: " ++ node.label) ]
                , p [] [ text ("Status: " ++ node.status) ]
                , p [] [ text ("Id: " ++ node.id) ]
                , Html.button
                    [ HtmlEvents.onClick ClearSelection ]
                    [ text "Clear selection" ]
                ]


statusFill : String -> String
statusFill status =
    case status of
        "PROVED" ->
            "#bbf7d0"

        "CONDITIONAL" ->
            "#fde68a"

        "FRONTIER" ->
            "#bfdbfe"

        "BLOCKED-BY-COUNTEREXAMPLE" ->
            "#fecaca"

        _ ->
            "#e2e8f0"


findNode : List Node -> String -> Maybe Node
findNode nodes nodeId =
    case nodes of
        [] ->
            Nothing

        node :: rest ->
            if node.id == nodeId then
                Just node
            else
                findNode rest nodeId
