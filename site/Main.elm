module Main exposing (main)

import Browser
import GeneratedAgdaGraph as Graph
import Html exposing (Html, a, button, code, div, h1, h2, input, li, main_, option, p, section, select, span, text, ul)
import Html.Attributes as HA
import Html.Events as HE
import String
import Svg as S
import Svg.Attributes as SA
import Svg.Events as SE


-- Canonical display palette.
-- The perceptual derivation is defined by the repository's CAT02-LMS
-- transform; Elm receives only the resulting display tokens, so the Pages
-- runtime remains pure Elm and does not execute ImageMagick.
type alias CanonicalPalette =
    { background : String
    , surface : String
    , ink : String
    , mutedInk : String
    , accent : String
    , accentInk : String
    }

canonicalPalette : CanonicalPalette
canonicalPalette =
    { background = "#F7F7F4"
    , surface = "#FFFFFF"
    , ink = "#171717"
    , mutedInk = "#5A5A55"
    , accent = "#2F5D62"
    , accentInk = "#FFFFFF"
    }



type FileFilter
    = AllFiles
    | LearnerOnly
    | TheoremOnly


type alias Model =
    { query : String
    , relationQuery : String
    , fileFilter : FileFilter
    , selected : Maybe String
    }


type Msg
    = SetQuery String
    | SetRelationQuery String
    | SetFileFilter String
    | SelectNode String


main : Program () Model Msg
main =
    Browser.sandbox
        { init = init
        , update = update
        , view = view
        }


init : Model
init =
    { query = ""
    , relationQuery = ""
    , fileFilter = AllFiles
    , selected = Graph.nodes |> List.head |> Maybe.map .id
    }


update : Msg -> Model -> Model
update msg model =
    case msg of
        SetQuery query ->
            keepVisibleSelection { model | query = query }

        SetRelationQuery query ->
            { model | relationQuery = query }

        SetFileFilter raw ->
            keepVisibleSelection { model | fileFilter = fileFilterFromString raw }

        SelectNode nodeId ->
            { model | selected = Just nodeId }


fileFilterFromString : String -> FileFilter
fileFilterFromString raw =
    case raw of
        "learner" ->
            LearnerOnly

        "theorem" ->
            TheoremOnly

        _ ->
            AllFiles


keepVisibleSelection : Model -> Model
keepVisibleSelection model =
    let
        visible =
            visibleNodes model

        ids =
            List.map .id visible
    in
    case model.selected of
        Just selected ->
            if List.member selected ids then
                model

            else
                { model | selected = List.head ids |> Maybe.map .id }

        Nothing ->
            { model | selected = List.head ids |> Maybe.map .id }


visibleNodes : Model -> List Graph.Node
visibleNodes model =
    let
        query =
            String.toLower model.query
    in
    List.filter
        (\node ->
            sourceAllowed model.fileFilter node.source
                && (String.isEmpty query
                    || String.contains query (String.toLower node.label)
                    || String.contains query (String.toLower node.id)
                   )
        )
        Graph.nodes


sourceAllowed : FileFilter -> String -> Bool
sourceAllowed fileFilter source =
    case fileFilter of
        AllFiles ->
            True

        LearnerOnly ->
            source == "learner"

        TheoremOnly ->
            source == "theorem"


nodeForId : String -> Maybe Graph.Node
nodeForId nodeId =
    Graph.nodes
        |> List.filter (\node -> node.id == nodeId)
        |> List.head


unique : List String -> List String
unique values =
    List.foldl
        (\value seen ->
            if List.member value seen then
                seen

            else
                seen ++ [ value ]
        )
        []
        values


incomingIds : String -> List String
incomingIds nodeId =
    Graph.edges
        |> List.filter (\edge -> edge.target == nodeId)
        |> List.map .source
        |> unique


outgoingIds : String -> List String
outgoingIds nodeId =
    Graph.edges
        |> List.filter (\edge -> edge.source == nodeId)
        |> List.map .target
        |> unique


relationCount : String -> Int
relationCount nodeId =
    List.length (incomingIds nodeId) + List.length (outgoingIds nodeId)


relationMatches : String -> Graph.Edge -> Bool
relationMatches query edge =
    let
        needle =
            String.toLower query
    in
    String.isEmpty needle
        || String.contains needle (String.toLower edge.source)
        || String.contains needle (String.toLower edge.target)
        || String.contains needle (String.toLower edge.relation)


visibleEdges : Model -> List Graph.Edge
visibleEdges model =
    List.filter (relationMatches model.relationQuery) Graph.edges


view : Model -> Html Msg
view model =
    let
        visible =
            visibleNodes model

        filteredEdges =
            visibleEdges model
    in
    main_ [ HA.class "repository", HA.style "background-color" canonicalPalette.background, HA.style "color" canonicalPalette.ink ]
        [ h1 [] [ text "Actions" ]
        , p []
            [ text "A pure-Elm presentation of the current Agda source graph and theorem surface. Agda proof terms remain authoritative; the generated graph records source-level declaration relations." ]
        , section [] [ h2 [] [ text "Authority and active tree" ]
            , p []
                [ text "Exactly two tracked Agda authority files remain. The active tree has no Exotic namespace." ]
            , ul [] (List.map codeItem
                [ "FullCoupled/CanonicalLearnerMonolith.agda"
                , "FullCoupled/TheoremsMonolith.agda"
                ])
            , p []
                [ text "The learner is the source definition. The theorem monolith is its one-way derived-semantic consumer." ]
            ]
        , section [] [ h2 [] [ text "GRU left inverse, injectivity, and tail stability" ]
            , p []
                [ text "The statistical encoding stores the original GRU state, its decoder is first projection, and the accepted proof chain derives injectivity from the left inverse. Tail stability is separately lifted through full-learner iteration." ]
            , ul [] (List.map codeItem
                [ "canonicalGRUStatisticalDecodeEncode"
                , "canonicalGRUStatisticalEncodeLeftInverse"
                , "leftInverse-implies-injective"
                , "canonicalGRUStatisticalEncodeInjective"
                , "GRUInjectiveTailStabilityConvergenceIdentifiabilityTheorem"
                ])
            ]
        , section [] [ h2 [] [ text "Canonical-learner Baird witness" ]
            , p []
                [ text "The active Baird construction is tied to the canonical learner kernel/state and its already-proved persistent-GRU iterate tail. There is no generic Baird record." ]
            , ul [] (List.map codeItem
                [ "CanonicalLearnerBairdSevenStarWitness K s"
                , "canonicalLearnerBairdSevenStar"
                , "seven states / eight features"
                , "behavior 6/7 versus 1/7"
                , "solid target"
                , "zero reward / 99-100 discount"
                , "persistent-GRU iterate tail"
                , "explicit divergence witness"
                ])
            ]
        , section [] [ h2 [] [ text "Hidden-Synergy finite surface" ]
            , p []
                [ text "The finite L1, 1-path norm, zero-threshold hard/soft sparsity, and Tsallis-2 definitions and theorem chain remain active." ]
            , ul [] (List.map codeItem
                [ "rowL1"
                , "weightL1"
                , "onePathVector"
                , "onePathNorm"
                , "hiddenSynergy-one-layer-exact"
                , "CanonicalHardSparsityDegeneracyTheorem"
                , "generalTsallis2NearSparsity"
                , "generalSupportSparsity"
                , "UniformSupportTsallisBoundary"
                ])
            ]
        , section [] [ h2 [] [ text "Physics, economics, and PPAD boundary" ]
            , p []
                [ text "Physics and economics remain in the theorem monolith, including Hodge-Maxwell, GRU/physics transport, production, demand/supply, excess demand, market clearing, Walrasian interfaces, stationary/fixed-point closures, and economic composition." ]
            , p []
                [ text "No PPAD-completeness theorem is claimed. A real completeness proof still requires a total polynomial-size search relation, encoding bounds, membership, and a hardness reduction." ]
            ]
        , section [] [ h2 [] [ text "Complete Agda relation dataset" ]
            , p []
                [ text ("Generated declarations: "
                    ++ String.fromInt (List.length Graph.nodes)
                    ++ " | generated relations: "
                    ++ String.fromInt (List.length Graph.edges)
                    ++ " | visible declarations: "
                    ++ String.fromInt (List.length visible)
                    ++ " | selected-node relations: "
                    ++ (case model.selected of
                            Just nodeId ->
                                String.fromInt (relationCount nodeId)

                            Nothing ->
                                "0"
                       )
                ]
            , div [ HA.class "graph-controls" ]
                [ input
                    [ HA.placeholder "Filter declaration names or ids"
                    , HA.value model.query
                    , HE.onInput SetQuery
                    ]
                    []
                , select [ HA.value (filterString model.fileFilter), HE.onInput SetFileFilter ]
                    [ option [ HA.value "all" ] [ text "All Agda" ]
                    , option [ HA.value "learner" ] [ text "Learner monolith" ]
                    , option [ HA.value "theorem" ] [ text "Theorem monolith" ]
                    ]
                ]
            , div [ HA.class "graph-node-list" ]
                (List.map nodeButton visible)
            , graphView model
            , relationLists model
            , section []
                [ h2 [] [ text "All generated relations" ]
                , p []
                    [ text "This list is the complete generated edge set, filtered only by the optional relation search. Selecting an edge endpoint changes the focused graph." ]
                , input
                    [ HA.placeholder "Filter source, target, or relation"
                    , HA.value model.relationQuery
                    , HE.onInput SetRelationQuery
                    ]
                    []
                , p []
                    [ text ("Matching relations: " ++ String.fromInt (List.length filteredEdges)) ]
                , ul [] (List.map relationRecord filteredEdges)
                ]
            ]
        , section [] [ h2 [] [ text "JAX execution mirror" ]
            , p []
                [ text "The JAX boundary uses only JAX imports and native array algorithms. Every current executable kernel has a named Agda counterpart in JAXExecutionMirrorReproof." ]
            , ul [] (List.map codeItem
                [ "vmap_affine -> jaxVmapAffine"
                , "associative_prefix_sum -> jaxAssociativePrefixSum"
                , "recurrent_scan -> jaxRecurrentScan"
                , "lexicographic_score_order -> jaxLexicographicScoreOrder"
                , "sparse_support_size -> jaxSparseSupportSize"
                , "sparse_support_top_k -> jaxSparseSupportTopK"
                , "sparsemax_policy_index -> jaxSparsemaxPolicyIndex"
                , "l1_row -> jaxL1Row"
                , "l1_matrix -> jaxL1Matrix"
                , "one_path_norm -> jaxOnePathNorm"
                , "tsallis2_near_sparsity_fraction -> jaxTsallis2NearSparsityFraction"
                , "support_sparsity_fraction -> jaxSupportSparsityFraction"
                , "integer_layernorm_centered_numerators -> jaxIntegerLayerNormCenteredNumerators"
                , "integer_layernorm_radicand -> jaxIntegerLayerNormRadicand"
                , "batched_integer_layernorm_radicand -> jaxBatchedIntegerLayerNormRadicand"
                , "signed_gate -> jaxSignedGate"
                , "gru_hidden_step -> jaxGRUHiddenStep"
                , "batched_gru_hidden_step -> jaxBatchedGRUHiddenStep"
                , "jitted_scan_sum -> jaxJittedScanSum"
                ])
            ]
        , section [] [ h2 [] [ text "Mirth and pure Elm" ]
            , p []
                [ text "Mirth generates synchronization and graph scripts before compilation. The Pages application itself remains pure Elm and does not execute Agda, Mirth, Mercury, JAX, SMT, or Vehicle at runtime." ]
            ]
        , section [] [ h2 [] [ text "Source navigation" ]
            , ul []
                [ linkItem "Canonical learner" "https://github.com/JohnChristianD/Actions/blob/main/FullCoupled/CanonicalLearnerMonolith.agda"
                , linkItem "Theorem monolith" "https://github.com/JohnChristianD/Actions/blob/main/FullCoupled/TheoremsMonolith.agda"
                , linkItem "JAX reference" "https://github.com/JohnChristianD/Actions/blob/main/tools/jax_reference.py"
                , linkItem "CI contracts" "https://github.com/JohnChristianD/Actions/tree/main/.ci"
                , linkItem "Repository" "https://github.com/JohnChristianD/Actions"
                ]
            ]
        ]


filterString : FileFilter -> String
filterString fileFilter =
    case fileFilter of
        AllFiles ->
            "all"

        LearnerOnly ->
            "learner"

        TheoremOnly ->
            "theorem"


nodeButton : Graph.Node -> Html Msg
nodeButton node =
    button
        [ HA.type_ "button"
        , HE.onClick (SelectNode node.id)
        , HA.class "graph-node-button"
        ]
        [ code [] [ text (node.source ++ ": " ++ node.label) ] ]


graphView : Model -> Html Msg
graphView model =
    case model.selected |> Maybe.andThen nodeForId of
        Nothing ->
            p [] [ text "No selected declaration." ]

        Just selected ->
            let
                incoming =
                    incomingIds selected.id

                outgoing =
                    outgoingIds selected.id

                incomingPositions =
                    List.indexedMap
                        (\index nodeId ->
                            { id = nodeId
                            , x = 160
                            , y = 120 + toFloat index * 52
                            }
                        )
                        incoming

                outgoingPositions =
                    List.indexedMap
                        (\index nodeId ->
                            { id = nodeId
                            , x = 840
                            , y = 120 + toFloat index * 52
                            }
                        )
                        outgoing

                selectedPosition =
                    { id = selected.id, x = 500, y = 62 }

                maxRows =
                    max (List.length incoming) (List.length outgoing)

                height =
                    toFloat (max 1 maxRows) * 52 + 160

                selectedSvg =
                    svgNode selectedPosition True

                incomingSvg =
                    List.map (edgeAndNode selectedPosition) incomingPositions

                outgoingSvg =
                    List.map (edgeAndNode selectedPosition) outgoingPositions
            in
            div [ HA.class "graph-canvas" ]
                [ S.svg
                    [ SA.viewBox ("0 0 1000 " ++ String.fromFloat height)
                    , SA.width "100%"
                    , SA.height (String.fromFloat height)
                    ]
                    (selectedSvg :: incomingSvg ++ outgoingSvg)
                ]


type alias Position =
    { id : String
    , x : Float
    , y : Float
    }


edgeAndNode : Position -> Position -> S.Svg Msg
edgeAndNode center position =
    let
        label =
            nodeForId position.id
                |> Maybe.map (\node -> node.label)
                |> Maybe.withDefault position.id
    in
    S.g []
        [ S.line
            [ SA.x1 (String.fromFloat center.x)
            , SA.y1 (String.fromFloat center.y)
            , SA.x2 (String.fromFloat position.x)
            , SA.y2 (String.fromFloat position.y)
            ]
            []
        , S.rect
            [ SA.x (String.fromFloat (position.x - 115))
            , SA.y (String.fromFloat (position.y - 16))
            , SA.width "230"
            , SA.height "32"
            , SA.rx "5"
            ]
            [ S.title [] [ S.text position.id ] ]
        , S.text_
            [ SA.x (String.fromFloat position.x)
            , SA.y (String.fromFloat (position.y + 5))
            , SA.textAnchor "middle"
            , SA.fontSize "11"
            ]
            [ S.text (String.left 36 label) ]
        ]


svgNode : Position -> Bool -> S.Svg Msg
svgNode position selected =
    let
        node =
            nodeForId position.id

        label =
            node |> Maybe.map .label |> Maybe.withDefault position.id

        fill =
            if selected then
                canonicalPalette.accent

            else
                canonicalPalette.surface

        textFill =
            if selected then
                canonicalPalette.accentInk

            else
                canonicalPalette.ink
    in
    S.g [ SE.onClick (SelectNode position.id) ]
        [ S.rect
            [ SA.x (String.fromFloat (position.x - 145))
            , SA.y (String.fromFloat (position.y - 20))
            , SA.width "290"
            , SA.height "40"
            , SA.rx "6"
            ]
            []
        , S.text_
            [ SA.x (String.fromFloat position.x)
            , SA.y (String.fromFloat (position.y + 6))
            , SA.textAnchor "middle"
            , SA.fontSize "13"
            , SA.fill textFill
            ]
            [ S.text (String.left 44 label) ]
        ]


relationLists : Model -> Html Msg
relationLists model =
    case model.selected of
        Nothing ->
            p [] [ text "Select a declaration to inspect its complete incoming and outgoing relations." ]

        Just selected ->
            section []
                [ h2 [] [ text "Selected declaration relations" ]
                , p [] [ text "Incoming references" ]
                , ul [] (List.map relationButton (incomingIds selected))
                , p [] [ text "Outgoing references" ]
                , ul [] (List.map relationButton (outgoingIds selected))
                ]


relationRecord : Graph.Edge -> Html Msg
relationRecord edge =
    li []
        [ button
            [ HA.type_ "button"
            , HE.onClick (SelectNode edge.source)
            ]
            [ code [] [ text edge.source ] ]
        , span [] [ text ("  --" ++ edge.relation ++ "-->  ") ]
        , button
            [ HA.type_ "button"
            , HE.onClick (SelectNode edge.target)
            ]
            [ code [] [ text edge.target ] ]
        ]


relationButton : String -> Html Msg
relationButton nodeId =
    button
        [ HA.type_ "button"
        , HE.onClick (SelectNode nodeId)
        ]
        [ code [] [ text nodeId ] ]


codeItem : String -> Html Msg
codeItem value =
    li [] [ code [] [ text value ] ]


linkItem : String -> String -> Html Msg
linkItem label url =
    li [] [ a [ HA.href url, HA.target "_blank", HA.title label ] [ text label ] ]
