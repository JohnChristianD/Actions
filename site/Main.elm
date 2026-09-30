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


type FileFilter
    = AllFiles
    | LearnerOnly
    | TheoremOnly


type alias Model =
    { query : String
    , fileFilter : FileFilter
    , selected : Maybe String
    }


type Msg
    = SetQuery String
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
    , fileFilter = AllFiles
    , selected = Graph.nodes |> List.head |> Maybe.map .id
    }


update : Msg -> Model -> Model
update msg model =
    case msg of
        SetQuery query ->
            let
                next =
                    { model | query = query }
            in
            keepVisibleSelection next

        SetFileFilter raw ->
            let
                next =
                    { model | fileFilter = fileFilterFromString raw }
            in
            keepVisibleSelection next

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
        (
ode ->
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
        |> List.filter (
ode -> node.id == nodeId)
        |> List.head


unique : List String -> List String
unique values =
    List.foldl
        (alue seen ->
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
        |> List.filter (edge -> edge.target == nodeId)
        |> List.map .source
        |> unique


outgoingIds : String -> List String
outgoingIds nodeId =
    Graph.edges
        |> List.filter (edge -> edge.source == nodeId)
        |> List.map .target
        |> unique


relationCount : String -> Int
relationCount nodeId =
    List.length (incomingIds nodeId) + List.length (outgoingIds nodeId)


view : Model -> Html Msg
view model =
    let
        visible =
            visibleNodes model
    in
    main_ [ HA.class "repository" ]
        [ h1 [] [ text "Actions" ]
        , p []
            [ text "Mechanically checked canonical recurrent-learner proof system with explicit Agda authority, theorem graph, execution mirrors, domain boundaries, and a pure-Elm presentation." ]
        , section [] [ h2 [] [ text "Authority and tree" ]
            , p []
                [ text "Exactly two tracked Agda authority files remain. The active tree has no Exotic namespace; .github is the only retained platform-convention directory without an application child." ]
            , ul [] (List.map codeItem
                [ "FullCoupled/CanonicalLearnerMonolith.agda"
                , "FullCoupled/TheoremsMonolith.agda"
                ])
            , p []
                [ text "Agda proof terms are authoritative. Mercury, Dhall, Mirth, Nix, SMT, Vehicle, JAX, and Elm support verification, orchestration, execution, discovery, or presentation." ]
            ]
        , section [] [ h2 [] [ text "L1 / 1-path norm / Tsallis-2 surface" ]
            , p []
                [ text "The formal surface restores the finite L1 row/weight definitions, the exact 1-path norm recurrence, the one-layer L1/path identity, the canonical zero-threshold hard/soft sparse derivation, and the exact rational Tsallis-2 extension. The Hidden Synergy paper's original near-sparsity definition is Shannon-entropy based; this repository keeps that analytic distinction explicit rather than relabeling Tsallis-2 as the paper definition." ]
            , ul [] (List.map codeItem
                [ "rowL1"
                , "weightL1"
                , "onePathVector"
                , "onePathNorm"
                , "rowL1OnesAbs"
                , "onePathOneLayer"
                , "CanonicalHardSparsityDegeneracyTheorem"
                , "generalTsallis2NearSparsity"
                , "generalTsallis2NearSparsity-zero"
                , "generalSupportSparsity"
                , "UniformSupportTsallisBoundary"
                ])
            ]
        , section [] [ h2 [] [ text "GRU left inverse, injectivity, and tail stability" ]
            , p []
                [ text "The canonical statistical encoding stores the original GRUState and decodes by first projection. The left inverse is proved first, then injectivity is derived. The separate convergence/identifiability theorem consumes exact conjugacy plus an eventually fixed feature tail." ]
            , ul [] (List.map codeItem
                [ "canonicalGRUStatisticalDecodeEncode"
                , "canonicalGRUStatisticalEncodeLeftInverse"
                , "leftInverse-implies-injective"
                , "canonicalGRUStatisticalEncodeInjective"
                , "GRUInjectiveTailStabilityConvergenceIdentifiabilityTheorem"
                ])
            ]
        , section [] [ h2 [] [ text "Canonical-learner Baird boundary" ]
            , p []
                [ text "There is no generic arbitrary-weight/arbitrary-update Baird theorem in the active surface. The surviving boundary is indexed by the concrete canonical learner K and s and carries its already-proven persistent-GRU iterate tail together with the explicit seven-state/eight-feature divergence witness." ]
            , ul [] (List.map codeItem
                [ "CanonicalLearnerBairdSevenStarBoundary K s"
                , "canonicalLearnerBairdSevenStar"
                , "seven states / eight features"
                , "behavior 6/7 versus 1/7"
                , "solid target"
                , "zero reward / 99-100 discount"
                , "persistent-GRU iterate tail"
                , "explicit divergence witness"
                ])
            ]
        , section [] [ h2 [] [ text "Physics, economics, and PPAD boundaries" ]
            , p []
                [ text "Physics and economics remain in the theorem monolith: Hodge-Maxwell/four-law semantic interfaces, GRU/physics transport, production, demand/supply, aggregate excess-demand structures, supporting-price and market-clearing witnesses, Walrasian interfaces, stationary/fixed-point closures, and economic composition." ]
            , p []
                [ text "The repository makes no PPAD-completeness claim. A real PPAD theorem would require a concrete total polynomial-size search relation, membership, size bounds, and a hardness reduction." ]
            ]
        , section [] [ h2 [] [ text "Dynamic Agda declaration graph" ]
            , p []
                [ text "Mirth generates the graph data directly from the two tracked Agda monoliths. Every discovered top-level declaration becomes a node; source-derived identifier references become directed edges. The complete relation dataset is retained in Elm, while this view shows the full incoming and outgoing neighborhood of the selected declaration." ]
            , p []
                [ text ("Declarations: "
                    ++ String.fromInt (List.length Graph.nodes)
                    ++ "  Relations: "
                    ++ String.fromInt (List.length Graph.edges)
                    ++ "  Visible declarations: "
                    ++ String.fromInt (List.length visible)
                    ++ "  Selected relations: "
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
                (List.map nodeButton (visibleNodes model))
            , graphView model
            , case model.selected of
                Just selected ->
                    relationLists selected

                Nothing ->
                    p [] [ text "Select a declaration to inspect all recorded relations." ]
            ]
        , section [] [ h2 [] [ text "JAX execution mirror" ]
            , p []
                [ text "tools/jax_reference.py is JAX-only at the third-party import boundary. The current mirror uses vmap, lax.scan, lax.associative_scan, lexsort, one-pass sparse-support prefix work, fixed-k top_k, exact int64 arithmetic, and the concrete GRU hidden-state update." ]
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
                , "JAXExecutionMirrorReproof"
                ])
            , p []
                [ text "Agda proves finite typed counterpart laws. It does not claim to prove the Python interpreter or JAX compiler." ]
            ]
        , section [] [ h2 [] [ text "Mirth, C99, and the presentation" ]
            , p []
                [ text "Mirth sources compile to C99 for fast-dirty synchronization and graph generation. The Pages application remains pure Elm; it does not execute Agda, JAX, Mirth, or Mercury at runtime." ]
            ]
        , section [] [ h2 [] [ text "CI contracts" ]
            , ul [] (List.map codeItem
                [ "exactly two tracked Agda monoliths"
                , "Agda 2.8.0 / stdlib 2.3"
                , "learner-to-theorem import direction"
                , "lock-safe concurrent Mirth predicates"
                , "source-derived Agda graph"
                , "canonical-learner Baird boundary"
                , "physics/economics semantic surfaces"
                , "Mercury theorem registry and purity"
                , "link-free Markdown outside Elm"
                , "pure Elm Pages compilation"
                , "pinned JAX execution and shape checks"
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
                        (index nodeId ->
                            { id = nodeId
                            , x = 160
                            , y = 120 + toFloat index * 52
                            }
                        )
                        incoming

                outgoingPositions =
                    List.indexedMap
                        (index nodeId ->
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
                    List.map (position -> edgeAndNode selectedPosition position) incomingPositions

                outgoingSvg =
                    List.map (position -> edgeAndNode selectedPosition position) outgoingPositions
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
                |> Maybe.map (
ode -> node.label)
                |> Maybe.withDefault position.id
    in
    S.g []
        [ S.line
            [ SA.x1 (String.fromFloat center.x)
            , SA.y1 (String.fromFloat center.y)
            , SA.x2 (String.fromFloat position.x)
            , SA.y2 (String.fromFloat position.y)
            , SA.stroke "#6b7280"
            , SA.strokeWidth "1.2"
            ]
            []
        , S.rect
            [ SA.x (String.fromFloat (position.x - 115))
            , SA.y (String.fromFloat (position.y - 16))
            , SA.width "230"
            , SA.height "32"
            , SA.rx "5"
            , SA.fill "#f4f4f4"
            , SA.stroke "#6b7280"
            ]
            [ S.title [] [ S.text (position.id) ] ]
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
                "#111827"

            else
                "#f4f4f4"

        textFill =
            if selected then
                "#ffffff"

            else
                "#111827"
    in
    S.g [ SE.onClick (SelectNode position.id) ]
        [ S.rect
            [ SA.x (String.fromFloat (position.x - 145))
            , SA.y (String.fromFloat (position.y - 20))
            , SA.width "290"
            , SA.height "40"
            , SA.rx "6"
            , SA.fill fill
            , SA.stroke "#111827"
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


relationLists : String -> Html Msg
relationLists selected =
    let
        incoming =
            incomingIds selected

        outgoing =
            outgoingIds selected
    in
    section []
        [ h2 [] [ text "Complete selected-node relations" ]
        , p [] [ text "Incoming references" ]
        , ul [] (List.map relationButton incoming)
        , p [] [ text "Outgoing references" ]
        , ul [] (List.map relationButton outgoing)
        ]


relationButton : String -> Html Msg
relationButton nodeId =
    button
        [ HA.type_ "button"
        , HE.onClick (SelectNode nodeId)
        , HA.class "graph-relation-button"
        ]
        [ code [] [ text nodeId ] ]


codeItem : String -> Html Msg
codeItem value =
    li [] [ code [] [ text value ] ]


linkItem : String -> String -> Html Msg
linkItem label url =
    li [] [ a [ HA.href url, HA.target "_blank", HA.title label ] [ text label ] ]
