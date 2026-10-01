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


-- Dynamic perceptual palette.
-- Palette candidates are derived from the generated Mirth graph cardinalities.
-- Display encoding happens only after the maximin selection in the custom
-- CAT02-LMS-derived perceptual coordinate space.
type alias DisplayColor =
    { r : Float
    , g : Float
    , b : Float
    }


type alias PerceptualColor =
    { display : DisplayColor
    , id : Int
    , lmsL : Float
    , lmsM : Float
    , lmsS : Float
    , opponentL : Float
    , opponentA : Float
    , opponentB : Float
    }


type alias DisplayPalette =
    { background : String
    , surface : String
    , ink : String
    , mutedInk : String
    , accent : String
    , accentInk : String
    }


paletteSeed : Int
paletteSeed =
    List.length Graph.nodes * 31 + List.length Graph.edges * 17


clamp01 : Float -> Float
clamp01 value =
    max 0 (min 1 value)


displayLuminosity : DisplayColor -> Float
displayLuminosity color =
    0.2126 * color.r + 0.7152 * color.g + 0.0722 * color.b


dynamicDisplayCandidate : Int -> DisplayColor
dynamicDisplayCandidate index =
    let
        seed =
            toFloat (paletteSeed + index * 37)

        r =
            0.04 + 0.92 * abs (sin (seed * 0.071))

        g =
            0.04 + 0.92 * abs (sin (seed * 0.113 + 1.7))

        b =
            0.04 + 0.92 * abs (sin (seed * 0.173 + 3.1))
    in
    { r = clamp01 r
    , g = clamp01 g
    , b = clamp01 b
    }


cat02Lms : DisplayColor -> ( Float, Float, Float )
cat02Lms color =
    ( 0.7328 * color.r + 0.4296 * color.g - 0.1624 * color.b
    , -0.7036 * color.r + 1.6975 * color.g + 0.0061 * color.b
    , 0.0030 * color.r + 0.0136 * color.g + 0.9834 * color.b
    )


scaledCat02Lms : DisplayColor -> ( Float, Float, Float )
scaledCat02Lms color =
    let
        ( l, m, s ) =
            cat02Lms color
    in
    ( 0.608191 * l
    , 0.557623 * m
    , 0.531035 * s
    )


newtonRootStep : Float -> Float -> Float
newtonRootStep magnitude current =
    let
        a =
            0.01

        b =
            0.01

        y2 =
            current * current

        y3 =
            y2 * current

        y4 =
            y2 * y2

        polynomial =
            y4 * current + a * y3 + b * current - magnitude

        derivative =
            5 * y4 + 3 * a * y2 + b
    in
    current - polynomial / derivative


newtonRoot : Float -> Float
newtonRoot value =
    let
        magnitude =
            abs value

        initial =
            if magnitude == 0 then
                0

            else
                exp (0.2 * log magnitude)

        step current remaining =
            if remaining == 0 then
                current

            else
                step
                    (newtonRootStep magnitude current)
                    (remaining - 1)
    in
    if magnitude == 0 then
        0

    else
        step initial 4


customPerceptualChannel : Float -> Float
customPerceptualChannel value =
    let
        magnitude =
            newtonRoot value
    in
    if value < 0 then
        -magnitude

    else
        magnitude


customPerceptualColor : Int -> DisplayColor -> PerceptualColor
customPerceptualColor id display =
    let
        ( l0, m0, s0 ) =
            scaledCat02Lms display

        l =
            customPerceptualChannel l0

        m =
            customPerceptualChannel m0

        s =
            customPerceptualChannel s0
    in
    { display = display
    , id = id
    , lmsL = l
    , lmsM = m
    , lmsS = s
    , opponentL = 0.577350 * l + 0.577350 * m + 0.577350 * s
    , opponentA = 0.707107 * l - 0.707107 * m
    , opponentB = 0.408248 * l + 0.408248 * m - 0.816497 * s
    }


perceptualDistanceSquared : PerceptualColor -> PerceptualColor -> Float
perceptualDistanceSquared left right =
    let
        dl =
            left.opponentL - right.opponentL

        da =
            left.opponentA - right.opponentA

        db =
            left.opponentB - right.opponentB
    in
    dl * dl + da * da + db * db


bestContrastPartner : PerceptualColor -> List PerceptualColor -> ( PerceptualColor, Float )
bestContrastPartner anchor candidates =
    case candidates of
        [] ->
            ( anchor, 0 )

        first :: rest ->
            List.foldl
                (\candidate ( best, bestScore ) ->
                    let
                        score =
                            perceptualDistanceSquared anchor candidate
                    in
                    if score > bestScore then
                        ( candidate, score )

                    else
                        ( best, bestScore )
                )
                ( first, perceptualDistanceSquared anchor first )
                rest


bestByMaximin :
    (PerceptualColor -> Float)
    -> PerceptualColor
    -> List PerceptualColor
    -> PerceptualColor
bestByMaximin score fallback candidates =
    List.maximumBy score candidates
        |> Maybe.withDefault fallback


candidateColors : List PerceptualColor
candidateColors =
    List.map
        (\index ->
            customPerceptualColor index (dynamicDisplayCandidate index)
        )
        (List.range 0 15)


fallbackPerceptualColor : PerceptualColor
fallbackPerceptualColor =
    customPerceptualColor 0 (dynamicDisplayCandidate 0)


backgroundPerceptualColor : PerceptualColor
backgroundPerceptualColor =
    bestByMaximin
        (\candidate -> displayLuminosity candidate.display)
        fallbackPerceptualColor
        candidateColors


inkPerceptualColor : PerceptualColor
inkPerceptualColor =
    bestByMaximin
        (\candidate ->
            min
                (perceptualDistanceSquared candidate backgroundPerceptualColor)
                (1 - displayLuminosity candidate.display)
        )
        fallbackPerceptualColor
        candidateColors


accentSelection : ( PerceptualColor, PerceptualColor )
accentSelection =
    let
        choices =
            List.map
                (\candidate ->
                    let
                        ( font, fontDistance ) =
                            bestContrastPartner candidate candidateColors

                        score =
                            min
                                (perceptualDistanceSquared candidate backgroundPerceptualColor)
                                (min
                                    (perceptualDistanceSquared candidate inkPerceptualColor)
                                    fontDistance
                                )
                    in
                    ( candidate, font, score )
                )
                candidateColors
    in
    case List.maximumBy (\( _, _, score ) -> score) choices of
        Just ( accent, font, _ ) ->
            ( accent, font )

        Nothing ->
            ( fallbackPerceptualColor, fallbackPerceptualColor )


accentPerceptualColor : PerceptualColor
accentPerceptualColor =
    Tuple.first accentSelection


accentInkPerceptualColor : PerceptualColor
accentInkPerceptualColor =
    Tuple.second accentSelection


surfacePerceptualColor : PerceptualColor
surfacePerceptualColor =
    let
        forbidden =
            [ backgroundPerceptualColor.id
            , inkPerceptualColor.id
            , accentPerceptualColor.id
            ]
    in
    bestByMaximin
        (\candidate ->
            min
                (perceptualDistanceSquared candidate backgroundPerceptualColor)
                (perceptualDistanceSquared candidate accentPerceptualColor)
        )
        fallbackPerceptualColor
        (List.filter (\candidate -> not (List.member candidate.id forbidden)) candidateColors)


mutedInkPerceptualColor : PerceptualColor
mutedInkPerceptualColor =
    bestByMaximin
        (\candidate ->
            min
                (perceptualDistanceSquared candidate surfacePerceptualColor)
                (0.5 + abs (displayLuminosity inkPerceptualColor.display - displayLuminosity candidate.display))
        )
        inkPerceptualColor
        candidateColors


cssDisplayColor : DisplayColor -> String
cssDisplayColor color =
    "color(srgb "
        ++ String.fromFloat (clamp01 color.r)
        ++ " "
        ++ String.fromFloat (clamp01 color.g)
        ++ " "
        ++ String.fromFloat (clamp01 color.b)
        ++ ")"


dynamicPalette : DisplayPalette
dynamicPalette =
    { background = cssDisplayColor backgroundPerceptualColor.display
    , surface = cssDisplayColor surfacePerceptualColor.display
    , ink = cssDisplayColor inkPerceptualColor.display
    , mutedInk = cssDisplayColor mutedInkPerceptualColor.display
    , accent = cssDisplayColor accentPerceptualColor.display
    , accentInk = cssDisplayColor accentInkPerceptualColor.display
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
    main_ [ HA.class "repository", HA.style "background-color" dynamicPalette.background, HA.style "color" dynamicPalette.ink ]
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
                [ text "The L1 and 1-path-norm surface has been pruned. The zero-threshold hard/soft sparsity theorem and the finite Tsallis-2/support-sparsity surface remain active." ]
            , ul [] (List.map codeItem
                [ "CanonicalHardSparsityDegeneracyTheorem"
                , "generalTsallis2NearSparsity"
                , "generalTsallis2NearSparsity-zero"
                , "generalTsallis2NearSparsity-definition"
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
                [ text "The executable Python/JAX wrapper has been removed. The retained JAX-facing algorithms are represented by typed Agda contracts in JAXExecutionMirrorReproof. The contracts cover the retained vector, scan, sparse-support, LayerNorm, gate, GRU, Tsallis-2, support-sparsity, and scan-sum algorithms." ]
            , ul [] (List.map codeItem
                [ "vmap_affine -> jaxVmapAffine"
                , "associative_prefix_sum -> jaxAssociativePrefixSum"
                , "recurrent_scan -> jaxRecurrentScan"
                , "lexicographic_score_order -> jaxLexicographicScoreOrder"
                , "sparse_support_size -> jaxSparseSupportSize"
                , "sparse_support_top_k -> jaxSparseSupportTopK"
                , "sparsemax_policy_index -> jaxSparsemaxPolicyIndex"
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
                dynamicPalette.accent

            else
                dynamicPalette.surface

        textFill =
            if selected then
                dynamicPalette.accentInk

            else
                dynamicPalette.ink
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
