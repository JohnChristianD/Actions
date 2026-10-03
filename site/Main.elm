module Main exposing (main)

import Browser
import Char
import GeneratedAgdaGraph as Graph
import GeneratedTheoremSurface as Surface
import Html exposing (Html, a, button, code, div, h1, h2, input, li, main_, node, option, p, section, select, span, text, ul)
import Html.Attributes as HA
import Html.Events as HE
import String
import Svg as S
import Svg.Attributes as SA
import Svg.Events as SE


type alias DisplayColor =
    { r : Float
    , g : Float
    , b : Float
    }


type alias PerceptualColor =
    { display : DisplayColor
    , id : Int
    , opponentL : Float
    , opponentA : Float
    , opponentB : Float
    }


type alias EncodedColor =
    { srgb : DisplayColor
    , p3 : DisplayColor
    , rec2020 : DisplayColor
    }


type alias PaletteChoice =
    { background : PerceptualColor
    , surface : PerceptualColor
    , ink : PerceptualColor
    , mutedInk : PerceptualColor
    , accent : PerceptualColor
    , accentInk : PerceptualColor
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


paletteSeed : Int
paletteSeed =
    List.length Graph.nodes * 31 + List.length Graph.edges * 17


clamp01 : Float -> Float
clamp01 value =
    max 0 (min 1 value)


dynamicDisplayCandidate : Int -> DisplayColor
dynamicDisplayCandidate index =
    let
        tau = 6.283185307179586
        hues = 8
        hueIndex = modBy hues index
        toneIndex = modBy 3 index
        phase = tau * toFloat hueIndex / toFloat hues
        tone =
            case toneIndex of
                0 -> 0.18
                1 -> 0.5
                _ -> 0.82
        amplitude =
            case toneIndex of
                1 -> 0.32
                _ -> 0.18
    in
    { r = clamp01 (tone + amplitude * cos phase)
    , g = clamp01 (tone + amplitude * cos (phase - 2.0943951023931953))
    , b = clamp01 (tone + amplitude * cos (phase + 2.0943951023931953))
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
                e ^ (0.2 * logBase e magnitude)

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


permutationsOfLength : Int -> List PerceptualColor -> List (List PerceptualColor)
permutationsOfLength count candidates =
    if count <= 0 then
        [ [] ]

    else
        List.concatMap
            (\candidate ->
                List.map
                    (\tail -> candidate :: tail)
                    (permutationsOfLength
                        (count - 1)
                        (List.filter (\other -> other.id /= candidate.id) candidates))
            )
            candidates


minimumPairDistance : List PerceptualColor -> Float
minimumPairDistance colors =
    case colors of
        [] ->
            0

        first :: rest ->
            case rest of
                [] ->
                    0

                _ ->
                    min
                        (List.foldl
                            (\other best ->
                                min best (perceptualDistanceSquared first other)
                            )
                            (perceptualDistanceSquared first (List.head rest |> Maybe.withDefault first))
                            rest
                        )
                        (minimumPairDistance rest)


paletteChoiceFromList : List PerceptualColor -> Maybe PaletteChoice
paletteChoiceFromList colors =
    case colors of
        background :: surface :: ink :: mutedInk :: accent :: accentInk :: [] ->
            Just
                { background = background
                , surface = surface
                , ink = ink
                , mutedInk = mutedInk
                , accent = accent
                , accentInk = accentInk
                }

        _ ->
            Nothing


combinationsOfLength : Int -> List a -> List (List a)
combinationsOfLength count values =
    if count <= 0 then
        [ [] ]
    else
        case values of
            [] ->
                []
            first :: rest ->
                List.map
                    ((::) first)
                    (combinationsOfLength (count - 1) rest)
                    ++ combinationsOfLength count rest


relativeLuminanceComponent : Float -> Float
relativeLuminanceComponent value =
    if value <= 0.04045 then
        value / 12.92
    else
        ((value + 0.055) / 1.055) ^ 2.4


relativeLuminance : DisplayColor -> Float
relativeLuminance color =
    0.2126 * relativeLuminanceComponent color.r
        + 0.7152 * relativeLuminanceComponent color.g
        + 0.0722 * relativeLuminanceComponent color.b


contrastRatio : DisplayColor -> DisplayColor -> Float
contrastRatio left right =
    let
        leftL = relativeLuminance left
        rightL = relativeLuminance right
        lighter = max leftL rightL
        darker = min leftL rightL
    in
    (lighter + 0.05) / (darker + 0.05)


paletteAccessibilityScore : PaletteChoice -> Float
paletteAccessibilityScore choice =
    min
        (contrastRatio choice.background.display choice.ink.display)
        (min
            (contrastRatio choice.accent.display choice.accentInk.display)
            (min
                (contrastRatio choice.background.display choice.surface.display)
                (contrastRatio choice.surface.display choice.ink.display)
            )
        )


paletteRoleDistance : PaletteChoice -> Float
paletteRoleDistance choice =
    min
        (perceptualDistanceSquared choice.background choice.ink)
        (min
            (perceptualDistanceSquared choice.accent choice.accentInk)
            (min
                (perceptualDistanceSquared choice.background choice.surface)
                (perceptualDistanceSquared choice.surface choice.ink)
            )
        )


paletteGlobalScore : PaletteChoice -> ( Float, Float, Float )
paletteGlobalScore choice =
    ( minimumPairDistance
        [ choice.background
        , choice.surface
        , choice.ink
        , choice.mutedInk
        , choice.accent
        , choice.accentInk
        ]
    , paletteAccessibilityScore choice
    , paletteRoleDistance choice
    )


maximumBy : (a -> comparable) -> List a -> Maybe a
maximumBy score values =
    case values of
        [] ->
            Nothing
        first :: rest ->
            Just
                (List.foldl
                    (\candidate current ->
                        if score candidate > score current then
                            candidate
                        else
                            current
                    )
                    first
                    rest
                )


candidateColors : List PerceptualColor
candidateColors =
    List.map
        (\\index ->
            customPerceptualColor index (dynamicDisplayCandidate index)
        )
        (List.range 0 23)


fallbackPerceptualColor : PerceptualColor
fallbackPerceptualColor =
    customPerceptualColor 0 (dynamicDisplayCandidate 0)


maximinColorSet : List PerceptualColor -> List PerceptualColor
maximinColorSet candidates =
    combinationsOfLength 6 candidates
        |> maximumBy minimumPairDistance
        |> Maybe.withDefault (List.take 6 candidates)


maximinPalette : List PerceptualColor
maximinPalette =
    maximinColorSet candidateColors


bestCandidate : (PerceptualColor -> Float) -> List Int -> List PerceptualColor -> Maybe PerceptualColor
bestCandidate score excluded candidates =
    candidates
        |> List.filter (\\candidate -> not (List.member candidate.id excluded))
        |> maximumBy score


bestContrastCandidate :
    (PerceptualColor -> Float)
    -> Float
    -> DisplayColor
    -> List Int
    -> List PerceptualColor
    -> Maybe PerceptualColor
bestContrastCandidate score threshold other excluded candidates =
    candidates
        |> List.filter
            (\\candidate ->
                not (List.member candidate.id excluded)
                    && contrastRatio candidate.display other >= threshold
            )
        |> maximumBy score


globalPaletteChoice : PaletteChoice
globalPaletteChoice =
    let
        contrastThreshold =
            4.5

        background =
            bestCandidate
                (\\candidate -> relativeLuminance candidate.display)
                []
                candidateColors
                |> Maybe.withDefault fallbackPerceptualColor

        surface =
            bestCandidate
                (\\candidate -> relativeLuminance candidate.display)
                [ background.id ]
                candidateColors
                |> Maybe.withDefault background

        ink =
            bestCandidate
                (\\candidate -> -relativeLuminance candidate.display)
                [ background.id, surface.id ]
                candidateColors
                |> Maybe.withDefault fallbackPerceptualColor

        mutedInk =
            bestCandidate
                (\\candidate ->
                    min
                        (contrastRatio background.display candidate.display)
                        (contrastRatio surface.display candidate.display)
                )
                [ background.id, surface.id, ink.id ]
                candidateColors
                |> Maybe.withDefault ink

        accent =
            bestContrastCandidate
                (\\candidate -> perceptualDistanceSquared background candidate)
                contrastThreshold
                background.display
                [ background.id, surface.id, ink.id, mutedInk.id ]
                candidateColors
                |> Maybe.withDefault mutedInk

        accentInk =
            bestContrastCandidate
                (\\candidate -> perceptualDistanceSquared accent candidate)
                contrastThreshold
                accent.display
                [ background.id, surface.id, ink.id, mutedInk.id, accent.id ]
                candidateColors
                |> Maybe.withDefault ink
    in
    { background = background
    , surface = surface
    , ink = ink
    , mutedInk = mutedInk
    , accent = accent
    , accentInk = accentInk
    }


srgbToLinear : Float -> Float
srgbToLinear value =
    let
        sign =
            if value < 0 then
                -1

            else
                1

        magnitude =
            abs value
    in
    if magnitude <= 0.04045 then
        value / 12.92

    else
        sign * ((magnitude + 0.055) / 1.055) ^ 2.4


linearToSrgb : Float -> Float
linearToSrgb value =
    let
        sign =
            if value < 0 then
                -1

            else
                1

        magnitude =
            abs value
    in
    if magnitude <= 0.0031308 then
        12.92 * value

    else
        sign * (1.055 * magnitude ^ (1 / 2.4) - 0.055)


linearToRec2020 : Float -> Float
linearToRec2020 value =
    if value == 0 then
        0

    else
        (if value < 0 then -1 else 1) * abs value ^ (1 / 2.4)


xyzFromSrgb : DisplayColor -> ( Float, Float, Float )
xyzFromSrgb color =
    let
        r =
            srgbToLinear color.r

        g =
            srgbToLinear color.g

        b =
            srgbToLinear color.b
    in
    ( 0.41239079926595934 * r + 0.357584339383878 * g + 0.1804807884018343 * b
    , 0.21263900587151027 * r + 0.715168678767756 * g + 0.07219231536073371 * b
    , 0.01933081871559182 * r + 0.11919477979462598 * g + 0.9505321522496607 * b
    )


xyzToP3 : ( Float, Float, Float ) -> DisplayColor
xyzToP3 xyz =
    let
        ( x, y, z ) =
            xyz
    in
    { r = linearToSrgb (1.716651187971268 * x - 0.355670783776392 * y - 0.25336628137365974 * z)
    , g = linearToSrgb (-0.666684351832489 * x + 1.6164812366349395 * y + 0.01576854581391113 * z)
    , b = linearToSrgb (0.017639857445310783 * x - 0.042770613257808524 * y + 0.9421031212354738 * z)
    }


xyzToRec2020 : ( Float, Float, Float ) -> DisplayColor
xyzToRec2020 xyz =
    let
        ( x, y, z ) =
            xyz

        r =
            1.660491002108434 * x - 0.5876411788327624 * y - 0.07284931861019282 * z

        g =
            -0.12455047452145676 * x + 1.1328998971259597 * y - 0.00834915146271733 * z

        b =
            -0.018150763487746622 * x - 0.100578898008244 * y + 1.118312588204183 * z
    in
    { r = linearToRec2020 r
    , g = linearToRec2020 g
    , b = linearToRec2020 b
    }


encodeFinal : DisplayColor -> EncodedColor
encodeFinal source =
    { srgb =
        { r = clamp01 source.r
        , g = clamp01 source.g
        , b = clamp01 source.b
        }
    , p3 =
        let
            ( x, y, z ) =
                xyzFromSrgb source

            converted =
                xyzToP3 ( x, y, z )
        in
        { r = clamp01 converted.r
        , g = clamp01 converted.g
        , b = clamp01 converted.b
        }
    , rec2020 =
        let
            ( x, y, z ) =
                xyzFromSrgb source

            converted =
                xyzToRec2020 ( x, y, z )
        in
        { r = clamp01 converted.r
        , g = clamp01 converted.g
        , b = clamp01 converted.b
        }
    }



maximinColorAt : Int -> PerceptualColor
maximinColorAt index =
    maximinPalette
        |> List.drop (modBy (List.length maximinPalette) index)
        |> List.head
        |> Maybe.withDefault fallbackPerceptualColor


bestNodeTextDisplayColor : DisplayColor -> DisplayColor
bestNodeTextDisplayColor nodeColor =
    [ globalPaletteChoice.ink.display
    , globalPaletteChoice.background.display
    , globalPaletteChoice.accentInk.display
    , globalPaletteChoice.surface.display
    ]
        |> maximumBy (\\candidate -> contrastRatio nodeColor candidate)
        |> Maybe.withDefault globalPaletteChoice.ink.display


paletteSwatch : Int -> PerceptualColor -> Html msg
paletteSwatch index color =
    let
        encoded =
            encodeFinal color.display

        textColor =
            bestNodeTextDisplayColor color.display
    in
    div
        [ HA.attribute
            "style"
            (cssFallbacks "background-color" encoded
                ++ cssFallbacks "color" (encodeFinal textColor)
                ++ "display:inline-block;min-width:7rem;margin:.25rem;padding:.5rem;border:1px solid;"
            )
        ]
        [ text ("maximin-" ++ String.fromInt (index + 1)) ]


backgroundColor : EncodedColor
backgroundColor =
    encodeFinal globalPaletteChoice.background.display


surfaceColor : EncodedColor
surfaceColor =
    encodeFinal globalPaletteChoice.surface.display


inkColor : EncodedColor
inkColor =
    encodeFinal globalPaletteChoice.ink.display


mutedInkColor : EncodedColor
mutedInkColor =
    encodeFinal globalPaletteChoice.mutedInk.display


accentColor : EncodedColor
accentColor =
    encodeFinal globalPaletteChoice.accent.display


accentInkColor : EncodedColor
accentInkColor =
    encodeFinal globalPaletteChoice.accentInk.display


cssNumber : Float -> String
cssNumber value =
    String.fromFloat (clamp01 value)


cssColor : String -> DisplayColor -> String
cssColor space color =
    "color("
        ++ space
        ++ " "
        ++ cssNumber color.r
        ++ " "
        ++ cssNumber color.g
        ++ " "
        ++ cssNumber color.b
        ++ ")"


cssRgb : DisplayColor -> String
cssRgb color =
    "rgb("
        ++ String.fromInt (round (clamp01 color.r * 255))
        ++ " "
        ++ String.fromInt (round (clamp01 color.g * 255))
        ++ " "
        ++ String.fromInt (round (clamp01 color.b * 255))
        ++ ")"


cssFallbacks : String -> EncodedColor -> String
cssFallbacks property color =
    property
        ++ ":"
        ++ cssRgb color.srgb
        ++ ";"
        ++ property
        ++ ":"
        ++ cssColor "srgb" color.srgb
        ++ ";"
        ++ property
        ++ ":"
        ++ cssColor "display-p3" color.p3
        ++ ";"
        ++ property
        ++ ":"
        ++ cssColor "rec2020" color.rec2020
        ++ ";"


svgColorStyle : String -> EncodedColor -> String
svgColorStyle property color =
    cssFallbacks property color


dynamicCss : String
dynamicCss =
    ".repository{"
        ++ cssFallbacks "background-color" backgroundColor
        ++ cssFallbacks "color" inkColor
        ++ "min-height:100vh;box-sizing:border-box;padding:2rem;"
        ++ "font-family:system-ui,sans-serif;"
        ++ "}"
        ++ ".dynamic-surface{"
        ++ cssFallbacks "background-color" surfaceColor
        ++ cssFallbacks "color" inkColor
        ++ cssFallbacks "border-color" mutedInkColor
        ++ "}"
        ++ ".dynamic-accent{"
        ++ cssFallbacks "background-color" accentColor
        ++ cssFallbacks "color" accentInkColor
        ++ cssFallbacks "border-color" accentColor
        ++ "}"
        ++ ".dynamic-ink{"
        ++ cssFallbacks "color" inkColor
        ++ "}"
        ++ ".dynamic-muted{"
        ++ cssFallbacks "color" mutedInkColor
        ++ "}"
        ++ ".dynamic-link{"
        ++ cssFallbacks "color" accentColor
        ++ "}"
        ++ ".repository input::placeholder{"
        ++ cssFallbacks "color" mutedInkColor
        ++ "}"
        ++ ".repository button,.repository input,.repository select{"
        ++ "font:inherit;box-sizing:border-box;"
        ++ "}"
        ++ ".repository button,.repository input,.repository select{"
        ++ cssFallbacks "background-color" surfaceColor
        ++ cssFallbacks "color" inkColor
        ++ cssFallbacks "border-color" mutedInkColor
        ++ "}"
        ++ ".repository button:focus,.repository input:focus,.repository select:focus{"
        ++ cssFallbacks "outline-color" accentColor
        ++ "}"
        ++ ".repository{"
        ++ cssFallbacks "caret-color" accentColor
        ++ cssFallbacks "accent-color" accentColor
        ++ "}"
        ++ ".graph-controls{display:grid;gap:.75rem;grid-template-columns:repeat(auto-fit,minmax(220px,1fr));margin:1rem 0;}"
        ++ ".graph-node-list{display:grid;gap:.5rem;grid-template-columns:repeat(auto-fit,minmax(260px,1fr));}"
        ++ ".graph-node-button{text-align:left;padding:.5rem;border:1px solid;}"
        ++ ".graph-canvas{overflow:auto;border:1px solid;padding:.5rem;}"
        ++ "a{text-decoration-thickness:.08em;text-underline-offset:.15em;}"
        ++ "ul{padding-left:1.5rem;}"


dynamicStyleSheet : Html msg
dynamicStyleSheet =
    node "style" [] [ text dynamicCss ]


sanitize : String -> String
sanitize value =
    String.map
        (\char ->
            if Char.toCode char < 128 then
                char

            else
                Char.fromCode 63
        )
        value


visibleNodes : Model -> List Graph.Node
visibleNodes model =
    let
        query =
            String.toLower (sanitize model.query)
    in
    List.filter
        (\nodeItem ->
            let
                label =
                    sanitize nodeItem.label

                nodeId =
                    sanitize nodeItem.id
            in
            sourceAllowed model.fileFilter nodeItem.source
                && (String.isEmpty query
                    || String.contains query (String.toLower label)
                    || String.contains query (String.toLower nodeId)
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


filterString : FileFilter -> String
filterString fileFilter =
    case fileFilter of
        AllFiles ->
            "all"

        LearnerOnly ->
            "learner"

        TheoremOnly ->
            "theorem"


nodeForId : String -> Maybe Graph.Node
nodeForId nodeId =
    Graph.nodes
        |> List.filter (\nodeItem -> nodeItem.id == nodeId)
        |> List.head


incomingIds : String -> List String
incomingIds nodeId =
    Graph.edges
        |> List.filter (\edge -> edge.target == nodeId)
        |> List.map .source


outgoingIds : String -> List String
outgoingIds nodeId =
    Graph.edges
        |> List.filter (\edge -> edge.source == nodeId)
        |> List.map .target


relationMatches : String -> Graph.Edge -> Bool
relationMatches query edge =
    let
        needle =
            String.toLower (sanitize query)
    in
    String.isEmpty needle
        || String.contains needle (String.toLower (sanitize edge.source))
        || String.contains needle (String.toLower (sanitize edge.target))
        || String.contains needle (String.toLower (sanitize edge.relation))


visibleEdges : Model -> List Graph.Edge
visibleEdges model =
    List.filter (relationMatches model.relationQuery) Graph.edges


keepVisibleSelection : Model -> Model
keepVisibleSelection model =
    let
        ids =
            List.map .id (visibleNodes model)
    in
    case model.selected of
        Just selected ->
            if List.member selected ids then
                model

            else
                { model | selected = List.head ids }

        Nothing ->
            { model | selected = List.head ids }


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


init : Model
init =
    { query = ""
    , relationQuery = ""
    , fileFilter = AllFiles
    , selected = Graph.nodes |> List.head |> Maybe.map .id
    }


nodeButton : Graph.Node -> Html Msg
nodeButton nodeItem =
    button
        [ HA.type_ "button"
        , HE.onClick (SelectNode nodeItem.id)
        , HA.class "graph-node-button dynamic-surface"
        ]
        [ code [] [ text (sanitize (nodeItem.source ++ ":" ++ nodeItem.label)) ] ]


relationButton : String -> Html Msg
relationButton nodeId =
    button
        [ HA.type_ "button"
        , HE.onClick (SelectNode nodeId)
        , HA.class "dynamic-surface"
        ]
        [ code [] [ text (sanitize nodeId) ] ]


relationRecord : Graph.Edge -> Html Msg
relationRecord edge =
    li []
        [ button
            [ HA.type_ "button"
            , HE.onClick (SelectNode edge.source)
            , HA.class "dynamic-surface"
            ]
            [ code [] [ text (sanitize edge.source) ] ]
        , span [ HA.class "dynamic-muted" ]
            [ text (sanitize (" --" ++ edge.relation ++ "--> ")) ]
        , button
            [ HA.type_ "button"
            , HE.onClick (SelectNode edge.target)
            , HA.class "dynamic-surface"
            ]
            [ code [] [ text (sanitize edge.target) ] ]
        ]


positionFor : Int -> Int -> { x : Float, y : Float }
positionFor index sideCount =
    { x =
        if sideCount == 0 then
            500

        else
            150 + toFloat index * (700 / toFloat (max 1 (sideCount - 1)))
    , y = 120
    }


graphView : Model -> Html Msg
graphView model =
    case model.selected |> Maybe.andThen nodeForId of
        Nothing ->
            p [ HA.class "dynamic-muted" ] [ text (sanitize Surface.siteTitle) ]

        Just selected ->
            let
                incoming =
                    incomingIds selected.id

                outgoing =
                    outgoingIds selected.id

                allNeighbors =
                    incoming ++ outgoing

                height =
                    180 + toFloat (max 1 (List.length allNeighbors)) * 60

                selectedText =
                    sanitize selected.label

                centerStyle =
                    "fill:"
                        ++ cssColor "srgb" accentColor.srgb
                        ++ ";fill:"
                        ++ cssColor "display-p3" accentColor.p3
                        ++ ";fill:"
                        ++ cssColor "rec2020" accentColor.rec2020
                        ++ ";stroke:"
                        ++ cssColor "srgb" mutedInkColor.srgb
                        ++ ";stroke:"
                        ++ cssColor "display-p3" mutedInkColor.p3
                        ++ ";stroke:"
                        ++ cssColor "rec2020" mutedInkColor.rec2020
                        ++ ";"

                neighborStyle =
                    "fill:"
                        ++ cssColor "srgb" surfaceColor.srgb
                        ++ ";fill:"
                        ++ cssColor "display-p3" surfaceColor.p3
                        ++ ";fill:"
                        ++ cssColor "rec2020" surfaceColor.rec2020
                        ++ ";stroke:"
                        ++ cssColor "srgb" mutedInkColor.srgb
                        ++ ";stroke:"
                        ++ cssColor "display-p3" mutedInkColor.p3
                        ++ ";stroke:"
                        ++ cssColor "rec2020" mutedInkColor.rec2020
                        ++ ";"
            in
            div [ HA.class "graph-canvas dynamic-surface" ]
                [ S.svg
                    [ SA.viewBox ("0 0 1000 " ++ String.fromFloat height)
                    , SA.width "100%"
                    , SA.height (String.fromFloat height)
                    ]
                    (List.concatMap
                        (\neighborIndex ->
                            let
                                position =
                                    positionFor neighborIndex (max 1 (List.length allNeighbors))

                                nodeId =
                                    List.drop neighborIndex allNeighbors
                                        |> List.head
                                        |> Maybe.withDefault selected.id

                                nodeColor =
                                    maximinColorAt neighborIndex

                                nodeEncoded =
                                    encodeFinal nodeColor.display

                                nodeTextColor =
                                    encodeFinal (bestNodeTextDisplayColor nodeColor.display)

                                neighborStyle =
                                    cssFallbacks "fill" nodeEncoded
                                        ++ cssFallbacks "stroke" (encodeFinal mutedInkColor.srgb)
                            in
                            [ S.line
                                [ SA.x1 "500"
                                , SA.y1 "60"
                                , SA.x2 (String.fromFloat position.x)
                                , SA.y2 (String.fromFloat position.y)
                                , SA.style
                                    ( "stroke:"
                                        ++ cssColor "srgb" mutedInkColor.srgb
                                        ++ ";stroke:"
                                        ++ cssColor "display-p3" mutedInkColor.p3
                                        ++ ";stroke:"
                                        ++ cssColor "rec2020" mutedInkColor.rec2020
                                        ++ ";"
                                    )
                                ]
                                []
                            , S.rect
                                [ SA.x (String.fromFloat (position.x - 120))
                                , SA.y (String.fromFloat (position.y - 18))
                                , SA.width "240"
                                , SA.height "36"
                                , SA.rx "6"
                                , SA.style neighborStyle
                                ]
                                [ S.title [] [ S.text (sanitize nodeId) ] ]
                            , S.text_
                                [ SA.x (String.fromFloat position.x)
                                , SA.y (String.fromFloat (position.y + 5))
                                , SA.textAnchor "middle"
                                , SA.fontSize "11"
                                , SA.style
                                    (cssFallbacks "fill" nodeTextColor)
                                ]
                                [ S.text
                                    (String.left 36
                                        (nodeForId nodeId
                                            |> Maybe.map .label
                                            |> Maybe.withDefault nodeId
                                            |> sanitize
                                        )
                                    )
                                ]
                            ]
                        )
                        (List.range 0 (max 0 (List.length allNeighbors - 1)))
                        ++ [ S.rect
                            [ SA.x "350"
                            , SA.y "35"
                            , SA.width "300"
                            , SA.height "50"
                            , SA.rx "8"
                            , SA.style centerStyle
                            ]
                            []
                           , S.text_
                                [ SA.x "500"
                                , SA.y "65"
                                , SA.textAnchor "middle"
                                , SA.fontSize "13"
                                , SA.style
                                    ( "fill:"
                                        ++ cssColor "srgb" accentInkColor.srgb
                                        ++ ";fill:"
                                        ++ cssColor "display-p3" accentInkColor.p3
                                        ++ ";fill:"
                                        ++ cssColor "rec2020" accentInkColor.rec2020
                                        ++ ";"
                                    )
                                ]
                                [ S.text (String.left 46 selectedText) ]
                           ]
                    )
                ]


view : Model -> Html Msg
view model =
    let
        visible =
            visibleNodes model

        edges =
            visibleEdges model

        titleText =
            sanitize Surface.siteTitle

        sourceText =
            String.join "," (List.map sanitize Surface.sourceFiles)

    in
    main_
        [ HA.class "repository" ]
        [ dynamicStyleSheet
        , h1 [ HA.class "dynamic-accent" ] [ text titleText ]
        , p [ HA.class "dynamic-muted" ]
            [ text sourceText ]
        , section []
            [ h2 [ HA.class "dynamic-ink" ]
                [ text (String.fromInt (List.length visible) ++ " declarations") ]
            , div [ HA.class "graph-controls" ]
                [ input
                    [ HA.placeholder "query"
                    , HA.value model.query
                    , HE.onInput SetQuery
                    ]
                    []
                , select [ HA.value (filterString model.fileFilter), HE.onInput SetFileFilter ]
                    [ option [ HA.value "all" ] [ text "all" ]
                    , option [ HA.value "learner" ] [ text "learner" ]
                    , option [ HA.value "theorem" ] [ text "theorem" ]
                    ]
                ]
            , div [ HA.class "graph-node-list" ]
                (List.map nodeButton visible)
            , graphView model
            ]
        , section []
            [ h2 [ HA.class "dynamic-ink" ]
                [ text (String.fromInt (List.length edges) ++ " directed relations") ]
            , input
                [ HA.placeholder "relation"
                , HA.value model.relationQuery
                , HE.onInput SetRelationQuery
                , HA.class "dynamic-surface"
                ]
                []
            , ul [] (List.map relationRecord edges)
            ]
        , section []
            [ h2 [ HA.class "dynamic-ink" ] [ text "Custom maximin palette" ]
            , div []
                (List.indexedMap paletteSwatch maximinPalette)
            ]
        , section []
            [ h2 [ HA.class "dynamic-ink" ] [ text "Mirth surface" ]
            , ul []
                [ li [] [ code [] [ text ("nodes=" ++ String.fromInt (List.length Surface.nodeLines)) ] ]
                , li [] [ code [] [ text ("edges=" ++ String.fromInt (List.length Surface.edgeLines)) ] ]
                , li [] [ code [] [ text ("ascii-nodes=" ++ String.fromInt (List.length (List.filter (\line -> String.all (\char -> Char.toCode char < 128) line) Surface.nodeLines))) ] ]
                , li [] [ code [] [ text ("ascii-edges=" ++ String.fromInt (List.length (List.filter (\line -> String.all (\char -> Char.toCode char < 128) line) Surface.edgeLines))) ] ]
                ]
            ]
        ]


main : Program () Model Msg
main =
    Browser.sandbox
        { init = init
        , update = update
        , view = view
        }
