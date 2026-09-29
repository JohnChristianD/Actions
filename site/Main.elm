-- sync probe
module Main exposing (main)

import Browser
import Html exposing (Html, text)

type alias Model = {}
type Msg = NoOp

main : Program () Model Msg
main = Browser.sandbox { init = {}, update = \\_ model -> model, view = \\_ -> text "Actions" }
