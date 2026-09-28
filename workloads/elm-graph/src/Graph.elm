module Graph exposing (Edge, Graph, Node)


type alias Graph =
    { title : String
    , nodes : List Node
    , edges : List Edge
    }


type alias Node =
    { id : String
    , label : String
    , status : String
    , x : Float
    , y : Float
    }


type alias Edge =
    { source : String
    , target : String
    , label : String
    }
