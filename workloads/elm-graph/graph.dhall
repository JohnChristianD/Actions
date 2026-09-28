let Node =
      { id : Text
      , label : Text
      , status : Text
      , x : Double
      , y : Double
      }

let Edge =
      { source : Text
      , target : Text
      , label : Text
      }

let Graph =
      { title : Text
      , nodes : List Node
      , edges : List Edge
      }

let graph : Graph =
      { title = "Actions semantic dependency view"
      , nodes =
        [ { id = "learner"
          , label = "Canonical learner"
          , status = "PROVED"
          , x = 160.0
          , y = 140.0
          }
        , { id = "representation"
          , label = "Representation"
          , status = "PROVED"
          , x = 420.0
          , y = 140.0
          }
        , { id = "stability"
          , label = "F4 stability"
          , status = "PROVED"
          , x = 680.0
          , y = 140.0
          }
        , { id = "egraph"
          , label = "E-graph / A*"
          , status = "PROVED"
          , x = 940.0
          , y = 140.0
          }
        , { id = "convergence"
          , label = "Convergence"
          , status = "CONDITIONAL"
          , x = 420.0
          , y = 360.0
          }
        , { id = "clearing"
          , label = "Market clearing"
          , status = "FRONTIER"
          , x = 680.0
          , y = 360.0
          }
        , { id = "equilibrium"
          , label = "Walrasian equilibrium"
          , status = "CONDITIONAL"
          , x = 940.0
          , y = 360.0
          }
        ]
      , edges =
        [ { source = "learner"
          , target = "representation"
          , label = "exact"
          }
        , { source = "representation"
          , target = "stability"
          , label = "transport"
          }
        , { source = "stability"
          , target = "egraph"
          , label = "search"
          }
        , { source = "stability"
          , target = "convergence"
          , label = "not implied"
          }
        , { source = "convergence"
          , target = "clearing"
          , label = "witness"
          }
        , { source = "clearing"
          , target = "equilibrium"
          , label = "witness"
          }
        , { source = "egraph"
          , target = "equilibrium"
          , label = "discovery only"
          }
        ]
      }

let renderNode =
      \(item : { index : Natural, value : Node }) ->
        (if Natural/isZero item.index then
            "            "
         else
            "\n            , ")
        ++ "{ id = ${Text/show item.value.id}"
        ++ ", label = ${Text/show item.value.label}"
        ++ ", status = ${Text/show item.value.status}"
        ++ ", x = ${Double/show item.value.x}"
        ++ ", y = ${Double/show item.value.y} }"

let renderEdge =
      \(item : { index : Natural, value : Edge }) ->
        (if Natural/isZero item.index then
            "            "
         else
            "\n            , ")
        ++ "{ source = ${Text/show item.value.source}"
        ++ ", target = ${Text/show item.value.target}"
        ++ ", label = ${Text/show item.value.label} }"

let renderNodes =
      List/fold
        { index : Natural, value : Node }
        (List/indexed Node graph.nodes)
        Text
        (\(item : { index : Natural, value : Node }) ->
          \(rest : Text) ->
            renderNode item ++ rest)
        ""

let renderEdges =
      List/fold
        { index : Natural, value : Edge }
        (List/indexed Edge graph.edges)
        Text
        (\(item : { index : Natural, value : Edge }) ->
          \(rest : Text) ->
            renderEdge item ++ rest)
        ""

in ''
module GeneratedGraph exposing (graph)

import Graph exposing (Graph)

graph : Graph
graph =
    { title = ${Text/show graph.title}
    , nodes =
        [
${renderNodes}
        ]
    , edges =
        [
${renderEdges}
        ]
    }
''
