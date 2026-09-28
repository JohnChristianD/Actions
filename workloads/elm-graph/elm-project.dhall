let Project =
      { type : Text
      , sourceDirectory : Text
      , elmVersion : Text
      , browserVersion : Text
      , coreVersion : Text
      , htmlVersion : Text
      , svgVersion : Text
      , timeVersion : Text
      , urlVersion : Text
      , virtualDomVersion : Text
      }

let project : Project =
      { type = "application"
      , sourceDirectory = "src"
      , elmVersion = "0.19.2"
      , browserVersion = "1.0.2"
      , coreVersion = "1.0.5"
      , htmlVersion = "1.0.0"
      , svgVersion = "1.0.1"
      , timeVersion = "1.0.0"
      , urlVersion = "1.0.0"
      , virtualDomVersion = "1.0.3"
      }

in ''
{
  "type": ${Text/show project.type},
  "source-directories": [${Text/show project.sourceDirectory}],
  "elm-version": ${Text/show project.elmVersion},
  "dependencies": {
    "direct": {
      "elm/browser": ${Text/show project.browserVersion},
      "elm/core": ${Text/show project.coreVersion},
      "elm/html": ${Text/show project.htmlVersion},
      "elm/svg": ${Text/show project.svgVersion}
    },
    "indirect": {
      "elm/time": ${Text/show project.timeVersion},
      "elm/url": ${Text/show project.urlVersion},
      "elm/virtual-dom": ${Text/show project.virtualDomVersion}
    }
  },
  "test-dependencies": {
    "direct": {},
    "indirect": {}
  }
}
''