{
  date = "2026-09-30",
  scope = "Markdown documentation index, Mirth-to-Elm presentation synchronization, and GitHub Pages recovery",
  request = "Audit the Markdown/Elm/Dhall/Mirth synchronization surfaces and repair the independently red GitHub Pages deployment.",
  affected_code = [
    "README.md",
    "docs/research/agda-auto-proof-search.md",
    "site/Main.elm",
    ".ci/readme-doc-sync.dhall",
    ".ci/presentation-contract.dhall",
    ".ci/mirth/agda_to_elm.mth",
    ".ci/actions_ci.dhall",
    ".github/workflows/github-pages.yml",
    ".ci/change-record-2026-09-29-ci-pages-verification.dhall"
  ],
  knowledge_delta = [
    ".ci/change-record-2026-09-30-documentation-pages-resync.dhall"
  ],
  changes = [
    "Broadened the README documentation index to all tracked Markdown outside internal .ci paths.",
    "Updated README and the Agda proof-search research note with the current proof-search and Pages synchronization boundaries.",
    "Changed the Mirth module declaration to package-qualified actions.agda_to_elm and extended its generated contract metadata.",
    "Repaired site/Main.elm by defining the missing moduleItem helper and consuming the generated synchronization metadata.",
    "Expanded the Dhall presentation contract and both Pages/Nix verification lanes to assert the generated fields.",
    "Corrected the prior Pages verification record so it no longer claims the Mirth failure was already fixed."
  ],
  verification = [
    "GitHub Pages run 36666156547 is a recorded failure at Mirth compilation with the package-qualified-module error.",
    "Nix connected-composition run 36666156516 for merge commit 07b1b1b9b5fbd2799c5c0998ead035ec023cedb4 succeeded.",
    "No local Mirth or Elm compiler receipt is available in the current environment.",
    "A fresh GitHub Pages run is required to verify the correction; no green result is claimed in this change record."
  ],
  caveat = "Generated presentation metadata is synchronization/build data, not proof evidence. Agda --safe remains the only proof authority.",
  stale_when = "Update this record when the Mirth compiler module rules, generated Elm fields, Markdown indexing policy, or Pages deployment architecture changes."
}