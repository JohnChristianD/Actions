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
    "Changed the Mirth module declaration to package-qualified actions.agda_to_elm and reduced the generated surface to compiler-stable Agda module metadata.",
    "Repaired site/Main.elm by defining the missing moduleItem helper and consuming the generated module metadata.",
    "Narrowed the Dhall presentation contract and both Pages/Nix verification lanes to the stable generated field, while independently checking both canonical Agda module declarations.",
    "Recorded the prior Mirth failures accurately; the latest Pages run is the authoritative verification receipt."
  ],
  verification = [
    "GitHub Pages run 36669143030 failed during Mirth compilation because the previous source used unsupported find, Path, and Int conversion forms for the pinned compiler.",
    "Nix connected-composition run 36669143067 for commit 8cc80d64d080f23ced42b2f728de1d58ca599a2e succeeded.",
    "No local Mirth or Elm compiler receipt is available in the current environment.",
    "This follow-up change intentionally does not claim a green Pages deployment until a new Pages run completes successfully."
  ],
  caveat = "Generated presentation metadata is synchronization/build data, not proof evidence. Agda --safe remains the only proof authority.",
  stale_when = "Update this record when the Mirth compiler module rules, generated Elm fields, Markdown indexing policy, or Pages deployment architecture changes."
}
