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
    "GitHub Pages run 36669916012 compiled the simplified Mirth source successfully, then failed because the emitted binary lacked the executable bit.",
    "Nix connected-composition run 36669915957 reached the Pages presentation job on the same commit; its final receipt is pending at the time of this change.",
    "GitHub Pages run 36670131582 confirmed that Mirth emits C99 source; treating the output as a shell-executable was incorrect.",
    "The remediation now compiles the emitted C99 source with the pinned Nix C compiler before execution, and adds that compiler to the devShell.",
    "No green Pages deployment is claimed until the C compilation path completes successfully."
  ],
  caveat = "Generated presentation metadata is synchronization/build data, not proof evidence. Agda --safe remains the only proof authority.",
  stale_when = "Update this record when the Mirth compiler module rules, generated Elm fields, Markdown indexing policy, or Pages deployment architecture changes."
}
