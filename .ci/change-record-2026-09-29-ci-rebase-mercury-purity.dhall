{
  date = "2026-09-29",
  scope = "CI rebase-run reliability, Pages deployment separation, and Mercury purity enforcement",
  request = "Fix repeated CI reds/skips around rebases, then land by rebase, and ensure every Mercury .m source contains no impure or semipure syntax.",
  affected_code = [
    ".github/workflows/nix-composition.yml",
    ".github/workflows/github-pages.yml",
    ".ci/actions_ci.dhall"
  ],
  knowledge_delta = [
    ".ci/change-record-2026-09-29-ci-rebase-mercury-purity.dhall"
  ],
  observed_cause = [
    "Nix composition used one concurrency group with cancel-in-progress=false but the default single pending slot, so repeated PR updates could replace older pending runs.",
    "Pages workflow ran on pull_request while its deploy job was intentionally skipped by an event guard, producing a persistent skipped deployment job on PR verification.",
    "Mercury purity was not enforced as an explicit source-level CI invariant."
  ],
  changes = [
    "Set concurrency queue = max so successive PR/rebase updates are queued instead of replacing the pending run.",
    "Move PR verification responsibility to the Nix composition workflow; Pages workflow is deployment-only for push/main and manual dispatch, removing the expected PR deploy skip.",
    "Add a Pages lane to Nix CI and require it for auto-merge, so Mirth-to-Elm presentation failures are caught before main."
    "Add a MercuryPurity lane that scans every tracked .m file and rejects impure/semipure syntax, purity-cast pragmas, and foreign_proc declarations.",
    "Run the Mercury purity lane explicitly in the Mercury job."
  ],
  verification = [
    "Current main was inspected before the patch.",
    "All indexed Mercury .m sources were searched for module declarations and impurity-related syntax; no current impure/semipure matches were observed.",
    "GitHub workflow configuration was edited on branch fix/ci-rebase-queue-mercury-purity.",
    "Runtime CI receipt is not yet exposed by the available workflow-run connector."
  ],
  rebase_policy = "After the patch branch is green and current, merge it with GitHub's rebase method; do not claim runtime success without an observed workflow receipt.",
  stale_when = "Update this record if the repository changes its CI concurrency policy, Pages trigger/deployment architecture, or Mercury purity boundary."
}
