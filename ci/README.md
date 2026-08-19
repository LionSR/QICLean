# QICLean CI scaffold

This directory holds a draft of QICLean's GitHub Actions workflow set,
adapted from TNLean's `.github/workflows/`. At extraction time these files
move to `.github/workflows/` in the new repository (this location is a
staging area, not the final path).

## Included in this scaffold

| File | Adapted from | What changed |
|---|---|---|
| `pr-ci.yml` | `pr-ci.yml` | Dropped all tenkz jobs (`tenkz-shrink`, `tenkz-corpus`, `tenkz-rmp`) and their path filters; dropped the tenkz-specific steps inside the `blueprint` job (native source lint, manual/example compilation, picture-pipeline smoke test, equation/label-overlap/PEPS-torus/index-routing/fusion-tree audits); module prefix `TNLean.*` → `QICLean.*`; cache key prefix `tnlean-build-` → `qiclean-build-`. Kept: the Lean build + style-lint + checkdecls job, the module-policy guards (oversized-file / numbered-sequel-file checks), the compile-time gate, and the blueprint-sync/reader-facing-prose checks. |
| `import-completeness.yml` | `import-completeness.yml` | Module prefix only; added a note that this workflow checks QICLean's own aggregator completeness, not cross-repository import direction (see below). |
| `blueprint.yml` | `blueprint.yml` | Dropped the tenkz source-lint/pipeline step and the FT-MPS split-volume packaging step (`build_blueprint_ch01_12.sh` has no QICLean analogue). Otherwise unchanged. |
| `docgen.yml` | `docgen.yml` | Dropped the paper-gap-PDF build step and the FT-MPS split-volume step. Otherwise unchanged. |
| `create-release.yml` | `create-release.yml` | Unchanged. Load-bearing for `docs/UPGRADE_RUNBOOK.md` — mints the toolchain release tag TNLean's pin depends on being current. |
| `update.yml` | `update.yml` | Unchanged content, but the file's role differs from TNLean's copy of the same workflow: QICLean is the leaf of the two-repo dependency graph, so its own `update.yml` can safely stay in normal auto-PR mode. TNLean's copy of this workflow must instead be reconfigured to report-only (`on_update_succeeds: issue`) per the runbook, since TNLean's Mathlib revision must follow QICLean's tag, not propose its own. |

## Deferred: the agentic review/auto-fix set

TNLean also runs an agent-driven CI layer, documented in full in
`docs/ci-automation.md` (copied verbatim into this scaffold's `docs/`):
`pr-review.yml`, `auto-fix.yml`, `agent-mention.yml`,
`claude-provider-limit-guard.yml`, plus the reusable
`_ci-auto-fix-shared.yml` template and supporting actions. None of these are
included in this scaffold.

**Why deferred, not dropped.** This is not a judgment that QICLean does not
want automated review and CI-failure auto-fix — the opposite: TNLean's
`docs/ci-automation.md` explains at length why this loop exists and how it
converges, and there is no reason QICLean's proof style would need it less.
The reason to defer is entirely operational, not evaluative:

- The set only works atomically. It depends on repository secrets
  (`CLAUDE_CODE_OAUTH_TOKEN`, optionally `DEEPSEEK_API_KEY`), repository
  labels (`auto-fix-claude`), and — if the new repository lands under a
  different GitHub org than `LionSR` — action-access grants for
  `texra-ai/lean-env-action` and any `LionSR/agent-ci-actions`-style
  composite actions. A partial copy (workflow files present, secrets or
  labels absent) fails silently or noisily depending on the missing piece,
  which is worse than not having the workflow at all.
- The iteration-cap and kill-switch machinery
  (`.github/actions/bot-fix-guard`, the `CLAUDE_AUTO_FIX_ENABLED` /
  `CLAUDE_REVIEW_ENABLED` repository variables) needs to be provisioned
  alongside the workflows, not after.
- Standing up this layer is an org/ops decision (which secrets, which
  labels, which provider) that belongs with whoever creates the QICLean
  repository, not baked into a scaffold produced ahead of that decision.

**What to do at extraction time**: copy the four workflows plus
`_ci-auto-fix-shared.yml` and `.github/actions/bot-fix-guard` from TNLean,
adjust the module-prefix and cache-key references the same way this
scaffold's other files were adjusted, provision the secrets and the
`auto-fix-claude` label, and grant the same external-action access TNLean
has. Bring them up together in one PR, not incrementally.

**Also not included, lower priority**: `issue-automation.yml`,
`housekeeping.yml`, `lean-linter-warning-autofix.yml`,
`docs-blueprint-sync.lock.yml`, `agent-mention.yml`'s DeepSeek-specific
configuration, `badges.yml`, `deploy-pages.yml`. `deploy-pages.yml` in
particular is referenced by both `blueprint.yml` and `docgen.yml` above and
must be ported (it is repo-agnostic — a thin GitHub Pages deploy wrapper —
so this is a straight copy, not an adaptation) before either of those two
workflows can complete a real run.

## The import-direction boundary

TNLean's phase-2 monorepo guard (`scripts/check_import_direction.py`, per
the migration plan) checks, inside the single TNLean repository, that no
file under `TNLean/Channel/` or the other QICLean-bound paths imports a
staying tensor-network module. That check has no QICLean-side counterpart
by construction: once the packages are split, QICLean cannot accidentally
import TNLean, because it has no TNLean requirement to resolve such an
import against — Lake itself enforces the boundary from QICLean's side.
`import-completeness.yml` above only verifies QICLean's own generated
import aggregators are complete, which is a different (weaker,
same-repository) property.
