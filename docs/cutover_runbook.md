# QICLean extraction cutover runbook

Consolidates three Lean-tree dry runs (`docs/extraction_dryrun3_report.md` on
this branch and its two predecessors, `extraction_dryrun_report.md` /
`extraction_dryrun2_report.md` from LionSR/TNLean issue #6622) and one
consumer-side dry run (`consumption_dryrun_report.md`, TNLean side) into a
single replayable procedure for the real cutover of `LionSR/TNLean` issue
#6560 Phase 3.

**Authoritative mover set: run 3's corrected seed rule.** Legacy
`TNLean/Wielandt/` is not seeded (it is the `MPSTensor`-typed consumer layer
and belongs to TNLean); the four "sanctioned interface module" force-seeds
from runs 1/2 are dropped in favor of letting the import closure decide.
This produced **512 movers**, a green build in 8m11s, and a 9-file dragged
ledger that is the definitive QIC/TN interface surface. Every command below
is transcribed from an actual dry-run report; nothing here was invented.
Steps no dry run ever rehearsed are marked **UNREHEARSED**.

Three source snapshots were used across the three Lean-tree runs
(`28d2c97b5` / `07ffebe4c` / `b51276ece`); none of them is current — TNLean
`main` has moved on again since (`beb2ff2b` at the time this runbook was
written). **Re-cut the mover set against the actual freeze commit; do not
reuse `docs/movers.txt` on this branch verbatim for the real extraction.**

---

## 1. Preconditions checklist

### 1.1 Boundary quiet (CI signals)

The consumer-side dry run's single class of build failure (§5.3, "snapshot
staleness") was caused by an in-flight PR (#6756, the word-core split)
landing on TNLean `main` between the QICLean snapshot cut and the consumer
build. The mechanical guard against a repeat:

```bash
# From a read-only TNLean checkout, at the intended freeze commit $FREEZE_SHA:
cd /path/to/TNLean-clone
git fetch origin main
git log --oneline $FREEZE_SHA..origin/main -- $(tr '\n' ' ' < docs/movers.txt 2>/dev/null || echo TNLean/)
# Non-empty output = a mover-touching commit landed after the freeze point.
# Re-cut before proceeding (see Section 2).

gh pr list --repo LionSR/TNLean --state open --json number,title,headRefName
# Cross-check each open PR's changed files against docs/movers.txt paths;
# any overlap is a "hold" candidate per Section 2's freeze announcement.
```

At the time this runbook was written, `LionSR/TNLean` `main` was at
`beb2ff2b`, past all three dry runs' snapshots (`28d2c97b5` / `07ffebe4c` /
`b51276ece`), and 7 PRs were open (#6808, #6820, #6826, #6827, #6828, #6829,
#6830) — several (`#6826`, `#6828`, `#6829`) touch `qic_blueprint_boundary_report.py`,
the tool the blueprint packaging pass depends on. **UNREHEARSED**: no dry
run checked open-PR overlap against `docs/movers.txt` as a gating step; this
is a template built from the consumption report's root-cause finding, not a
rehearsed command.

### 1.2 Owner decision — freeze window

Per the freeze procedure in Section 2: announce on issue #6622, then hold
merges of any PR touching a `docs/movers.txt` path until the re-cut (Section
3) completes. **UNREHEARSED as a formal mechanism** — no dry run exercised
an actual merge freeze; issue #6622's own comment thread shows the owner
manually sequencing PRs around each dry run instead (e.g. "the remaining
order is: land #6711 and #6719, land #6731, freeze the final reports at
exact main").

### 1.3 Owner decision — QICLean `main` cleared or force-replace approved

**Confirmed still unresolved.** Live `git ls-remote` at runbook-writing time:

```
$ git ls-remote https://github.com/LionSR/QICLean.git
e1650a1fdbc47c2d0535a7e15209e710ff1c09c3  HEAD
...
e1650a1fdbc47c2d0535a7e15209e710ff1c09c3  refs/heads/main
e1650a1fdbc47c2d0535a7e15209e710ff1c09c3  refs/heads/scaffold-preview
```

`main` still holds the pre-existing `scaffold-preview` commit `e1650a1f`
("scaffold preview: lakefile, toolchain, docs, and adapted CI for the
extracted library"), unchanged across all three dry runs (run 1 §6, run 2
§7, run 3 §7). A history-preserving `git push` of the filtered extraction
history to `main` will **not** fast-forward over this unrelated commit.
Section 4 gives both the clear-and-replace and the merge/rebase-forward
options; **the choice between them is an owner decision that must be made
before Section 4 runs**, not a mechanical extraction step.

### 1.4 Owner decision — Wolf lecture-note redistribution permission

**Verification performed for this runbook; finding: no moved file embeds
Wolf-derived source material, but Section 1.4's underlying permission
record does not exist and should be created before the repository goes
public.**

- `Notes/WolfNoteTexSource/` (Wolf's own lecture-note LaTeX, e.g.
  `ch01_deconstructing_quantum.tex` … `ch11_quantum_spin_chains.tex`) and
  `Notes/WolfNotePDF/` are tracked in TNLean git but **do not appear in any
  of the three runs' `docs/movers.txt`** (`grep -l "Notes/" docs/movers*.txt`
  across every dry-run scratch copy returned no hits) and are **not** among
  the 65 blueprint content-fragment files `packaging_report.md` §2 lists as
  moved. Both trees stay in TNLean under the current plan.
- The moved blueprint chapters (`blueprint/src/chapter/*.tex`,
  `blueprint/src/appendix/**/*.tex`) are TNLean's own original prose per
  `docs/blueprint_style_guide.md` and `docs/prose_style.md` (pure
  mathematics, no reproduced lecture-note text); they cite Wolf's
  theorem/equation numbers (`Wolf2012Quantum`, e.g. "Theorem 6.2(1)") the
  same way they cite arXiv papers, they do not quote his notes. Wolf's
  chapter order was consulted only to derive the Wolf-chapter mapping table
  in `packaging_report.md` §2, not copied into any moved file.
- **The gap**: unlike `Papers/` (which carries `Papers/NOTICE.md`,
  documenting each arXiv paper's redistribution terms and the authors'
  permission to include the source), `Notes/` has no equivalent notice file
  recording that Wolf granted permission to base a public, Apache-2.0
  repository's organizing structure and citation scheme on his lecture
  notes — QICLean's own `README.md` states "The organizing source is M.
  Wolf's lecture notes." A structural/citation relationship, absent
  reproduced text, likely does not require the same redistribution grant
  `Papers/NOTICE.md` documents, but no dry run checked this and no note
  records that the question was ever asked of Wolf. **UNREHEARSED**:
  confirm with the repository owner whether such permission has been
  sought/received, and if the answer is "not yet," decide whether to record
  a `Notes/NOTICE.md` (or an equivalent line in QICLean's own `README.md`)
  before or shortly after the real cutover, and before QICLean's repository
  visibility changes from what it is now.

---

## 2. Freeze

1. **Announce** on `LionSR/TNLean` issue #6622 (see also Section 8 for the
   comment this runbook's own publication posts): freeze window start/end,
   and the exact path list being held (`docs/movers.txt` from the
   re-derivation below, once cut).
2. **Hold** merges of any open PR whose changed files intersect
   `docs/movers.txt` for the freeze window's duration (Section 1.1's `git
   log --oneline $FREEZE_SHA..origin/main -- ...` check, re-run immediately
   before Section 3 starts, must come back empty).
3. **Re-derive `movers.txt`** against the frozen commit, using run 3's
   corrected algorithm (`build_movers3.py`, unchanged from the dry run):

   ```bash
   # Confirm the two seed-rule scouting claims still hold before running the
   # algorithm (run 3 §1's own pre-check; both must return the reported counts):
   grep -rl "^import TNLean\.MPS\|^import TNLean\.Spectral" \
     TNLean/Kraus/Wielandt/ TNLean/Kraus/Wielandt.lean   # expect: zero hits (30 files)
   grep -rl "^import TNLean\.Wielandt" TNLean/ --include='*.lean' \
     | grep -v '^TNLean/Wielandt/'                        # expect: the 9 MPS files + 1 PEPS
                                                            # file + Algebra/BurnsideMatrix.lean
                                                            # + Spectral/QuantitativeGap.lean

   python3 build_movers3.py /path/to/TNLean-clone /path/to/output-dir
   # Produces movers.txt / dragged.txt / excluded.txt / seed_source.txt.
   # Seed = scripts/qic_layer0_modules.txt (a) + full Channel/, Entropy/,
   # Kraus/ (includes Kraus/Wielandt/), QPF/ (b) + poison-filtered Spectral/
   # (c); legacy Wielandt/ is never in the loop; no force-seeded (d) entries.
   ```

   Expected result (run 3's numbers, for comparison — the real freeze commit
   will differ since `main` has moved on): 512 final movers, 11 excluded
   (the `Spectral/MPVOverlapTrace.lean` chain), 9 dragged (the interface
   surface — see Section 3's verification points), zero legacy-`Wielandt/`
   movers. A materially different count is not itself wrong (mover-set
   growth tracked upstream refactors 1:1 across runs 1→2, +5 files, all
   explained) but should be diffed against `docs/movers.txt`/`docs/dragged.txt`
   on this branch and explained before proceeding, the same way run 2's
   report explained its 5-file delta from run 1.

---

## 3. Re-cut

Full command sequence (run 3's pipeline, structurally identical to runs 1–2
except for the corrected seed script in step 1 and the absence of the
`_tNLean` mechanical-fix step, which upstream has not needed since run 2):

```bash
# 1. Build the mover set — done in Section 2 above; movers.txt/dragged.txt/
#    excluded.txt/seed_source.txt are inputs to the steps below.

# 2. Fresh clone (real run: clone the canonical GitHub remote directly, to
#    preserve author/committer identity; a --no-hardlinks local clone is
#    bit-identical if a local source is used instead).
git clone https://github.com/LionSR/TNLean.git TNLean-src
cd TNLean-src
git checkout -B main origin/main   # or the frozen $FREEZE_SHA if main has
                                    # advanced past it (expected — see the
                                    # note at the top of this runbook)

# 3. Extract with history.
cp movers.txt paths.txt
cat >> paths.txt <<'EOF'
lean-toolchain
lakefile.toml
lake-manifest.json
LICENSE
.gitignore
EOF
git-filter-repo --paths-from-file paths.txt --force

# 4. Re-root.
git mv TNLean QICLean
find QICLean -name '*.lean' | xargs perl -pi -e 's/^import TNLean\./import QICLean./'
# hand-edit lakefile.toml (name/lean_lib -> QICLean, drop checkdecls +
# lint_style lean_exe since scripts/ didn't move, keep Gametheory + mathlib)
# hand-edit lake-manifest.json (drop checkdecls package entry, rename "name")
python3 generate_import_aggregators.py --root /path/to/TNLean-src   # after
# sed s/TNLean/QICLean/g on a copy of scripts/generate_import_aggregators.py
git add -A && git commit -m "..."   # 3-4 commits; run 3's pattern: re-root +
                                     # import rewrite, lakefile/manifest,
                                     # generated QICLean.lean aggregator,
                                     # doc/ledger record

# 5. Build.
lake exe cache get   # must report "already-cached" / no source rebuild —
                      # this is the hard cache-policy gate from CLAUDE.md
lake build
# Rename-hazard check (cheap, do it regardless of whether the build fails —
# run 1 needed this fix, runs 2-3 did not because the anonymous-instance
# hazard was fixed upstream in a1d8ac88c; a NEW anonymous instance could
# reintroduce the class):
grep -rn "_tNLean\b" --include="*.lean" .
# Any hit: repoint the call site at the QICLean-suffixed name (verify via
# `lake env lean` on a probe file) and re-run `lake build`.

# 6. Push (to a dry-run/staging branch first — see Section 4 for the
#    decision on pushing to `main` itself).
git remote add qiclean https://github.com/LionSR/QICLean.git
git push qiclean refs/heads/main:refs/heads/<staging-branch>
```

### Expected timings

Run 3 (smallest, cleanest cut — no legacy `Wielandt/`): `lake exe cache get`
~81s, `lake build` green on the first pass in **~8m11s** (9235/9235 jobs).
Runs 1–2 (larger trees, 535/540 files, legacy `Wielandt/` included) took
~13.5 and ~14.5 minutes respectively. **A real cut under the run-3 seed rule
should land close to the ~8 minute figure**, plus `git-filter-repo`'s own
runtime (not separately timed in any report, folded into the ~15 minute
combined estimate this runbook's task brief anticipates).

### Verification points

1. **History preservation** — sample `git log --oneline --follow` on files
   spread across the tree (run 1's three samples: a shallow file with 3
   commits, `Channel/Basic.lean`-equivalent with 21, a
   `Wielandt/SpanGrowth`-equivalent with 14 — all traced back to the
   original `4fc72eb refactor: reorganize TNLean into Mathlib-standard
   directory hierarchy` commit). Confirm the filtered branch's commit count
   dropped from the source's full history (run 1: ~12084 → 1652 pre-re-root;
   run 3's corrected, smaller cut: 1579 commits) but each sampled file still
   shows multiple real commits, not a single squash.
2. **Green build at scale** — run 3's reference point is **9235/9235 jobs,
   zero failures**; treat a first-pass count far below that (with the
   run-3-derived mover set) as a sign the closure computation regressed.
3. **`ls-remote` hygiene** — before AND after pushing, `git ls-remote
   https://github.com/LionSR/QICLean.git` and confirm every branch other
   than the one just pushed is at its pre-push SHA (run 3's own
   verification table, Section 7 of `extraction_dryrun3_report.md`, is the
   template — copy it into the real cutover's own report).
4. **`sorry`/`axiom`** — `grep -rnE '^\s*axiom\s'` and a manual check of
   word-boundary `sorry`/`axiom` hits; all three dry runs found zero real
   occurrences (only docstring prose, e.g. "sorry-free"). A real hit here
   blocks the push.

---

## 4. Publish

**UNREHEARSED in its entirety — no dry run pushed to `main`, tagged, or
enabled CI on the real repository.** The two branch-state options below are
both mechanically simple; the choice between them is Section 1.3's owner
decision.

### Option A — clear `main` (owner has approved discarding the scaffold commit)

```bash
# DESTRUCTIVE to QICLean main's history. Confirm Section 1.3's decision was
# made explicitly (not inferred) before running this.
git push qiclean +refs/heads/main:refs/heads/main   # force-push the
                                                      # filtered history over
                                                      # the scaffold commit
```

### Option B — force-replace is not approved; graft the scaffold commit as an ancestor

```bash
# Rebase the filtered extraction history onto e1650a1f instead of pushing
# over it, preserving the scaffold commit as part of main's ancestry.
git rebase --onto e1650a1fdbc47c2d0535a7e15209e710ff1c09c3 --root
git push qiclean HEAD:refs/heads/main   # ordinary fast-forward or PR merge,
                                          # depending on branch protection
```

**Protection against pushing the wrong ref**: run `git ls-remote` (Section
3's verification point 3) immediately before this step and diff against the
last-known-good table; never construct the push command by hand-editing a
previous dry run's command line (the branch name is the single field every
dry run changed between runs — `dryrun-2026-08-20` →
`dryrun-2026-08-21`/`dryrun-packaging-2026-08-21` →
`dryrun3-2026-08-21`/`dryrun3-packaging-2026-08-21`).

### Stack the packaging commits

The packaging content (CI workflows, `blueprint/`, `docs/`, `scripts/`,
`home_page/`, `interface_edges.md`, `missing_decls.md`, `README.md`,
`docs/getting_started.md`) cherry-picks cleanly onto a fresh Lean-tree cut —
verified twice (`packaging_report.md` §6 onto run 1's cut; run 2's report §5
and run 3's report §6 onto their respective cuts, all zero-conflict):

```bash
git log <prior-packaging-branch>..<prior-packaging-branch-tip> --oneline
git cherry-pick <the 3-4 packaging commits, oldest first>
# Then regenerate the two ledgers against the real cut's own tree/movers.txt
# (mechanical, both tools already exist):
python3 scripts/blueprint_lean_sync.py --root .   # -> missing_decls.md
python3 scripts/qic_blueprint_boundary_report.py --mode blueprint-files \
  # -> interface_edges.md; use PR #6806's item-level split (schema v4), NOT
  # run 1/2/3's whole-file >=50%-item-fraction method, which every dry run
  # flagged as superseded but never replaced (see Section 7's follow-ups)
```

### Tagging — **UNREHEARSED**

No dry run cut a tag. Present options for the owner to choose from (none
rehearsed): `v0.1.0-pre` (pre-release, signals "extracted but not yet
load-bearing"), `v0.1.0` (first real release, if the consumer switch in
Section 5 is landing in the same change window), or a date-stamped tag
matching the freeze-commit convention already used for branch names
(`extraction-2026-MM-DD`). Whichever is chosen, TNLean's `lakefile.toml`
`[[require]]` block in Section 5 must pin `rev` to it exactly, not to a
branch name — branches move, tags (by convention, not enforced by Lake)
should not.

### Enabling CI and verifying first runs — **UNREHEARSED**

`packaging_report.md` §1 lists 7 workflows staged (`pr-ci.yml`,
`blueprint.yml`, `import-completeness.yml`, `docgen.yml`,
`create-release.yml`, `update.yml`, `deploy-pages.yml`) plus 5 agentic
workflows explicitly deferred pending secrets/labels/action-access grants
(`agent-mention.yml`, `auto-fix.yml`, `pr-review.yml`,
`claude-provider-limit-guard.yml`, `lean-linter-warning-autofix.yml`). No
dry run ran any of these workflows for real (all `actionlint`/`py_compile`/
unit-test checks were static, not live CI runs). Before declaring CI green:
confirm the 7 staged workflows' secrets exist on the real `LionSR/QICLean`
repository (in particular whatever `pr-ci.yml`/`blueprint.yml` need beyond
the deploy key already provisioned for the *reverse* direction — see Section
5), and watch the first live run of each to completion.

---

## 5. Consumer switch

Rehearsed end-to-end in `consumption_dryrun_report.md` against run 1's
snapshot (`dryrun-2026-08-20`, 535 movers) — the mechanics below are
mover-set-agnostic (they operate on whatever `docs/movers.txt` the real cut
produces) and were **10065/10070 targets green**, with the only 4 failures
traced to one root cause (snapshot staleness), not a procedural defect.

### 5.1 TNLean-side PR recipe

```bash
# 1. Delete the mover files (100% of docs/movers.txt paths existed and were
#    removed cleanly in the dry run; 0 missing).
xargs rm < docs/movers.txt   # from TNLean repo root; adjust for the real,
                              # re-derived movers.txt from Section 2

# 2. Add the QICLean git dependency, pinned to the real tag from Section 4
#    (the dry run pinned to a branch name; the real cutover must pin to the
#    tag once one exists):
cat >> lakefile.toml <<'EOF'
[[require]]
name = "qiclean"
git = "https://github.com/LionSR/QICLean.git"
rev = "<the tag from Section 4>"
EOF
lake update qiclean
# Dry-run result: ~80s, zero manifest conflicts — QICLean's lakefile pins
# the identical mathlib rev (v4.34.0-rc1) and Gametheory rev TNLean already
# uses, so Lake's solver converges without vendoring.

# 3. Generic import rewrite (script: rewrite_imports.py from the dry run;
#    applies `import TNLean.X` -> `import QICLean.X` for every X in
#    movers.txt):
python3 rewrite_imports.py --root .
# Dry-run result: 273 files touched, 630 import statements rewritten.

# 4. Regenerate import aggregators.
python3 scripts/generate_import_aggregators.py
# Dry-run result: aggregators for wholesale-moved directories (Channel,
# Entropy, Kraus, QPF under run 1's seed rule) are dropped entirely; the
# remaining aggregators (root TNLean.lean, Algebra.lean, MPS.lean, etc.) are
# regenerated. Under run 3's corrected seed rule, Wielandt.lean stays
# populated (legacy Wielandt/ never moves), so the exact directory list
# will differ from the dry run's — verify against the real movers.txt, not
# by copying run 1's 4-removed/11-regenerated list verbatim.
# Generator caveat (informational, confirmed safe in the dry run but not
# guaranteed in general): the generator has no QICLean awareness and drops
# references to moved umbrella modules rather than rewriting them to
# `import QICLean.X`; this was safe because no production file imports a
# directory-umbrella file directly (only TNLean.lean does). Re-verify this
# invariant still holds at cutover time.

lake exe cache get   # must show "already-cached" per the hard cache rule
lake build
```

### 5.2 Expected result

10065+ targets build cleanly. Watch specifically for the failure class the
dry run found and root-caused:

> **Snapshot-staleness hazard** — if an in-flight TNLean PR renamed or
> restructured a file that's in `movers.txt` between when the QICLean
> extraction snapshot was cut and when this consumer switch runs, the moved
> file exists in both trees with mismatched namespaces/identifiers (dry-run
> example: `QICLean/Kraus/Word.lean` predated PR #6756's Kraus/MPSTensor
> split, so `MPSTensor` was declared twice and `Kraus.evalWord` didn't
> resolve — 4 failed targets, all traced to this one cause).

**Freeze rule (the actionable fix, process not code)**: re-cut or rebase the
QICLean extraction snapshot immediately before running this consumer
switch, inside the freeze window from Section 2 — do not reuse an
extraction snapshot that predates the freeze window's start.

### 5.3 In-repo boundary-guard retirement

`import-completeness.yml`'s TNLean-side, pre-extraction guards
(`check_import_direction.py`'s forbidden-prefix enforcement,
`qic_blueprint_boundary_report.py`) become structurally unnecessary once
QICLean is a real, separate Lake dependency — QICLean cannot import TNLean
regardless of any in-repo guard, because there is no Lake requirement on the
TNLean side of that edge for such an import to resolve against
(`packaging_report.md` §1's reasoning for why `import-completeness.yml`
drops those two steps in the QICLean-side copy of the workflow).
**UNREHEARSED as a TNLean-side removal step**: no dry run deleted or
disabled these guards on the TNLean side; retire them only after Section
5.2's build is verified green with the real dependency in place, not before.

### 5.4 TNLean-side blueprint/docs split

Once the QICLean-side `blueprint/` tree from Section 4 exists with real
content, TNLean's own `blueprint/` should drop the 65+ content-fragment
files that moved (per `packaging_report.md` §2's Wolf-chapter mapping
table) and gain an interface chapter restating any label still cited by a
TNLean-side `\uses` edge (per issue #6622's own preflight comment: "keep a
TNLean interface chapter that restates every moved label still used by TN
`\uses` edges"). **UNREHEARSED**: no dry run wrote or tested this interface
chapter's content; `interface_edges.md`/`missing_decls.md` on this branch
are the worklist (112 `\lean{}` tags currently unresolved, concentrated in
the two Wielandt blueprint files and 4 `Matrix.*` RFP/MPDO helper lemmas —
see run 3 report §6), not the interface chapter itself.

---

## 6. Rollback per stage

**Before main-push** (Sections 1–3): trivial. Nothing outside a disposable
local clone and disposable QICLean feature/staging branches has been
touched. Delete the staging branch (`git push qiclean :refs/heads/<staging-branch>`)
and re-run Section 3 from a fresh clone; `main`, `scaffold-preview`, and
every prior dry-run branch are untouched by construction (verified after
every one of the three dry runs via `git ls-remote`).

**After main-push, before TNLean merge** (Section 4 done, Section 5 not yet
merged): `main` now carries the real extraction history (Option A) or the
grafted history (Option B). Recovery is a force-push back to the
pre-cutover SHA (`e1650a1fdbc47c2d0535a7e15209e710ff1c09c3` under Option A,
or the pre-rebase tip under Option B) — this is safe precisely because no
external consumer (TNLean's `lakefile.toml`) references the new `main`/tag
yet. **UNREHEARSED**: no dry run exercised this recovery path; treat the
pre-cutover SHA as the recorded rollback point and confirm it via
`git ls-remote` immediately before Section 4 runs, the same way Section 3's
verification point 3 does for staging branches.

**After TNLean merge** (Section 5's PR is merged to TNLean `main`): rollback
means reverting the TNLean-side PR (restores the deleted mover files, the
`lakefile.toml` dependency, and the import rewrites via ordinary `git
revert`) — QICLean's own `main`/tag does not need to move, since TNLean
reverting to importing its own local copies of the mover files does not
require QICLean to be rolled back. **UNREHEARSED**: no dry run performed a
revert; this is the standard TNLean PR-revert path (`git revert -m 1
<merge-commit>` for a squash/merge-commit PR), not a novel procedure, but no
report exercised it against this specific PR shape (bulk file deletion +
lakefile edit + 630-import rewrite + aggregator regeneration).

---

## 7. Post-cutover

- **CI caches** — `lake exe cache get` behavior confirmed correct in all
  four dry runs (three Lean-tree, one consumer-side): every run reported
  "already-cached"/"No files to download" against the shared Mathlib
  `v4.34.0-rc1` pin, satisfying `CLAUDE.md`'s hard cache-fetch-before-build
  rule with no source rebuild. Post-cutover, confirm the real QICLean CI
  (once enabled per Section 4) populates its own cache the same way rather
  than triggering a from-source Mathlib build on its first live run.
- **Archive dry-run branches** — six branches currently exist on
  `LionSR/QICLean` beyond `main`/`scaffold-preview`: `dryrun-2026-08-20`,
  `dryrun-packaging`, `dryrun-2026-08-21`, `dryrun-packaging-2026-08-21`,
  `dryrun3-2026-08-21`, `dryrun3-packaging-2026-08-21` (this branch's
  Lean-tree counterpart). Once the real cutover's history-preserving push
  lands on `main`, these are superseded; delete or rename with an
  `archive/` prefix per the repository owner's preference. **UNREHEARSED**
  as a decision (no dry run deleted anything — Section 1.3/Section 4 branch
  hygiene was the point of every `ls-remote` check across all three runs).
- **Tracking-issue update** — close out `LionSR/TNLean` #6622 (and its
  sub-issues, most already closed per the issue thread: #6684, #6695,
  #6701, #6702, #6728, #6731, #6734, #6740, #6743) with a pointer to the
  real cutover's commit/tag, mirroring the pattern already used for every
  dry run in this thread (each dry run posted its own summary comment; the
  real cutover's comment should supersede, not duplicate, the three dry-run
  summaries already there).
- **Known follow-ups**:
  - **Remaining `MPSTensor` namespaces in QICLean** — run 3's dragged ledger
    still carries `TNLean/MPS/Defs.lean` (the `MPSTensor` core definition
    itself, dragged in for its Kraus/word-evaluation machinery via
    `MPS/Core/Transfer.lean`) and `TNLean/MPS/Tactic/Attr.lean`. This is
    the one place QICLean's tree still carries MPS-vocabulary content by
    necessity (run 1 §1's own note); no dry run treated this as a defect,
    but it is the residual surface a future MPS-core split (analogous to
    the already-landed #6745–#6749 word-core split) would need to
    address if the goal is a zero-`MPSTensor` QICLean tree.
  - **`interface_edges.md` residue** — every packaging pass (Section 4)
    flagged this file as using the superseded whole-file
    ≥50%-item-fraction classification instead of PR #6806's item-level
    split (schema v4, `docs/audits/data/qiclean/blueprint-files.txt`).
    Regenerating it correctly requires re-running
    `qic_blueprint_boundary_report.py --mode blueprint-files` against the
    real cut's `movers.txt`, not hand-porting any dry run's numbers
    forward — flagged three times (run 1's packaging pass, run 2's report
    §5, run 3's report §6) and still open at the time of this runbook.

---

## Appendix: dry-run report and branch cross-reference

| Report | TNLean snapshot | Mover count | Build result | QICLean branch(es) |
|---|---|---|---|---|
| `docs/extraction_dryrun_report.md` (run 1) | `28d2c97b5` | 535 (34 poisoned, 8 orphaned) | Green after 1 mechanical fix, 9262 jobs, ~13m31s combined | `dryrun-2026-08-20` (`324135a8`); packaging `dryrun-packaging` (`ee1ecd81`) |
| run 2 (`extraction_dryrun2_report.md`) | `07ffebe4c` | 540 (34 poisoned, 9 orphaned) | Green first pass, 9267 jobs, ~14m24s | `dryrun-2026-08-21` (`505a4c04`); packaging `dryrun-packaging-2026-08-21` (`65021ab7`) |
| `docs/extraction_dryrun3_report.md` (run 3, **authoritative seed rule**) | `b51276ece` | **512** (11 poisoned, 7 orphaned) | Green first pass, 9235 jobs, ~8m11s | `dryrun3-2026-08-21` (`7b7b832d`); packaging `dryrun3-packaging-2026-08-21` (`ed2c50a9`, **this branch**) |
| `consumption_dryrun_report.md` (consumer side) | `53d3e966e` (TNLean), dep on `dryrun-2026-08-20` | n/a (deletes run 1's 535) | 10065/10070 green, 4 failures = 1 snapshot-staleness cause | n/a (TNLean-side scratch tree only, nothing pushed) |
