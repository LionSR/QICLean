# Polar correction publication snapshot

This package republishes the checked local snapshot
`76309870283b5cee3122ac409405e100c2b51744` on QICLean main
`c7a904b2bc203906aa2f5c4a44f61fa465ee2eaf` (2026-10-07).
Its parent tree is `ca578cd8101b343b3bac2d07fbcd1008de1bb904`.

The earlier [audit](../../../audits/2026-10-07_polar_unitary_correction.md),
JSON records and logs remain historical evidence with their original hashes.
Their publication-hold statements describe the earlier local checkpoint.
Destination authorization was subsequently given for a draft QICLean PR.
The draft PR and its checks are the authority for remote publication and CI status.
Neither the retained local records nor this note certify a full root build or CI.

## Source preservation

All two production modules, four regression/axiom-guard modules, the raw
axiom driver, the blueprint leaf and the historical evidence are unchanged
from the checked snapshot. All 12 QICLean modules in the production import
closure are byte-identical. The toolchain, Lake configuration and dependency
manifest also match the checked snapshot exactly. The old worktree is retained.

The generated Analysis imports retain current-main additions. The existing
build job keeps its shifted-density power, shifted-density truncation and
global-gap regressions, with one additional polar regression step. The entropy
chapter retains its current conditional-continuity input. No independent
polar branch or PR was found in the publication preflight; open QICLean PRs
overlap only in the generated Analysis aggregator.

## Publication preflight

The following source checks passed in the refreshed publication worktree:

- `python3 scripts/generate_import_aggregators.py --check`
- `python3 scripts/check_numbered_lean_files.py`
- `python3 scripts/check_oversized_lean_files.py`
- `python3 scripts/blueprint_lean_sync.py --root . --ci`
- `python3 scripts/check_reader_facing_prose.py --root . --diff-base c7a904b2bc203906aa2f5c4a44f61fa465ee2eaf --ci`
- `sha256sum -c docs/provenance/evidence/8766/SHA256SUMS`
- The pinned external-policy provenance checker documented in the audit
- YAML parsing, `bash -n` on the polar regression step and `git diff --check`

The original strict production/consumer checks, all six standard-axiom reports,
the native 3107-job target build and four-page PDF/static-HTML review remain
recorded at their actual execution revisions. They are not relabelled as fresh
runs on the publication commit. Exact-head full PR CI remains pending at
publication. No generated binaries or Git LFS files are included.

The full-book PDF has a separately reproduced inherited blocker at
`blueprint/src/chapter/ch13_spectral_filter.tex:114`: unbraced `\int_\R`
fails XeLaTeX. That unrelated source is unchanged here. The earlier focused
polar render does not establish that the entire book renders.

This is the generic singular-square polar correction component. It does not
complete geometric reset, angular support, full area-law amplification or either
manuscript headline theorem. No mathematical hypothesis or proof text changed
while preparing this publication snapshot.
