# Source assembly for the ALVV physical hard-truncation client

This revision is an assembly snapshot, not a new mathematical feature or an
acceptance record. Its exact base is the existing TN #10404 candidate pin
`716753c025d95fe36e3dc8f421571c81754adaaf`. The existing source provenance is
retained in `2026-10-29_aklv_published_prerequisites.md`.

The base already assembles the still-open prerequisites QICLean #978, #979,
#1005, #1006, #1007 and #1008. Their original independent PRs remain the units of
review and upstream acceptance. This snapshot adds only these exact reviewed
source files:

| Source file | Existing PR | Exact source revision |
|---|---|---|
| `QICLean/Analysis/WeylMonotonicity.lean` | [#1011](https://github.com/LionSR/QICLean/pull/1011) | `c04b69cdc483bc79c2512bbf1aba33e03e111d3e` |
| `QICLean/Analysis/RelativeLowEnergyCloseness.lean` | [#1013](https://github.com/LionSR/QICLean/pull/1013) | `4e688e3d81704e0906aae8b75cf31bf8dd4ea32b` |

Their SHA-256 digests are respectively
`7c56d7857c8ac48a0de3f3eddc5d92941fd4b9e7df9135202c62b84b374ba0cb` and
`9c71bc4ab62b9a7908a912a31dfde3185c59ae6241ce66096abbfd27dc6214fc`.
No proof or theorem statement is changed while assembling them. The generated
Analysis aggregator adds only the actual new relative-closeness module.
Every other existing Lean source blob, the toolchain, lakefile, and manifest
remain byte-identical to the exact base.

## Blueprint reconciliation

Copy only the exact new eigenvalue-comparison statement/proof from #1011 and
relative-ground-energy statement/proof from #1013 into the existing low-energy
chapter. Both statements and proofs remain `notready`. The first is inserted
before the existing one-window statement; the second is appended. Removing
these two inserted byte strings recovers the complete original base chapter
byte for byte. No existing source entry is overwritten or dropped.

The existing paper-gap notes, including the hard-truncation windows note,
remain base-byte-identical. The separate #1012 counterexample/note publication
and acceptance are not included or claimed by this snapshot.

## Validation and boundaries

At preparation all eight listed mathematical prerequisite PRs remain OPEN;
#1011/#1013 require their own fresh exact-head hosted acceptance. Independent
native source reviews of those feature sources are recorded in their existing
PRs; copying identical blobs is not an additional proof claim.

Native generated-import, full Blueprint/source and reverse-coverage checks,
source width/size/integrity, active references, whitespace, and exact source-
blob/pin preservation checks are run for this assembly. The QIC toolchain and
Mathlib dependency entries are compared with the existing TN #10404 pin's
manifests. No local Lean, Lake, build, elaboration, or compiled Blueprint check
is run. No source test fixture, dependency update, physical client, or TN pin
change is introduced.

The branch is a coherent immutable candidate for a separately owned downstream
physical client. It is published only after parent review, without a duplicate
QIC mathematical PR. Main integration and acceptance of every independent
prerequisite remain separate obligations.
