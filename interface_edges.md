# Cross-boundary blueprint edges severed by the QICLean extraction

Regenerated 2026-08-21 against this branch's final tree (see `missing_decls.md`
for the item-level repair that produced it) and the authoritative item-level
boundary report, computed by running `scripts/qic_blueprint_boundary_report.py`
(LionSR/TNLean, schema v4, carried since issue #6801 / PR #6806, atomicity
fix PR #6818) against a read-only snapshot of `LionSR/TNLean` at
`b51276ece7fcbe1cc845f6548106f3796c638204` -- the exact commit this branch's
own Lean-tree dry run (`docs/extraction_dryrun3_report.md`) used -- with the
script's own `mover_files()` (the narrower, 498-file CI-guard boundary at
that commit) substituted for this branch's `docs/movers.txt` (512 files, the
corrected extraction boundary). This supersedes every number in the prior
revision of this file, which used the superseded whole-file `>=50%`-item-
fraction classification (PR #6806 replaced that method entirely; this file's
own staleness note said so and is now resolved).

Two report classes below: (1) edges this pass repaired or produced zero of,
regenerated fresh against the item-level scheme; (2) a pre-existing coverage
gap the item-level scheme surfaces but this pass does not close, because
closing it means adding new chapter files, not reclassifying existing ones,
which is out of scope for a `\lean{}`-tag repair pass (`missing_decls.md`
records the same boundary).

## 1. `qic`-disposition statement `\uses`/`\ref`-ing a `tn`-disposition label

The authoritative report finds exactly **2** such edges in TNLean's entire
4,809-item blueprint (down from the last full recount of 19): one `\uses`
edge and one reference edge.

| Kind | Source label | File:line | Target label | Status |
|---|---|---|---|---|
| `\uses` | `lem:trace_transfer_map_left_canonical` | `chapter/ch04_channels_transfer_map_foundations.tex:193` | `def:left_canonical_tensor` | **Fixed this pass** -- `def:left_canonical_tensor` is `tn`-disposition (`MPSTensor.IsLeftCanonical`, `TNLean/MPS/Core/CanonicalNormalization.lean`) and was removed from `chapter/ch06_qpf.tex` in this pass; `def:transfer_map` dropped from the `\uses{...}` list, statement text unchanged. |
| reference | `def:eventually_nonzero_proportional_mpv` | `chapter/ch02_mps.tex:353` | `lem:bnt_overlap_orthonormal_li` | **Not applicable to this branch** -- both labels are defined in chapter files (`ch02_mps.tex`, `ch10_bnt_normal_and_gram_support.tex`) that are not present in this branch's blueprint at all (see \S3). |

A whole-tree scan (`\uses`, `\ref`, `\eqref`, `\cref`, `\Cref`, multi-line-safe)
confirms **zero** other instances anywhere in this branch's current
`blueprint/src` tree of a retained statement depending on a label this pass
removed: all 109 labels removed in this repair (`missing_decls.md`) were
checked and none is still referenced.

## 2. Item-level classification of the whole TNLean blueprint (context)

For reference, the authoritative report's whole-tree counts (all of TNLean's
blueprint, not just what is present on this branch):

| Category | Count |
|---|---:|
| Items classified `qic` | 1,532 |
| Items classified `tn` | 3,277 |
| Items classified `mixed` or `unresolved` | 0 |
| Mixed physical files (both `qic` and `tn` items) | 47 |
| Internal `\uses` edges | 10,336 |
| `tn`-statement `\uses`-ing a `qic` label (expected direction) | 1,150 |
| Internal reference edges | 3,381 |
| `tn`-side reference to a `qic` label (expected direction) | 183 |
| Non-item-block internal references | 388 |
| Non-item-block `tn`-to-`qic` references | 54 |
| `blueprint_files` manifest size (ideal QIC-side file set) | 167 |
| `tn-interface-labels` manifest size | 308 |

Of the 47 mixed physical files, this pass item-split the 10 responsible for
the 112 dangling `\lean{}` tags (`missing_decls.md`); the remaining 37 are
untouched by this pass (\S3).

## 3. Coverage gap: `qic`-disposition content absent from this branch entirely

**Status update (2026-08-21, second pass): the 77-occurrence severed-edge
symptom below is closed; the underlying 64-file coverage gap is deliberately
NOT closed by copying those files.** Re-running the boundary report against
the same recorded TNLean snapshot found that the 64 `.tex` files this section
lists skew overwhelmingly `tn`-disposition item-by-item (1,202 `tn` items
against 249 `qic` items across those files) -- the item-level `qic` fraction
that put them on this list is concentrated in a handful of items per file,
not the file as a whole, exactly the "Lean-level bridge-module drag" pattern
this section's own note already flagged for `ch02_mps.tex`. This branch
already carries the same verdict for other files by name:
`appendix/ft_mps_appendices.tex` and `chapter/ch08_wielandt.tex` exclude
`ch08_wielandt_word_span_and_block_injectivity`, `ch09_canonical` (chapter
and appendix), and `ch10_bnt` with the comment "their statements conclude in
MPS/MPV vocabulary". Copying all 64 files and then stripping ~83% of their
content back out was rejected as the repair method.

Instead, every one of the 32 target labels was resolved individually: 22 by
relocating the specific `qic`-disposition item (verbatim text, with a note
citing its TNLean source chapter) into the existing QICLean chapter that
already depends on it, and 10 by pruning the dangling `\uses`/`\ref` from the
citing statement (content stays in TNLean; the citing statement's own text is
unchanged). Full accounting, per-label disposition, and the exact insertion
points are in `missing_decls.md` ("Coverage-gap closure pass"). Verified
result: 0 dangling `\uses`/`\ref`/`\eqref`/`\cref`/`\Cref` targets anywhere in
`blueprint/src` (one pre-existing `##1` regex false match inside a
`\clist_map_inline` macro parameter aside), and `leanblueprint web` builds
with zero label-resolution errors.

The **64-file physical gap itself remains open** -- no new chapter files were
added for the content still absent from this tree (parent-Hamiltonian,
MPDO/RFP, BNT, canonical forms, periodic/algebraic FT, PEPS FT, MPU,
`ch02_mps.tex`, `ch01_intro.tex`), and none of those file paths were copied.
That is an intentional, narrower scope than "close the coverage gap by
copying the files": the per-item ratio above means most of that content
would need to be deleted immediately after copying, and several of those
chapters (`ch02_mps.tex` foremost) are ones this branch has already decided,
by name, belong to TNLean. See `docs/cutover_runbook.md` \S7 for that
residual scope.

**Update (2026-08-21, third pass): the `appendix/ft_mps`/`appendix/full_only`
split itself is now gone**, on explicit confirmation from the repository
owner that this reflects standing direction (QICLean's blueprint should
match Wolf's own chapter organization, not carry TNLean's paper-volume
split). `appendix/ft_mps/{ch05_schwarz,ch06_qpf,ch07_spectral,
ch08_wielandt}.tex`, `appendix/full_only/{ch25_positive_not_cp,
ch25_schmidt_number_and_witnesses,ch27_channel_asymptotics}.tex`, and the two
router shells `appendix/ft_mps_appendices.tex` /
`appendix/full_only_appendices.tex` are deleted. Their content is now six
`chapter/chNN_..._supporting_results.tex` files (`ch25_positive_not_cp_
supporting_results.tex` also carries the former `ch25_schmidt_number_and_
witnesses.tex` content, which TNLean nested inside it), each `\input` in
`content.tex` immediately after its Wolf-chapter's main content, so it reads
as a same-chapter continuation rather than a separate numbered appendix part
(`\appendix`/`\part{Appendices}` is gone; there is no longer a distinct
appendix numbering track). Every former `\label{ch:*_supporting_results}`
name is preserved (now labelling a `\section` instead of a `\chapter`, since
the content no longer opens its own chapter); none of those six labels was
referenced by `\ref` anywhere in this tree before or after the change. No
path under `blueprint/src` contains `ft_mps` or `full_only` after this pass.
`content.tex`'s final Wolf-chapter-to-file mapping is in `missing_decls.md`.

Comparing this branch's `blueprint/` tree against the authoritative report's
own `blueprint_files` manifest (167 paths) shows **68** `.tex` content files
and **4** non-`.tex` build-support files (`library.bib`,
`src/Packages/tenkz_pic.py`, `src/plastex_templates/TenkzPictures.jinja2s`,
`src/tenkz_pic.sty`) that the item-level scheme selects as carrying `qic`
content but that this branch's whole-file packaging pass never copied,
`chapter/ch02_mps.tex` foremost (TNLean's core "Matrix Product Vectors"
chapter -- `MPSTensor`, word evaluation, `mpv` -- kept in TNLean by an
explicit, documented override in the prior revision of this file, because
its item-level `qic` fraction is an artifact of a Lean-level bridge-module
drag, not a verdict on the chapter's subject).

This is a **coverage** gap (content that should exist in this tree and does
not), distinct from the dangling-tag gap `missing_decls.md` repairs, and it
is why a whole-tree label scan still finds severed edges after this pass:

| Kind | Occurrences | Distinct target labels |
|---|---:|---:|
| `\uses` | 51 | 21 |
| `\ref`/`\eqref`/`\cref`/`\Cref` | 26 | 18 |
| **Total** | **77** | **32 (union)** |

Every one of the 32 target labels resolves, in the authoritative report, to
`qic`-disposition content (or a `shared`/`tn`-disposition chapter-level
label) defined inside one of the 68 missing files -- none is a typo or an
orphan. Representative targets and their true home:

```
def:transfer_map, def:injective, def:eval_word, def:gauge_phase_equiv,
eq:mps_transfer_map                                -> chapter/ch02_mps.tex
def:mixed_transfer, def:mixed_transfer_rect,
eq:spectral_mixed_transfer      -> chapter/ch07_spectral_mixed_transfer_and_overlap.tex
thm:cyclic_decomposition_irreducible_schwarz, thm:peripheral_cyclic_group,
thm:channel_period_divides_dim, thm:peripheral_multiplicity_one
                    -> chapter/ch07_spectral_peripheral_refinements_and_primitive_overlap.tex
lem:is_kraus_cp_comp, lem:is_kraus_cptp_comp, lem:mpdo_right_partial_trace_cptp,
lem:mpdo_single_kraus_map_cp, lem:mpdo_state_preparation_cp,
lem:mpdo_state_preparation_cptp, thm:mpdo_equiv_reindex_cptp,
thm:mpdo_single_kraus_map_cptp       -> chapter/ch21_mpdo_rfp_renormalization.tex
def:bipartite_operator_schmidt_rank,
thm:mpdo_support_log_kronecker -> chapter/ch21_mpdo_rfp_area_law_diagonal_and_pure_state_bounds.tex
lem:trace_lift_left_factor_mul, lem:trace_lift_right_factor_mul,
thm:partial_trace_left_pos  -> chapter/ch13_parent_hamiltonian_decorrelation_marginal_supports.tex
thm:mpu_transfer_matrix_vectorization              -> chapter/ch28_mpu.tex
thm:skolem_noether                                 -> chapter/ch03_single.tex
ch:mps, ch:spectral, ch:mpdo_rfp, ch:parent_hamiltonian, ch:ft_proof
        -> chapter section labels of the corresponding missing chapter files
```

Per-file occurrence counts (files with severed edges pointing at \S3's
missing content):

| File | `\uses` | `\ref`/`\eqref`/`\cref` |
|---|---:|---:|
| `appendix/ft_mps/ch07_spectral.tex` | 7 | 11 |
| `chapter/ch04_channels_transfer_map_foundations.tex` | 6 | -- |
| `chapter/ch05_schwarz_ft_core.tex` | 2 | 1 |
| `chapter/ch06_qpf.tex` | 10 | -- |
| `chapter/ch12_auxiliary_wolf_ch01_positive_maps.tex` | 11 | 6 |
| `chapter/ch16_channel_representations_self_dual.tex` | 1 | 1 |
| `chapter/ch19_entropy_tripartite_and_ssa_i.tex` | 1 | -- |
| `chapter/ch19_entropy_tripartite_and_ssa_ii.tex` | 3 | 1 |
| `chapter/ch19_entropy_von_neumann_and_relative_ii.tex` | 9 | -- |
| `chapter/ch27_channel_asymptotics_direct_sum_schwarz_maps.tex` | 1 | -- |
| `chapter/ch04_channels_peripheral_spectrum_and_primitivity.tex` | -- | 2 |
| `chapter/ch05_schwarz.tex` | -- | 1 |
| `chapter/ch07_spectral_ft_peripheral_cyclic.tex` | -- | 1 |
| `chapter/ch12_auxiliary_channel_theory.tex` | -- | 2 |

All 77 occurrences pre-date this pass (they cite content that was never on
this branch, in files this pass did not touch, or -- for `ch04`/`ch06`/
`ch07_spectral`/`ch27_channel_asymptotics_direct_sum_schwarz_maps`, which
this pass did edit -- they sit on statements that were `qic`-disposition
and retained both before and after this pass); none is new. Closing this
gap means physically adding the 68 missing files (an item-level split of
`chapter/ch02_mps.tex` in particular, since only part of its content is
`qic`-disposition, per the same rule this pass applied to the 10 files it
did split) -- that is the real cutover's Section 4-6 content pull, not a
`\lean{}`-tag repair, and is exactly the gap `docs/cutover_runbook.md` \S7
"Known follow-ups" already flags as open. Not attempted here.

## 4. Reverse direction: `tn`-side entry `\uses`/`\ref`-ing a `qic` label

Expected direction (TNLean depends on QICLean once split), not itself a
defect. See \S2's whole-tree counts (1,150 `\uses` + 183 reference + 54
non-item-block edges); this branch does not carry TNLean's own blueprint, so
there is nothing to check on this side of the boundary here.

## Summary

| Category | Prior revision (whole-file scheme) | Item-level scheme (10-file pass) | This revision (coverage-gap pass) |
|---|---|---|---|
| Classification method | `>=50%`-item-fraction, whole file | PR #6806 schema v4, per item | same, per item |
| `\lean{}` tags dangling in this tree | 112 | 0 | **0** |
| `qic`-to-`tn` `\uses` edges (whole TNLean tree) | 1 | 0 | 0 |
| `qic`-to-`tn` reference edges (whole TNLean tree) | not tracked by the old method | 0 (1 exists but its labels are outside this branch, \S1) | 0 |
| Severed `\ref`/`\uses` occurrences pointing at content missing from this branch | 79 (50 labels) | 77 (32 labels) | **0** (32/32 labels resolved: 22 by relocation, 10 by reference pruning; see \S3) |
| Physical files item-split this pass | 0 | 10 | 0 (relocation into existing files, not physical item-splitting; see \S3/`missing_decls.md`) |
| Blocks removed as `tn`-disposition this pass | 0 | 120 (101 theorem-like items, 19 non-item blocks; 96 of the items carried 115 `\lean{}` declaration names between them -- 112 of those were this branch's dangling tags, the rest already happened to resolve by name coincidence; 24 blocks carried no `\lean{}` tag at all) | 5 (the `def:mixed_transfer*`-carrying items in `appendix/ft_mps/ch07_spectral.tex`) |
| Items relocated into an existing chapter this pass | -- | -- | 41 (across 8 target files; see `missing_decls.md`) |
| 64-file/4-support-file physical coverage gap (\S3) | -- | -- | 63 `.tex` files still absent (unchanged; not attempted); `library.bib` copied, 3 tenkz support files intentionally not copied |
