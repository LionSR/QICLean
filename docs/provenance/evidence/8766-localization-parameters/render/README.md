# Localization parameters: combined PDF and static HTML

The fixture is bound to frozen source revision
`ef3d4684394cb70e9f0bb3b73cbf11a6aaf7e9db`. It reuses the Gaussian-reindex
render workflow and copies eight complete leaves byte for byte: physical-buffer
overlap, doubled-system gap, Gaussian filtering, parameter choice, generic
uniform approximation, physical-buffer uniform approximation, finite reindexing,
and the new localization parameters. Only the external fixture's router and PDF
title differ from the source. No Lean source or blueprint leaf was edited.

[Verification](verification.json) passes for 17 PDF pages and six static HTML
pages. All 126 source labels resolve in both outputs. All 73 equation labels have
their own HTML display-block anchor and distinct PDF destination. All 120 linked
declarations match the source, including all 61 public Gaussian declarations.
All 503 HTML fragment links and 126 PDF internal links resolve, with zero missing
anchors, duplicate HTML IDs, unresolved references, or final TeX layout errors.
Declaration parsing checks identity and coverage; it does not validate proofs.

The new leaf has exactly three theorem tags, three proofs, six `leanok` markers,
and three equation labels. Both static dependency graphs contain exactly the two
proof edges into `thm:localization_parameters`, from
`thm:localization_parameter_constant` and `thm:localization_error_bound`.
The static chapter includes all three proof blocks and declaration links.

The [visual review](visual-review.json) covers physical PDF pages 16–17
(printed pages 15–16). The complete new leaf is on physical page 16. Its theorem
statements, proofs, badges, ceiling notation, three-line exponent calculation,
and equations (1.72)–(1.74) are readable without clipping or overlap. The scalar
error theorem permits arbitrary real `K` and explicitly takes the nonnegative
maximum of zero and the integer ceiling, matching the Lean natural ceiling.
The final theorem chooses positive `K`; its proof explains why the ceiling of
the positive argument equals the natural ceiling. The next page's bibliography
is also legible. Other pages receive automated checks only.

The inherited Tenkz picture renders and its sweep passes: one picture, zero hard
findings, zero advisories. It has no `tenkzeq` scope, so no hard equation-group
comparison is claimed. The existing checkout matches the source's Tenkz pin.
No scalar diagram was added. The supported PDF-to-SVG fallback succeeds without
`dvisvgm`. [Commands](commands.json) records this and the existing font-map and
title-page destination warnings. The final `print.log` has no layout or
reference warnings.

The [manifest](focus-manifest.json) binds the exact leaves, Gaussian sources,
support files, fixture, and tool versions. The workflow uses the existing cached
TeX formats and pinned `texra-blueprint` 0.3.8, with no toolchain installation or
cache copies. Generated PDF, HTML, SVG, page images, and raw logs remain in the
persistent external fixture named in `commands.json`. Only these compact text
receipts and reproducible scripts are committed; there are no binary or LFS
artifacts.

To reproduce with the existing configured environment:

```sh
source ${WORKSPACE}/glm23-blueprint-env.sh
bash docs/provenance/evidence/8766-localization-parameters/render/run.sh \
  "$SOURCE_ROOT" "$NEW_EXTERNAL_FIXTURE"
```

`prepare.py` refuses to overwrite an existing fixture and requires the leaves
and Gaussian source files to match the frozen commit. `run.sh` renders both
outputs, runs the Tenkz sweep, and verifies exact-source hashes and outputs.
No Lean, Lake, or checkdecls build was run. This is focused PDF and static HTML
verification, with no full-book, live-browser, MathJax-runtime, responsive-layout,
or remote declaration-URL availability claim.
