# Tenkz blueprint infrastructure attribution

This change integrates diagram rendering and audit support only. It adds no
mathematical statements or Lean proofs. The physical-buffer mathematics used
for validation remains in its separate change and is not copied here.

## Source and license

The twelve source paths below come from LionSR/TNLean at
[`b053c4ca45dd9f181695aaa1ea3879fc2f413e87`](https://github.com/LionSR/TNLean/commit/b053c4ca45dd9f181695aaa1ea3879fc2f413e87).
Each published Git blob was checked against the local source revision
`7ac4122847a7c16e6e6267343a5faf6901ff6183`; all twelve matched.
Paths are unchanged in QICLean. Hashes below are SHA-256 of the complete
upstream file bytes before adaptation. Existing source comments are retained.

TNLean, QICLean, and the pinned Tenkz package supply the same Apache-2.0
license text in `LICENSE`, SHA-256
`c71d239df91726fc519c6eb72d318ec65820627232b2f796219e87dcf35d0ab4`.
TNLean has no root `NOTICE` file at the source revision. Modified source files
carry a prominent adaptation notice linking this record. The package is fetched
as a complete checkout, preserving its license and attribution, rather than
vendoring selected TeX implementation files.

| Source path | Source SHA-256 | Source lines | Final lines | Treatment |
| --- | --- | ---: | ---: | --- |
| `tenkz.toml` | `b47dd85f2a66ae5a809712f494b50176ada4ffb5809ec5cbc74012c851242e39` | 4 | 4 | Byte-identical copy |
| `scripts/fetch_tenkz.py` | `80a658ed603eb28e6be0ddbee456d85eea5886d25feb4e61c19a058503b67d87` | 95 | 95 | Byte-identical copy |
| `scripts/tenkz_paths.py` | `b301db3e900ab33d7d43cc271a914361b989034d106ebe66713343beb37e1236` | 48 | 48 | Byte-identical copy |
| `blueprint/src/Packages/tenkz_pic.py` | `9f4018011ad353065f58b3958c2c629d4bdfe40c7216a9182ff753c0f7d1ba70` | 526 | 526 | Byte-identical copy |
| `scripts/tenkz_blueprint_sweep.py` | `21f052752921d3acc940ac40b596dc91b95b7b88362adb4a40b1ce621ef5005d` | 227 | 233 | Adapted; see below |
| `scripts/test_tenkz_blueprint_sweep.py` | `0e7d81d121e41d1fb8f7e5c25c1891b52e5facd8fc6b3cd30b96c84b603ea8b4` | 100 | 105 | Adapted; see below |
| `scripts/test_tenkz_pic.py` | `ee560bd1347d411bd57128cfacc74848d53ea18937a812aa60318005eb9cd94d` | 238 | 188 | Adapted; see below |
| `blueprint/src/macros/diagrams.tex` | `275794e8e3fcf74aa7c000b38420f9150dd52017ea61216875103dc62908bf2e` | 14 | 14 | Byte-identical copy |
| `blueprint/src/latexmkrc` | `6bf5c08358866b42ad8062b7dcf7fa08b892361af7dd5547235f31aed33629e0` | 12 | 12 | Byte-identical copy |
| `blueprint/src/tenkz_pic.sty` | `adf747cb82f51ce4da80003c3352c58164f60ce04a33cbb1d6b560e1042004f5` | 3 | 3 | Byte-identical copy |
| `blueprint/src/plastex_templates/TenkzPictures.jinja2s` | `879380488675beb1bc55fe420f966e6a5f3fa86b9c1cf76489ace0e5dbb4c3c5` | 10 | 10 | Byte-identical copy |
| `blueprint/src/plastex_templates/DocumentCommands.jinja2s` | `38fb147cde71e0c9e943ca6a7645950f12869d1d19b6f2cd843f56c8f0add921` | 1 | 1 | Byte-identical copy |

Line counts include comments and blank lines. Nine byte-identical files contain
713 lines. The three adapted files contain 526 final lines: 490 source lines
retained, 36 lines added, and 75 source lines removed (line-sequence comparison,
with automatic popularity heuristics disabled). Of the copied `latexmkrc`, five
lines already existed in QICLean; its patch adds seven lines and removes one.
These are infrastructure reuse counts, not claims of authored mathematics.

## Adaptations and integration

- `test_tenkz_pic.py`: omit TNLean slide preamble/theme checks. Retain the
  generic cold/warm/edited-cache tests. Check the sentinel in all three QICLean
  workflows and exercise the CI missing-renderer exception. This test now uses
  the installed plasTeX renderer as well as its standalone core.
- `tenkz_blueprint_sweep.py`: add an explicit `--allow-empty` mode for QICLean's
  extraction-era blueprint with no diagrams. The default still rejects empty
  corpora. An absent source directory always fails. Present diagrams still
  undergo the actual event audit and any hard finding fails the command.
- `test_tenkz_blueprint_sweep.py`: retain unit-selection regressions and cover
  default-empty rejection, explicit-empty allowance, and absent-directory
  rejection.
- Existing QICLean preambles now load Tenkz for print and the verbatim SVG
  renderer for web. `plastex.cfg` enables the copied picture templates and the
  one-line no-output `tenkzkernel` template. Existing picture CSS is reused.
- The existing PR, Blueprint, and Full documentation jobs each fetch the pin,
  run generic smoke/unit-selection checks, sweep actual blueprint event
  streams, and reject the stable `tenkz SVG unavailable` HTML sentinel.
  PR smoke runs after TeX lint, avoiding generated render-cache TeX in that
  unchanged lint command. Trigger paths and blueprint change gating include
  the pin/helpers/tests; PR gating also covers the other two changed workflows.
- No jobs, permissions, concurrency settings, existing build steps, Lean/Lake
  dependencies, or `texra-blueprint@v0.3.8` pins are changed. Existing steps
  retain their order. Tenkz changes inherit the existing blueprint-to-Lean
  build gating. No package-corpus, per-paper, or full extra workflow is added.
- Generated `.deps/` and SVG compile caches are ignored. Build documentation
  describes package setup, checks, and the limits of equation-scope auditing.

## Added tool pin

`tenkz.toml` selects `https://github.com/LionSR/tenkz.git` at immutable revision
`08a6493f3605dcf2ca5b512823ccb2698dfc027b` for both `rev` and expected `sha`.
Print, standalone SVG rendering, and the audit helper resolve the same package.
The helper verifies the fetched commit and resets only its managed
`.deps/tenkz` directory. `TENKZ_ROOT` supports an existing local package for
rendering; the fetch helper does not manage that override.

## Validation and limitations

Validated locally on 2026-10-07 with the unchanged shared Tenkz checkout at
that pin; the fetch/reset helper was not executed against the shared checkout.

- Python syntax, Perl `latexmkrc` syntax, exact package-pin inspection, YAML
  parsing, original workflow steps/order/permissions preservation, and positive
  and negative execution of each workflow sentinel guard passed.
- Generic smoke checks passed: chain and sandwich SVG ink and extent, untouched
  warm caches, exactly one new SVG after a body edit, and CI missing-tool
  rejection. The six-source scanner regression selected five units correctly;
  empty and absent-directory regressions passed.
- An outside-Git integration fixture containing the actual physical-buffer
  leaf produced a six-page PDF with QICLean's preamble. Strict texra-blueprint
  0.3.8 rendering passed for both the focused fixture and the full blueprint
  plus that leaf (4 and 34 HTML pages respectively). Because leanblueprint's
  CLI requires a Git repository, these fixtures used its exact underlying
  `latexmk`/`plastex` commands and the texra strict log gate.
- The actual physical-buffer diagram produced one unique SVG, correctly linked
  from every generated occurrence. HTML source checks passed; the PDF page
  containing the diagram was visually inspected. Its event sweep reported one
  picture, zero hard findings, and zero advisories. Its presentational
  `tenkzequation` row declares no hard equation-group check, as reported.
- Negative fixtures verified both rejection of a signature mismatch during
  compilation and rejection of a successfully rendered empty picture by the
  event auditor (`HARD [empty-picture]`, exit 1).
- Full-book PDF did not pass: unchanged `ch13_spectral_filter.tex:114` uses
  `\int_\R`, causing `Missing { inserted` at `\__um_group_begin:` under the
  installed unicode-math. The exact base preamble, without Tenkz, and that
  unchanged expression reproduce the error. No mathematical-source fix is
  included.
- Local dvisvgm is absent; the probed XeLaTeX/PDF/pdftocairo route passed.
  Browser checks could not run: the Playwright-managed Chromium is absent,
  and installed system Chromium is blocked by the executor's socket policy.
  `chktex` is also absent locally. Existing CI browser and lint steps remain.
- No Lean/Lake builds, dependency changes, remote writes, publication,
  generated binaries, or LFS additions are part of this validation.

Before editing, all fourteen open QICLean PR file lists were checked: none
modified these infrastructure paths. Main had one independent PR CI addition
since base `90a2e8a1f5ae8d00dbbcecb5fa7eda032c5950e5` (the strict shifted-density
truncation regression). This narrow patch does not replace that workflow or
remove that step when applied to current main.
