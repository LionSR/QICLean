# Blueprint

This directory contains the mathematical blueprint for QICLean. The blueprint is
the reader-facing account of the formalization: it states the definitions,
lemmas, and theorems in mathematical language and links them to the
corresponding Lean declarations with `\lean{...}` and `\leanok` tags.

QICLean's blueprint was extracted from TNLean's blueprint in a monorepo
split (see the extraction report in the repository history / PR description
for the moved-file list, the Wolf-chapter mapping, and the severed
cross-boundary `\uses`/`\ref` edges recorded in
`docs/extraction/interface_edges.md`). Chapter contents are unchanged from
TNLean except for three tensor-network diagrams removed during extraction
and two `\input` lines dropped where the
corresponding content stayed in TNLean.

## Layout

- `src/` contains the LaTeX source.
- `src/chapter/` contains one file per chapter.
- `src/content.tex` is the chapter router, ordered to follow M. Wolf's
  *Quantum Channels & Operations: A Guided Tour* as closely as possible; see
  the mapping comment at the top of that file. The `chNN_` prefix on each
  file name is this volume's own sequential chapter number, matching the
  router order.
- `src/appendix/` contains the supporting-results appendices carried over
  from TNLean's `ft_mps/` and `full_only/` appendix trees.
- `src/macros/` contains blueprint-specific macros.
- `src/references.bib` is the blueprint bibliography, subset to the 18 keys
  actually cited by the moved chapters.
- `print/` and `web/` are generated outputs (not checked in).

## Build and Check

Run these commands from the repository root:

```bash
lake build
python3 scripts/fetch_tenkz.py
cd blueprint
leanblueprint checkdecls
leanblueprint pdf
leanblueprint web
```

`leanblueprint checkdecls` should be run after adding or changing `\lean{...}`
tags.  The PDF and web builds regenerate `blueprint/print/` and
`blueprint/web/`.

Tensor-network pictures use the immutable companion revision in `tenkz.toml`.
Both print and standalone web rendering load `.deps/tenkz`; an existing local
checkout can be selected with `TENKZ_ROOT`. The fetch helper manages only
`.deps/tenkz` and resets that generated checkout to the pin. Do not store local
edits there. It does not change the Lean toolchain or Lake dependencies.

After installing XeLaTeX and either dvisvgm with working PDF-special support
or Poppler's `pdftocairo`, run from the repository root:

```bash
python3 scripts/test_tenkz_pic.py
python3 scripts/test_tenkz_blueprint_sweep.py
python3 scripts/tenkz_blueprint_sweep.py --allow-empty
```

The smoke test checks SVG ink, cold/warm caching, one-picture invalidation,
and missing-tool failure. The sweep compiles and audits actual picture event
streams and fails on hard findings or missing renders. `--allow-empty` permits
the extraction-era blueprint with no pictures and reports that no pictures were
checked; omit it when a nonempty diagram corpus is expected. A presentational
`tenkzequation` row does not assert an equality of boundary signatures. Only a
declared `tenkzeq` scope receives the corresponding hard group checks.

All three existing CI routes fetch this pin, run the smoke and sweep checks,
and reject HTML containing the missing-SVG sentinel. See
[`docs/provenance/tenkz-blueprint-support.md`](../docs/provenance/tenkz-blueprint-support.md)
for the copied infrastructure's source, hashes, license, and adaptations.

## Writing Conventions

Blueprint prose should be mathematical prose.  Avoid Lean-specific explanations
in visible text; the `\lean{...}` tag supplies the link to the formal
declaration.  Maintainer notes about proof status, local formalization choices,
or paper-gap documents should be written as LaTeX comments unless they are part
of the mathematical statement being presented to readers.

When a result is claimed to formalize a source theorem, the blueprint statement
must match the source hypotheses.  If the current Lean theorem has extra
hypotheses, the source theorem should not be marked as fully formalized until a
source-faithful statement exists.

The detailed style rules are in:

- `docs/blueprint_style_guide.md`
- the `lean-conventions` skill (prose_style, MATHLIB_doc references)
