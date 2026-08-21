# Blueprint

This directory contains the mathematical blueprint for QICLean. The blueprint is
the reader-facing account of the formalization: it states the definitions,
lemmas, and theorems in mathematical language and links them to the
corresponding Lean declarations with `\lean{...}` and `\leanok` tags.

QICLean's blueprint was extracted from TNLean's blueprint in a monorepo
split (see the extraction report in the repository history / PR description
for the moved-file list, the Wolf-chapter mapping, and the severed
cross-boundary `\uses`/`\ref` edges recorded in `interface_edges.md` at the
repository root). Chapter contents are unchanged from TNLean except for
three tensor-network diagrams removed (QICLean carries no tenkz diagram
pipeline) and two `\input` lines dropped where the corresponding content
stayed in TNLean.

## Layout

- `src/` contains the LaTeX source.
- `src/chapter/` contains one file per chapter.
- `src/content.tex` is the chapter router, ordered to follow M. Wolf's
  *Quantum Channels & Operations: A Guided Tour* as closely as possible; see
  the mapping comment at the top of that file. The `chNN_` prefix on each
  file name is a stable subject identifier inherited from TNLean and is not
  renumbered to match the router order.
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
cd blueprint
leanblueprint checkdecls
leanblueprint pdf
leanblueprint web
```

`leanblueprint checkdecls` should be run after adding or changing `\lean{...}`
tags.  The PDF and web builds regenerate `blueprint/print/` and
`blueprint/web/`.

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
- `docs/prose_style.md`
- `docs/MATHLIB_doc.md`
