# Gaussian-filter focused blueprint render

This packet verifies `blueprint/src/chapter/ch12_entropy_gaussian_filter.tex`
against the four Gaussian-filter modules at source revision
`63a3390d92754752fcfbf055cb30e694bd31cfcb`. It covers all 43 public declarations:
15 kernel declarations, 21 matrix-integral declarations, two spectral-gap
results, and five integral ground-vector estimates. The leaf contains 18
mathematical entries and 16 checked proof sketches.

The source is the Gaussian-filter passage in the proof of the reset lemma of
*Polynomial PEPS approximation of gapped square-grid ground states*
(September 24, 2026), pinned revision
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`, `02-information.tex`, lines 426–452.
The real-overlap input is separately identified at lines 402–414.

The exposition retains the normalized density with variance `h`, the
probability-measure definition at zero variance, the unrenormalized closed
interval truncation, the adjoint's exchanged generators, the actual integral
multiplier, the dimension-free Parseval argument, the complex overlap and its
conjugate, the real-overlap contraction specialization, and the exact
positive-variance tail coefficient `2 exp(-T²/(2h))` in both truncated errors.
It does not assert Hermiticity of the filtered operator, spatial locality, or
the full reset conclusion. No diagram is introduced: the cited passage is an
algebraic integral argument. The Tenkz sweep with `--allow-empty` confirms zero
pictures; it is not evidence about a nonempty diagram corpus.

## Verification

- Focused XeLaTeX PDF: eight pages; no overfull/underfull boxes, undefined
  references, duplicate labels, or LaTeX errors in the final engine log.
- Static HTML: six pages, 44 source labels present, 197 internal fragment links
  checked, and no missing anchors.
- All 43 declaration links occur in both PDF and HTML; every public declaration
  is represented exactly once in the source leaf.
- PDF pages 3–7 were inspected at full reading size after the final render.
  The normalized kernel, adjoint phases, spectral cases, Parseval sum, and the
  two-sided truncated estimates are legible and do not overlap.
- Final source, supporting files, PDF, HTML, and page pixels have recorded hashes.
  Generated PDF/HTML/PNG files remain outside the checkout and are untracked.
- Log paths are normalized to placeholders; no private absolute paths are retained.

The final web log has a generic missing-vector-imager warning (`dvisvgm` and
`pdf2svg` are unavailable). There are no diagram images in this excerpt, and
no package-loading errors remain. The PDF conversion reports its existing
font-map fallbacks and title-page destination warning; the inspected pages and
all 43 declaration links render correctly.

This is focused PDF and static-source validation, not a complete-book render,
Lean `checkdecls`, a browser/MathJax check, or responsive-layout testing. Native
production, strict consumers, and axiom evidence are recorded in the separate
kernel, matrix, spectral, and ground packets. The five capstone checked tags
were added only after parent confirmation of successful native production,
strict production, consumers, and all five guards at `2ae6e259`; their source
bytes match the frozen `63a3390` snapshot.

## Reproduce

Use the repository's supported blueprint environment and pinned Tenkz checkout.
Choose a writable output directory outside the repository and a readable copy
of the pinned paper source. For example, with task-specific shell variables:

```bash
python docs/provenance/evidence/8766-gaussian-filter/render/prepare.py \
  --output "$GAUSSIAN_RENDER" --paper "$GAUSSIAN_PAPER"
cd "$GAUSSIAN_RENDER/blueprint/src"
latexmk -xelatex -interaction=nonstopmode -halt-on-error print.tex
cp print.bbl web.bbl
plastex -c plastex.cfg web.tex
cd "$GAUSSIAN_RENDER"
python scripts/tenkz_blueprint_sweep.py --src blueprint/src --allow-empty
```

Save the web command's output as `web-build.log` in the render directory and
then run `render/verify.py --render "$GAUSSIAN_RENDER"` from the checkout.
The preparer checks the production and test bytes against the frozen source
revision before writing its manifest. `render/check.py` verifies the committed
source/coverage/hash evidence without requiring generated artifacts or Lean.
