# Conditional Minkowski reduction, issues 426 and 378

Base: `e9cc1cc6cd52c6dfc27d7b3aab4b1ba39ea7ed19` (main).
Branch: `work/426-canonical-pair-transport`.

The current issue bodies, issue 426's comment, main, remote branches and open
PR search were inspected before editing. No open PR or remote branch for this
work was found. Main already contains PR 441's block infrastructure and PR 445's
published dependency note. Neither is reimplemented. The checkout has no
AGENTS.md or .agents skills; CLAUDE.md, the project and blueprint conventions,
and the referenced texra-ai lean-conventions skill were consulted.

## Source gate

The exact GLR 1983 Theorem 5.3 existence clause has **not** been inspected.
The Internet Archive metadata for `matricesindefini0000gohb` lists both the
ordinary PDF and OCR text as private; its book page was not readable through
the web tool. Open Library identifies the 1983 edition, but supplies no theorem
text. The accessible primary VDDM text identifies the dependency and the
algebraic proof route, not the complete GLR convention choices.

- Edition record: https://openlibrary.org/books/OL3169756M
- Archive record: https://archive.org/details/matricesindefini0000gohb
- VDDM: https://arxiv.org/html/quant-ph/0011111v1
- Task boundary: https://github.com/LionSR/QICLean/issues/426

No GLR existence declaration has been frozen. The note's wording was corrected
so that its reconstructed convention translation explicitly assumes the
similarity and congruence equations. A legible authorized copy of the theorem
and preceding block definitions is still required.

## Proved scope

`QICLean/Algebra/MinkowskiReduction.lean` imports only the existing algebraic
canonical-block module. Its nine theorems prove:

1. Transpose selfadjointness for an involutory metric and selfadjointness of
   `M R M Rᵀ` without positivity or rank assumptions.
2. The inverse-transpose translation of a supplied canonical pair, followed
   by a supplied involutory reversal preserving the metric.
3. Normalization of a supplied pair and the resulting row Gram identity.
4. Right-isometry recovery from an invertible square Gram factor, and
   equivalence of the row and column isometry equations for `H² = I`.
5. The complete algebraic composition yielding `R = L₁ Sigma L₂ᵀ` from those
   supplied data and an invertible square root.

The last theorem is over arbitrary finite real square matrices. Its exact
hypotheses are `H² = I`, invertibility of `X` and `Sigma`, and

```text
H R H Rᵀ = X⁻¹ J X
X H Xᵀ = N
Oᵀ O = I
O N Oᵀ = H
H (O J Oᵀ) = Sigma H Sigmaᵀ
```

It constructs `L₁ = (O X)ᵀ` and recovers `L₂` by inverse multiplication with
`L₁ Sigma`. The conclusion is metric preservation for both factors and the
factorization. For `H = M`, this is `O(1,3)`, not `SO⁺(1,3)`.

There is no construction of `J, N, X, O, Sigma` from an arbitrary input.
Real Jordan existence, simultaneous signed canonical-pair existence,
inertia/exhaustiveness, square-root construction, positivity exclusions,
ordering, singular nondegenerate-row-space Witt extension, rank-drop cases,
properness and time orientation remain open. Issues 426, 378, 379 and 1 are
not solved by this change.

## Verification

- Pinned Lean `v4.36.0-rc1`; fetched the prebuilt Mathlib dependency closure
  before building. No Mathlib source rebuild was used.
- `lake build QICLean.Algebra.MinkowskiReduction`: passed, 5011 jobs.
  Only the unchanged predecessor module emits module-system import warnings.
- Direct Lean elaboration of the new module with CI flags, including
  `autoImplicit=false`, `relaxedAutoImplicit=false`,
  `linter.mathlibStandardSet=true`, and `warningAsError=true`: passed.
- All nine declarations' axiom audits contain only `propext`,
  `Classical.choice`, and `Quot.sound`; see
  [axioms.txt](evidence/minkowski-reduction/axioms.txt).
- No `sorry`, `admit`, new `axiom`, `native_decide` or unsafe proof bypass.
- Generated import aggregator check, blueprint source/declaration synchronization,
  changed-declaration blueprint coverage, reader-facing prose check, paper-gap
  references (92 slugs), and `git diff --check`: passed.
- Paper-gap PDF: two successful pdfLaTeX passes, four pages; `dsfont` was
  installed locally for this check. The second pass has no undefined references.
- Compiled Algebra/root aggregate checks were attempted and stopped on absent
  unrelated artifacts (`QICLean.Algebra.AKLVFrequencyBounds.olean`, then
  `QICLean.Algebra.olean`). This is a fresh checkout, not a full-library build;
  global compiled `leanblueprint checkdecls` is consequently not certified.
- Full blueprint PDF: passed (949 pages); the new main theorem was visually
  inspected on PDF page 92. Existing document-wide overfull-box warnings remain.
- Full blueprint web build: passed; no reported unknown commands or missing-file
  errors. Generated HTML source checks passed for all 78 pages.
- Affected chapter browser regression: passed (1 page, 2298 typeset expressions),
  including reader text and mobile/desktop layout. Chromium initially rejected
  the jsDelivr MathJax CDN certificate (`ERR_CERT_AUTHORITY_INVALID`); the local
  test used `ignore_https_errors=True`. No repository/browser-test source or
  published configuration was changed for this environment workaround.

All work remains local on the isolated branch; no push, PR, merge,
or external issue/comment mutation was performed.
