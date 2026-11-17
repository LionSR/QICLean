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

At the original validation checkpoint, all work remained local on the isolated
branch; no push, PR, merge, or external issue/comment mutation was performed.


## Review preparation, 2026-11-17

Fetched current main at `4fd4962204b7abdd012d4d0495d52d9d77003688` and checked
open PRs and the Minkowski PR history. No overlapping open contribution was
found. The original branch `work/426-canonical-pair-transport` remains at
`e53705df676c08ebf06ecf06bea4264bb51a921b`. Its change was cherry-picked without
conflicts onto `review/426-conditional-minkowski-reduction` from current main.
The Lean module, affected blueprint chapter, and paper-gap note are identical
to the original validated versions.

On the review branch, the focused 5011-job build, strict Lean elaboration,
all nine axiom audits, generated import manifest, blueprint synchronization
(after regenerating the ignored declaration list), changed-declaration coverage,
reader-facing prose, paper-gap references, and diff whitespace checks passed.
The Algebra/root compiled aggregate attempts still stop on missing unrelated
artifacts, so a full-library build and global compiled checkdecls are not
certified. The PDF/web/browser results above describe the original validation
checkpoint; those render builds were not repeated after unrelated main changes.

Publication is authorized for review only. The PR should remain a draft pending
full-library validation and scope review; the mathematical source gate and all
explicit assumptions remain unchanged. No approval or merge is authorized.

## Review revisions, 2026-11-17

Addressed the subsequent style/documentation review after independent review
confirmed soundness of the conditional result. Merged main
`476b3531e6a7352c4523a379284e63f08e11c144` without conflicts.

- Expanded the two theorem-statement `let` expressions directly.
- Reused Mathlib's `IsUnit.of_mul_eq_one` and `of_mul_eq_one_right` in all five
  identified sites, including the two predecessor-module proofs. No new helper
  duplicates these existing lemmas. The orthogonal case uses a left inverse,
  not a self-involution hypothesis.
- Added the general symmetric-involutory Gram selfadjointness theorem and made
  the Minkowski instance its corollary; synchronized its blueprint entry.
- Renamed the local `Sigma` variable to `sigma`.
- Defined the general matrices in the gap note and labeled every equation of
  the supplied-data hypothesis system.

Focused build (5011 jobs), strict new-module elaboration, axiom audits (the ten
reduction theorems and two refactored predecessor proofs), generated imports,
blueprint source synchronization and changed-declaration coverage, and the
paper-gap PDF passed. The GLR source gate and mathematical scope are unchanged.
Current-head CI and review acceptance must follow the push. No merge performed;
merges are being serialized by the coordinating thread.

## Documentation re-review, 2026-11-17

Addressed the 11:09/11:11 review's remaining documentation findings:
introduced general H-selfadjointness before use, wrote the resulting
selfadjointness/normalization/cancellation identities explicitly, attached
separate formal-traceability footnotes to the two corresponding results, and
used the note's full semantic prefix on all five hypothesis labels.
No Lean declarations, proof bodies, or hypotheses changed in this pass.

Blueprint source synchronization, reader-facing prose, paper-gap reference
checks (93 slugs), unique/prefixed equation labels, and the two-pass five-page
paper-gap PDF passed. CI for the preceding `bbfe1344` head was green; new-head
CI and review acceptance are required after the documentation push. Latest
main `ea327f3de350991566fcd4fcfd34c238170640fb` changes unrelated detailed-balance
files and was inspected without merging it into this documentation-only pass.
The GLR source gate and all open mathematical prerequisites remain unchanged.

Full blueprint PDF build also passed (957 pages).
