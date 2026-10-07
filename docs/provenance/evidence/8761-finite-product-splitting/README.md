# Verification of finite-region purification splitting

Proof source: `2ba107e29c07b623707d030eca3240e52a804b50` in LionSR/QICLean.
Base: `c7a904b2bc203906aa2f5c4a44f61fa465ee2eaf`.
The immutable source contains all six public declarations, the three regressions,
the mathematical source comparison and the new blueprint chapter.

The source is an original formalization of Lemma 6.4, `lem:splitting`,
`05-frames.tex:352–391`, in the September 24, 2026 polynomial-PEPS manuscript at
OpenAI commit `adc7f1241b42e322a6451854ab7e4b4c146bf78a`. No upstream Lean proof
text is reused.

## Checks

- `build.log`: the final source passed the targeted Lake build with package
  options and standard linters, without warnings. The prebuilt Mathlib cache was
  fetched and checked before compilation; no Mathlib source build was performed.
- `strict-source.log`: the exact source additionally passed `lake env lean
  -Dlinter.mathlibStandardSet=true -DwarningAsError=true
  QICLean/Entropy/FiniteProductSplitting.lean`.
- `regressions.log`: `lake env lean -DwarningAsError=true
  QICLeanTest/FiniteProductSplitting.lean` passed. The tests cover unequal local
  dimensions, normalization when there are no physical sites, and exact zero-error
  splitting for empty T,E with an arbitrary whole complement space.
- `Axioms.lean` and `axioms.log`: every public definition and theorem is audited.
  The only dependencies are `propext`, `Classical.choice`, and `Quot.sound`.
- `latex.log` and `bibtex.log`: the new chapter passed a standalone three-pass
  LaTeX/BibTeX compilation. Every public declaration has a blueprint link.
- Generated imports, changed prose, file-length/name checks, proof-pattern scan
  and whitespace checks passed. The proof-pattern scan found no repeated pattern
  requiring a new abstraction.

The six new provenance records are in
`docs/provenance/openai-math.d/8761-finite-product-splitting.json`. Their
verification commands, immutable source revision and log hashes are explicit.
`provenance.log` records validation of this shard using the policy fixed in
`policy-snapshot.json`. This is a shard validation, not a new audit of unrelated
historical records. The validator uses the current source file, the immutable
Git revision, exact quoted axiom outputs, and SHA-256 hashes of the retained logs.

No full-library build or aggregate blueprint declaration check is claimed by
this evidence. Those checks belong to the combined integration after the separate
contributions are merged. The full ground-state area law and polynomial PEPS
approximation theorem remain open.
