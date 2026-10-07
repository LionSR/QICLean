# Gaussian filtering kernel evidence

The fifteen public declarations cover the normalized scalar Gaussian kernel,
density/probability integral conversion, the angular-frequency characteristic
integral, and the two-sided time-tail bound. The parameter `h` is the variance:

- `g_h(t) = (sqrt(2πh))⁻¹ exp(-t²/(2h))`
- `∫ g_h(t) exp(iωt) dt = exp(-hω²/2)`
- `∫_{[-T,T]ᶜ} g_h(t) dt ≤ 2 exp(-T²/(2h))` for `T ≥ 0`

Normalization and every density-to-measure conversion require `h ≠ 0`.
At zero variance Mathlib's Gaussian measure is Dirac at zero, while its
density is identically zero. The characteristic and probability-tail
statements remain valid at zero variance. No locality or full-reset
assertion is included.

## Source and library reuse

The source is *Polynomial PEPS approximation of gapped square-grid ground
states* (September 24, 2026), the Gaussian-filter paragraph in
[`02-information.tex`, lines 426–452](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Polynomial-PEPS-approximation-of-gapped-square-grid-ground-states-September-24-2026/build/sections/02-information.tex#L426-L452),
pinned at `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.

The [fifteen-row ledger](../../openai-math.d/gaussiankernel8766.json)
and matching inline provenance pairs identify every public declaration,
including the kernel definition and intermediate wrappers. The
`original` category concerns OpenAI proof-text provenance: no Lean proof
text from the paper repository was copied or adapted. It does not claim
new proofs of standard Gaussian integration.

[library-reuse.json](library-reuse.json) records the direct Mathlib calls
per declaration and the inspected files at
`c55e6e786f49471c72fbddbec5415808896aec1e`. Normalization and characteristic
evaluation use the Gaussian distribution API. The tail argument constructs
`HasSubgaussianMGF` from the exact Gaussian MGF and exponential
integrability, applies the Chernoff estimate to the identity and its
negative, and adds the two one-sided bounds. No Gaussian tail estimate is
assumed. The characteristic-function convention has no extra `2π`.

## Exact checked revisions

[verification.json](verification.json) binds the actual run revisions,
commands, source and log hashes, exit codes, timings, and scope.

- Production and the separate all-fifteen raw axiom driver passed strict
  checking at `b45bc4ae2196fc64724808a605ddd14c3d92fc1d`.
- The final native target and nine consumer examples with all fifteen
  guarded axiom reports passed at
  `e3a17bc6af4f0b09b8ab49c533dace7218408c98`.
- Production and raw-driver bytes are unchanged between those revisions.
  The final commit adds the ten remaining guards to the already checked
  test. No run is relabeled as executing at a different revision.
- Every raw report contains exactly `propext`, `Classical.choice`, and
  `Quot.sound`. The fifteen informational hash-command messages are
  retained; no linter is disabled.

The strict invocations disable both implicit-variable options, enable
Mathlib's standard linters, and treat warnings as errors. The nine
examples exercise variance one, the kernel's value at zero, variance two
at angular frequency one, cutoff zero, cutoff two, and the distinction
between zero density and zero-variance Dirac probability.

The native checks report 3,226 jobs for the scalar module target. This
packet makes no full-root, complete-CI, remote-publication, or blueprint
rendering claim.

## Preserved failed attempts

Historical receipts and logs are kept separately in `history/`:

1. `2daa03b`: the first native check failed because the left-tail
   set-membership goal was not exposed as a real inequality before
   `linarith`. The repair explicitly changes the goal to `T ≤ -t`.
2. `a2bc118`: production passed both native and strict checks. The test
   failed four style diagnostics: two unnecessary sequence-focus
   combinators and two unnecessary `simpa` calls. Proof statements were
   preserved, and the zero-variance tail test was strengthened to exact
   zero probability.

Every historical diagnostic, command, timing, exit code, and revision is
retained. Executor prefixes are replaced by role tokens, and log links in
receipts are made repository-relative. Original and normalized hashes
are recorded for all fourteen retained inputs.

## Replay

Run `python3 docs/provenance/evidence/8766-gaussian-kernel/check.py` from
the repository. It checks file and log identity, the fifteen-way agreement
between declarations, inline pairs, ledger rows, raw reports and guards,
the standard axiom lists, strict command flags, library reuse coverage,
and historical-failure retention. It performs no Lean or network action.

An optional schema path reruns JSON-schema validation. The recorded
schema check used the supplied OpenAI provenance ledger schema v1; its
SHA256 is retained. This is not a claim to have executed the complete
external provenance policy checker.
