# Typical pure-state estimates on complementary subsystems

The mathematical source is OpenAI, *A two-dimensional area law from a global
spectral gap* (September 24, 2026), at
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`, equation
`comparator:post-marginal` in `07-comparators.tex`. The complete production
source revision is `382468eec8f32d2776b7a30d281ff75c0702640b`.

For an actual vector on three finite tensor factors, the spectral projection
is determined by its actual first marginal. Taking the partial trace over the
first and third factors gives the selected/discarded decomposition on the
second factor. These contributions are positive and their traces are preserved.
The normalized selected marginal is bounded in positive-semidefinite order by
the original marginal divided by the selected mass. For a unit input vector,
its entropy has the same upper bound. No spectral hypothesis on an enlarged
region, full-rank assumption, supplied Schmidt coordinates, or assumed entropy
inequality occurs. A zero discarded contribution remains unnormalized.

This directory verifies the entire extended source, including the original 13
public declarations and the three new subsystem declarations. The original
source revision `42f0b20238cc164e912f7d73ce6a33239a581e52` and its evidence in
`typicalPureState8753` remain historical records; the current provenance entries
refer to this complete follow-up audit.

`build.log` records the successful Lake target. `strict-source.log` records the
entire source with warnings as errors, standard Mathlib linters, and strict
implicit arguments. `axioms.log` reports the dependencies of all 16 public
declarations, including both definitions; each report contains only `propext`,
`Classical.choice`, and `Quot.sound`. The diagnostic file disables only the linter
against hash commands. `regressions.log` records the existing singular-marginal,
full-selection, and empty-selection checks under the same strict options.

Codex (GPT-6) assisted this independently written formalization. No upstream
Lean proof text was reused. The unique blueprint fragment and the source
comparison describe both whole-complement and proper-subsystem estimates.
Root imports, the full combined build, and global blueprint checks belong to
the integration branch.
