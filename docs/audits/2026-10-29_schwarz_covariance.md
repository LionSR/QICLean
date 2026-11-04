# Wolf Proposition 6.7: Schwarz covariance

## Source and integration boundary

Issue: LionSR/QICLean #478. Source:
`Notes/WolfNoteTexSource/ch06_spectral_properties.tex`, lines 803–817,
including Equation (6.38). The preceding Theorem 6.6 is at lines 756–801.

The prerequisite abstract spectrum theorem from PR994 is merged into main
at `a2f54b6f3375b7072d4284163cfe5d9b2609cf4a`. This change targets main and
contains only Proposition 6.7 and its supporting tests and documentation.
The dependency's `AbstractEigenvectors.lean` and `IrreducibleSchwarz.lean`
are unchanged, as are all dependency pins. Main was integrated with a normal
merge; the original reviewed proof, tests, and Blueprint statements are
preserved exactly.

## Theorem boundary

The seven new public declarations in
`QICLean/Channel/Peripheral/SchwarzCovariance.lean` are:

- `SchwarzMap.mem_multiplicativeDomain_of_peripheral_unitary`
- `SchwarzMap.map_mul_peripheral_unitary`
- `SchwarzMap.map_peripheral_unitary_conjTranspose_mul`
- `SchwarzMap.map_conj_peripheral_unitary`
- `SchwarzMap.eigenvector_shifts_of_peripheral_unitary`
- `SchwarzMap.hasEigenvector_shifts_of_peripheral_unitary`
- `SchwarzMap.wolf_proposition_6_7`

The capstone assumes precisely an irreducible positive unital complex-linear
Schwarz map on `M_D(ℂ)`, with positive dimension. It obtains the canonical
phase `γ = exp(2πi/m)`, `1 ≤ m ≤ D²`, the full peripheral set, and the same
normalized unitary `U` from `SchwarzMap.wolf_theorem_6_6`. It derives
`T(U) = γ U` from the first power identity and retains `U^m = I`.
It then proves, for every matrix `X`,

```text
T(U† X U) = U† T(X) U
T(X) = μ X  ⇒  T(U† X) = conj(γ) μ U† X  and  T(XU) = γ μ XU.
```

The eigenvalue `μ` is arbitrary and may be zero or nonperipheral. The
nonzero transport theorem gives genuine `HasEigenvector` conclusions in
both orientations. Lower-level identities do not assume irreducibility or
nonzero dimension once a peripheral unitary is given. They use unitarity
to establish equality in both Schwarz inequalities and invoke the existing
abstract multiplicative-domain characterization. Positivity preserves
adjoints, giving the left identity from the right; covariance cancels the
two phases. No CP, Kraus representation, TP, supplied faithful state,
conclusion-shaped premise, new axiom, or proof hole is introduced.

## Owned files

- `QICLean/Channel/Peripheral/SchwarzCovariance.lean`
- `QICLean/Channel/Peripheral.lean` — generated one-line export addition
- `QICLeanTest/SchwarzCovariance.lean`
- `QICLeanTest/SchwarzCovarianceNonTP.lean`
- `blueprint/src/chapter/ch08_spectral_schwarz_covariance.tex`
- `blueprint/src/chapter/ch08_spectral_ft_peripheral_cyclic.tex` — fragment input
- `docs/wolf_numbering_coverage.md` — only the Proposition 6.7 entry
- `docs/audits/2026-10-29_schwarz_covariance.md`

The fragment lives under `chapter/` because the repository's declaration
coverage checker scans chapters and appendices. Its two mathematical
entries group the lower-level statements and the source proposition.
The existing coverage ledger's historical tally is preserved.

## Independent native review

A separate native agent independently read the exact source hypotheses,
the actual proof bodies, `IsPositiveMap`'s adjoint preservation, the abstract
multiplicative-domain proof, and Theorem 6.6's unitary construction and
internally derived faithful weight. Verdict: **PASS**, no mathematical or
source-scope blockers. This is an automated review, not a human approval.

The reviewer independently strictly elaborated the production module,
both regression files, and a separate boundary file. The independent
boundaries include zero-dimensional covariance, shifted `HasEigenvalue`
conclusions from nonzero vectors, the canonical phase and normalization,
and `γ = μ = i`: the left shift has eigenvalue one on `U†U = I`, while
the right shift has eigenvalue minus one on `U²`. That non-real-phase
regression is retained in the main test. The reviewer's requested Blueprint
edge to `thm:abstract_md_characterization` is included. The production proof
is unchanged since the independent passing review.

## Validation

Toolchain: Lean `v4.35.0-rc3` (compiler commit
`470d5ce1400764999581fd26d5d72b00d990b0f4`). Mathlib:
`c55e6e786f49471c72fbddbec5415808896aec1e`.

Matching prebuilt Mathlib artifacts were verified before building. No
Mathlib Lean source module was rebuilt. The text linter compiled native
objects from prebuilt generated C.

Passed checks:

- Target build `lake --fail-fast build QICLean.Channel.Peripheral.SchwarzCovariance`.
- Export integration build `lake --fail-fast build QICLean.Channel.Peripheral`
  passed (9,190 jobs, overwhelmingly cached prerequisites).
- Repository CI strict selector against the verified dependency head:
  `python3 scripts/ci_lean_checks.py strict --base 57cf28551248b0f7dd275359fca20f156b8b29c0
  --jobs 2 --timeout 240`. Both changed production files (including the
  generated Peripheral import) and all three selected tests passed with
  warnings treated as errors. The selected tests are the two new regressions
  and their existing non-TP fixture dependency.
- Direct strict elaboration of both new regression files and the imported
  existing `QICLeanTest.IrreducibleSchwarzNonTP` fixture, using a temporary
  object overlay for test imports. Warnings are errors; auto-implicit
  arguments are disabled and the standard Mathlib linter set is enabled.
- All seven production declarations and the independent nonzero-transport
  regression depend only on `propext`, `Classical.choice`, and `Quot.sound`.
- Traversal of actual kernel types and proof values, including opaque
  values: **56,948 declarations**, **50 opaque definitions**, no unsafe
  declarations, and only those three standard foundations.
- The new module's repository import closure has **85 modules**, is acyclic,
  and has one direct import, `QICLean.Channel.Peripheral.IrreducibleSchwarz`.
  A prohibited-proof-token source scan of all 85 modules found no violations.
- Concrete non-TP regression using the dependency's proved map
  `T(X) = ((9/25) X₀₀ + (16/25) X₁₁) I`. The source capstone applies to this
  irreducible positive unital Schwarz map while `¬ IsTracePreservingMap T`
  is proved. A nonzero off-diagonal matrix unit at eigenvalue zero remains
  a nonzero eigenvector under both shifts.
- `lake exe lint_style` over the production tree; generated imports
  `--check`; module naming and size policies; changed reader-facing prose;
  whitespace; source-level Blueprint synchronization and reverse coverage
  for all seven declarations.
- Forty-five applicable Python tests in `test_ci_lean_checks.py`,
  `test_generate_import_aggregators.py`, and `test_lean_file_policies.py`,
  run with `PYTHONPATH=scripts`.
- The exact final Blueprint fragment plus Theorem 6.6 rendered in an isolated
  one-page excerpt and was visually inspected. Two final LaTeX passes have
  no warnings or overfull boxes.

Not run or not claimed: full `QICLean` library build, full compiled
`leanblueprint checkdecls`, full Blueprint web/PDF, or downstream TNLean
build. Source-level declaration checks and compiled actual-name/axiom checks
passed; they do not replace the unrun full-library gates. Hosted CI must
validate the complete library and Blueprint before readiness is considered.
