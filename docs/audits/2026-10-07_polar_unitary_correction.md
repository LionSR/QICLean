# Generic unitary polar correction

This QICLean package is a locally checked draft. QIC publication is held pending
repository-destination authorization; no upstream source commit or PR is claimed.
The work is tracked by [TNLean #8766](https://github.com/LionSR/TNLean/issues/8766#issuecomment-6035995318)
within #8757. Neither a full QIC root build nor full CI has run.

Two modules prove six public matrix theorems, with one private norm-preservation
helper. Six consumer examples and all six permanent axiom guards pass. A separate
raw audit reports exactly `propext`, `Classical.choice` and `Quot.sound` for each
public theorem. The [inventory](2026-10-07_polar_unitary_correction.json) and
[execution records](../provenance/evidence/8766/validation.json) retain exact
source bytes, commands, revisions, outcomes and raw/sanitized hashes.

## Mathematical scope

For a positive-semidefinite matrix `P`, the proof expands the squared Hilbert
norm to show `norm x <= norm ((I + P)x)`. Applying this to a difference of vectors
and to `(I - P)x` gives the two-residual and quadratic-defect estimates.

Equal Gram matrices provide a unitary `U` on the original finite-dimensional
space with `D = U sqrt(D†D)`, even for singular `D`. The same `U` satisfies
both vectorwise bounds, simultaneously for all vectors:

- `norm ((U - D)psi) <= norm ((I - D†D)psi)`
- `norm (U phi - eta) <= norm (D phi - eta) + norm (D† eta - phi)`

Each displayed coefficient is exactly one. These are Hilbert-space vector norms,
not claims about a matrix entry norm. No invertibility, normalization or positive
dimension hypothesis is added, and no extra-space dilation is used. Optimality of
the numerical coefficients is not asserted as an additional formalized theorem.

For any fixed such `U`, the Kronecker theorem retains the factorization and both
estimates for `U tensor I` and `D tensor I`. The local unitary is chosen before
arbitrary finite spectator spaces. Vectors may be entangled; no decomposition or
product-vector hypothesis is imposed. Consumers check uniform residual bounds,
zero and singular nonzero operators, empty local spaces, one unitary across all
spectators, and an empty spectator.

The proofs use the native equal-Gram unitary theorem and positive square-root
Kronecker identity. This is the generic polar component only: geometric support,
reset/angular constructions, complete amplification and both manuscript headline
theorems remain separate.

## Source, checks and history

The verified combined source/test checkpoint is local
`c849b612e6e7c37c4c38263316681ff92b7ed5de`. The native command
`lake build QICLean.Analysis.PolarUnitaryCorrectionKronecker` passed with 3107
jobs and rebuilt both new modules. It ran before a CI-location-only amendment;
the production bytes are identical at the native, strict and combined checkpoints.
Its per-module timings are 3.7 and 5.5 seconds. Total wall time was not recorded,
and these numbers are not added to invent one.

Strict checks use explicit package options, the standard linter set and
warnings as errors. The first final batch passed both production modules,
the core consumer and both guard modules; the spectator consumer failed on a
let-binder introduction. The test-only repair passed in 3.47 seconds. The
[raw query](../provenance/evidence/8766/PolarAxioms.lean) then ran successfully at
the combined checkpoint and reported all six actual axiom sets.
No earlier command is represented as a new build at the combined checkpoint.

The two modules contain 255 lines, including 34 provenance-comment lines added
to the 221-line proof-source checkpoint. The private helper remains private and
is compiled with the core module; its dependencies are covered transitively by
the public raw reports. [Compact history](../provenance/evidence/8766/history.json)
retains meaningful failures with original and sanitized hashes. Original full
artifacts remain preserved locally; no executor directories or unrelated notes
are published in this packet.

## Provenance

The [six-row ledger](../provenance/openai-math.d/8766.json) uses
`LionSR/QICLean` as both downstream and verification repository. Every row is
`original`, with `upstream: null` and `no_upstream_proof_text_reused: true`.
The schema's `ported`/`passed` values mean a locally implemented, checked result,
not an upstream publication. The source team used OpenAI Codex, GPT-6; no OpenAI
Lean code was copied or adapted.

The mathematical sources are the September 24, 2026 manuscripts pinned at
`openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`:
[polynomial-PEPS polar errors and unitary correction](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Polynomial-PEPS-approximation-of-gapped-square-grid-ground-states-September-24-2026/build/sections/02-information.tex#L565-L595)
and [area-law two-sided polar correction](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-two-dimensional-area-law-from-a-global-spectral-gap-September-24-2026/build/sections/09-amplification.tex#L524-L545).
Their exact labels were checked by immutable source reads.

The [scoped policy result](../provenance/evidence/8766/provenance-validation.json)
uses the unchanged hardened TNLean validator at
`a05ef8f8db19f28e987bf3ce599c5f284f96921f`, with an explicit QIC repository root.
It checks the schema, exact source bytes, all six owned declarations and notices,
log hashes and exact named raw reports. Owned-module notice coverage is checked
explicitly. Repository-wide notice scanning and the unrelated #8765 evidence
are not certified or changed; their private-path records are not copied here.

The portable checker takes the policy repository separately:

```sh
python3 docs/provenance/evidence/8766/check_provenance.py --root . --policy-root ../TNLean
```

It requires `jsonschema` and a TNLean Git checkout containing that policy commit.
It executes no Lean build and performs no remote fetch or policy refactor.

## Focused blueprint review

The [render record](../provenance/evidence/8766/render-validation.json) covers four
PDF pages, six exact declaration links in PDF and static HTML, and three theorem/
proof pairs. The final leaf uses theorem environments matching the primary Lean
declarations, explicit display references, and the pinned `latexindent` 3.24.7
format. Every final PDF page was directly inspected. No clipping, missing glyphs,
missing anchors, duplicate IDs or HTML error sentinels were found.

The coefficients, vector norms, singular case and fixed-unitary spectator scope
match the source and rendered mathematics. This is a focused PDF/static-HTML
check, not a full-book, live-browser, MathJax-runtime or remote-document-availability
claim. Inherited font-map/vector-imager warnings are recorded; no tensor diagram
is needed for these algebraic norm identities.
