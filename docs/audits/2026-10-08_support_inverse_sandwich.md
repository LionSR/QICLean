# Singular support-inverse sandwich bound

The generic QIC matrix-order component of restoration issue #8757 is proved
in `QICLean/Analysis/SupportInverseSandwich.lean`. For finite complex matrices,
the public theorem `Matrix.PosSemidef.mul_supportInv_mul_le` states
`M * hρ.supportInv * M ≤ M` from `M.PosSemidef`, `ρ.PosSemidef`, and `M ≤ ρ`.
There is no invertibility, positive-dimension, commutation, support-inclusion,
or sandwich-conclusion hypothesis.

The mathematical source is the restoration construction in
[AreaLaw Section 9, lines 417–446](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-two-dimensional-area-law-from-a-global-spectral-gap-September-24-2026/build/sections/09-amplification.tex#L417-L446).
This implementation is independently written; no upstream Lean proof text was
copied or adapted. It uses QIC's support inverse and Mathlib's positivity of
matrix congruences. The key identity is

`M − Mρ⁺M = (I−Mρ⁺)M(I−Mρ⁺)ᴴ + (Mρ⁺)(ρ−M)(Mρ⁺)ᴴ`.

Both summands are positive semidefinite. Expanding them uses only
`ρ⁺ρρ⁺ = ρ⁺`, derived from the existing support identities. Separate results
derive kernel inclusion, left/right support absorption, and the normalized
order bound from `M ≤ ρ`.

## Checks

The exact source/test checkpoint is
`e68b9e13d7e57f6f4486f97a86a4e3d89b9e38a6`, based on fresh main
`fbe84eae5cc0e223bee1676c2434ada3e77cb194`. The later audit-only commit changes
no production, consumer, or guard bytes. The
[execution inventory](2026-10-08_support_inverse_sandwich.json) records input
and log SHA-256 hashes, actual exit codes, elapsed times, and reproducible
Lean argument lists. All Lean/Lake invocations were serialized by the shared
build lock and used `LEAN_NUM_THREADS=2`.

- Targeted native build: `lake build QICLean.Analysis.SupportInverseSandwich`
  passed at source commit `769fe086c5805bf5a94b8af7686759818279d09f`.
  The source bytes are identical at the final checked checkpoint. The log
  reports 3105 jobs and 2.3 seconds for the new module; total build wall time
  was not recorded.
- Production, consumer, and guard modules passed with explicit strict
  `autoImplicit=false`, `relaxedAutoImplicit=false`, `pp.unicode.fun=true`,
  `maxSynthPendingDepth=3`, `linter.mathlibStandardSet=true`, and
  `warningAsError=true` flags.
- Six consumer examples include nonzero singular matrices sharing an explicit
  nonzero kernel vector, a directly verified noncommuting pair, derived support
  absorption, normalization order, the zero reference, and an empty ambient
  space. The singular noncommuting example uses
  `M = u uᴴ`, `u = (1,1,0)`, and `ρ = M + diag(1,2,0)`.
- Seven permanent guarded axiom checks passed. The independently executed
  [raw query](evidence/support-inverse-sandwich/SupportInverseSandwichAxiomsRaw.lean)
  and its [actual output](evidence/support-inverse-sandwich/raw-final.txt)
  report exactly `propext`, `Classical.choice`, and `Quot.sound` for each of
  the seven public declarations.
- `git diff --check` passed, and the changed Lean files contain no proof holes,
  added axioms, or prohibited kernel-bypass tactics.

The toolchain, manifest, dependencies, shared routers, and existing source files
are unchanged. No full Analysis/root build, CI, blueprint rendering, or blueprint
declaration checker was run. A standalone mathematical blueprint leaf is supplied
for integration. The convention-referenced `scripts/tactic_pattern_scan.py` is
absent in this checkout; that optional scan was not run.

This is only the matrix-order component. The restoration operator construction,
downstream tensor-network integration, and full amplification theorem remain
separate work.
