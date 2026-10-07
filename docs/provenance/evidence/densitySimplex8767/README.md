# Density-simplex verification

The proof source is the immutable QICLean revision
`5633d8d7d931717c6eb9c5ed41e83ee7eb73eaa4`. The production theorem assumes an
actual minimum on the closed probability simplex. The concrete last-filter
application proves its derivative and derives normalized weights from the
actual scalar objective. It permits boundary minima and zero input weights.
It does not prove the earlier-factor derivative or descending commutation in
the noncommuting ordered chain; hence it is not the full Proposition 4.1.

`checks.json` records the checked source hashes, public names, exit codes and
log hashes. The production module passed the package build with standard
linters. The regressions and public axiom audit used warnings as errors,
strict implicit arguments, the standard linter set and the package synthesis
limit. All eight public declarations, including both definitions, depend only
on `propext`, `Classical.choice`, and `Quot.sound`. The regressions verify a
boundary minimizer, a feasible nonminimizer, and the failure of a positive
support multiplier for exponent zero.

The text style audit checks both owned Lean files; it disables only Mathlib's
repository-wide Python style script, which is absent from QICLean. The tactic
pattern scan ran on an exact copy of the production module in its own temporary
directory. Neither check modifies the production source.

The provenance checker applies the exact TNLean policy and schema at
`c738e87489bc1b4ae1d58a6bdefb2c1cbd654114`, whose hashes are asserted by
`check_provenance.py`. It checks this eight-row shard, immutable production
bytes, declaration names, complete original notices, recorded log hashes and
kernel reports. It does not re-audit unrelated inherited provenance entries.
Reproduce it with Python and jsonschema, supplying the frozen validator and
schema through the documented script arguments.

The exact auxiliary blueprint fragment was rendered independently with the
existing bibliography. The final one-page output was inspected and has no
undefined citations or overfull boxes. This is a standalone check; the combined
book and declaration check remain integration checks. No root import aggregator
or shared chapter was changed. The source's gap-note reference is provided by
the companion regulator commit `68341c64` on the combined branch.

These proofs and checks were prepared with assistance from OpenAI Codex
(GPT-6). Human mathematical review is separate from kernel verification.
