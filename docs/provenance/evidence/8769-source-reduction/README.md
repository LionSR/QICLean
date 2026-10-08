# Source-only density and ambient-source evidence

This packet adds 51 named public declarations for
[TNLean #8769](https://github.com/LionSR/TNLean/issues/8769).
The exact proof revision is `ba4afd141b06de7889126d2ec18f25c1797d8f6f`.
All 51 have original proof text. Imported OpenAI/math adaptations retain
their separate attribution in the foundations packet.

The packet proves chronological contraction estimates through changing finite
memory spaces, a marked-gate rescaling budget, density and partial-trace error
estimates for subnormalized vectors, and actual Gaussian source expectation
identities after arbitrary finite ambient transport.
If only M marked gates are approximated within delta, rescaling those gates
gives a reduced-density nuclear error at most 4 M delta. With positive M and
delta = epsilon/(8 M), the error is at most epsilon/2.

The changing memories, marked gates and common final readout are given data.
Identifying them with an actual distributed circuit, choosing its Schmidt
frames, proving the correction-position expansion, and constructing the final
local tensor network remain separate obligations. This is not the complete
compression theorem or the ground-state area-law theorem.

Targeted builds, all 51 compiled public axiom reports, four strict regression
suites, complete public-source parity, generated imports, style, size and
blueprint synchronization pass. Kernel dependencies are only `propext`,
`Classical.choice`, `Quot.sound`, or none. Six blueprint entries link all 51
declarations and pass independent source review. The standalone LaTeX/BibTeX
smoke test passes; full library and blueprint checks run in PR CI.

The regression command ran each of these files with
`lake env lean -DrelaxedAutoImplicit=false -DmaxSynthPendingDepth=3
-Dlinter.mathlibStandardSet=true -Dlinter.hashCommand=false
-DwarningAsError=true` and stopped on any failure:

- `QICLeanTest/ContractionChain.lean`
- `QICLeanTest/SubnormalizedPureStateError.lean`
- `QICLeanTest/SourceOnlyDensityError.lean`
- `QICLeanTest/GaussianProductSourceTransport.lean`

Successful regression compilation is silent. The hash-command linter is
disabled for the dedicated audit containing `#print axioms`; proof checking
and warning-as-error checking remain enabled.

The shards record this exact proof revision and successful commands with
SHA-256 hashes of the committed build, axiom and source-audit transcripts.
The source audit uses the TNLean provenance parser at revision
`4e9d9c898a4401d51cf1eeeabcea8572242387fe`.
Reproduce historical evidence by checking out the proof revision.

OpenAI Codex (GPT-6) assisted with proofs, agent review, tests and documentation
under the repository owner's direction. Human mathematical review is pending.
