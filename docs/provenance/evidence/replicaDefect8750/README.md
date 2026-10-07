# Physical replica gap and exact excitation sectors

The complete mathematical source is frozen at
`68849bf729881c780a0a66f3a7fe80d22a350bba`. The parent is
`14778d7ee2e8c12efbf3a8029f7e5ef6d4d52bf4`, with the independently checked
spectral first-moment result added by cherry-pick `7078c007` from
`8f0020f9670356b79727bb6f23383f9c952c93a5`.
`source-freeze.json` binds both entire production files, including every
private proof, both unique blueprint fragments and the mathematical scope
note. It also verifies that the spectral cutoff dependency is byte-identical
to its original source.

The fourteen declarations construct the physical replica Hamiltonian and
defect count, derive the replica gap from the one-copy gap, prove the literal
product eigenvalue and its physical mean with any auxiliary vector, and
bound the mass of the actual cutoff from the mean excess energy. They also
construct the exact excitation sectors, derive their identity partition,
orthogonality and cardinality eigenvalue, identify the literal spectral
cutoff by finite spectral calculus, and prove the actual component
decomposition and its squared mass identity with arbitrary auxiliary factors.
`mathematical-review.json` records the hypotheses, primitive constructions and
the independent parent review. Copy symmetry, ground-factor decomposition,
Schur labels and metric estimates remain subsequent source steps.

The source is OpenAI's September 24, 2026 manuscript, revision
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`, comparator Section 7, lines
130–147 and 421–456. `source-comparison.json` compares the actual local
manuscript bytes with the immutable pinned source digest and Git blob already
recorded in the parent compression evidence. The new proofs are original;
no upstream Lean proof text was reused.

The frozen two-module package build passed, with 3,131 jobs and 9.7/4.2
seconds for the new modules. Each full production source passed strict
elaboration with warnings as errors, strict implicit arguments and the
standard Mathlib linter set. All fourteen exact-name kernel reports,
including all three definitions, contain only `propext`, `Classical.choice`
and `Quot.sound`. The public statements and primitive definitions were
printed separately. Text style returned zero violations. The two owned
provenance shards passed the frozen TNLean policy at
`806099b4dddcce591b3a62ee1921926a6af5ad55`, checking the committed source
bytes, independence notices, immutable source revision, exact kernel names
and log hashes. `verification.json` records every actual command and exit.

The initial diagnostic commands are retained verbatim. Two omitted diagnostic
module docstrings and a long diagnostic configuration line were repaired
without changing production source. The first provenance invocation used a
Python installation without `jsonschema`; the successful invocation uses
the existing Miniforge interpreter used by the parent audit. No initial
failure concerned a mathematical statement or proof.

The warm cache was copied from the explicitly authorized parent worktree.
The explicit prebuilt Mathlib fetch and the pre-build artifact check both
passed. `seed.log` and `cache-fetch.log` preserve those original outputs.
No Mathlib source build was performed. Every final command checks the frozen
production hashes before running. Complete library and blueprint verification
will be recorded separately after the new fragments are included.
