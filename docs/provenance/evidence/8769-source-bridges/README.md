# Source-contraction and chronological-density evidence

This packet adds 84 named public declarations in seven modules for
[TNLean #8769](https://github.com/LionSR/TNLean/issues/8769).
The exact checked proof revision is
`2e14ca2f7f61384a461822f67ff630ccd5ff51dd`.
The published proof tree is byte-identical to the locally compiled revision
`364bd6045bafd20a9e51912c18a49b514c0b4096`. Publication used the connected
GitHub app after the workspace CLI credential expired.
Every new declaration has original proof text and an individual provenance
notice. Imported OpenAI/math adaptations retain their separate attribution.
These counts include definitions and supporting lemmas; they are not counts
of paper theorems or a percentage of the compression proof.

The packet constructs the literal finite source contraction as a multilinear
map and proves its corrected-position expansion. It constructs a global
Gaussian branch law, proves its selected-coordinate projection preserves the
law, obtains genuine Schmidt frames for arbitrary finite source vectors,
and proves the actual sampled coefficient contraction is Bochner-integrable
and unbiased. Positive sample count and nonnegative weights suffice for
unbiasedness; normalization and coefficient norm bounds are not premises.

The chronological construction carries fresh pure garbage through changing
memories and traces it out after the common physical readout. Approximating
only a marked set S gives physical-density nuclear error at most
4 |S| delta against the original circuit. If |S| is positive and
delta = epsilon/(8 |S|), the error is at most epsilon/2. Empty marked sets
and zero-length chains are covered. Canonical dependent branch embeddings
and adjoint domain extensions preserve the exact operator norm.

The finite coefficient array, branch selectors, changing memories, fresh
garbage vectors and readout are supplied data. Identifying them with a
concrete distributed circuit, proving its separated exterior-weight
identities and trace-error estimate, identifying its local network tensors,
and assembling uniform polynomial bounds remain separate obligations.
The full compression, PEPS approximation and ground-state area-law theorems
remain open.

All seven modules compile under the package options, all 84 public kernel
reports use only `propext`, `Classical.choice`, `Quot.sound`, or no axioms,
and all seven strict regression files compile without warnings. Source
parity, placeholder/custom-axiom exclusion, style, size, generated imports,
numbered-module policy and blueprint synchronization pass. Thirteen blueprint
entries cover exactly all 84 public names. The standalone four-chapter
LaTeX/BibTeX smoke build produces 23 pages; the full library and web blueprint
are checked in PR CI.

Run the regression files with
`lake env lean -DrelaxedAutoImplicit=false -DmaxSynthPendingDepth=3
-Dlinter.mathlibStandardSet=true -DwarningAsError=true`:

- `QICLeanTest/SourceContraction.lean`
- `QICLeanTest/ChronologicalGarbage.lean`
- `QICLeanTest/ChronologicalGarbageError.lean`
- `QICLeanTest/GlobalBranchLaw.lean`
- `QICLeanTest/SchmidtSource.lean`
- `QICLeanTest/IsometricDomainExtension.lean`
- `QICLeanTest/GaussianContraction.lean`

These include complex phases, unequal and empty dimensions, empty marked
sets, zero stages, unnormalized weights, changing memories and a zero-sample
counterexample explaining why positive sample count is necessary.
Successful regression compilation is silent. The dedicated kernel-audit
command disables only the hash-command linter so that `#print axioms` can
run; proof checking and warning-as-error checking remain enabled.

The seven provenance shards record this exact revision and SHA-256 hashes
of the build, kernel and source-audit logs. All 47 recursive Mathlib import
roots pass the no-build cache preflight. The source audit uses the separate
TNLean provenance parser at revision
`4e9d9c898a4401d51cf1eeeabcea8572242387fe`.

OpenAI Codex (GPT-6) assisted with proofs, independent agent review,
regressions and documentation under the repository owner's direction.
Independent agent review passed; human mathematical review remains pending.
