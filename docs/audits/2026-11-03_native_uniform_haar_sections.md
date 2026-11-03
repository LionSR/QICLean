# Uniform sampling in physical coordinates

A fixed bijection `e : Fin d ≃ C` identifies native configuration coordinates
with finite Euclidean coordinates. For a native subspace `W`, the sampled
matrix is exactly the orthogonal projection matrix of `W`, reindexed by
`e.symm` in both indices. The native sample is exactly the image, under the
coordinate isometry, of the existing canonical range sampler of this matrix.
There is no additional sampling definition.

The theorem chooses the same explicit sample size and common overlap as the
uniform actual-rank theorem before `W` and the full tensor target `T`.
From quarter-viability, `dim W ≤ D^12*s^6`, and `dim T ≤ r`, it proves that
the true native failure measure at overlap `3/(32D^12*s^5)` is at most
`beta`. The exterior factor is an arbitrary finite-dimensional complex
Hilbert space. Zero ranges and empty native coordinate sets are included.

The proof identifies the actual reindexed projection with the projection
onto the inverse coordinate image of `W`; its range and rank are therefore
derived. The same tensor isometry transports the entire target, preserves
its dimension and viability, and transports the sampled space back for
each individual seed. The argument does not identify the canonical sampler
with one using an arbitrary changing choice of orthonormal basis.

This supports ALVV, arXiv:1602.08828v2, Definition `d:vs`, lines 433–440,
Lemma `l:rs`, lines 530–558, and the merge analysis, lines 1777–1817.
It retains the corrected sphere-net exponent documented in
`docs/paper-gaps/alvv16_random_sampling_net_count.tex`. It is a fixed-input
section bound, not a probability theorem for an adaptive construction.

## Verification

The actual module passed strict checking in 5.997 seconds against the
immutable TNLean `435cbe7fe53e5d3a04c1b8eb2382753749f21a64` provider and its
own QICLean `b2ea12a0139820758e161514968ed9ead661c5a7` package, with the
previously checked uniform-sampling module as an explicit source/object
override. The checker guarded 47 selected source/object pairs and the build
inputs. Default elaboration options were retained. The imported foundation inspection passed in 4.709 seconds and uses only
`propext`, `Classical.choice`, and `Quot.sound`; its temporary source was
deleted. Source/blueprint synchronization, reader prose, generated imports,
proof integrity, whitespace checks, and the pattern scan passed. The reader
section was rendered and inspected. Exact hashes and check records are in
the companion verification manifest. No provider source, artifact, cache, or pin was changed;
no Mathlib source was built. Ordinary combined compilation and the compiled
blueprint declaration check remain integration checks.
