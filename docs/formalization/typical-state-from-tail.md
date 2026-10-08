# Typical states from a spectral tail

This finite-dimensional consequence uses OpenAI's two-dimensional area-law
manuscript (September 24, 2026), at
`openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`:
the typical-set and entropy estimates in `07-comparators.tex`, lines 39–55,
the selected vector in lines 240–247, and Lemma 3.1 in `02-initial.tex`.

For an actual density matrix with eigenvalues p and entropy S, the existing
canonical typical set consists of its positive eigenvalue indices satisfying
`|-log p_i - S| ≤ w`. No second typical-set definition is introduced.
If its actual spectral tail is at most δ < 1, the selected mass z satisfies
`1 - δ ≤ z ≤ 1` and is positive. The existing normalized spectral restriction
is positive semidefinite, has trace one and rank equal to the cardinality of
the selected set. Its logarithmic rank and entropy differ from S by at most
`w - log (1 - δ)`.

For a unit bipartite vector, the same set is formed from its actual first
marginal. The existing selected vector is unit and differs from the original
vector in norm by at most `sqrt (2δ)`. Its actual first marginal satisfies the
same rank and entropy estimates. The proof uses the density conclusion,
the previously proved selected-marginal identity, and the squared vector-error
bound. It assumes neither a full-rank marginal nor independently supplied
positive selected mass.

The two declarations are conditional consequences of a spectral tail estimate,
not new proofs of the physical marginal concentration theorem. The later
physical choice `w = n^(3/5)` and `δ = n^-100` remains separate. The accepted
native marginal-tail results and Schur-label estimates are reused or left to
their existing mathematical developments.

Codex (GPT-6) assisted this independently written formalization. No upstream
Lean proof text was copied or adapted.
