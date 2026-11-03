# The matrix order bound for an energy-weighted power

This is an explicit operator auxiliary for ALVV, arXiv:1602.08828v2,
`t:alg1`, final power step, lines 1811–1815. Let H be Hermitian with
0<=H<=A I, where A>0, and suppose 0<gamma<=A. If each spectral value
is either zero or at least gamma and A<=(tau+1)gamma, the theorem gives

    0 <= H (I-H/A)^(2tau) <= gamma(1-gamma/A)^tau I.

There is no simplicity or nonzero-kernel assumption. Zero matrices, empty
finite matrix index types and zero powers are included. In particular, the
zero spectral branch is handled separately; it does not require a positive
excitation energy to be attained.

The proof derives the upper spectral bound from H<=A I, then uses the
proved scalar estimate at each nonzero spectral value. Mathlib continuous
functional calculus identifies the scalar polynomial with the literal
matrix product and transports its lower and upper bounds. No energy
estimate is supplied as a premise.

The new module imports only Mathlib matrix order and the separately proved
scalar module `EnergyWeightedPowerDecay`. The worktree starts at scalar
revision `0178f7bea8470418d85df93a4e94f9823b69d57b` over exact QICLean
base `ba01733099b5a18bed5c9bfb62f95f175b4c9b57`, with no `.lake` directory.
All checks write temporary objects only and preserve the selected source,
object and build-input guards of the warmed provider.

This theorem does not identify A with a physical spectral width or construct
the shifted Hamiltonian. It does not supply a simultaneous preimage for a
viable space, repeated trimming control, the final compressed eigenvectors,
or the algorithmic conclusion. Those are separate mathematical steps.

The complete module passed a fresh strict actual-name check in 24.901 seconds.
A separate imported foundation audit passed in 18.837 seconds. The public
order theorem depends only on `propext`, `Classical.choice` and `Quot.sound`.
The warmed provider remained at `24a2ee589c5ff8da34a5cc6d8b7026dc7700e929`;
the guarded build inputs equal the exact target revision, and the two new
private source/object pairs are explicitly selected. No existing QIC
mathematical object enters the selected dependency closure. No provider or
cache was modified and no Mathlib source was rebuilt.

The mathematical book entry is included. Added prose, whitespace, generated
imports and the new-source tactic-pattern scan pass. No test fixture or
permanent foundation command is added. Ordinary full and complete compiled-book
checks remain pending.
