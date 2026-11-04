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

This theorem does not identify A with a physical spectral width or construct
the shifted Hamiltonian. It does not supply a simultaneous preimage for a
viable space, repeated trimming control, the final compressed eigenvectors,
or the algorithmic conclusion. Those are separate mathematical steps.
