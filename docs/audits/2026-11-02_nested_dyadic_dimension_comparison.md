# Strict comparison of nested viable dimensions

The dyadic comparison selects actual minimizing spaces for increasing
targets. At the first index where the count bounds the least dimension,
the preceding minimum is `p`, while the next minimizing space has
dimension `Q`. The actual calibrated Haar sample has dimension
`p / (2 * D²)` inside that next space. Its improving image remains viable
for the preceding target and has dimension strictly below `p`, which
contradicts the attained minimum. The proof does not substitute `Q` for
`p` in the sample size.

The first theorem assumes the nested families, the logarithmic count
comparison and a finite count bound. The second theorem derives the two
count conditions for the actual natural ceiling schedule; its nested
families remain explicit hypotheses. Both are generic auxiliaries to
ALVV, arXiv:1602.08828v2, Proposition `prop:albootstrap-ld`, lines
1112–1128. The strict-decrease repair is documented in
`docs/paper-gaps/alvv16_low_density_sampling.tex`. Neither statement
assumes or proves a physical spectral gap. The actual Hamiltonian family
and canonical targets must be substituted separately before claiming a
physical low-density dimension estimate.

The final production module passed a strict actual-name private check in
6.462 seconds against immutable TNLean
`994a1963ab36a234e1b02689a13bf1da965573b2` and its own QICLean package
`67a788fdb9660c16c70c97bf36be5da6bbbaa348`. All selected source and
object hashes, build inputs and the prebuilt Mathlib sentinel were
guarded. An imported inspection of both public declarations passed in
5.057 seconds, reporting only `propext`, `Classical.choice` and
`Quot.sound`; the temporary diagnostic source was removed. Blueprint
source synchronization and reverse coverage, prose and whitespace checks
passed. Ordinary combined compilation and compiled blueprint checking
remain integration checks.
