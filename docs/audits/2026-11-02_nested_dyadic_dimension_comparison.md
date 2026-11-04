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
