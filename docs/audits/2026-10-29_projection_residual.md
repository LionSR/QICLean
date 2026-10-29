# An orthogonal projection with a perturbed input

For an orthogonal projection P on a real or complex Hilbert space and
arbitrary vectors x,y, the squared residual of Py from x is at most the
squared residual of Px plus the squared input error. The two components
x-Px and P(x-y) are orthogonal, so the proof is Pythagoras followed by the
existing projection contraction estimate. No normalization of either
vector is required, and y need not itself arise from a projection.

This auxiliary estimate supports the regional frustration-free converse
in ALVV, arXiv:1602.08828v2, `thm:FF-tH`, lines 1543–1550. Its application
to the actual internal and external parity products is separate work;
no regional gap or rank conclusion is asserted by this lemma alone.

Mathlib's existing orthogonal-sum identity and QICLean's projection
identities are reused. The production source passed strict checking in
7.450 seconds against the read-only QICLean provider
`4276de2eeb5c4122f4482ef5e4fa205be5b71bd9`. A separate import of the actual
compiled object audited the public theorem in 3.830 seconds; only
`propext`, `Classical.choice` and `Quot.sound` occur. The imported
QICLean source/object, build inputs and Mathlib sentinel remained fixed.
Records and objects are under `/tmp/qiclean-projection-residual-20261029`.

The source-only worktree has no Lake cache. No provider, pin or ordinary
artifact was changed or copied; Mathlib was not rebuilt. Ordinary combined
verification and compiled blueprint checks remain integration tasks.
