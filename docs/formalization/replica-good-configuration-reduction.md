# Reductions of the density of the good copies

The physical factors are Q, Y and V; Y is an independent middle factor.
The auxiliary factors are C and R. For a set B of bad copies, the actual
component is w = (R_B ⊗ I)u. Its full good-copy density retains Q, Y, V,
C and R on the complementary set G, using the same chosen enumeration of G
in all five factors.

The reduction to the two pairs first groups the retained coordinates as
((Q^m × C^m) × (V^m × R^m)) × Y^m, where m = |G|. Tracing Y^m gives the
existing actual common-pair density of w. This identity is unconditional
on the one-copy vector and on u: no product, marginal or coordinate identity
is assumed.

For a unit one-copy physical vector, the physical symmetric projection P
fixes the full good-copy density Γ. The compatible physical-label identity
JP = P, with J the nonnegative spectral projection of F_Q + F_V − F_Y,
therefore gives JΓ = Γ. This conclusion requires no symmetry assumption on
u and does not assert that the QC or VR label measurements preserve P.

For a collection T of factors, let $F_T$ be the copy-permutation observable
whose value on an irreducible label is the logarithm of the dimension of
that irreducible representation. Define

$$
D_C = F_Q + F_C - F_{QC},\qquad D_R = F_V + F_R - F_{VR}.
$$

If u is fixed by the original simultaneous copy permutations, then the
existing two-pair moment bound transfers to Γ. The exact rearrangement of
coordinates sends each of the six actual label operators defining D_C and
D_R to its paired action tensored with the identity on Y^m. The same holds
for their sum and its exponential. For every real a with 2a ≤ 1, the bound is

$$
\operatorname{Re}\operatorname{Tr}\bigl(\Gamma\exp(a(D_C+D_R))\bigr)
\le \frac{p_{QC}+p_{VR}}{2}\,\lVert w\rVert^2.
$$

where p_QC = (m+1)^((|Q||C|)²) and p_VR = (m+1)^((|V||R|)²).
The mass is the literal squared norm of the original excitation component.
Zero mass, zero copies and empty good sets are included. The arithmetic-mean
polynomial is an auxiliary estimate, rather than the sharper printed constant
or a complete metric comparison.

References: OpenAI, *A two-dimensional area law from a global spectral gap*,
September 24, 2026, Section 7, lines 23, 103–110 and 501–555, especially
`comparator:merge-decomposition` and `comparator:merge-moments`, at manuscript
commit `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
