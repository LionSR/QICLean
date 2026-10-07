# Product densities in actual excitation components

Let \(\Omega\) be a unit one-copy physical vector and let
\(w=(R_B\otimes I)u\), for arbitrary \(u\) and auxiliary register \(\mathcal K\).
The excitation factorization extracts the good-copy tensor
\(\Omega_G=\bigotimes_{i\notin B}\Omega\) and gives a contracted remainder
on the bad physical copies and the auxiliary system.

The auxiliary marginal of that remainder equals the actual auxiliary marginal
\(\rho_{\mathcal K}\) of \(w\). Tracing the bad physical copies gives
\[
 \operatorname{Tr}_{\mathcal H^{\otimes B}}|w\rangle\langle w|
 =|\Omega_G\rangle\langle\Omega_G|\otimes\rho_{\mathcal K},
\]
after reordering the registers. The proof derives this product structure;
it does not assume independence or a separately supplied auxiliary state.
Neither normalization nor nonvanishing of the component is needed, and zero
copies are included.

These are the product-density identities used in the September 24, 2026
manuscript *A two-dimensional area law from a global spectral gap*, Section 7,
lines 520–549, equation `comparator:merge-moments`. They are auxiliary results.
Restriction to the actual physical and auxiliary regions, application of
permutation symmetry and independent-copy physical moment estimates, and the
representation-theoretic merge estimate remain separate.
