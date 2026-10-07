# Common Schur labels for independent copies

The module `QICLean/Representation/HighLabelWindow.lean` proves the simultaneous label selection of OpenAI, *A two-dimensional area law from a global spectral gap* (September 24, 2026), Section 7, `comparator:high-label`, source lines 255–281 at commit `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.

For a density matrix ρ on a q-dimensional system it constructs one actual irreducible-label sequence λₖ. Eventually its mass in ρ⊗k is at least [2(k+1)^(q²)]⁻¹, while log dim λₖ = k S(ρ) + o(k). Both conclusions hold for the same sequence. Singular density matrices are included. The theorem requires only positivity and trace one of the one-copy density; independent-copy concentration, permutation invariance and the numerical threshold are proved from these assumptions.

A finite intermediate criterion is stated separately for an arbitrary permutation-invariant density. Its explicit tail condition is discharged in the independent-copy theorem. It is not presented as the unrestricted source theorem. The joint spectral argument discards zero-eigenvalue weights, bounds the bad-label mass by the actual surprisal tail plus its exponential remainder, and uses the polynomial count of occurring labels.

For an arbitrary unit bipartite vector, a further theorem applies the selection to its actual reduced density and its literal tensor powers. It proves the inverse polynomial squared projection-norm bound and the entropy asymptotic for one sequence, without a supplied marginal or projection-mass hypothesis.

These statements establish the high-label selection input. They do not establish the ground-state area law, the comparator construction and inverse metrics, amplification, or the spatially separated physical realization. The unique mathematical fragment is `blueprint/src/fragment/high_label_window.tex`. No upstream Lean proof text was reused.
