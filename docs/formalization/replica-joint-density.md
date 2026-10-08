# Joint density on the good physical and auxiliary copies

Let Ω be a one-copy vector on Q⊗T, and let w=(R_B⊗I)u be the actual
excitation component of a vector with auxiliary registers C^⊗k and D^⊗k.
The joint marginal retains Q and C on the good copies. It traces T on those
copies, all bad physical copies, the bad C coordinates and every D coordinate.
The physical and auxiliary coordinates use the same chosen enumeration of the
good set; no increasing-order property is assumed.

For unit Ω, this literal marginal is ρ_Q^⊗|Bᶜ|⊗ρ_Cgood(w), where ρ_Q is
the original Q marginal of Ω and ρ_Cgood(w) is the actual good auxiliary
marginal of the same component. The proof first uses the regional density
identity with the whole auxiliary register. It then regroups that register
and composes partial traces. Tracing the unwanted auxiliary factor of a
Kronecker product leaves the physical factor unchanged.

The definition accepts arbitrary Ω; its excitation operator is a projection
when Ω is unit. Only the product theorem requires unit Ω. Neither u nor w needs normalization or nonvanishing, and no independence,
permutation fixedness or supplied marginal identity is assumed. Zero copies
and empty good sets are included.

This result is the reduced-density product identity in the September 24, 2026
OpenAI area-law manuscript, Section 7, `07-comparators.tex`, lines 520–549,
equation `comparator:merge-moments`. The auxiliary permutation symmetry is
proved separately. The paired merge-moment estimate and final area-law bound
remain further assertions.
