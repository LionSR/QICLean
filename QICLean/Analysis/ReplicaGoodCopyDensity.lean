/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.ReplicaGoodCopyFactorization
import QICLean.Channel.PartialTrace

/-!
# Product densities of the good physical copies and auxiliary systems

An actual excitation component factors into the prescribed ground states on
its good copies and a partial contraction on the remaining registers. Taking
partial traces gives a product density on the good physical copies and the
entire auxiliary register. The auxiliary factor is the literal marginal of
the same component, rather than a separately supplied state.

These identities supply the product step in *A two-dimensional area law from
a global spectral gap*, `07-comparators.tex`, lines 520–549, equation
`comparator:merge-moments`. Only normalization of the one-copy ground vector
is used. Zero components and zero copies are included. Regional restriction,
independent-copy physical moments, auxiliary permutation invariance and the
merge-moment bound are further assertions.

Independently formalized from the manuscript; no upstream Lean proof text is
reused.
-/

open scoped BigOperators Matrix Kronecker

namespace Matrix

variable {A C : Type*} [Fintype A] [DecidableEq A] [Fintype C] [DecidableEq C]
private theorem goodAuxiliary_density_factorization_with_remainder
    (Ω : A → ℂ) (hΩ : ‖WithLp.toLp 2 Ω‖ = 1) {k : ℕ} (B : Finset (Fin k))
    (u : (Fin k → A) × C → ℂ) :
    let w := (replicaExcitationProjection Ω k B ⊗ₖ (1 : Matrix C C ℂ)) *ᵥ u
    let φ : FiniteProduct.Configuration (fun _ : Fin k => A) Bᶜ → ℂ :=
      fun g => ∏ i : ↥(Bᶜ), Ω (g i)
    let f := fun x : (FiniteProduct.Configuration (fun _ : Fin k => A) Bᶜ × C) ×
        FiniteProduct.Configuration (fun _ : Fin k => A) B =>
      w ((FiniteProduct.splitEquiv (fun _ : Fin k => A) B).symm (x.2, x.1.1), x.1.2)
    partialTraceRight (vecMulVec f (star f)) =
      vecMulVec φ (star φ) ⊗ₖ
        partialTraceLeft (vecMulVec (replicaGoodCopyRemainder Ω B w)
          (star (replicaGoodCopyRemainder Ω B w))) := by
  classical
  dsimp only
  ext ⟨g, c⟩ ⟨g', c'⟩
  simp only [partialTraceRight_apply, vecMulVec_apply, Pi.star_apply,
    replicaExcitationProjection_mulVec_factorization Ω hΩ B u,
    kroneckerMap_apply, partialTraceLeft_apply, star_mul]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  ring

/-
Original formalization, no upstream Lean proof text reused.
Manuscript: September 24, 2026, comparator:merge-moments, lines 520–549.
-/

/-- The actual auxiliary marginal is unchanged by contracting the unit ground
state on every good physical copy. *A two-dimensional area law from a global
spectral gap*, `07-comparators.tex`, lines 520–549, equation
`comparator:merge-moments`. The component need not be normalized or nonzero. -/
theorem partialTraceLeft_replicaExcitationComponent_eq_remainder
    (Ω : A → ℂ) (hΩ : ‖WithLp.toLp 2 Ω‖ = 1) {k : ℕ} (B : Finset (Fin k))
    (u : (Fin k → A) × C → ℂ) :
    let w := (replicaExcitationProjection Ω k B ⊗ₖ (1 : Matrix C C ℂ)) *ᵥ u
    partialTraceLeft (vecMulVec w (star w)) =
      partialTraceLeft (vecMulVec (replicaGoodCopyRemainder Ω B w)
        (star (replicaGoodCopyRemainder Ω B w))) := by
  classical
  dsimp only
  have hdot : (∑ a : A, Ω a * star (Ω a)) = 1 := by
    simpa only [EuclideanSpace.inner_toLp_toLp, dotProduct, Pi.star_apply, hΩ,
      RCLike.ofReal_one, one_pow] using
      (inner_self_eq_norm_sq_to_K (𝕜 := ℂ) (WithLp.toLp 2 Ω))
  have hgood : (∑ g : FiniteProduct.Configuration (fun _ : Fin k => A) Bᶜ,
      (∏ i : ↥(Bᶜ), Ω (g i)) * star (∏ i : ↥(Bᶜ), Ω (g i))) = 1 := by
    simp only [star_prod, ← Finset.prod_mul_distrib]
    simpa only [hdot, Finset.prod_const_one] using
      (Fintype.prod_sum (fun (_ : ↥(Bᶜ)) (a : A) => Ω a * star (Ω a))).symm
  ext c c'
  rw [partialTraceLeft_apply]
  rw [← (FiniteProduct.splitEquiv (fun _ : Fin k => A) B).symm.sum_comp]
  simp only [Fintype.sum_prod_type, vecMulVec_apply, Pi.star_apply,
    replicaExcitationProjection_mulVec_factorization Ω hΩ B u,
    partialTraceLeft_apply, star_mul]
  apply Finset.sum_congr rfl
  intro b _
  calc
    _ = (∑ g : FiniteProduct.Configuration (fun _ : Fin k => A) Bᶜ,
        (∏ i : ↥(Bᶜ), Ω (g i)) * star (∏ i : ↥(Bᶜ), Ω (g i))) *
        (replicaGoodCopyRemainder Ω B
          ((replicaExcitationProjection Ω k B ⊗ₖ (1 : Matrix C C ℂ)) *ᵥ u) (b,c) *
        star (replicaGoodCopyRemainder Ω B
          ((replicaExcitationProjection Ω k B ⊗ₖ (1 : Matrix C C ℂ)) *ᵥ u) (b,c'))) := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro g _
      ring
    _ = _ := by rw [hgood, one_mul]

/-
Original formalization, no upstream Lean proof text reused.
Manuscript: September 24, 2026, comparator:merge-moments, lines 520–549.
-/

/-- Tracing the bad physical copies of an actual excitation component gives
exactly the tensor product of the good ground-state density and that component's
actual auxiliary marginal. *A two-dimensional area law from a global spectral
gap*, `07-comparators.tex`, lines 520–549, equation `comparator:merge-moments`.
No product-state or independence hypothesis is supplied. -/
theorem partialTraceRight_replicaExcitationComponent_goodAuxiliary_density
    (Ω : A → ℂ) (hΩ : ‖WithLp.toLp 2 Ω‖ = 1) {k : ℕ} (B : Finset (Fin k))
    (u : (Fin k → A) × C → ℂ) :
    let w := (replicaExcitationProjection Ω k B ⊗ₖ (1 : Matrix C C ℂ)) *ᵥ u
    let φ : FiniteProduct.Configuration (fun _ : Fin k => A) Bᶜ → ℂ :=
      fun g => ∏ i : ↥(Bᶜ), Ω (g i)
    let f := fun x : (FiniteProduct.Configuration (fun _ : Fin k => A) Bᶜ × C) ×
        FiniteProduct.Configuration (fun _ : Fin k => A) B =>
      w ((FiniteProduct.splitEquiv (fun _ : Fin k => A) B).symm (x.2, x.1.1), x.1.2)
    partialTraceRight (vecMulVec f (star f)) =
      vecMulVec φ (star φ) ⊗ₖ partialTraceLeft (vecMulVec w (star w)) := by
  dsimp only
  rw [partialTraceLeft_replicaExcitationComponent_eq_remainder Ω hΩ B u]
  exact goodAuxiliary_density_factorization_with_remainder Ω hΩ B u

end Matrix
