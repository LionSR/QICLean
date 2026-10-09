/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.ReplicaGoodConfigurationDensity
import QICLean.Analysis.ReplicaJointDensity
import QICLean.Analysis.TraceDistance

/-!
# The physical tensor power in the actual good-copy density

After tracing all bad copies, the five-factor density is the tensor product
of the original pure physical state on the good copies and the actual joint
good auxiliary marginal of the same excitation component. Consequently every
observable on the good physical copies has its original tensor-power
expectation, multiplied by the squared norm of that component.

Only the one-copy ground vector is normalized. The original vector and its
excitation components may be zero or unnormalized. The auxiliary marginal
is obtained by partial trace, rather than supplied as independent data.

Source: *A two-dimensional area law from a global spectral gap*, September 24,
2026, `07-comparators.tex`, lines 520–560, `comparator:merge-moments`, revision
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

noncomputable section
open scoped BigOperators Matrix Kronecker
open TensorPower

namespace Matrix

/-- The good physical copies, enumerated by the chosen finite-set equivalence,
have the original pure tensor-power density, independently of the literal
whole auxiliary marginal. Source: `07-comparators.tex`, lines 520–549. -/
theorem partialTraceRight_replicaExcitationComponent_goodFin_density
    {A K : Type*} [Fintype A] [DecidableEq A] [Fintype K] [DecidableEq K]
    (Ω : A → ℂ) (hΩ : ‖WithLp.toLp 2 Ω‖ = 1) {k : ℕ} (B : Finset (Fin k))
    (u : (Fin k → A) × K → ℂ) :
    let w := (replicaExcitationProjection Ω k B ⊗ₖ (1 : Matrix K K ℂ)) *ᵥ u
    let f := fun x : ((Fin Bᶜ.card → A) × K) × (↥B → A) =>
      w ((FiniteProduct.splitEquiv (fun _ : Fin k => A) B).symm
        (x.2, fun i => x.1.1 ((Finset.equivFin Bᶜ) i)), x.1.2)
    partialTraceRight (vecMulVec f (star f)) =
      finKronecker (fun _ : Fin Bᶜ.card => vecMulVec Ω (star Ω)) ⊗ₖ
        partialTraceLeft (vecMulVec w (star w)) := by
  classical
  intro w f
  let e : (↥(Bᶜ) → A) ≃ (Fin Bᶜ.card → A) :=
    Equiv.arrowCongr (Finset.equivFin Bᶜ) (Equiv.refl A)
  have hd := congrArg (fun M : Matrix ((↥(Bᶜ) → A) × K) ((↥(Bᶜ) → A) × K) ℂ =>
    M.submatrix (e.prodCongr (Equiv.refl K)).symm
      (e.prodCongr (Equiv.refl K)).symm)
    (partialTraceRight_replicaExcitationComponent_goodAuxiliary_density Ω hΩ B u)
  rw [← partialTraceRight_submatrix_prod_equiv (e.prodCongr (Equiv.refl K))
    (Equiv.refl (↥B → A))] at hd
  have hprod (g : Fin Bᶜ.card → A) :
      (∏ i : ↥(Bᶜ), Ω (g ((Finset.equivFin Bᶜ) i))) = ∏ i, Ω (g i) :=
    (Finset.equivFin Bᶜ).prod_comp (fun i => Ω (g i))
  change partialTraceRight (vecMulVec f (star f)) =
    vecMulVec (fun g : Fin Bᶜ.card → A => ∏ i : ↥(Bᶜ), Ω (g ((Finset.equivFin Bᶜ) i)))
      (star (fun g : Fin Bᶜ.card → A => ∏ i : ↥(Bᶜ), Ω (g ((Finset.equivFin Bᶜ) i)))) ⊗ₖ
        partialTraceLeft (vecMulVec w (star w)) at hd
  simp_rw [hprod] at hd
  rw [hd]
  congr 1
  ext x y
  simp only [vecMulVec_apply, Pi.star_apply, finKronecker_apply, star_prod,
    Finset.prod_mul_distrib]

variable (ι : Fin 5 → Type*) [∀ f, Fintype (ι f)] [∀ f, DecidableEq (ι f)]
variable (Ω : ι 0 × (ι 1 × ι 2) → ℂ) (hΩ : ‖WithLp.toLp 2 Ω‖ = 1)
variable (k : ℕ) (B : Finset (Fin k))
variable (u : (Fin k → ι 0 × (ι 1 × ι 2)) ×
  ((Fin k → ι 3) × (Fin k → ι 4)) → ℂ)

include hΩ

/-- Regrouping the actual good density into its physical and auxiliary
registers gives an exact product. The auxiliary factor is the literal
reduced density of the same component. Source: `07-comparators.tex`,
lines 520–560. -/
theorem replicaGoodConfigurationMarginal_product :
    let w := (replicaExcitationProjection Ω k B ⊗ₖ
      (1 : Matrix ((Fin k → ι 3) × (Fin k → ι 4))
        ((Fin k → ι 3) × (Fin k → ι 4)) ℂ)) *ᵥ u
    (replicaGoodConfigurationMarginal ι Ω k B u).submatrix
        (fiveFactorCopiesEquiv ι Bᶜ.card).symm (fiveFactorCopiesEquiv ι Bᶜ.card).symm =
      finKronecker (fun _ : Fin Bᶜ.card => vecMulVec Ω (star Ω)) ⊗ₖ
        partialTraceRight ((partialTraceLeft (vecMulVec w (star w))).submatrix
          (goodAuxiliarySplit ι B).symm (goodAuxiliarySplit ι B).symm) := by
  intro w
  rw [replicaGoodConfigurationMarginal_eq, submatrix_submatrix,
    Equiv.self_comp_symm, submatrix_id_id,
    partialTraceRight_replicaExcitationComponent_goodFin_density Ω hΩ B u,
    partialTraceRightAlong_kronecker]

/-- Tracing all good auxiliary coordinates leaves the original pure physical
tensor power with precisely the squared norm of the excitation component.
Source: `07-comparators.tex`, lines 550–560. -/
theorem partialTraceRight_replicaGoodConfigurationMarginal_physical :
    let w := (replicaExcitationProjection Ω k B ⊗ₖ
      (1 : Matrix ((Fin k → ι 3) × (Fin k → ι 4))
        ((Fin k → ι 3) × (Fin k → ι 4)) ℂ)) *ᵥ u
    partialTraceRight ((replicaGoodConfigurationMarginal ι Ω k B u).submatrix
      (fiveFactorCopiesEquiv ι Bᶜ.card).symm (fiveFactorCopiesEquiv ι Bᶜ.card).symm) =
        (‖WithLp.toLp 2 w‖ ^ 2 : ℂ) •
          finKronecker (fun _ : Fin Bᶜ.card => vecMulVec Ω (star Ω)) := by
  intro w
  rw [replicaGoodConfigurationMarginal_product ι Ω hΩ k B u,
    partialTraceRight_kronecker, trace_partialTraceRight, trace_submatrix_equiv,
    trace_partialTraceLeft, trace_vecMulVec,
    ← EuclideanSpace.inner_eq_star_dotProduct (WithLp.toLp 2 w) (WithLp.toLp 2 w),
    inner_self_eq_norm_sq_to_K]
  rfl

/-- An arbitrary observable on all good physical copies has its original
pure tensor-power expectation times the component mass. No sign, symmetry,
or nonvanishing condition on the component is required.
Source: `07-comparators.tex`, lines 550–560. -/
theorem trace_replicaGoodConfigurationMarginal_physical_mul
    (H : Matrix (Fin Bᶜ.card → ι 0 × (ι 1 × ι 2))
      (Fin Bᶜ.card → ι 0 × (ι 1 × ι 2)) ℂ) :
    let w := (replicaExcitationProjection Ω k B ⊗ₖ
      (1 : Matrix ((Fin k → ι 3) × (Fin k → ι 4))
        ((Fin k → ι 3) × (Fin k → ι 4)) ℂ)) *ᵥ u
    (((replicaGoodConfigurationMarginal ι Ω k B u).submatrix
      (fiveFactorCopiesEquiv ι Bᶜ.card).symm (fiveFactorCopiesEquiv ι Bᶜ.card).symm) *
      (H ⊗ₖ (1 : Matrix ((Fin Bᶜ.card → ι 3) × (Fin Bᶜ.card → ι 4))
        ((Fin Bᶜ.card → ι 3) × (Fin Bᶜ.card → ι 4)) ℂ))).trace =
      (‖WithLp.toLp 2 w‖ ^ 2 : ℂ) *
        (finKronecker (fun _ : Fin Bᶜ.card => vecMulVec Ω (star Ω)) * H).trace := by
  intro w
  rw [← trace_partialTraceRight_mul,
    partialTraceRight_replicaGoodConfigurationMarginal_physical ι Ω hΩ k B u,
    smul_mul_assoc, trace_smul, smul_eq_mul]

end Matrix
