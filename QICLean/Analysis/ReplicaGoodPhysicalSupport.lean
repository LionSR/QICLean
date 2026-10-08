/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.ReplicaGoodCopyDensity
import QICLean.Representation.TensorPowerAction

/-!
# Symmetric support of the actual good physical-copy density

The excitation component has the prescribed unit ground vector on every good
physical copy. After tracing the bad physical copies, its actual density is
the tensor product of the pure ground-state power and the same component's
whole auxiliary marginal. Since the ground-state power is fixed by every
copy permutation, the physical symmetrizer fixes this actual density.

This proves the physical symmetric-support assertion in *A two-dimensional
area law from a global spectral gap*, `07-comparators.tex`, lines 513–517,
using the product-density step in lines 520–549. The physical coordinate set
may be `Q × (Y × V)`, as in lines 23 and 103–110. In this application every
middle physical coordinate is retained until symmetrization. No symmetry or
support hypothesis on the original vector is supplied. The compatible
physical spectral projection and its commutation with merged labels are
further assertions.
-/

open scoped BigOperators Matrix Kronecker
open PermutationRepresentation TensorPower

namespace Matrix

variable {A C : Type*} [Fintype A] [DecidableEq A] [Fintype C] [DecidableEq C]

/-
Provenance-ID: 8750-qic-good-physical-support-01
Original formalization, no upstream Lean proof text reused.
Declaration: Matrix.symProj_mul_replicaExcitationComponent_goodAuxiliary_density
Manuscript: September 24, 2026, 07-comparators.tex,
lines 23, 103–110, 513–517 and 520–549.
Labels: comparator:merge-decomposition, comparator:merge-moments.
-/

/-- The actual density on the good physical copies and the whole auxiliary
register is supported on the symmetric physical-copy subspace. Only the
one-copy ground vector is unit. *A two-dimensional area law from a global
spectral gap*, `07-comparators.tex`, lines 513–517 and 520–549. Taking
`A = Q × (Y × V)`, as in lines 23 and 103–110, retains every middle physical
coordinate until this projection. The original vector is arbitrary; zero
components, zero copies and empty good sets are included. -/
theorem symProj_mul_replicaExcitationComponent_goodAuxiliary_density
    (Ω : A → ℂ) (hΩ : ‖WithLp.toLp 2 Ω‖ = 1) {k : ℕ} (B : Finset (Fin k))
    (u : (Fin k → A) × C → ℂ) :
    let w := (replicaExcitationProjection Ω k B ⊗ₖ (1 : Matrix C C ℂ)) *ᵥ u
    let f := fun x : ((Fin (Bᶜ.card) → A) × C) × (↥B → A) =>
      w ((FiniteProduct.splitEquiv (fun _ : Fin k => A) B).symm
        (x.2, fun i => x.1.1 ((Finset.equivFin Bᶜ) i)), x.1.2)
    (symProj (copyPerm A Bᶜ.card) ⊗ₖ (1 : Matrix C C ℂ)) *
      partialTraceRight (vecMulVec f (star f)) =
        partialTraceRight (vecMulVec f (star f)) := by
  classical
  intro w f
  let e : (↥(Bᶜ) → A) ≃ (Fin Bᶜ.card → A) :=
    Equiv.arrowCongr (Finset.equivFin Bᶜ) (Equiv.refl A)
  have hd := congrArg (fun M : Matrix ((↥(Bᶜ) → A) × C) ((↥(Bᶜ) → A) × C) ℂ =>
    M.submatrix (e.prodCongr (Equiv.refl C)).symm
      (e.prodCongr (Equiv.refl C)).symm)
    (partialTraceRight_replicaExcitationComponent_goodAuxiliary_density Ω hΩ B u)
  rw [← partialTraceRight_submatrix_prod_equiv (e.prodCongr (Equiv.refl C))
    (Equiv.refl (↥B → A))] at hd
  have hprod (g : Fin Bᶜ.card → A) :
      (∏ i : ↥(Bᶜ), Ω (g ((Finset.equivFin Bᶜ) i))) = ∏ i, Ω (g i) :=
    (Finset.equivFin Bᶜ).prod_comp (fun i => Ω (g i))
  change partialTraceRight (vecMulVec f (star f)) =
    vecMulVec (fun g : Fin Bᶜ.card → A => ∏ i : ↥(Bᶜ), Ω (g ((Finset.equivFin Bᶜ) i)))
      (star (fun g : Fin Bᶜ.card → A => ∏ i : ↥(Bᶜ), Ω (g ((Finset.equivFin Bᶜ) i)))) ⊗ₖ
      partialTraceLeft (vecMulVec w (star w)) at hd
  simp_rw [hprod] at hd
  rw [hd, ← mul_kronecker_mul, one_mul, mul_vecMulVec]
  suffices hs : symProj (copyPerm A Bᶜ.card) *ᵥ (fun g => ∏ i, Ω (g i)) =
      (fun g => ∏ i, Ω (g i)) by rw [hs]
  apply symProj_mulVec_of_mem
  intro σ
  rw [permOp_mulVec]
  ext g
  exact Equiv.prod_comp σ (fun i => Ω (g i))

end Matrix
