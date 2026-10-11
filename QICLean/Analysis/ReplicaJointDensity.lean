/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.ReplicaRegionalDensity
import QICLean.Analysis.ReplicaGoodAuxiliaryMarginal

/-!
# Joint density on the good physical and auxiliary copies

For the actual excitation component, retain a physical region and the auxiliary
register on each good copy. Tracing the remaining coordinates gives the tensor
power of the original physical marginal, tensored with the actual good auxiliary
marginal of the same component. All coordinates use the chosen finite-set
enumerations of the good and bad copies.

This is the reduced-density product identity in *A two-dimensional area law from
a global spectral gap*, `07-comparators.tex`, lines 520–549, equation
`comparator:merge-moments`. Only the one-copy ground vector is unit. The original
vector and its excitation component may be zero or unnormalized. Zero copies
and empty good sets are included. Permutation symmetry and merge-moment estimates
are separate results.

Independently formalized from the manuscript; no upstream Lean proof text is
reused.
-/
open scoped BigOperators Matrix Kronecker
namespace Matrix
private theorem partialTraceRight_retained_auxiliary
    {α K C R H : Type*} [Fintype R] [Fintype H]
    (e : K ≃ C × R) (g : (α × K) × H → ℂ) :
    partialTraceRightAlong e (partialTraceRight (vecMulVec g (star g))) =
      partialTraceRight (vecMulVec
        (fun x : (α × C) × (R × H) => g ((x.1.1, e.symm (x.1.2, x.2.1)), x.2.2))
        (star (fun x : (α × C) × (R × H) =>
          g ((x.1.1, e.symm (x.1.2, x.2.1)), x.2.2)))) := by
  dsimp only [partialTraceRightAlong]
  rw [partialTraceRight_submatrix_left, partialTraceRight_partialTraceRight]
  rfl

/-- A partial trace on the second tensor factor leaves the first factor unchanged.
This identity is used in the reduced-density product calculation of
`07-comparators.tex`, lines 520–549. -/
theorem partialTraceRightAlong_kronecker
    {α K C R : Type*} [Fintype R] (e : K ≃ C × R)
    (A : Matrix α α ℂ) (B : Matrix K K ℂ) :
    partialTraceRightAlong e (A ⊗ₖ B) =
      A ⊗ₖ partialTraceRight (B.submatrix e.symm e.symm) := by
  ext ⟨a, b⟩ ⟨a', b'⟩
  simp only [partialTraceRightAlong_apply, kroneckerMap_apply,
    partialTraceRight_apply, submatrix_apply, Finset.mul_sum]

private theorem goodRegionalRetained_density {Q T K C R : Type*} [Fintype Q] [DecidableEq Q]
    [Fintype T] [DecidableEq T] [Fintype K] [DecidableEq K]
    [Fintype R]
    (Ω : Q × T → ℂ) (hΩ : ‖WithLp.toLp 2 Ω‖ = 1)
    {k : ℕ} (B : Finset (Fin k)) (e : K ≃ C × R)
    (u : (Fin k → Q × T) × K → ℂ) :
    let w := (replicaExcitationProjection Ω k B ⊗ₖ (1 : Matrix K K ℂ)) *ᵥ u
    let f := fun x : ((Fin (Bᶜ.card) → Q) × C) ×
        (R × ((Fin (Bᶜ.card) → T) × (↥B → Q × T))) =>
      w ((FiniteProduct.splitEquiv (fun _ : Fin k => Q × T) B).symm
        (x.2.2.2, fun i => (x.1.1 ((Finset.equivFin Bᶜ) i),
          x.2.2.1 ((Finset.equivFin Bᶜ) i))), e.symm (x.1.2, x.2.1))
    partialTraceRight (vecMulVec f (star f)) =
      finKronecker (fun _ : Fin (Bᶜ.card) => partialTraceRight (vecMulVec Ω (star Ω))) ⊗ₖ
        partialTraceRight ((partialTraceLeft (vecMulVec w (star w))).submatrix
          e.symm e.symm) := by
  classical
  dsimp only
  let w := (replicaExcitationProjection Ω k B ⊗ₖ (1 : Matrix K K ℂ)) *ᵥ u
  let g := fun x : ((Fin (Bᶜ.card) → Q) × K) ×
      ((Fin (Bᶜ.card) → T) × (↥B → Q × T)) =>
    w ((FiniteProduct.splitEquiv (fun _ : Fin k => Q × T) B).symm
      (x.2.2, fun i => (x.1.1 ((Finset.equivFin Bᶜ) i),
        x.2.1 ((Finset.equivFin Bᶜ) i))), x.1.2)
  have hg := partialTraceRight_replicaExcitationComponent_goodRegional_density Ω hΩ B u
  rw [← partialTraceRight_retained_auxiliary e g, hg]
  exact partialTraceRightAlong_kronecker e _ _

/-
Original formalization, no upstream Lean proof text reused.
Manuscript: September 24, 2026, comparator:merge-moments, lines 520–549.
-/

/-- The literal density on the good physical region and good auxiliary copies,
after tracing every other coordinate of the same excitation component.
*A two-dimensional area law from a global spectral gap*, `07-comparators.tex`,
lines 520–549, equation `comparator:merge-moments`. The ground vector is arbitrary
in this definition; the product identity below requires its normalization. -/
noncomputable def replicaGoodRegionalAuxiliaryMarginal
    {Q T C D : Type*} [Fintype Q] [DecidableEq Q] [Fintype T] [DecidableEq T]
    [Fintype C] [DecidableEq C] [Fintype D] [DecidableEq D]
    (Ω : Q × T → ℂ) (k : ℕ) (B : Finset (Fin k))
    (u : (Fin k → Q × T) × ((Fin k → C) × (Fin k → D)) → ℂ) :
    Matrix ((Fin (Bᶜ.card) → Q) × (Fin (Bᶜ.card) → C))
      ((Fin (Bᶜ.card) → Q) × (Fin (Bᶜ.card) → C)) ℂ :=
  let w := (replicaExcitationProjection Ω k B ⊗ₖ
    (1 : Matrix ((Fin k → C) × (Fin k → D)) ((Fin k → C) × (Fin k → D)) ℂ)) *ᵥ u
  let e := ((TensorPower.goodBadCopiesEquiv C B).prodCongr
    (Equiv.refl (Fin k → D))).trans
      (Equiv.prodAssoc (Fin (Bᶜ.card) → C) (Fin B.card → C) (Fin k → D))
  let f := fun x : ((Fin (Bᶜ.card) → Q) × (Fin (Bᶜ.card) → C)) ×
      (((Fin B.card → C) × (Fin k → D)) ×
        ((Fin (Bᶜ.card) → T) × (↥B → Q × T))) =>
    w ((FiniteProduct.splitEquiv (fun _ : Fin k => Q × T) B).symm
      (x.2.2.2, fun i => (x.1.1 ((Finset.equivFin Bᶜ) i),
        x.2.2.1 ((Finset.equivFin Bᶜ) i))), e.symm (x.1.2, x.2.1))
  partialTraceRight (vecMulVec f (star f))

/-
Original formalization, no upstream Lean proof text reused.
Manuscript: September 24, 2026, comparator:merge-moments, lines 520–549.
-/

/-- The actual joint marginal factors into the tensor power of the original
physical marginal and the actual good auxiliary marginal of the same component.
*A two-dimensional area law from a global spectral gap*, `07-comparators.tex`,
lines 520–549, equation `comparator:merge-moments`. Only the one-copy ground vector
is normalized. No independence, fixedness or marginal identity is assumed. -/
theorem replicaGoodRegionalAuxiliaryMarginal_eq
    {Q T C D : Type*} [Fintype Q] [DecidableEq Q] [Fintype T] [DecidableEq T]
    [Fintype C] [DecidableEq C] [Fintype D] [DecidableEq D]
    (Ω : Q × T → ℂ) (hΩ : ‖WithLp.toLp 2 Ω‖ = 1)
    (k : ℕ) (B : Finset (Fin k))
    (u : (Fin k → Q × T) × ((Fin k → C) × (Fin k → D)) → ℂ) :
    replicaGoodRegionalAuxiliaryMarginal Ω k B u =
      finKronecker (fun _ : Fin (Bᶜ.card) => partialTraceRight (vecMulVec Ω (star Ω))) ⊗ₖ
        replicaGoodAuxiliaryMarginal Ω k B u := by
  exact goodRegionalRetained_density Ω hΩ B
    (((TensorPower.goodBadCopiesEquiv C B).prodCongr
      (Equiv.refl (Fin k → D))).trans
        (Equiv.prodAssoc (Fin (Bᶜ.card) → C) (Fin B.card → C) (Fin k → D))) u
end Matrix
