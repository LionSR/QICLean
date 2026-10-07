/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.ReplicaGoodCopyDensity

/-!
# Regional product density of the good physical copies

For a bipartite one-copy ground vector, the actual excitation component has
that ground vector on every good copy. Tracing the complementary physical
region on those copies, together with all bad physical copies, gives the
tensor power of the original regional density, tensored with the literal
auxiliary marginal of the same component. The good coordinates are enumerated
by the canonical finite-set equivalence.

This is the regional product step in *A two-dimensional area law from a
global spectral gap*, `07-comparators.tex`, lines 520–549, equation
`comparator:merge-moments`. Only the one-copy ground vector is unit. The
original vector and component may be unnormalized or zero; zero copies and
empty good sets are included. Restriction to the good auxiliary register,
its permutation symmetry and the merge-moment estimate remain further steps.
-/

open scoped BigOperators Matrix Kronecker
namespace Matrix
variable {Q T C : Type*} [Fintype Q] [DecidableEq Q]
  [Fintype T] [DecidableEq T] [Fintype C] [DecidableEq C]

/-
Provenance-ID: 8750-qic-regional-good-copy-density-01
Original formalization, no upstream Lean proof text reused.
Declaration: Matrix.partialTraceRight_replicaExcitationComponent_goodRegional_density
Manuscript: September 24, 2026, comparator:merge-moments, lines 520–549.
-/

/-- The actual marginal on the good copies of a physical region and the whole
auxiliary register is the tensor product of the original regional density
power and the auxiliary marginal of the same component. *A two-dimensional
area law from a global spectral gap*, `07-comparators.tex`, lines 520–549,
equation `comparator:merge-moments`. No regional product hypothesis is supplied. -/
theorem partialTraceRight_replicaExcitationComponent_goodRegional_density
    (Ω : Q × T → ℂ) (hΩ : ‖WithLp.toLp 2 Ω‖ = 1)
    {k : ℕ} (B : Finset (Fin k)) (u : (Fin k → Q × T) × C → ℂ) :
    let w := (replicaExcitationProjection Ω k B ⊗ₖ (1 : Matrix C C ℂ)) *ᵥ u
    let f := fun x : ((Fin (Bᶜ.card) → Q) × C) ×
        ((Fin (Bᶜ.card) → T) × (↥B → Q × T)) =>
      w ((FiniteProduct.splitEquiv (fun _ : Fin k => Q × T) B).symm
        (x.2.2, fun i => (x.1.1 ((Finset.equivFin Bᶜ) i),
          x.2.1 ((Finset.equivFin Bᶜ) i))), x.1.2)
    partialTraceRight (vecMulVec f (star f)) =
      finKronecker (fun _ : Fin (Bᶜ.card) => partialTraceRight (vecMulVec Ω (star Ω))) ⊗ₖ
        partialTraceLeft (vecMulVec w (star w)) := by
  classical
  dsimp only
  rw [partialTraceLeft_replicaExcitationComponent_eq_remainder Ω hΩ B u]
  have hprod (a : Fin (Bᶜ.card) → Q) (b : Fin (Bᶜ.card) → T) :
      (∏ i : ↥(Bᶜ), Ω (a ((Finset.equivFin Bᶜ) i),
        b ((Finset.equivFin Bᶜ) i))) = ∏ i, Ω (a i, b i) :=
    (Finset.equivFin Bᶜ).prod_comp (fun i => Ω (a i, b i))
  ext ⟨q, c⟩ ⟨q', c'⟩
  simp only [partialTraceRight_apply, vecMulVec_apply, Pi.star_apply,
    Fintype.sum_prod_type, replicaExcitationProjection_mulVec_factorization Ω hΩ B u,
    kroneckerMap_apply, partialTraceLeft_apply, finKronecker_apply, star_mul]
  simp_rw [hprod]
  let R := replicaGoodCopyRemainder Ω B
    ((replicaExcitationProjection Ω k B ⊗ₖ (1 : Matrix C C ℂ)) *ᵥ u)
  change (∑ t : Fin (Bᶜ.card) → T, ∑ b : ↥B → Q × T,
      (∏ i, Ω (q i, t i)) * R (b, c) *
      (star (R (b, c')) * star (∏ i, Ω (q' i, t i)))) =
    (∏ i, ∑ t, Ω (q i, t) * star (Ω (q' i, t))) *
      ∑ b : ↥B → Q × T, R (b, c) * star (R (b, c'))
  calc
    _ = (∑ t : Fin (Bᶜ.card) → T,
        (∏ i, Ω (q i, t i)) * star (∏ i, Ω (q' i, t i))) *
        ∑ b : ↥B → Q × T, R (b, c) * star (R (b, c')) := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro t _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro b _
      ring
    _ = _ := by
      congr 1
      simp only [star_prod, ← Finset.prod_mul_distrib]
      exact (Fintype.prod_sum (fun (i : Fin (Bᶜ.card)) (t : T) =>
        Ω (q i, t) * star (Ω (q' i, t)))).symm
end Matrix
