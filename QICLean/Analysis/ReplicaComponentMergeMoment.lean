/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Representation.PairMergeMoment
import QICLean.Representation.MergeExponential
import QICLean.Analysis.ReplicaJointDensity
import QICLean.Algebra.TraceReindex
import QICLean.Analysis.ReplicaPermutationCovariance

/-!
# Exponential merge moments of excitation components

The good regional and auxiliary marginal of an actual excitation component
satisfies the exponential Schur-label merge-moment estimate. Its positivity,
separate copy-permutation invariances and trace mass are derived from the
component itself. The moment is bounded by a polynomial in the number of good
copies times the squared norm of the component.

OpenAI, *A two-dimensional area law from a global spectral gap* (September 24,
2026), `07-comparators.tex`, lines 520–549, equation
`comparator:merge-moments`, at commit
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Zero components, zero copies and an empty set of good copies are included.

Independently formalized from the manuscript; no upstream Lean proof text is
reused.
-/
open Matrix PermutationRepresentation

open scoped Kronecker
namespace TensorPower
variable {Q C : Type*} [Fintype Q] [Fintype C] [DecidableEq Q] [DecidableEq C]
    {m : ℕ}

private theorem permOp_pairCopyLeft (σ : Equiv.Perm (Fin m)) :
    permOp (pairCopyLeft Q C m) σ =
      permOp (copyPerm Q m) σ ⊗ₖ (1 : Matrix (Fin m → C) (Fin m → C) ℂ) := by
  ext ⟨x, a⟩ ⟨y, b⟩
  simp only [permOp_apply_apply, Matrix.kroneckerMap_apply, Matrix.one_apply]
  change (if (((copyPerm Q m) σ) y, b) = (x, a) then (1 : ℂ) else 0) =
    (if ((copyPerm Q m) σ) y = x then 1 else 0) * (if a = b then 1 else 0)
  simp only [Prod.mk.injEq]
  split_ifs <;> simp_all

private theorem permOp_pairCopyRight (σ : Equiv.Perm (Fin m)) :
    permOp (pairCopyRight Q C m) σ =
      (1 : Matrix (Fin m → Q) (Fin m → Q) ℂ) ⊗ₖ permOp (copyPerm C m) σ := by
  ext ⟨x, a⟩ ⟨y, b⟩
  simp only [permOp_apply_apply, Matrix.kroneckerMap_apply, Matrix.one_apply]
  change (if (y, ((copyPerm C m) σ) b) = (x, a) then (1 : ℂ) else 0) =
    (if x = y then 1 else 0) * (if ((copyPerm C m) σ) b = a then 1 else 0)
  simp only [Prod.mk.injEq]
  split_ifs <;> simp_all

private theorem commute_pair_product_left {A : Matrix (Fin m → Q) (Fin m → Q) ℂ}
    (B : Matrix (Fin m → C) (Fin m → C) ℂ) (σ : Equiv.Perm (Fin m))
    (hA : Commute (permOp (copyPerm Q m) σ) A) :
    Commute (permOp (pairCopyLeft Q C m) σ) (A ⊗ₖ B) := by
  rw [permOp_pairCopyLeft]
  change (permOp (copyPerm Q m) σ ⊗ₖ 1) * (A ⊗ₖ B) =
    (A ⊗ₖ B) * (permOp (copyPerm Q m) σ ⊗ₖ 1)
  simp only [← Matrix.mul_kronecker_mul, Matrix.one_mul, Matrix.mul_one, hA.eq]

private theorem commute_pair_product_right (A : Matrix (Fin m → Q) (Fin m → Q) ℂ)
    {B : Matrix (Fin m → C) (Fin m → C) ℂ} (σ : Equiv.Perm (Fin m))
    (hB : Commute (permOp (copyPerm C m) σ) B) :
    Commute (permOp (pairCopyRight Q C m) σ) (A ⊗ₖ B) := by
  rw [permOp_pairCopyRight]
  change (1 ⊗ₖ permOp (copyPerm C m) σ) * (A ⊗ₖ B) =
    (A ⊗ₖ B) * (1 ⊗ₖ permOp (copyPerm C m) σ)
  simp only [← Matrix.mul_kronecker_mul, Matrix.one_mul, Matrix.mul_one, hB.eq]
end TensorPower

open scoped BigOperators Matrix Kronecker ComplexOrder Matrix.Norms.Operator
namespace Matrix

private theorem trace_actualGoodAuxiliary {A C D : Type*} [Fintype A] [DecidableEq A]
    [Fintype C] [DecidableEq C] [Fintype D] [DecidableEq D]
    (Ω : A → ℂ) (k : ℕ) (B : Finset (Fin k))
    (u : (Fin k → A) × ((Fin k → C) × (Fin k → D)) → ℂ) :
    (replicaGoodAuxiliaryMarginal Ω k B u).trace =
      let w := (replicaExcitationProjection Ω k B ⊗ₖ
        (1 : Matrix ((Fin k → C) × (Fin k → D)) ((Fin k → C) × (Fin k → D)) ℂ)) *ᵥ u
      (vecMulVec w (star w)).trace := by
  dsimp only [replicaGoodAuxiliaryMarginal]
  rw [trace_partialTraceRight, trace_reindex, trace_partialTraceLeft]

private theorem trace_finKronecker_const {Q : Type*} [Fintype Q] (H : Matrix Q Q ℂ) (m : ℕ) :
    (finKronecker (fun _ : Fin m ↦ H)).trace = H.trace ^ m := by
  simp only [Matrix.trace, Matrix.diag, finKronecker_apply]
  calc
    _ = ∏ _ : Fin m, ∑ i : Q, H i i :=
      (Fintype.prod_sum (fun (_ : Fin m) (i : Q) ↦ H i i)).symm
    _ = _ := by simp

private theorem trace_groundRegional {Q T : Type*} [Fintype Q] [Fintype T]
    (Ω : Q × T → ℂ) (hΩ : ‖WithLp.toLp 2 Ω‖ = 1) :
    (partialTraceRight (vecMulVec Ω (star Ω))).trace = 1 := by
  rw [trace_partialTraceRight, trace_vecMulVec,
    ← EuclideanSpace.inner_eq_star_dotProduct (WithLp.toLp 2 Ω) (WithLp.toLp 2 Ω),
    inner_self_eq_norm_sq_to_K, hΩ]
  norm_num

private theorem trace_vecMulVec_re_norm_sq {X : Type*} [Fintype X] (w : X → ℂ) :
    (vecMulVec w (star w)).trace.re = ‖WithLp.toLp 2 w‖ ^ 2 := by
  rw [trace_vecMulVec,
    ← EuclideanSpace.inner_eq_star_dotProduct (WithLp.toLp 2 w) (WithLp.toLp 2 w),
    inner_self_eq_norm_sq_to_K]
  change ((‖WithLp.toLp 2 w‖ : ℂ) ^ 2).re = ‖WithLp.toLp 2 w‖ ^ 2
  rw [← Complex.ofReal_pow, Complex.ofReal_re]

/-
Original formalization, no upstream Lean proof text reused.
Manuscript: September 24, 2026, comparator:merge-moments, lines 520–549.
-/

/-- The exponential merge moment of the actual good regional and auxiliary
marginal is bounded by a polynomial times the squared norm of the same
excitation component. OpenAI, *A two-dimensional area law from a global
spectral gap*, `07-comparators.tex`, lines 520–549, equation
`comparator:merge-moments`. The only vector assumptions are normalization of
the one-copy ground vector and simultaneous permutation symmetry of the
original vector. The component need not be nonzero or normalized. -/
theorem replicaGoodRegionalAuxiliaryMarginal_exp_mergeDeficit_le
    {Q T C D : Type*} [Fintype Q] [DecidableEq Q] [Fintype T] [DecidableEq T]
    [Fintype C] [DecidableEq C] [Fintype D] [DecidableEq D]
    (Ω : Q × T → ℂ) (hΩ : ‖WithLp.toLp 2 Ω‖ = 1) (k : ℕ) (B : Finset (Fin k))
    (u : (Fin k → Q × T) × ((Fin k → C) × (Fin k → D)) → ℂ)
    (hu : ∀ σ : Equiv.Perm (Fin k),
      (permOp (TensorPower.copyPerm (Q × T) k) σ ⊗ₖ
        (permOp (TensorPower.copyPerm C k) σ ⊗ₖ
          permOp (TensorPower.copyPerm D k) σ)) *ᵥ u = u)
    {b : ℝ} (hb : b ≤ 1) :
    let m := Bᶜ.card
    let ρ := replicaGoodRegionalAuxiliaryMarginal Ω k B u
    let w := (replicaExcitationProjection Ω k B ⊗ₖ
      (1 : Matrix ((Fin k → C) × (Fin k → D)) ((Fin k → C) × (Fin k → D)) ℂ)) *ᵥ u
    (ρ * NormedSpace.exp ((b : ℂ) •
      (labelEntropy (TensorPower.pairCopyLeft Q C m) +
        labelEntropy (TensorPower.pairCopyRight Q C m) -
          labelEntropy (TensorPower.pairCopyBoth Q C m)))).trace.re ≤
      ((m + 1) ^ ((Fintype.card Q * Fintype.card C) ^ 2) : ℕ) * ‖WithLp.toLp 2 w‖ ^ 2 := by
  classical
  dsimp only
  let ρ := replicaGoodRegionalAuxiliaryMarginal Ω k B u
  have hρ : ρ.PosSemidef := by
    dsimp only [ρ, replicaGoodRegionalAuxiliaryMarginal]
    exact (posSemidef_vecMulVec_self_star (R := ℂ) _).partialTraceRight
  have hρQ (σ : Equiv.Perm (Fin Bᶜ.card)) :
      Commute (permOp (TensorPower.pairCopyLeft Q C Bᶜ.card) σ) ρ := by
    dsimp only [ρ]
    rw [replicaGoodRegionalAuxiliaryMarginal_eq Ω hΩ]
    exact TensorPower.commute_pair_product_left _ σ
      (commute_finKronecker_const_permOp _ _ σ).symm
  have hρC (σ : Equiv.Perm (Fin Bᶜ.card)) :
      Commute (permOp (TensorPower.pairCopyRight Q C Bᶜ.card) σ) ρ := by
    dsimp only [ρ]
    rw [replicaGoodRegionalAuxiliaryMarginal_eq Ω hΩ]
    exact TensorPower.commute_pair_product_right _ σ
      (commute_replicaGoodAuxiliaryMarginal_copyPerm Ω k B u hu σ)
  rw [re_trace_mul_exp_mergeDeficit_eq_sum (TensorPower.commute_pairCopy Q C Bᶜ.card)
    (TensorPower.pairCopyBoth_eq_mul Q C Bᶜ.card)]
  have h := TensorPower.pair_merge_moment_le_mul_trace Q C Bᶜ.card hρ hρQ hρC hb
  have hmass : ρ.trace =
      let w := (replicaExcitationProjection Ω k B ⊗ₖ
        (1 : Matrix ((Fin k → C) × (Fin k → D)) ((Fin k → C) × (Fin k → D)) ℂ)) *ᵥ u
      (vecMulVec w (star w)).trace := by
    dsimp only [ρ]
    rw [replicaGoodRegionalAuxiliaryMarginal_eq Ω hΩ, trace_kronecker,
      trace_finKronecker_const, trace_groundRegional Ω hΩ, one_pow, one_mul,
      trace_actualGoodAuxiliary]
  rw [hmass, trace_vecMulVec_re_norm_sq] at h
  exact h
end Matrix
