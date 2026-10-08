/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.ReplicaComponentMergeMoment
import QICLean.Analysis.ReplicaGoodPairMarginal
import QICLean.Representation.PairMergeDeficit
import QICLean.Analysis.WeightedTraceExponential
/-!
# Two merge moments of an actual excitation component

For a one-copy ground vector on three physical regions, retain the two exterior
physical regions and their auxiliary registers on the good copies. Trace every
middle physical coordinate and all bad-copy coordinates. The resulting positive
matrix has the two actual regional auxiliary marginals. Their doubled merge
moments bound the exponential of the sum of the two lifted merge deficits.

The second moment is derived by exchanging the exterior physical regions and
auxiliary registers, while preserving the middle physical region. Normalization,
simultaneous copy symmetry and the component norm are preserved by this literal
coordinate permutation; none is supplied independently for the exchanged state.

This is an auxiliary arithmetic-mean consequence for the rough estimate in
OpenAI, *A two-dimensional area law from a global spectral gap* (September 24,
2026), `07-comparators.tex`, lines 23, 103–110 and 524–555, equations
`comparator:merge-moments` and `comparator:component-inverse`, at commit
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`. It does not assert the printed
Cauchy–Schwarz geometric-mean bound or the full inverse-filter estimate.
The exponent may be any real number whose double is at most one. Zero
components, zero copies and an empty good set are included.
-/

open scoped Kronecker BigOperators ComplexOrder Matrix.Norms.Operator
open Matrix PermutationRepresentation
namespace Matrix
variable {A C R : Type*} [Fintype A] [DecidableEq A]
  [Fintype C] [DecidableEq C] [Fintype R] [DecidableEq R]
omit [Fintype A] [Fintype C] in
/-- The matrix of a product coordinate permutation is the Kronecker product.
This elementary identity is used for the simultaneous copy symmetries in
OpenAI area-law manuscript, `07-comparators.tex`, lines 524–549. -/
private theorem perm_kronecker (e : Equiv.Perm A) (f : Equiv.Perm C) :
    e.permMatrix ℂ ⊗ₖ f.permMatrix ℂ =
      (show Equiv.Perm (A × C) from e.prodCongr f).permMatrix ℂ := by
  ext x y
  simp [Matrix.kroneckerMap_apply, Equiv.Perm.permMatrix, PEquiv.toMatrix_apply]
  simp only [Prod.ext_iff, Prod.map_fst, Prod.map_snd]
  split_ifs <;> simp_all
omit [DecidableEq A] in
/-- A finite coordinate equivalence preserves the Euclidean vector norm.
This is used for the exterior-region exchange in the OpenAI area-law manuscript,
`07-comparators.tex`, lines 524–549. -/
private theorem norm_reindex {A' : Type*} [Fintype A']
    (e : A ≃ A') (v : A → ℂ) :
    ‖WithLp.toLp 2 (v ∘ e.symm)‖ = ‖WithLp.toLp 2 v‖ := by
  exact (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e).norm_map (WithLp.toLp 2 v)

/-- The simultaneous copy action precomposes each literal copy string.
OpenAI area-law manuscript, `07-comparators.tex`, lines 524–549. -/
private theorem tripleCopy_mulVec (k : ℕ) (σ : Equiv.Perm (Fin k))
    (u : (Fin k → A) × ((Fin k → C) × (Fin k → R)) → ℂ) :
    (permOp (TensorPower.copyPerm A k) σ ⊗ₖ
      (permOp (TensorPower.copyPerm C k) σ ⊗ₖ
        permOp (TensorPower.copyPerm R k) σ)) *ᵥ u =
      fun x => u (fun i => x.1 (σ i),
        (fun i => x.2.1 (σ i), fun i => x.2.2 (σ i))) := by
  rw [permOp_apply, permOp_apply, permOp_apply, perm_kronecker, perm_kronecker,
    Matrix.permMatrix_mulVec]
  rfl
/-- A coordinate equivalence transports every actual ground and defect factor.
OpenAI area-law manuscript, `07-comparators.tex`, lines 441–456 and 524–549. -/
private theorem excitation_reindex {A' : Type*} [Fintype A'] [DecidableEq A']
    (e : A ≃ A') (Ω : A → ℂ) (k : ℕ) (B : Finset (Fin k)) :
    replicaExcitationProjection (fun x => Ω (e.symm x)) k B =
      (replicaExcitationProjection Ω k B).submatrix
        (fun x i => e.symm (x i)) (fun x i => e.symm (x i)) := by
  ext x y
  simp only [replicaExcitationProjection, finKronecker_apply, submatrix_apply]
  apply Finset.prod_congr rfl
  intro i _
  by_cases hi : i ∈ B <;>
    simp [hi, Matrix.sub_apply, Matrix.one_apply, vecMulVec_apply, e.symm.injective.eq_iff]

/-- Transporting the actual excitation component preserves its norm.
OpenAI area-law manuscript, `07-comparators.tex`, lines 441–456 and 524–549. -/
private theorem norm_excitation_reindex {A' K K' : Type*}
    [Fintype A'] [DecidableEq A'] [Fintype K] [DecidableEq K]
    [Fintype K'] [DecidableEq K'] (e : A ≃ A') (g : K ≃ K')
    (Ω : A → ℂ) (k : ℕ) (B : Finset (Fin k)) (u : (Fin k → A) × K → ℂ) :
    let E := (Equiv.arrowCongr (Equiv.refl (Fin k)) e).prodCongr g
    ‖WithLp.toLp 2 ((replicaExcitationProjection (fun x => Ω (e.symm x)) k B ⊗ₖ
      (1 : Matrix K' K' ℂ)) *ᵥ (u ∘ E.symm))‖ =
      ‖WithLp.toLp 2 ((replicaExcitationProjection Ω k B ⊗ₖ
        (1 : Matrix K K ℂ)) *ᵥ u)‖ := by
  classical
  dsimp only
  have hmatrix : (replicaExcitationProjection (fun x => Ω (e.symm x)) k B ⊗ₖ
      (1 : Matrix K' K' ℂ)) =
      (replicaExcitationProjection Ω k B ⊗ₖ (1 : Matrix K K ℂ)).submatrix
        ((Equiv.arrowCongr (Equiv.refl (Fin k)) e).prodCongr g).symm
        ((Equiv.arrowCongr (Equiv.refl (Fin k)) e).prodCongr g).symm := by
    ext x y
    simp [excitation_reindex, kroneckerMap_apply, Matrix.one_apply,
      g.symm.injective.eq_iff, Equiv.arrowCongr, Function.comp_def]
  rw [hmatrix, submatrix_mulVec_equiv]
  simp only [Equiv.symm_symm, Function.comp_assoc, Equiv.symm_comp_self, Function.comp_id]
  exact norm_reindex _ _

/-- Exchange the exterior physical coordinates while preserving the middle one.
OpenAI area-law manuscript, `07-comparators.tex`, lines 23, 103–110 and 524–549. -/
private def physicalExchange (Q Y V : Type*) : Q × (Y × V) ≃ V × (Y × Q) where
  toFun x := (x.2.2, (x.2.1, x.1))
  invFun x := (x.2.2, (x.2.1, x.1))
  left_inv _ := rfl
  right_inv _ := rfl

/-- The literal exterior-region exchange preserves the one-copy ground norm.
OpenAI area-law manuscript, `07-comparators.tex`, lines 524–549. -/
private theorem norm_physicalExchange {Q Y V : Type*}
    [Fintype Q] [Fintype Y] [Fintype V] (Ω : Q × (Y × V) → ℂ) :
    ‖WithLp.toLp 2 (fun x : V × (Y × Q) => Ω (x.2.2, (x.2.1, x.1)))‖ =
      ‖WithLp.toLp 2 Ω‖ := by
  exact norm_reindex (physicalExchange Q Y V) Ω

/-- Original simultaneous copy fixedness implies fixedness after exchanging both
exterior physical and auxiliary coordinates. The middle physical coordinates
are retained. OpenAI area-law manuscript, `07-comparators.tex`, lines 524–549. -/
private theorem swapped_fixed {Q Y V : Type*}
    [Fintype Q] [DecidableEq Q] [Fintype Y] [DecidableEq Y]
    [Fintype V] [DecidableEq V] (k : ℕ)
    (u : (Fin k → Q × (Y × V)) × ((Fin k → C) × (Fin k → R)) → ℂ)
    (hu : ∀ σ : Equiv.Perm (Fin k),
      (permOp (TensorPower.copyPerm (Q × (Y × V)) k) σ ⊗ₖ
        (permOp (TensorPower.copyPerm C k) σ ⊗ₖ
          permOp (TensorPower.copyPerm R k) σ)) *ᵥ u = u) :
    ∀ σ : Equiv.Perm (Fin k),
      (permOp (TensorPower.copyPerm (V × (Y × Q)) k) σ ⊗ₖ
        (permOp (TensorPower.copyPerm R k) σ ⊗ₖ
          permOp (TensorPower.copyPerm C k) σ)) *ᵥ
        (fun x => u ((fun i => ((x.1 i).2.2, ((x.1 i).2.1, (x.1 i).1))),
          (x.2.2, x.2.1))) =
        fun x => u ((fun i => ((x.1 i).2.2, ((x.1 i).2.1, (x.1 i).1))),
          (x.2.2, x.2.1)) := by
  intro σ
  simp only [tripleCopy_mulVec] at hu ⊢
  exact funext fun x => congrFun (hu σ)
    ((fun i => ((x.1 i).2.2, ((x.1 i).2.1, (x.1 i).1))), (x.2.2, x.2.1))
end Matrix

namespace Matrix

/-
Provenance-ID: 8750-qic-two-deficit-moment-01
Original formalization, no upstream Lean proof text reused.
Declaration: Matrix.replicaGoodPairMarginal_exp_sum_mergeDeficit_le
Manuscript: September 24, 2026, comparator:merge-moments and comparator:component-inverse,
lines 23, 103–110 and 524–555.
-/

/-- The exponential of the two actual merge deficits on the common good-copy
marginal is bounded by the average of their polynomial bounds, multiplied by
the squared norm of the same excitation component. The physical middle region
is independent of the two exterior regions and all its copies are traced out.
The exchanged one-copy norm, simultaneous symmetry and component norm are
derived from the original vector by the literal exterior-region and auxiliary
exchange. No separate moment or marginal-invariance premise is imposed.
OpenAI, *A two-dimensional area law from a global spectral gap*, September 24,
2026, `07-comparators.tex`, lines 23, 103–110 and 524–555, equations
`comparator:merge-moments` and `comparator:component-inverse`. This is an auxiliary
arithmetic-mean bound; the full inverse-filter estimate is a subsequent result. -/
theorem replicaGoodPairMarginal_exp_sum_mergeDeficit_le {Q Y V C R : Type*}
    [Fintype Q] [DecidableEq Q] [Fintype Y] [DecidableEq Y]
    [Fintype V] [DecidableEq V] [Fintype C] [DecidableEq C] [Fintype R] [DecidableEq R]
    (Ω : Q × (Y × V) → ℂ) (hΩ : ‖WithLp.toLp 2 Ω‖ = 1) (k : ℕ) (B : Finset (Fin k))
    (u : (Fin k → Q × (Y × V)) × ((Fin k → C) × (Fin k → R)) → ℂ)
    (hu : ∀ σ : Equiv.Perm (Fin k),
      (permOp (TensorPower.copyPerm (Q × (Y × V)) k) σ ⊗ₖ
        (permOp (TensorPower.copyPerm C k) σ ⊗ₖ
          permOp (TensorPower.copyPerm R k) σ)) *ᵥ u = u)
    (a : ℝ) (ha : 2 * a ≤ 1) :
    let m := Bᶜ.card
    let ρ := replicaGoodPairMarginal Ω k B u
    let w := (replicaExcitationProjection Ω k B ⊗ₖ
      (1 : Matrix ((Fin k → C) × (Fin k → R)) ((Fin k → C) × (Fin k → R)) ℂ)) *ᵥ u
    let DC := TensorPower.pairMergeDeficit Q C m ⊗ₖ
      (1 : Matrix ((Fin m → V) × (Fin m → R)) ((Fin m → V) × (Fin m → R)) ℂ)
    let DR := (1 : Matrix ((Fin m → Q) × (Fin m → C)) ((Fin m → Q) × (Fin m → C)) ℂ) ⊗ₖ
      TensorPower.pairMergeDeficit V R m
    (ρ * NormedSpace.exp ((a : ℂ) • (DC + DR))).trace.re ≤
      ((((m + 1) ^ ((Fintype.card Q * Fintype.card C) ^ 2) : ℕ) : ℝ) +
        (((m + 1) ^ ((Fintype.card V * Fintype.card R) ^ 2) : ℕ) : ℝ)) / 2 *
          ‖WithLp.toLp 2 w‖ ^ 2 := by
  classical
  intro m ρ w DC DR
  have hρ : ρ.PosSemidef :=
    (posSemidef_vecMulVec_self_star (R := ℂ) _).partialTraceRight
  have hDC : DC.IsHermitian := by
    simp only [IsHermitian, DC, conjTranspose_kronecker,
      (TensorPower.isHermitian_pairMergeDeficit Q C m).eq, conjTranspose_one]
  have hDR : DR.IsHermitian := by
    simp only [IsHermitian, DR, conjTranspose_kronecker,
      (TensorPower.isHermitian_pairMergeDeficit V R m).eq, conjTranspose_one]
  have hAM := hρ.re_trace_mul_exp_add_le_half_sum hDC hDR
    (TensorPower.commute_pairMergeDeficit_lifts Q C m V R) a
  have hQC : (ρ * NormedSpace.exp (((2 * a : ℝ) : ℂ) • DC)).trace.re ≤
      (((m + 1) ^ ((Fintype.card Q * Fintype.card C) ^ 2) : ℕ) : ℝ) *
        ‖WithLp.toLp 2 w‖ ^ 2 := by
    rw [TensorPower.trace_exp_pairMergeDeficit_left,
      partialTraceRight_replicaGoodPairMarginal]
    exact replicaGoodRegionalAuxiliaryMarginal_exp_mergeDeficit_le Ω hΩ k B u hu ha
  have hVR : (ρ * NormedSpace.exp (((2 * a : ℝ) : ℂ) • DR)).trace.re ≤
      (((m + 1) ^ ((Fintype.card V * Fintype.card R) ^ 2) : ℕ) : ℝ) *
        ‖WithLp.toLp 2 w‖ ^ 2 := by
    rw [TensorPower.trace_exp_pairMergeDeficit_right,
      partialTraceLeft_replicaGoodPairMarginal]
    have hlocal := replicaGoodRegionalAuxiliaryMarginal_exp_mergeDeficit_le
      (fun x : V × (Y × Q) => Ω (x.2.2, (x.2.1, x.1)))
      ((norm_physicalExchange Ω).trans hΩ) k B
      (fun x => u ((fun i => ((x.1 i).2.2, ((x.1 i).2.1, (x.1 i).1))),
        (x.2.2, x.2.1))) (swapped_fixed k u hu) ha
    have hnorm :
        ‖WithLp.toLp 2 ((replicaExcitationProjection
          (fun x : V × (Y × Q) => Ω (x.2.2, (x.2.1, x.1))) k B ⊗ₖ
          (1 : Matrix ((Fin k → R) × (Fin k → C)) ((Fin k → R) × (Fin k → C)) ℂ)) *ᵥ
          (fun x => u ((fun i => ((x.1 i).2.2, ((x.1 i).2.1, (x.1 i).1))),
            (x.2.2, x.2.1))))‖ = ‖WithLp.toLp 2 w‖ := by
      simpa [physicalExchange, Equiv.arrowCongr, Function.comp_def, Prod.map, Prod.swap] using
        norm_excitation_reindex (physicalExchange Q Y V)
          (Equiv.prodComm (Fin k → C) (Fin k → R)) Ω k B u
    simpa only [hnorm, TensorPower.pairMergeDeficit, m] using hlocal
  linarith only [hAM, hQC, hVR]
end Matrix
