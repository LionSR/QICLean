/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Representation.ReplicaSpectralLaw
import QICLean.Representation.ReplicaMetric
import QICLean.Analysis.TraceCompression
import QICLean.Analysis.OperatorMean.MatrixPowers

/-!
# The integral representation of the replica metrics

This file proves the integral formula of Lemma 6.2 of the area-law paper (*A two-dimensional
area law from a global spectral gap*, `05-replicas.tex`, equation `replicas:W-integral`,
lines 314–316 and 380–392): for every subsystem `Q` there is a probability law of positive
definite subdensities `τ` on `Q`, with `Tr τ ≤ 1`, independent of `k`, such that

`W_{Q,k} = ∫ (τ^t)^{⊗k} dζ_Q(τ)`  for all `k ≥ 0`,

with the identity on the complement of `Q` implicit.

The full-system case is `TensorPower.integral_specSample_tensorPow`, on `ℂ^d` with
`d = dim V`. For a subsystem, embed `Q` into `ℂ^d` by an injection `j` of basis
configurations. Restricting a permutation operator of `(ℂ^d)^{⊗k}` to configurations in the
range of `j` gives the permutation operator of `Q^{⊗k}`, so the restriction of the label
function `∑ w_k(λ) π^λ` is the same label function on `Q`. On each sample, the restriction of
`(σ^t)^{⊗k}` is `B^{⊗k}` for the compression `B = E† σ^t E`; put `τ = B^{1/t}`. The trace bound
`Tr τ ≤ Tr σ = 1` is the trace inequality for powers of compressions (the paper argues it
with the min–max principle).

## Statement

The law is given by a random subdensity: a probability space `(Ω, P)` and a map
`τ : Ω → Matrix Q Q ℂ`, positive definite with trace at most one almost surely, such that the
entries of `(τ^t)^{⊗k}` are integrable and integrate to those of `W_{Q,k}`. The law `ζ_Q` of
`τ` is the measure of the paper; working on `Ω` avoids measurability questions for the matrix
power on the space of all matrices.

The proofs are written from the paper; no Lean source was adapted.

## Main declarations

* `TensorPower.groupAlgebraRep_comp_embedding` — restriction along an injection.
* `TensorPower.subSample` — the compressed samples `τ`.
* `TensorPower.exists_replicaMetric_integral` — **Lemma 6.2, integral representation**.
-/

open MeasureTheory Matrix Finset PermutationRepresentation Partition
open scoped MatrixOrder ComplexOrder Kronecker

namespace TensorPower

/-! ### Restriction along an injection of one-copy spaces -/

section Restriction

variable {Ω Ω' : Type*} [Fintype Ω] [DecidableEq Ω] [Fintype Ω'] [DecidableEq Ω']

theorem groupAlgebraRep_comp_embedding (j : Ω' ↪ Ω) {k : ℕ}
    (a : MonoidAlgebra ℂ (Equiv.Perm (Fin k))) (b b' : Fin k → Ω') :
    groupAlgebraRep (copyPerm Ω k) a (j ∘ b) (j ∘ b') =
      groupAlgebraRep (copyPerm Ω' k) a b b' := by
  rw [groupAlgebraRep_eq_sum, groupAlgebraRep_eq_sum, Matrix.sum_apply, Matrix.sum_apply]
  refine sum_congr rfl fun g _ => ?_
  simp only [Matrix.smul_apply, permOp_apply_apply]
  congr 2
  have : copyPerm Ω k g (j ∘ b') = j ∘ copyPerm Ω' k g b' := rfl
  rw [this]
  exact propext (j.injective.comp_left).eq_iff

theorem labelProj_comp_embedding (j : Ω' ↪ Ω) {k : ℕ} (l : IrrepLabel (Equiv.Perm (Fin k)))
    (b b' : Fin k → Ω') :
    labelProj (copyPerm Ω k) l (j ∘ b) (j ∘ b') = labelProj (copyPerm Ω' k) l b b' :=
  groupAlgebraRep_comp_embedding j _ b b'

omit [Fintype Ω] [Fintype Ω'] in
theorem tensorPow_submatrix (j : Ω' ↪ Ω) {k : ℕ} (M : Matrix Ω Ω ℂ) (b b' : Fin k → Ω') :
    tensorPow (k := k) (M.submatrix j j) b b' = tensorPow (k := k) M (j ∘ b) (j ∘ b') := by
  simp [tensorPow_apply]

end Restriction

/-! ### The compressed samples -/

variable {d : ℕ}

theorem posDef_unitary_conj_diagonal (U : unitaryGroup (Fin d) ℂ) {y : Fin d → ℝ}
    (hy : ∀ i, 0 < y i) :
    ((U : Matrix (Fin d) (Fin d) ℂ) * diagonal (fun i => (y i : ℂ)) *
      star (U : Matrix (Fin d) (Fin d) ℂ)).PosDef := by
  have hD : (diagonal (fun i => (y i : ℂ))).PosDef :=
    posDef_diagonal_iff.mpr fun i => Complex.zero_lt_real.mpr (hy i)
  have hinj : Function.Injective (star (U : Matrix (Fin d) (Fin d) ℂ)).mulVec := by
    refine Function.LeftInverse.injective (g := fun v => (U : Matrix (Fin d) (Fin d) ℂ) *ᵥ v)
      fun v => ?_
    simp only [mulVec_mulVec, (mem_unitaryGroup_iff.mp U.2), one_mulVec]
  have := hD.conjTranspose_mul_mul_same hinj
  rwa [star_eq_conjTranspose, conjTranspose_conjTranspose] at this

theorem specSample_rpow_posDef (hd : 0 < d) {t : ℝ} (ht : 0 ≤ t) {x : Fin d → ℝ}
    (hx : ∀ i, 0 < x i) (U : unitaryGroup (Fin d) ℂ) : (specSample x U ^ t).PosDef := by
  have hS : 0 < ∑ j, x j := sum_pos (fun j _ => hx j) ⟨⟨0, hd⟩, mem_univ _⟩
  rw [specSample_rpow hd ht hx]
  exact posDef_unitary_conj_diagonal U fun i => Real.rpow_pos_of_pos (div_pos (hx i) hS) t

/-- The compressed sample `τ = (E† σ^t E)^{1/t}` on the coordinates in the range of `j`. -/
noncomputable def subSample {Ω' : Type*} [Fintype Ω'] [DecidableEq Ω'] (j : Ω' ↪ Fin d)
    (t : ℝ) (ω : (Fin d → ℝ) × unitaryGroup (Fin d) ℂ) : Matrix Ω' Ω' ℂ :=
  ((specSample ω.1 ω.2 ^ t).submatrix j j) ^ (1 / t)

section Sub

variable {Ω' : Type*} [Fintype Ω'] [DecidableEq Ω'] (j : Ω' ↪ Fin d)

omit [Fintype Ω'] [DecidableEq Ω'] in
theorem compression_posDef (hd : 0 < d) {t : ℝ} (ht : 0 ≤ t) {x : Fin d → ℝ}
    (hx : ∀ i, 0 < x i) (U : unitaryGroup (Fin d) ℂ) :
    ((specSample x U ^ t).submatrix j j).PosDef :=
  (specSample_rpow_posDef hd ht hx U).submatrix j.injective

theorem subSample_posDef (hd : 0 < d) {t : ℝ} (ht : 0 ≤ t) {x : Fin d → ℝ}
    (hx : ∀ i, 0 < x i) (U : unitaryGroup (Fin d) ℂ) : (subSample j t (x, U)).PosDef :=
  (compression_posDef j hd ht hx U).rpow _

theorem subSample_rpow (hd : 0 < d) {t : ℝ} (ht : 0 < t) {x : Fin d → ℝ}
    (hx : ∀ i, 0 < x i) (U : unitaryGroup (Fin d) ℂ) :
    subSample j t (x, U) ^ t = (specSample x U ^ t).submatrix j j := by
  rw [subSample, (compression_posDef j hd ht.le hx U).rpow_rpow, one_div,
    inv_mul_cancel₀ ht.ne', (compression_posDef j hd ht.le hx U).rpow_one]

/-- The compressed samples are subdensities: `Tr τ ≤ Tr σ = 1`. -/
theorem re_trace_subSample_le (hd : 0 < d) {t : ℝ} (ht0 : 0 < t) (ht1 : t ≤ 1)
    {x : Fin d → ℝ} (hx : ∀ i, 0 < x i) (U : unitaryGroup (Fin d) ℂ) :
    (subSample j t (x, U)).trace.re ≤ 1 := by
  have hσ := specSample_posDef hd hx U
  have hp : 1 ≤ 1 / t := by rw [le_div_iff₀ ht0]; linarith
  have h := re_trace_rpow_submatrix_le (hσ.rpow t).posSemidef j hp
  rw [hσ.rpow_rpow, mul_one_div_cancel ht0.ne', hσ.rpow_one, trace_specSample hd hx U,
    Complex.one_re] at h
  exact h

end Sub

/-! ### Lemma 6.2: the integral representation -/

variable {F : Type*} [DecidableEq F] [Fintype F] (ι : F → Type*) [∀ f, Fintype (ι f)]
  [∀ f, DecidableEq (ι f)]

/-- An injection of the configurations of a subsystem into `Fin d`, `d = dim V`. -/
noncomputable def subEmbedding [∀ f, Nonempty (ι f)] (Q : Finset F) :
    SubConfig ι Q ↪ Fin (replicaDim ι) :=
  (Fintype.equivFin (SubConfig ι Q)).toEmbedding.trans (Fin.castLEEmb (card_subConfig_le ι Q))

/-- The label function of a subsystem on `Q^{⊗k}`. -/
theorem replicaMetric_reindex (t : ℝ) (k : ℕ) (Q : Finset F) :
    reindex (splitEquiv ι k Q) (splitEquiv ι k Q) (replicaMetric ι t k Q) =
      (∑ l, ((replicaLabelWeight ι t l : ℝ) : ℂ) • labelProj (copyPerm (SubConfig ι Q) k) l) ⊗ₖ
        (1 : Matrix (Fin k → ComplConfig ι Q) (Fin k → ComplConfig ι Q) ℂ) := by
  ext p p'
  simp only [replicaMetric, labelObservable, reindex_apply, submatrix_apply, Matrix.sum_apply,
    Matrix.smul_apply, kroneckerMap_apply, Finset.sum_mul, smul_eq_mul]
  refine sum_congr rfl fun l _ => ?_
  have h := congrFun (congrFun (labelProj_subsystemPerm_eq ι k Q l) p) p'
  simp only [reindex_apply, submatrix_apply, kroneckerMap_apply] at h
  rw [h, mul_assoc]

/-- **Lemma 6.2, integral representation** (`05-replicas.tex`, equation `replicas:W-integral`):
for `0 < t ≤ 1` and every subsystem `Q` there is a random positive definite subdensity `τ` on
`Q` with `Tr τ ≤ 1`, whose law does not depend on `k`, such that
`W_{Q,k} = ∫ (τ^t)^{⊗k}` (tensored with the identity on the complement) for every `k`. -/
theorem exists_replicaMetric_integral [∀ f, Nonempty (ι f)] {t : ℝ} (ht0 : 0 < t)
    (ht1 : t ≤ 1) (Q : Finset F) :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω), IsProbabilityMeasure P ∧
      ∃ τ : Ω → Matrix (SubConfig ι Q) (SubConfig ι Q) ℂ,
        (∀ᵐ ω ∂P, (τ ω).PosDef ∧ (τ ω).trace.re ≤ 1) ∧
        (∀ (k : ℕ) (a b : Fin k → SubConfig ι Q),
          Integrable (fun ω => tensorPow (k := k) (τ ω ^ t) a b) P) ∧
        ∀ k : ℕ, reindex (splitEquiv ι k Q) (splitEquiv ι k Q) (replicaMetric ι t k Q) =
          (Matrix.of fun a b => ∫ ω, tensorPow (k := k) (τ ω ^ t) a b ∂P) ⊗ₖ
            (1 : Matrix (Fin k → ComplConfig ι Q) (Fin k → ComplConfig ι Q) ℂ) := by
  set d := replicaDim ι
  have hd : 0 < d := replicaDim_pos ι
  set j := subEmbedding ι Q
  have hprob := isProbabilityMeasure_specMeasure hd ht0
  -- the entries of `(τ^t)^{⊗k}` are restricted entries of `(σ^t)^{⊗k}`
  have hentry : ∀ (k : ℕ) (a b : Fin k → SubConfig ι Q),
      (fun ω => tensorPow (k := k) (subSample j t ω ^ t) a b) =ᵐ[(specMeasure d t).prod
        (unitaryHaar (Fin d))] fun ω => tensorPow (k := k) (specSample ω.1 ω.2 ^ t) (j ∘ a)
          (j ∘ b) := fun k a b => by
    filter_upwards [ae_prod_pos] with ω hω
    rw [subSample_rpow j hd ht0 hω ω.2, tensorPow_submatrix]
  refine ⟨(Fin d → ℝ) × unitaryGroup (Fin d) ℂ, inferInstance,
    (specMeasure d t).prod (unitaryHaar (Fin d)), inferInstance, subSample j t, ?_, ?_, ?_⟩
  · filter_upwards [ae_prod_pos] with ω hω
    exact ⟨subSample_posDef j hd ht0.le hω ω.2, re_trace_subSample_le j hd ht0 ht1 hω ω.2⟩
  · exact fun k a b => ((integral_specSample_tensorPow hd ht0 (j ∘ a) (j ∘ b)).1).congr
      (hentry k a b).symm
  intro k
  rw [replicaMetric_reindex]
  congr 1
  ext a b
  rw [of_apply, integral_congr_ae (hentry k a b),
    (integral_specSample_tensorPow hd ht0 (j ∘ a) (j ∘ b)).2, Matrix.sum_apply]
  refine sum_congr rfl fun l _ => ?_
  rw [Matrix.smul_apply, smul_eq_mul, labelProj_comp_embedding]
  rfl

end TensorPower
