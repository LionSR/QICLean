/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.LiebConcavity
import QICLean.Channel.ConvexFunctionalMonotonicity

/-!
# Data processing for the ordinary Petz overlap

Wolf, Equation (8.35), `Notes/WolfNoteTexSource/ch08_distance_measures.tex`,
lines 480–486, for exponents in `[0, 1]`. The functional is the real trace
of the ordinary product of powers. Negative overlap on positive-semidefinite
pairs satisfies the hypotheses of `Matrix.ConvexMatrixFunctional.map_le`.

Real powers use the continuous functional calculus, with `A ^ (0 : ℝ) = 1`
for every positive-semidefinite `A`, including singular matrices. Thus the
endpoint overlaps of density matrices are one. No inverse powers or support
conditions occur in this interval; the reversed inequality outside it is separate.
-/

open scoped Matrix Kronecker ComplexOrder MatrixOrder Matrix.Norms.L2Operator
open Matrix

namespace Matrix

noncomputable section

variable {m n : Type} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]

/-- The ordinary Petz overlap in Wolf, Equation (8.35). -/
def petzOverlap (s : ℝ) (ρ σ : Matrix m m ℂ) : ℝ :=
  (ρ ^ s * σ ^ (1 - s)).trace.re

/-- At exponent zero the ordinary overlap is the trace of the second argument,
including when the first argument is singular. -/
theorem petzOverlap_zero {ρ σ : Matrix m m ℂ}
    (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef) : petzOverlap 0 ρ σ = σ.trace.re := by
  simp [petzOverlap, CFC.rpow_zero ρ hρ.nonneg, CFC.rpow_one σ hσ.nonneg]

/-- At exponent one the ordinary overlap is the trace of the first argument. -/
theorem petzOverlap_one {ρ σ : Matrix m m ℂ}
    (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef) : petzOverlap 1 ρ σ = ρ.trace.re := by
  simp [petzOverlap, CFC.rpow_one ρ hρ.nonneg, CFC.rpow_zero σ hσ.nonneg]

/-- Simultaneous unitary conjugation preserves the ordinary overlap. -/
theorem petzOverlap_conj_unitary (s : ℝ) {ρ σ : Matrix m m ℂ}
    (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef) (U : unitaryGroup m ℂ) :
    petzOverlap s ((U : Matrix m m ℂ) * ρ * Uᴴ)
        ((U : Matrix m m ℂ) * σ * Uᴴ) = petzOverlap s ρ σ := by
  simp only [petzOverlap, ← star_eq_conjTranspose,
    rpow_conj_unitary hρ s U, rpow_conj_unitary hσ (1 - s) U]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (star (U : Matrix m m ℂ)) (U : Matrix m m ℂ),
    Unitary.star_mul_self_of_mem U.property, Matrix.one_mul,
    ← Matrix.mul_assoc, ← Matrix.mul_assoc, trace_mul_cycle,
    ← Matrix.mul_assoc, Unitary.star_mul_self_of_mem U.property, Matrix.one_mul]

/-- Changing finite coordinates preserves the ordinary overlap. -/
theorem petzOverlap_reindex (s : ℝ) {ρ σ : Matrix m m ℂ}
    (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef) (e : m ≃ n) :
    petzOverlap s (reindex e e ρ) (reindex e e σ) = petzOverlap s ρ σ := by
  have hp (A : Matrix m m ℂ) (hA : A.PosSemidef) (t : ℝ) :
      (reindex e e A) ^ t = reindex e e (A ^ t) := by
    change (A.submatrix e.symm e.symm) ^ t = (A ^ t).submatrix e.symm e.symm
    rw [CFC.rpow_eq_cfc_real (hA.submatrix e.symm).nonneg,
      CFC.rpow_eq_cfc_real hA.nonneg]
    exact cfc_submatrix_equiv hA.isHermitian _ e
  unfold petzOverlap
  rw [hp ρ hρ, hp σ hσ]
  simp only [reindex_apply, submatrix_mul_equiv, trace_submatrix_equiv]

private theorem rpow_mul_one_sub {τ : Matrix n n ℂ} (hτ : τ.PosSemidef)
    {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) 1) : τ ^ s * τ ^ (1 - s) = τ := by
  rw [CFC.rpow_eq_cfc_real hτ.nonneg, CFC.rpow_eq_cfc_real hτ.nonneg,
    ← cfc_mul _ _ τ (τ.finite_real_spectrum.continuousOn _)
      (τ.finite_real_spectrum.continuousOn _)]
  calc
    cfc (fun x : ℝ => x ^ s * x ^ (1 - s)) τ = cfc (fun x : ℝ => x) τ := by
      apply cfc_congr
      intro x hx
      change x ^ s * x ^ (1 - s) = x
      rw [← Real.rpow_add_of_nonneg (spectrum_nonneg_of_nonneg hτ.nonneg hx)
        hs.1 (sub_nonneg.mpr hs.2), add_sub_cancel, Real.rpow_one]
    _ = τ := cfc_id ℝ τ hτ.isHermitian

/-- A common density ancilla preserves the overlap, even when singular.
The nonnegative exponents sum to one, so their powers multiply to the ancilla. -/
theorem petzOverlap_tensor_density {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) 1)
    {ρ σ : Matrix m m ℂ} (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef)
    {τ : Matrix n n ℂ} (hτ : τ.PosSemidef) (htr : τ.trace = 1) :
    petzOverlap s (ρ ⊗ₖ τ) (σ ⊗ₖ τ) = petzOverlap s ρ σ := by
  unfold petzOverlap
  rw [hρ.rpow_kronecker hτ, hσ.rpow_kronecker hτ,
    ← mul_kronecker_mul, rpow_mul_one_sub hτ hs, trace_kronecker, htr, mul_one]

private def psdPairs : MatrixTupleDomains Bool := fun _ _ _ => {A | ∀ i, (A i).PosSemidef}

private def negOverlap (s : ℝ) : MatrixTupleFunctional Bool :=
  fun _ _ _ A => -petzOverlap s (A false) (A true)

private theorem petzOverlap_concave {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) 1)
    {A₁ A₂ B₁ B₂ : Matrix m m ℂ}
    (hA₁ : A₁.PosSemidef) (hA₂ : A₂.PosSemidef)
    (hB₁ : B₁.PosSemidef) (hB₂ : B₂.PosSemidef)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    t * petzOverlap s A₁ B₁ + (1 - t) * petzOverlap s A₂ B₂ ≤
      petzOverlap s (t • A₁ + (1 - t) • A₂) (t • B₁ + (1 - t) • B₂) := by
  let e := Fintype.equivFin m
  have h := lieb_concavity_psd hs
    (hA₁.submatrix e.symm) (hA₂.submatrix e.symm)
    (hB₁.submatrix e.symm) (hB₂.submatrix e.symm) (K := 1) ht
  simp only [conjTranspose_one, Matrix.one_mul, Matrix.mul_one] at h
  change t * petzOverlap s (reindex e e A₁) (reindex e e B₁) +
    (1 - t) * petzOverlap s (reindex e e A₂) (reindex e e B₂) ≤
    petzOverlap s (reindex e e (t • A₁ + (1 - t) • A₂))
      (reindex e e (t • B₁ + (1 - t) • B₂)) at h
  rw [petzOverlap_reindex s hA₁ hB₁, petzOverlap_reindex s hA₂ hB₂,
    petzOverlap_reindex s ((hA₁.smul ht.1).add (hA₂.smul (sub_nonneg.mpr ht.2)))
      ((hB₁.smul ht.1).add (hB₂.smul (sub_nonneg.mpr ht.2)))] at h
  exact h

private theorem negOverlap_convex {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) 1) :
    ConvexMatrixFunctional psdPairs (negOverlap s) where
  convex α := by
    refine ⟨?_, ?_⟩
    · intro A hA B hB a b ha hb _ i
      exact ((hA i).smul ha).add ((hB i).smul hb)
    · intro A hA B hB a b ha hb hab
      have h := petzOverlap_concave hs (hA false) (hB false) (hA true) (hB true)
        (t := a) ⟨ha, by linarith⟩
      have hb' : b = 1 - a := by linarith
      change -petzOverlap s (a • A false + b • B false) (a • A true + b • B true) ≤
        a * -petzOverlap s (A false) (A true) + b * -petzOverlap s (B false) (B true)
      rw [hb']
      linarith
  unitary_mem := by
    intro α _ _ A hA U i
    change ((U : Matrix α α ℂ) * A i * Uᴴ).PosSemidef
    exact (hA i).mul_mul_conjTranspose_same (U : Matrix α α ℂ)
  unitary_eq := by
    intro α _ _ A hA U
    exact congrArg Neg.neg (petzOverlap_conj_unitary s (hA false) (hA true) U)
  tensor_mem := by
    intro α β _ _ _ _ A hA τ hτ _ i
    exact (hA i).kronecker hτ
  tensor_eq := by
    intro α β _ _ _ _ A hA τ hτ htr
    exact congrArg Neg.neg (petzOverlap_tensor_density hs (hA false) (hA true) hτ htr)
  reindex_mem := by
    intro α β _ _ _ _ A hA e i
    exact (hA i).submatrix e.symm
  reindex_eq := by
    intro α β _ _ _ _ A hA e
    exact congrArg Neg.neg (petzOverlap_reindex s (hA false) (hA true) e)

/-- Ordinary Petz overlap increases under a rectangular CPTP map on arbitrary
PSD pairs in positive input dimension; normalization is not needed. -/
theorem petzOverlap_le_map [Nonempty m] {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) 1)
    {T : Matrix m m ℂ →ₗ[ℂ] Matrix n n ℂ} (hT : IsKrausCPTP T)
    {ρ σ : Matrix m m ℂ} (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef) :
    petzOverlap s ρ σ ≤ petzOverlap s (T ρ) (T σ) := by
  let A : MatrixTuple Bool m := fun i => if i then σ else ρ
  have hA : A ∈ psdPairs m := by intro i; cases i <;> assumption
  have hTA : (fun i => T (A i)) ∈ psdPairs n := fun i => hT.map_posSemidef (hA i)
  have h := (negOverlap_convex hs).map_le hT hA hTA
  simpa only [negOverlap, A, Bool.false_eq_true, ↓reduceIte, neg_le_neg_iff] using h

/-- Wolf, Equation (8.35), for density matrices and rectangular CPTP maps.
Exponent zero is the identity power, including for singular density matrices.
The reverse inequality for negative exponents is outside this theorem. -/
theorem petzOverlap_data_processing {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) 1)
    {T : Matrix m m ℂ →ₗ[ℂ] Matrix n n ℂ} (hT : IsKrausCPTP T)
    {ρ σ : Matrix m m ℂ} (hρ : ρ.PosSemidef) (hρtr : ρ.trace = 1)
    (hσ : σ.PosSemidef) (_hσtr : σ.trace = 1) :
    petzOverlap s ρ σ ≤ petzOverlap s (T ρ) (T σ) := by
  let := nonempty_of_trace_eq_one ρ hρtr
  exact petzOverlap_le_map hs hT hρ hσ

/-- Discarding a nonempty right tensor factor increases the ordinary overlap.
The retained system may have dimension zero. -/
theorem petzOverlap_le_partialTraceRight {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) 1)
    [Nonempty n] {ρ σ : Matrix (m × n) (m × n) ℂ}
    (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef) :
    petzOverlap s ρ σ ≤ petzOverlap s (partialTraceRight ρ) (partialTraceRight σ) := by
  let A : MatrixTuple Bool (m × n) := fun i => if i then σ else ρ
  have hA : A ∈ psdPairs (m × n) := by intro i; cases i <;> assumption
  have hTA : (fun i => partialTraceRight (A i)) ∈ psdPairs m :=
    fun i => partialTraceRightLM_isKrausCPTP.map_posSemidef (hA i)
  have h := (negOverlap_convex hs).partialTraceRight_le hA hTA
  simpa only [negOverlap, A, Bool.false_eq_true, ↓reduceIte, neg_le_neg_iff] using h

end

end Matrix
