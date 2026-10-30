/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Channel.ChoiJamiolkowski
import QICLean.Channel.WolfTheorem67
import QICLean.Channel.WolfTheorem68

/-! Independent scope and boundary regressions for primitive positive maps. -/

open Matrix WolfTheorem67 Filter
open scoped Matrix ComplexOrder MatrixOrder Topology
noncomputable section

namespace WolfTheorem67ScopeTest

private abbrev Mat₂ := Matrix (Fin 2) (Fin 2) ℂ
private abbrev End₂ := Module.End ℂ Mat₂

-- Half transposition plus half the maximally mixed replacement channel.
private def mixedTranspose : End₂ :=
  (2 : ℂ)⁻¹ • transposeLinearMapComplex (Fin 2) +
    (4 : ℂ)⁻¹ • (Matrix.traceLinearMap (Fin 2) ℂ ℂ).smulRight (1 : Mat₂)

private theorem mixedTranspose_pos : IsPositiveMap mixedTranspose := by
  intro X hX
  have ht := hX.transpose.smul
    (show (0 : ℂ) ≤ (2 : ℂ)⁻¹ from (by norm_num : (0 : ℂ) < (2 : ℂ)⁻¹).le)
  have hd := (Matrix.PosSemidef.one : (1 : Mat₂).PosSemidef).smul
    (mul_nonneg (show (0 : ℂ) ≤ (4 : ℂ)⁻¹ from
      (by norm_num : (0 : ℂ) < (4 : ℂ)⁻¹).le) hX.trace_nonneg)
  simpa [mixedTranspose, transposeLinearMapComplex, smul_smul] using ht.add hd

private theorem mixedTranspose_tp : IsTracePreservingMap mixedTranspose := by
  intro X
  change Matrix.trace ((2 : ℂ)⁻¹ • Xᵀ + (4 : ℂ)⁻¹ • Matrix.trace X • (1 : Mat₂)) = Matrix.trace X
  simp only [Matrix.trace_add, Matrix.trace_smul, Matrix.trace_transpose,
    Matrix.trace_one, Fintype.card_fin, smul_eq_mul]
  ring

private theorem mixedTranspose_strict : HasStrictlyPositivePower mixedTranspose := by
  refine ⟨1, fun ρ hρ ↦ ?_⟩
  have ht := hρ.1.transpose.smul
    (show (0 : ℂ) ≤ (2 : ℂ)⁻¹ from (by norm_num : (0 : ℂ) < (2 : ℂ)⁻¹).le)
  have hd := (Matrix.PosDef.one : (1 : Mat₂).PosDef).smul
    (show (0 : ℂ) < (4 : ℂ)⁻¹ by norm_num)
  simpa [mixedTranspose, hρ.2, transposeLinearMapComplex, add_comm] using hd.add_posSemidef ht

example : ∃ σ ∈ densityMatrices 2, σ.PosDef ∧
    ∀ ρ ∈ densityMatrices 2, Tendsto (fun n : ℕ ↦ (mixedTranspose ^ n) ρ) atTop (𝓝 σ) :=
  ((wolf_theorem_6_7_tfae mixedTranspose mixedTranspose_pos mixedTranspose_tp).out 1 3).mp
    mixedTranspose_strict

example : ∃ n : ℕ, ∀ m : ℕ, n ≤ m → ∀ ρ ∈ densityMatrices 2, ((mixedTranspose ^ m) ρ).PosDef :=
  (strictlyPositivePower_iff_uniform_eventual
    mixedTranspose mixedTranspose_pos mixedTranspose_tp).mp mixedTranspose_strict

private theorem mixedTranspose_choi : ChoiJamiolkowski.choiMatrix mixedTranspose =
    (4 : ℂ)⁻¹ • Matrix.swapMatrix 2 +
      (8 : ℂ)⁻¹ • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) := by
  have hdep : ChoiJamiolkowski.choiMatrix
      ((Matrix.traceLinearMap (Fin 2) ℂ ℂ).smulRight (1 : Mat₂)) =
      (2 : ℂ)⁻¹ • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) := by
    ext ⟨i₁, i₂⟩ ⟨j₁, j₂⟩
    rw [ChoiJamiolkowski.choiMatrix_apply, ChoiJamiolkowski.omegaSlice_eq_single]
    simp only [LinearMap.smulRight_apply, Matrix.traceLinearMap_apply]
    rw [ChoiJamiolkowski.omegaCoeff_eq_inv (by norm_num : 0 < 2)]
    fin_cases i₁ <;> fin_cases i₂ <;> fin_cases j₁ <;> fin_cases j₂ <;>
      norm_num [Matrix.trace, Matrix.single_apply, Matrix.one_apply]
  rw [mixedTranspose, ChoiJamiolkowski.choiMatrix_add, ChoiJamiolkowski.choiMatrix_smul,
    ChoiJamiolkowski.choiMatrix_smul,
    ChoiJamiolkowski.choiMatrix_transposeLinearMapComplex_eq_swap (by norm_num : 0 < 2), hdep]
  norm_num [smul_smul]

-- The actual primitive positive map lies outside the CP hypothesis of Theorem 6.8.
example : ¬ IsCPMap mixedTranspose := by
  intro hcp
  have hp := (ChoiJamiolkowski.cp_iff_choi_posSemidef (T := mixedTranspose)).mp hcp
  have hn := (Matrix.posSemidef_iff_dotProduct_mulVec.mp hp).2 Matrix.finTwoAntisymmVec
  rw [mixedTranspose_choi] at hn
  norm_num [dotProduct, Matrix.mulVec, Fintype.sum_prod_type,
    Matrix.finTwoAntisymmVec, Matrix.swapMatrix_apply, Matrix.one_apply, Complex.le_def] at hn

-- Existing CP/Kraus primitivity remains available after importing the positive-map theorem.
example {r D : ℕ} [NeZero D]
    (K : Fin r → Matrix (Fin D) (Fin D) ℂ) (hTP : Kraus.IsTP K) :
    (IsIrreducibleMap (Kraus.mapLM K) ∧ IsPrimitive (Kraus.mapLM K)) ↔
      ∃ q, Kraus.HasFullWordSpanFrom K q :=
  (Kraus.wolf_theorem_6_8_tfae K hTP).out 1 3

-- Without D ≥ 1, positivity on the empty density set is vacuous, while a limit state cannot exist.
example :
    HasStrictlyPositivePower (1 : Module.End ℂ (Matrix (Fin 0) (Fin 0) ℂ)) ∧
      ¬ ConvergesToFaithfulDensity (1 : Module.End ℂ (Matrix (Fin 0) (Fin 0) ℂ)) := by
  constructor
  · refine ⟨0, fun ρ hρ ↦ ?_⟩
    have htr := hρ.2
    simp [Matrix.trace] at htr
  · rintro ⟨σ, hσ, _⟩
    have htr := hσ.2
    simp [Matrix.trace] at htr

end WolfTheorem67ScopeTest
