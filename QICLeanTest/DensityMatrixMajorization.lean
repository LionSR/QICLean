/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.DensityMatrixMajorization
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! Actual-name and density-state boundary regressions for Wolf Theorem 8.7. -/

open Matrix Finset TNLean
open scoped ComplexOrder

-- Actual decreasing eigenvalues, all prefixes, and equal total sum.
example {d : ℕ} {ρ σ : Matrix (Fin d) (Fin d) ℂ}
    (hρ : ρ.IsHermitian) (hσ : σ.IsHermitian) :
    hρ.Majorizes hσ ↔
      (∀ k ≤ d, vectorPrefix (decreasingSort hσ.eigenvalues) k ≤
        vectorPrefix (decreasingSort hρ.eigenvalues) k) ∧
      ∑ i, hσ.eigenvalues i = ∑ i, hρ.eigenvalues i := Iff.rfl

-- Density hypotheses instantiate both equivalences with the actual functional calculus.
example {d : ℕ} {ρ σ : Matrix (Fin d) (Fin d) ℂ}
    (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef) (htρ : ρ.trace = 1) (htσ : σ.trace = 1) :
    0 < d ∧
      (hρ.isHermitian.Majorizes hσ.isHermitian ↔
        ∀ f : ℝ → ℝ, ConvexOn ℝ Set.univ f → (cfc f σ).trace.re ≤ (cfc f ρ).trace.re) ∧
      ((∀ f : ℝ → ℝ, ConvexOn ℝ Set.univ f →
        (cfc f σ).trace.re ≤ (cfc f ρ).trace.re) ↔ IsRandomUnitaryImage ρ σ) := by
  have hdρ := Matrix.dimension_pos_of_trace_one htρ
  have hdσ := Matrix.dimension_pos_of_trace_one htσ
  exact ⟨by omega, hρ.isHermitian.majorizes_iff_trace_convex hσ.isHermitian,
    (hρ.isHermitian.majorizes_iff_trace_convex hσ.isHermitian).symm.trans
      (hρ.isHermitian.majorizes_iff_randomUnitaryImage hσ.isHermitian)⟩

-- Unitarity and probability normalization are consequences of the actual witnesses.
example {d : ℕ} {ρ σ : Matrix (Fin d) (Fin d) ℂ} (h : IsRandomUnitaryImage ρ σ) :
    ∃ k : ℕ, ∃ p : Fin k → ℝ, ∃ U : Fin k → Matrix (Fin d) (Fin d) ℂ,
      (∀ i, 0 ≤ p i) ∧ ∑ i, p i = 1 ∧
      (∀ i, U i * (U i)ᴴ = 1 ∧ (U i)ᴴ * U i = 1) ∧
      σ = ∑ i, (p i : ℂ) • (U i * ρ * (U i)ᴴ) := by
  obtain ⟨k, p, U, hp, hs, heq⟩ := h
  refine ⟨k, p, fun i => U i, hp, hs, ?_, heq⟩
  intro i
  exact ⟨Unitary.coe_mul_star_self (U i), Unitary.coe_star_mul_self (U i)⟩

example {d : ℕ} (U : Matrix.unitaryGroup (Fin d) ℂ) :
    (∀ i j, 0 ≤ Complex.normSq ((U : Matrix (Fin d) (Fin d) ℂ) i j)) ∧
      (∀ i, ∑ j, Complex.normSq ((U : Matrix (Fin d) (Fin d) ℂ) i j) = 1) ∧
      (∀ j, ∑ i, Complex.normSq ((U : Matrix (Fin d) (Fin d) ℂ) i j) = 1) :=
  mem_doublyStochastic_iff_sum.mp (unitary_normSq_mem_doublyStochastic U)

example : ¬ ∃ ρ : Matrix (Fin 0) (Fin 0) ℂ, ρ.PosSemidef ∧ ρ.trace = 1 := by
  rintro ⟨ρ, _, ht⟩
  have := Matrix.dimension_pos_of_trace_one ht
  omega

example : IsRandomUnitaryImage (0 : Matrix (Fin 0) (Fin 0) ℂ) 0 := by
  refine ⟨1, fun _ => 1, fun _ => 1, by simp, by simp, ?_⟩
  simp

example {d : ℕ} {ρ : Matrix (Fin d) (Fin d) ℂ} (hρ : ρ.IsHermitian) :
    hρ.Majorizes hρ ∧ IsRandomUnitaryImage ρ ρ := by
  have h : hρ.Majorizes hρ := ⟨fun _ _ => le_rfl, rfl⟩
  exact ⟨h, h.isRandomUnitaryImage⟩

example {ρ σ : Matrix (Fin 1) (Fin 1) ℂ} (hρ : ρ.IsHermitian) (hσ : σ.IsHermitian) :
    hρ.Majorizes hσ ↔ hσ.eigenvalues = hρ.eigenvalues := by
  constructor
  · intro h
    ext i
    simpa only [Fin.sum_univ_one, Subsingleton.elim i 0] using h.2
  · intro h
    exact ⟨fun _ _ => by rw [h], by rw [h]⟩

example {d : ℕ} {ρ σ : Matrix (Fin d) (Fin d) ℂ}
    (hρ : ρ.IsHermitian) (hσ : σ.IsHermitian) (he : hρ.eigenvalues = hσ.eigenvalues) :
    hρ.Majorizes hσ ∧ hσ.Majorizes hρ := by
  constructor <;> constructor <;> simp_all

-- Every unitary change of eigenbasis, in particular every permutation, preserves majorization.
example {d : ℕ} {ρ σ : Matrix (Fin d) (Fin d) ℂ}
    (hρ : ρ.IsHermitian) (hσ : σ.IsHermitian) (U : Matrix.unitaryGroup (Fin d) ℂ)
    (heq : σ = (U : Matrix (Fin d) (Fin d) ℂ) * ρ * star (U : Matrix (Fin d) (Fin d) ℂ)) :
    hρ.Majorizes hσ ∧ hσ.Majorizes hρ := by
  have hforward : IsRandomUnitaryImage ρ σ := by
    refine ⟨1, fun _ => 1, fun _ => U, by simp, by simp, ?_⟩
    simpa using heq
  have hreverse : IsRandomUnitaryImage σ ρ := by
    refine ⟨1, fun _ => 1, fun _ => star U, by simp, by simp, ?_⟩
    change σ = Unitary.conjStarAlgAut ℂ _ U ρ at heq
    have hi := congrArg (Unitary.conjStarAlgAut ℂ _ U).symm heq
    rw [StarAlgEquiv.symm_apply_apply] at hi
    simpa only [Fin.sum_univ_one, Complex.ofReal_one, one_smul,
      Unitary.conjStarAlgAut_symm, Unitary.conjStarAlgAut_star_apply,
      Unitary.coe_star, star_star] using hi.symm
  exact ⟨hρ.majorizes_of_randomUnitaryImage hσ hforward,
    hσ.majorizes_of_randomUnitaryImage hρ hreverse⟩

private def pureState : Matrix (Fin 3) (Fin 3) ℂ := diagonal ![1, 0, 0]

private noncomputable def rotation : Matrix (Fin 3) (Fin 3) ℂ :=
  ![![3 / 5, -4 / 5, 0], ![4 / 5, 3 / 5, 0], ![0, 0, 1]]

private noncomputable def mixedState : Matrix (Fin 3) (Fin 3) ℂ :=
  ![![9 / 50, 6 / 25, 0], ![6 / 25, 8 / 25, 0], ![0, 0, 1 / 2]]

private def swapMatrix : Matrix (Fin 3) (Fin 3) ℂ :=
  (Equiv.swap (0 : Fin 3) 2).permMatrix ℂ

private theorem rotation_unitary : rotation ∈ Matrix.unitaryGroup (Fin 3) ℂ := by
  rw [mem_unitaryGroup_iff]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [Matrix.mul_apply, Matrix.star_apply, Fin.sum_univ_three]
  all_goals norm_num [rotation]

private theorem mixedState_eq : mixedState =
    (1 / 2 : ℂ) • (rotation * pureState * star rotation) +
      (1 / 2 : ℂ) • (swapMatrix * pureState * star swapMatrix) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Matrix.mul_apply,
      Matrix.star_apply, Fin.sum_univ_three]
  all_goals norm_num [mixedState, pureState, rotation, swapMatrix, Matrix.mul_apply,
      Matrix.star_apply, Fin.sum_univ_three, Equiv.Perm.permMatrix,
      PEquiv.toMatrix_apply, Equiv.toPEquiv_apply, Equiv.swap_apply_def]

private theorem pureState_psd : pureState.PosSemidef := by
  apply PosSemidef.diagonal
  intro i
  fin_cases i <;> norm_num

private theorem mixedState_psd : mixedState.PosSemidef := by
  rw [mixedState_eq]
  have hhalf : (0 : ℂ) ≤ 1 / 2 := by norm_num [Complex.le_def]
  exact (pureState_psd.mul_mul_conjTranspose_same rotation).smul hhalf |>.add
    ((pureState_psd.mul_mul_conjTranspose_same swapMatrix).smul hhalf)

private theorem pure_to_mixed : IsRandomUnitaryImage pureState mixedState := by
  refine ⟨2, fun _ => 1 / 2,
    ![⟨rotation, rotation_unitary⟩,
      ⟨swapMatrix, (Equiv.swap (0 : Fin 3) 2).permMatrix_mem_unitaryGroup⟩],
    fun _ => by norm_num, by norm_num [Fin.sum_univ_two], ?_⟩
  simpa only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat] using mixedState_eq

-- Both matrices are genuine density states, singular, and fail to commute.
example : pureState.trace = 1 ∧ mixedState.trace = 1 ∧
    pureState.det = 0 ∧ mixedState.det = 0 ∧
      pureState * mixedState ≠ mixedState * pureState := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · norm_num [pureState, Matrix.trace_diagonal, Fin.sum_univ_three]
  · norm_num [mixedState, Matrix.trace, Matrix.diag, Fin.sum_univ_three]
  · norm_num [pureState, det_diagonal, Fin.prod_univ_three]
  · rw [Matrix.det_fin_three]
    norm_num [mixedState]
  · intro h
    have h01 := congrArg (fun A : Matrix (Fin 3) (Fin 3) ℂ => A 0 1) h
    simp only [Matrix.mul_apply, Fin.sum_univ_three] at h01
    norm_num [pureState, mixedState] at h01

example : pureState * pureState = pureState := by
  simp only [pureState, diagonal_mul_diagonal]
  congr 1
  ext i
  fin_cases i <;> norm_num

example : mixedState * mixedState ≠ mixedState := by
  intro h
  have h22 := congrArg (fun A : Matrix (Fin 3) (Fin 3) ℂ => A 2 2) h
  simp only [Matrix.mul_apply, Fin.sum_univ_three] at h22
  norm_num [mixedState] at h22

example : pureState_psd.isHermitian.Majorizes mixedState_psd.isHermitian :=
  pureState_psd.isHermitian.majorizes_of_randomUnitaryImage mixedState_psd.isHermitian pure_to_mixed

example (f : ℝ → ℝ) (hf : ConvexOn ℝ Set.univ f) :
    (cfc f mixedState).trace.re ≤ (cfc f pureState).trace.re :=
  (pureState_psd.isHermitian.majorizes_iff_trace_convex mixedState_psd.isHermitian).mp
    (pureState_psd.isHermitian.majorizes_of_randomUnitaryImage
      mixedState_psd.isHermitian pure_to_mixed) f hf

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let declarations := #[``TNLean.IsRandomUnitaryImage,
    ``TNLean.unitary_normSq_mem_doublyStochastic, ``Matrix.IsHermitian.Majorizes,
    ``Matrix.IsHermitian.majorizes_iff_trace_convex,
    ``Matrix.IsHermitian.Majorizes.isRandomUnitaryImage,
    ``Matrix.IsHermitian.majorizes_of_randomUnitaryImage,
    ``Matrix.IsHermitian.majorizes_iff_randomUnitaryImage,
    ``Matrix.dimension_pos_of_trace_one]
  for decl in declarations do
    unless (← Lean.getEnv).contains decl do
      throwError "Missing declaration {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"
