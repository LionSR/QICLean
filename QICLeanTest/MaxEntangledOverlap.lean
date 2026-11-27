/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Channel.Entanglement.MaxEntangledOverlap
import Lean.Util.CollectAxioms
import Lean.Elab.Command

/-!
Regression tests and strict transitive axiom guards for `Matrix.maxEntangledOverlap`,
the PPT overlap bound, trace-norm stability, and the algebraic partial-transpose lemmas.

Covers `d = 1`, qubit product states (`|00⟩⟨00|` saturating `1 / 2` and `|01⟩⟨01|`
having overlap `0`), the normalized identity state `I / d²` (overlap `1 / d²`),
explicit exclusion of `d = 0` from normalized Bell facts, finite-sum PPT caps,
continuity, and the full trace-norm gap bound.
-/

open Matrix
open scoped Kronecker ComplexOrder BigOperators

namespace MaxEntangledOverlapTest

/-! ## `d = 1` boundary case -/

/-- At `d = 1`, the maximally entangled projector equals the identity matrix. -/
theorem omegaProj_one_eq_one :
    omegaProj 1 = (1 : Matrix (Fin 1 × Fin 1) (Fin 1 × Fin 1) ℂ) := by
  ext ⟨i₁, i₂⟩ ⟨j₁, j₂⟩
  fin_cases i₁; fin_cases i₂; fin_cases j₁; fin_cases j₂
  simp [omegaProj_apply, omegaVec_apply]

/-- At `d = 1`, the maximally entangled overlap of the identity is `1`, saturating
the normalized PPT bound `1 / 1`. -/
theorem dim_one_overlap :
    maxEntangledOverlap 1 (1 : Matrix (Fin 1 × Fin 1) (Fin 1 × Fin 1) ℂ) = 1 ∧
      maxEntangledOverlap 1 (omegaProj 1) = 1 :=
  ⟨maxEntangledOverlap_one (by decide), maxEntangledOverlap_omegaProj (by decide)⟩

/-! ## `d = 0` exclusion from normalized Bell facts -/

/-- At `d = 0`, `omegaProj 0` is the empty matrix, whose overlap is `0 ≠ 1`.
This witnesses why `0 < d` is required in normalized Bell statements. -/
theorem dim_zero_excluded :
    maxEntangledOverlap 0 (omegaProj 0) = 0 ∧
      maxEntangledOverlap 0 (omegaProj 0) ≠ 1 := by
  have h0 : omegaProj 0 = 0 := Subsingleton.elim _ _
  rw [h0, maxEntangledOverlap_zero]
  exact ⟨rfl, zero_ne_one⟩

/-! ## Qubit product states (`d = 2`) -/

/-- Single-qubit computational-basis projector `|i⟩⟨i|`. -/
def qubitBasisProj (i : Fin 2) : Matrix (Fin 2) (Fin 2) ℂ :=
  Matrix.single i i 1

theorem qubitBasisProj_posSemidef (i : Fin 2) : (qubitBasisProj i).PosSemidef := by
  have h : qubitBasisProj i = (qubitBasisProj i)ᴴ * qubitBasisProj i := by
    ext a b
    fin_cases i <;> fin_cases a <;> fin_cases b <;>
      simp [qubitBasisProj, Matrix.mul_apply, Matrix.single_apply]
  rw [h]
  exact posSemidef_conjTranspose_mul_self _

theorem qubitBasisProj_trace (i : Fin 2) : (qubitBasisProj i).trace = 1 := by
  fin_cases i <;> simp [qubitBasisProj, Matrix.trace, Matrix.diag, Matrix.single_apply]

/-- The qubit product state `|00⟩⟨00|` is PSD, PPT, trace-one, has overlap `1 / 2`
(saturating the PPT bound `≤ 1 / 2`), and has full trace-norm distance at least `1 / 2`
from `|Ω₂⟩⟨Ω₂|`. -/
theorem qubit_product_00 :
    let ρ := qubitBasisProj 0 ⊗ₖ qubitBasisProj 0
    ρ.PosSemidef ∧ ρ.IsPPT ∧ ρ.trace = 1 ∧
      maxEntangledOverlap 2 ρ = 1 / 2 ∧
      (1 / 2 : ℝ) ≤ rectangularTraceNorm (ρ - omegaProj 2) := by
  intro ρ
  have hpsd : ρ.PosSemidef := (qubitBasisProj_posSemidef 0).kronecker (qubitBasisProj_posSemidef 0)
  have hppt : ρ.IsPPT := by
    rw [IsPPT, partialTransposeLeft_kronecker]
    exact (qubitBasisProj_posSemidef 0).transpose.kronecker (qubitBasisProj_posSemidef 0)
  have htr : ρ.trace = 1 := by
    simp [ρ, Matrix.trace_kronecker, qubitBasisProj_trace]
  have hov : maxEntangledOverlap 2 ρ = 1 / 2 := by
    rw [maxEntangledOverlap_kronecker]
    have hmul : ((qubitBasisProj 0)ᵀ * qubitBasisProj 0).trace = 1 := by
      simp [qubitBasisProj, Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.single_apply]
    rw [hmul]
    norm_num
  have hgap : (1 / 2 : ℝ) ≤ rectangularTraceNorm (ρ - omegaProj 2) := by
    have h := one_sub_one_div_le_rectangularTraceNorm_sub_omegaProj_of_isPPT
      (d := 2) (by decide) hppt htr
    linarith
  exact ⟨hpsd, hppt, htr, hov, hgap⟩

/-- The orthogonal qubit product state `|01⟩⟨01|` has maximally entangled overlap `0`. -/
theorem qubit_product_01_overlap :
    maxEntangledOverlap 2 (qubitBasisProj 0 ⊗ₖ qubitBasisProj 1) = 0 := by
  rw [maxEntangledOverlap_kronecker]
  have hmul : ((qubitBasisProj 0)ᵀ * qubitBasisProj 1).trace = 0 := by
    simp [qubitBasisProj, Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.single_apply]
  rw [hmul]
  simp

/-! ## Normalized identity state `I / d²` -/

/-- The maximally mixed state `I_{d²} / d²` on `ℂ^d ⊗ ℂ^d`. -/
noncomputable def normalizedIdentity (d : ℕ) :
    Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ :=
  ((d : ℝ) ^ 2)⁻¹ • (1 : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ)

/-- For `d > 0`, the normalized identity is PSD, PPT, trace-one, and has maximally
entangled overlap `1 / d² ≤ 1 / d`. -/
theorem normalizedIdentity_properties {d : ℕ} (hd : 0 < d) :
    (normalizedIdentity d).PosSemidef ∧
      (normalizedIdentity d).IsPPT ∧
      (normalizedIdentity d).trace = 1 ∧
      maxEntangledOverlap d (normalizedIdentity d) = 1 / (d : ℝ) ^ 2 ∧
      maxEntangledOverlap d (normalizedIdentity d) ≤ 1 / (d : ℝ) := by
  have hd_pos : (0 : ℝ) < d := Nat.cast_pos.mpr hd
  have hpsd : (normalizedIdentity d).PosSemidef := by
    refine Matrix.PosSemidef.one.smul ?_
    positivity
  have hppt : (normalizedIdentity d).IsPPT := by
    rw [IsPPT]
    have hpt : partialTransposeLeft (normalizedIdentity d) = normalizedIdentity d := by
      ext p q
      simp only [normalizedIdentity, partialTransposeLeft_apply, Matrix.smul_apply,
        Matrix.one_apply, Prod.ext_iff]
      congr 2
      simp [eq_comm]
    rw [hpt]
    exact hpsd
  have htr : (normalizedIdentity d).trace = 1 := by
    rw [normalizedIdentity, trace_smul, Matrix.trace_one, Fintype.card_prod, Fintype.card_fin]
    have hd_ne : (d : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hd.ne'
    simp only [Complex.real_smul, Nat.cast_mul]
    push_cast
    field_simp [hd_ne]
  have hov : maxEntangledOverlap d (normalizedIdentity d) = 1 / (d : ℝ) ^ 2 := by
    rw [normalizedIdentity, maxEntangledOverlap_smul_real, maxEntangledOverlap_one hd,
      mul_one, one_div]
  have hbound : maxEntangledOverlap d (normalizedIdentity d) ≤ 1 / (d : ℝ) :=
    maxEntangledOverlap_le_one_div_of_isPPT hd hppt htr
  exact ⟨hpsd, hppt, htr, hov, hbound⟩

/-- Concrete qubit check: the maximally mixed two-qubit state has overlap `1 / 4`. -/
theorem normalizedIdentity_two_overlap :
    maxEntangledOverlap 2 (normalizedIdentity 2) = 1 / 4 := by
  have h := (normalizedIdentity_properties (d := 2) (by decide)).2.2.2.1
  norm_num at h
  exact h

/-! ## Finite-sum PPT cap and continuity smoke checks -/

theorem sum_ppt_cap_smoke {d : ℕ} (hd : 0 < d)
    (σ τ : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) (hσ : σ.IsPPT) (hτ : τ.IsPPT) :
    maxEntangledOverlap d (σ + τ) ≤ (σ.trace.re + τ.trace.re) / (d : ℝ) := by
  have h := maxEntangledOverlap_sum_le_sum_trace_re_div_of_isPPT hd (Finset.univ : Finset (Fin 2))
    (fun i ↦ if i = 0 then σ else τ) (by
      intro i _
      fin_cases i
      · exact hσ
      · exact hτ)
  simpa [Fin.sum_univ_two] using h

theorem continuous_overlap_smoke (d : ℕ) : Continuous (maxEntangledOverlap d) :=
  continuous_maxEntangledOverlap d

/-! ## Strict transitive axiom guard -/

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for decl in #[
      ``Matrix.trace_partialTransposeLeft_mul_partialTransposeLeft,
      ``Matrix.partialTransposeLeft_omegaProj,
      ``Matrix.isStarProjection_omegaProj,
      ``Matrix.omegaProj_posSemidef,
      ``Matrix.one_sub_omegaProj_posSemidef,
      ``Matrix.l2_opNorm_omegaProj_le_one,
      ``Matrix.maxEntangledOverlap,
      ``Matrix.maxEntangledOverlap_zero,
      ``Matrix.maxEntangledOverlap_add,
      ``Matrix.maxEntangledOverlap_sub,
      ``Matrix.maxEntangledOverlap_neg,
      ``Matrix.maxEntangledOverlap_smul_real,
      ``Matrix.maxEntangledOverlap_sum,
      ``Matrix.continuous_maxEntangledOverlap,
      ``Matrix.maxEntangledOverlap_omegaProj,
      ``Matrix.maxEntangledOverlap_one,
      ``Matrix.maxEntangledOverlap_nonneg_of_posSemidef,
      ``Matrix.maxEntangledOverlap_le_trace_re_of_posSemidef,
      ``Matrix.maxEntangledOverlap_le_one_of_posSemidef,
      ``Matrix.maxEntangledOverlap_eq_swap_partialTransposeLeft,
      ``Matrix.maxEntangledOverlap_kronecker,
      ``Matrix.maxEntangledOverlap_le_trace_re_div_of_isPPT,
      ``Matrix.maxEntangledOverlap_le_one_div_of_isPPT,
      ``Matrix.maxEntangledOverlap_sum_le_sum_trace_re_div_of_isPPT,
      ``Matrix.abs_maxEntangledOverlap_sub_le,
      ``Matrix.abs_one_sub_maxEntangledOverlap_le,
      ``Matrix.one_sub_rectangularTraceNorm_le_maxEntangledOverlap,
      ``Matrix.one_sub_one_div_le_rectangularTraceNorm_sub_omegaProj_of_isPPT,
      ``omegaProj_one_eq_one,
      ``dim_one_overlap,
      ``dim_zero_excluded,
      ``qubit_product_00,
      ``qubit_product_01_overlap,
      ``normalizedIdentity_properties,
      ``normalizedIdentity_two_overlap,
      ``sum_ppt_cap_smoke,
      ``continuous_overlap_smoke] do
    let axs ← Lean.collectAxioms decl
    unless axs.all (allowed.contains ·) do
      throwError "Unexpected axioms for {decl}: {axs}"
    Lean.logInfo m!"{decl}: {axs}"

end MaxEntangledOverlapTest
