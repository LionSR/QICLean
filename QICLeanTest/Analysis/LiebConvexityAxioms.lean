/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.LiebConvexity
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! Standard-axiom and exponent-boundary checks for Wolf Theorem 5.15. -/

open scoped Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator
open Matrix

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for decl in #[``lieb_convexity_variational_le, ``lieb_convexity_posSemidef_posDef,
      ``lieb_convexity_posDef,
      ``convexOn_re_trace_conj_rpow_mul_rpow] do
    unless (← Lean.getEnv).contains decl do
      throwError "Missing declaration {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"

variable {D : ℕ} (K : Matrix (Fin D) (Fin D) ℂ)

-- All three vertices of the closed exponent triangle, with arbitrary complex K.
example : ConvexOn ℝ {p : Matrix (Fin D) (Fin D) ℂ × Matrix (Fin D) (Fin D) ℂ |
    p.1.PosDef ∧ p.2.PosDef}
    (fun p => (trace (Kᴴ * p.1 ^ (1 : ℝ) * K * p.2 ^ (0 : ℝ))).re) :=
  convexOn_re_trace_conj_rpow_mul_rpow K ⟨le_rfl, by norm_num⟩ (by norm_num)

example : ConvexOn ℝ {p : Matrix (Fin D) (Fin D) ℂ × Matrix (Fin D) (Fin D) ℂ |
    p.1.PosDef ∧ p.2.PosDef}
    (fun p => (trace (Kᴴ * p.1 ^ (2 : ℝ) * K * p.2 ^ (-1 : ℝ))).re) :=
  convexOn_re_trace_conj_rpow_mul_rpow K (by norm_num) (by norm_num)

example : ConvexOn ℝ {p : Matrix (Fin D) (Fin D) ℂ × Matrix (Fin D) (Fin D) ℂ |
    p.1.PosDef ∧ p.2.PosDef}
    (fun p => (trace (Kᴴ * p.1 ^ (2 : ℝ) * K * p.2 ^ (0 : ℝ))).re) :=
  convexOn_re_trace_conj_rpow_mul_rpow K (by norm_num) (by norm_num)

-- The empty matrix algebra is permitted, without a nonzero-dimension hypothesis.
example : ConvexOn ℝ {p : Matrix (Fin 0) (Fin 0) ℂ × Matrix (Fin 0) (Fin 0) ℂ |
    p.1.PosDef ∧ p.2.PosDef}
    (fun p => (trace ((1 : Matrix (Fin 0) (Fin 0) ℂ)ᴴ * p.1 ^ (3 / 2 : ℝ) *
      1 * p.2 ^ (-1 / 4 : ℝ))).re) :=
  convexOn_re_trace_conj_rpow_mul_rpow 1 (by norm_num) (by norm_num)

-- A singular first argument is allowed even at the inverse-power corner.
example {B₁ B₂ : Matrix (Fin D) (Fin D) ℂ} (hB₁ : B₁.PosDef) (hB₂ : B₂.PosDef)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    (trace (Kᴴ * (t • (0 : Matrix (Fin D) (Fin D) ℂ) + (1 - t) • 1) ^ (2 : ℝ) * K *
      (t • B₁ + (1 - t) • B₂) ^ (-1 : ℝ))).re ≤
    t * (trace (Kᴴ * (0 : Matrix (Fin D) (Fin D) ℂ) ^ (2 : ℝ) * K * B₁ ^ (-1 : ℝ))).re +
      (1 - t) * (trace (Kᴴ * (1 : Matrix (Fin D) (Fin D) ℂ) ^ (2 : ℝ) * K *
        B₂ ^ (-1 : ℝ))).re :=
  lieb_convexity_posSemidef_posDef (by norm_num) (by norm_num)
    Matrix.PosSemidef.zero Matrix.PosSemidef.one hB₁ hB₂ ht

-- Assigning the inverse power of zero the value zero violates joint convexity.
example :
    ¬ (trace ((1 : Matrix (Fin 1) (Fin 1) ℂ) ^ (2 : ℝ) *
      ((1 / 2 : ℝ) • (1 : Matrix (Fin 1) (Fin 1) ℂ)) ^ (-1 : ℝ))).re ≤
        (1 / 2 : ℝ) * (trace ((1 : Matrix (Fin 1) (Fin 1) ℂ) ^ (2 : ℝ) *
          (0 : Matrix (Fin 1) (Fin 1) ℂ) ^ (-1 : ℝ))).re +
        (1 / 2 : ℝ) * (trace ((1 : Matrix (Fin 1) (Fin 1) ℂ) ^ (2 : ℝ) *
          (1 : Matrix (Fin 1) (Fin 1) ℂ) ^ (-1 : ℝ))).re := by
  have hz : (0 : Matrix (Fin 1) (Fin 1) ℂ) ^ (-1 : ℝ) = 0 := CFC.zero_rpow (by norm_num)
  rw [hz]
  rw [Matrix.PosDef.smul_rpow Matrix.PosDef.one (by norm_num : (0 : ℝ) < 1 / 2)]
  simp only [CFC.one_rpow, one_mul, mul_zero, Real.rpow_neg_one]
  norm_num [Matrix.trace, Matrix.smul_apply, Matrix.one_apply]
