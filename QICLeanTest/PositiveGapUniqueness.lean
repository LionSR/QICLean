/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.PositiveGapUniqueness
import QICLean.Analysis.DoubledSystemGap

/-! Regression checks for uniqueness at a strictly positive global gap. -/

open Complex Matrix
open scoped InnerProductSpace ComplexOrder

namespace PositiveGapUniquenessTest

variable {n : Type*} [Fintype n] [DecidableEq n]

-- No eigenvalue equation on Ω or normalization/nonzero hypothesis on ψ is required.
example {H : Matrix n n ℂ} {E₀ Δ : ℝ} {Ω ψ : EuclideanSpace ℂ n}
    (hgap : (H - (E₀ : ℂ) • 1 -
      (Δ : ℂ) • (1 - vecMulVec (WithLp.ofLp Ω) (star (WithLp.ofLp Ω)))).PosSemidef)
    (hΔ : 0 < Δ) (hΩ : ‖Ω‖ = 1)
    (hψ : H *ᵥ WithLp.ofLp ψ = (E₀ : ℂ) • WithLp.ofLp ψ) :
    ψ = ⟪Ω, ψ⟫_ℂ • Ω :=
  hgap.eq_inner_smul_of_gap hΔ hΩ hψ

private noncomputable def H (Ω : EuclideanSpace ℂ n) : Matrix n n ℂ :=
  ((-7 : ℝ) : ℂ) • 1 + ((2 : ℝ) : ℂ) •
    (1 - vecMulVec (WithLp.ofLp Ω) (star (WithLp.ofLp Ω)))

omit [Fintype n] in
private theorem gap (Ω : EuclideanSpace ℂ n) :
    (H Ω - ((-7 : ℝ) : ℂ) • 1 - ((2 : ℝ) : ℂ) •
      (1 - vecMulVec (WithLp.ofLp Ω) (star (WithLp.ofLp Ω)))).PosSemidef := by
  rw [H, add_sub_cancel_left, sub_self]
  exact PosSemidef.zero

private theorem ground (Ω : EuclideanSpace ℂ n) (hΩ : ‖Ω‖ = 1) :
    H Ω *ᵥ WithLp.ofLp Ω = ((-7 : ℝ) : ℂ) • WithLp.ofLp Ω := by
  have hself : ⟪Ω, Ω⟫_ℂ = 1 := by
    rw [inner_self_eq_norm_sq_to_K, hΩ]
    simp
  have hlin : toEuclideanLin (H Ω) Ω = ((-7 : ℝ) : ℂ) • Ω := by
    simp only [H, map_add, map_sub, map_smul, LinearMap.add_apply, LinearMap.sub_apply,
      LinearMap.smul_apply, toLpLin_one, LinearMap.id_apply,
      toEuclideanLin_vecMulVec_star_self_apply, hself, one_smul, sub_self, smul_zero,
      add_zero]
  exact congrArg WithLp.ofLp hlin

private theorem ground_smul (Ω : EuclideanSpace ℂ n) (hΩ : ‖Ω‖ = 1) (c : ℂ) :
    H Ω *ᵥ WithLp.ofLp (c • Ω) = ((-7 : ℝ) : ℂ) • WithLp.ofLp (c • Ω) := by
  change H Ω *ᵥ (c • WithLp.ofLp Ω) = ((-7 : ℝ) : ℂ) • (c • WithLp.ofLp Ω)
  rw [mulVec_smul, ground Ω hΩ, smul_comm]

-- The zero ground vector is accepted directly by the same theorem.
example (Ω : EuclideanSpace ℂ n) (hΩ : ‖Ω‖ = 1) :
    (0 : EuclideanSpace ℂ n) = ⟪Ω, 0⟫_ℂ • Ω := by
  apply (gap Ω).eq_inner_smul_of_gap two_pos hΩ
  simp

-- A normalized ground vector can have a non-real phase.
example (Ω : EuclideanSpace ℂ n) (hΩ : ‖Ω‖ = 1) :
    ‖I • Ω‖ = 1 ∧ I • Ω = ⟪Ω, I • Ω⟫_ℂ • Ω := by
  refine ⟨by simp [norm_smul, hΩ], ?_⟩
  exact (gap Ω).eq_inner_smul_of_gap two_pos hΩ (ground_smul Ω hΩ I)

-- An unnormalized ground vector retains its full complex coefficient.
example (Ω : EuclideanSpace ℂ n) (hΩ : ‖Ω‖ = 1) :
    ‖(2 * I) • Ω‖ = 2 ∧ (2 * I) • Ω = ⟪Ω, (2 * I) • Ω⟫_ℂ • Ω := by
  refine ⟨by norm_num [norm_smul, norm_mul, hΩ], ?_⟩
  exact (gap Ω).eq_inner_smul_of_gap two_pos hΩ (ground_smul Ω hΩ (2 * I))

-- Both eigenspace conclusions hold for the model at the negative energy -7.
example (Ω : EuclideanSpace ℂ n) (hΩ : ‖Ω‖ = 1) :
    Module.End.eigenspace (toEuclideanLin (H Ω)) ((-7 : ℝ) : ℂ) =
      Submodule.span ℂ {Ω} :=
  (gap Ω).eigenspace_eq_span_of_gap two_pos hΩ (ground Ω hΩ)

example (Ω : EuclideanSpace ℂ n) (hΩ : ‖Ω‖ = 1) :
    Module.finrank ℂ (Module.End.eigenspace (toEuclideanLin (H Ω)) ((-7 : ℝ) : ℂ)) = 1 :=
  (gap Ω).finrank_eigenspace_eq_one_of_gap two_pos hΩ (ground Ω hΩ)

-- The doubled, physically swapped Hamiltonian has a unique ground ray when Δ > 0.
example {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    {K : Matrix (A × B) (A × B) ℂ} {Ω : A × B → ℂ} {E₀ Δ : ℝ}
    (hgap : (K - (E₀ : ℂ) • 1 -
      (Δ : ℂ) • (1 - vecMulVec Ω (star Ω))).PosSemidef)
    (hΩ : ∑ i, ‖Ω i‖ ^ 2 = 1) (heigen : K *ᵥ Ω = (E₀ : ℂ) • Ω) (hΔ : 0 < Δ) :
    let F := partialSwap A B
    let K' := F * doubledHamiltonian K * Fᴴ
    Module.finrank ℂ (Module.End.eigenspace (toEuclideanLin K') ((2 * E₀ : ℝ) : ℂ)) = 1 := by
  obtain ⟨hnorm, heig, hswapped⟩ := doubled_gap_partialSwap hgap hΩ heigen hΔ.le
  exact hswapped.finrank_eigenspace_eq_one_of_gap
    (Ω := WithLp.toLp 2 (partialSwap A B *ᵥ doubledVector Ω)) hΔ hnorm heig

-- At Δ = 0 the PSD defect and eigenvalue equation permit an independent ground vector.
-- This counterexample is why the uniqueness theorems require strict positivity.
example : ∃ Ω ψ : EuclideanSpace ℂ Bool, ‖Ω‖ = 1 ∧
    ((0 : Matrix Bool Bool ℂ) - (0 : ℂ) • 1 - (0 : ℂ) •
      (1 - vecMulVec (WithLp.ofLp Ω) (star (WithLp.ofLp Ω)))).PosSemidef ∧
    (0 : Matrix Bool Bool ℂ) *ᵥ WithLp.ofLp ψ = (0 : ℂ) • WithLp.ofLp ψ ∧
    ψ ≠ ⟪Ω, ψ⟫_ℂ • Ω := by
  refine ⟨PiLp.single 2 false 1, PiLp.single 2 true 1, by simp, ?_, ?_, ?_⟩
  · simpa using (PosSemidef.zero : (0 : Matrix Bool Bool ℂ).PosSemidef)
  · rw [Matrix.zero_mulVec, zero_smul]
  · intro h
    have hcoord := congrArg (fun v : EuclideanSpace ℂ Bool ↦ v true) h
    simp [EuclideanSpace.inner_single_left] at hcoord

end PositiveGapUniquenessTest

/--
info: 'Matrix.PosSemidef.eq_inner_smul_of_gap' depends on axioms:
[propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms Matrix.PosSemidef.eq_inner_smul_of_gap

/--
info: 'Matrix.PosSemidef.eigenspace_eq_span_of_gap' depends on axioms:
[propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms Matrix.PosSemidef.eigenspace_eq_span_of_gap

/--
info: 'Matrix.PosSemidef.finrank_eigenspace_eq_one_of_gap' depends on axioms:
[propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms Matrix.PosSemidef.finrank_eigenspace_eq_one_of_gap
