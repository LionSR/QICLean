/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Entropy.RegionPureApproximationTail
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! The zero approximant has error exactly one; all half-error results are audited. -/

example {n : Type*} [Fintype n] [DecidableEq n]
    (ψ : EuclideanSpace ℂ n) (hψ : ‖ψ‖ = 1) :
    Matrix.rectangularTraceNorm (Matrix.euclideanOuterProduct ψ ψ -
      Matrix.euclideanOuterProduct (0 : EuclideanSpace ℂ n) 0) = 1 := by
  have hz : Matrix.euclideanOuterProduct (0 : EuclideanSpace ℂ n) 0 =
      (0 : Matrix n n ℂ) := by
    simp [Matrix.euclideanOuterProduct]
  rw [hz, sub_zero, Matrix.rectangularTraceNorm_euclideanOuterProduct_self, hψ, one_pow]

open scoped ComplexOrder

example {V : Type*} [Fintype V] [DecidableEq V] {n : V → ℕ}
    (ψ : EuclideanSpace ℂ (Entropy.SiteConfig n)) (hψ : ‖ψ‖ = 1) (R : Finset V) :
    ∑ i ∈ Finset.Ico (Entropy.regionState R ψ).rank
      (Fintype.card (Entropy.RegionConfig n R)),
      (Entropy.regionState_posSemidef R ψ).isHermitian.descEigenvalue i ≤ 0 := by
  simpa using Entropy.sum_descEigenvalue_regionState_tail_le_half_pure_trace_error
    ψ ψ hψ R (D := (Entropy.regionState R ψ).rank) le_rfl
    (δ := 0) (by norm_num) (by simp)

example {V : Type*} [Fintype V] [DecidableEq V] {n : V → ℕ}
    (ψ φ : EuclideanSpace ℂ (Entropy.SiteConfig n)) (hψ : ‖ψ‖ = 1)
    (R : Finset V) {D : ℕ} (hD : Fintype.card (Entropy.RegionConfig n R) ≤ D)
    {δ : ℝ} (hδ : δ < 1)
    (he : Matrix.rectangularTraceNorm
      (Matrix.euclideanOuterProduct ψ ψ - Matrix.euclideanOuterProduct φ φ) ≤ δ) :
    ∑ i ∈ Finset.Ico D (Fintype.card (Entropy.RegionConfig n R)),
      (Entropy.regionState_posSemidef R ψ).isHermitian.descEigenvalue i ≤ δ / 2 := by
  exact Entropy.sum_descEigenvalue_regionState_tail_le_half_pure_trace_error
    ψ φ hψ R ((Entropy.regionState R φ).rank_le_card_width.trans hD) hδ he

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for decl in #[``Matrix.one_sub_normalized_overlap_le_half_pure_trace_error,
      ``Matrix.sum_descEigenvalue_tail_le_half_pure_trace_error,
      ``Entropy.sum_descEigenvalue_regionState_tail_le_half_pure_trace_error] do
    unless (← Lean.getEnv).contains decl do
      throwError "Missing declaration {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"
