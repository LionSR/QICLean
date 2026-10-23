/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Channel.MaximalOverlap
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! Boundary cases and homogeneous scope of the Schmidt overlap bound. -/

open Matrix
open scoped ComplexOrder InnerProductSpace

section
variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m]

-- The target may have any norm, including zero.
example (Ψ Φ : EuclideanSpace ℂ (m × n)) (hΦ : ‖Φ‖ = 1)
    (a : ℂ) {D : ℕ} (hr : (schmidtCoeffMatrix (WithLp.ofLp Φ)).rank ≤ D) :
    ‖inner ℂ (a • Ψ) Φ‖ ^ 2 ≤
      (Matrix.posSemidef_self_mul_conjTranspose
        (schmidtCoeffMatrix (WithLp.ofLp (a • Ψ)))).isHermitian.kyFanNorm D :=
  Matrix.normSq_inner_le_kyFanNorm (a • Ψ) Φ hΦ D hr

example (Φ : EuclideanSpace ℂ (m × n)) (hΦ : ‖Φ‖ = 1)
    {D : ℕ} (hr : (schmidtCoeffMatrix (WithLp.ofLp Φ)).rank ≤ D) :
    ‖inner ℂ (0 : EuclideanSpace ℂ (m × n)) Φ‖ ^ 2 ≤
      (Matrix.posSemidef_self_mul_conjTranspose
        (schmidtCoeffMatrix
          (WithLp.ofLp (0 : EuclideanSpace ℂ (m × n))))).isHermitian.kyFanNorm D :=
  Matrix.normSq_inner_le_kyFanNorm 0 Φ hΦ D hr

-- A zero budget needs no separate positivity premise in the public theorem.
example (Ψ Φ : EuclideanSpace ℂ (m × n)) (hΦ : ‖Φ‖ = 1)
    (hr : (schmidtCoeffMatrix (WithLp.ofLp Φ)).rank ≤ 0) :
    ‖inner ℂ Ψ Φ‖ ^ 2 ≤
      (Matrix.posSemidef_self_mul_conjTranspose
        (schmidtCoeffMatrix (WithLp.ofLp Ψ))).isHermitian.kyFanNorm 0 :=
  Matrix.normSq_inner_le_kyFanNorm Ψ Φ hΦ 0 hr

-- Above the ambient dimension no rank assumption is necessary.
example (Ψ Φ : EuclideanSpace ℂ (m × n)) (hΦ : ‖Φ‖ = 1)
    {D : ℕ} (hD : Fintype.card m ≤ D) :
    ‖inner ℂ Ψ Φ‖ ^ 2 ≤
      (Matrix.posSemidef_self_mul_conjTranspose
        (schmidtCoeffMatrix (WithLp.ofLp Ψ))).isHermitian.kyFanNorm D := by
  classical
  exact Matrix.normSq_inner_le_kyFanNorm Ψ Φ hΦ D
    ((schmidtCoeffMatrix (WithLp.ofLp Φ)).rank_le_card_height.trans hD)

end

run_cmd do
  let decl := ``Matrix.normSq_inner_le_kyFanNorm
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let axioms ← Lean.collectAxioms decl
  unless axioms.all (allowed.contains ·) do
    throwError "Unexpected axioms for {decl}: {axioms}"
  Lean.logInfo m!"{decl}: {axioms}"
