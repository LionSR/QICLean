/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Circuit.Party.Source.PreparedSourceGate
import QICLean.Circuit.Party.Syntax.CoarsenLocal

/-!
# Prepared gates on a type of no parties

On an empty type of parties every system has one configuration and every word has all entries
of its operator equal to `1`. A prepared gate therefore acts by the sum of its branch
coefficients: every entry of its operator is this sum. The sum may vanish, also when there is no
branch label. Since the gate is a contraction, the sum has modulus at most one.

## Main results

* `QuantumCircuit.Party.PreparedSourceGate.eval_apply_of_isEmpty`,
  `QuantumCircuit.Party.PreparedSourceGate.norm_coeffSum_le_one_of_isEmpty`.

## References

* Polynomial-PEPS manuscript (September 24, 2026), Theorem 5.2, `04-compression.tex`,
  lines 24–28 and 233–251.
-/

open Matrix ManyBody
open scoped Matrix.Norms.L2Operator

namespace QuantumCircuit.Party.PreparedSourceGate

variable {P : Type} [DecidableEq P] [Fintype P] [IsEmpty P] {ι : Type} [Fintype ι] {c : ι → ℂ}
  {X Y : P → Type} [∀ p, Fintype (X p)] [∀ p, DecidableEq (X p)] [∀ p, Fintype (Y p)]
  [∀ p, DecidableEq (Y p)]

omit [∀ p, Fintype (Y p)] [∀ p, DecidableEq (Y p)] in
/-- **A prepared gate on no parties acts by the sum of its branch coefficients**: every entry of
its operator, between the single configurations of the two systems, is this sum. Source:
`04-compression.tex`, lines 24–28 and 233–251. -/
theorem eval_apply_of_isEmpty (G : PreparedSourceGate c X Y) (y : Config Y) (x : Config X) :
    G.eval y x = ∑ ξ, c ξ := by
  simp only [eval, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  exact Finset.sum_congr rfl fun ξ _ ↦ by rw [Word.op_apply_of_isEmpty, mul_one]

omit [∀ p, Fintype (X p)] [∀ p, DecidableEq (X p)] [∀ p, Fintype (Y p)]
  [∀ p, DecidableEq (Y p)] in
/-- Contractivity bounds the scalar of a gate on no parties. Source: `04-compression.tex`,
lines 24–28 and 233–251. -/
theorem norm_coeffSum_le_one_of_isEmpty (G : PreparedSourceGate c X Y) : ‖∑ ξ, c ξ‖ ≤ 1 := by
  let _ : ∀ p, Fintype (X p) := fun p ↦ isEmptyElim p
  let _ : ∀ p, DecidableEq (X p) := fun p ↦ isEmptyElim p
  let _ : ∀ p, Fintype (Y p) := fun p ↦ isEmptyElim p
  have h := Matrix.l2_opNorm_mulVec G.eval
    (EuclideanSpace.single (isEmptyElim : Config X) (1 : ℂ))
  have h1 : ‖EuclideanSpace.single (isEmptyElim : Config X) (1 : ℂ)‖ = 1 := by simp
  rw [h1, mul_one] at h
  refine le_trans (le_of_eq ?_) ((PiLp.norm_apply_le _ (isEmptyElim : Config Y)).trans
    (h.trans G.norm_eval_le_one))
  simp [G.eval_apply_of_isEmpty]

end QuantumCircuit.Party.PreparedSourceGate
