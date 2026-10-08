/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.Transport.Defs

/-!
# Transport states and the commutant of the inputs

A matrix `Z` commuting with every input of a mean tree commutes with the root, and every map
in the construction of the leaf maps is a right module map over `Z`:
`Φ_j(X Z) = Φ_j(X) Z`. Dually the trace adjoint satisfies `Φ_j^*(Z Y) = Z Φ_j^*(Y)`.
Consequently, when `Z` fixes the root vector `v`, it fixes the transport states from the left:
`Z σ_{j,u} = σ_{j,u}`.

In the area-law paper this is used with `Z` the symmetrizer of the replica copies: all inputs
commute with copy permutations, so the transport states live on the symmetric subspace
(`06-transport.tex`, display `transport:states`, lines 395--401, and line 491).

The proofs are written from the paper; no Lean source was adapted.
-/

open scoped Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator
open MeasureTheory Set

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- A matrix commuting with `a` commutes with its ring inverse. -/
theorem commute_ringInverse_right {Z a : Matrix n n ℂ} (h : Commute Z a) :
    Commute Z (Ring.inverse a) := by
  by_cases hu : IsUnit a
  · obtain ⟨u, rfl⟩ := hu
    rw [Ring.inverse_unit]
    exact h.units_inv_right
  · rw [Ring.inverse_non_unit _ hu]
    exact Commute.zero_right Z

omit [Fintype n] [DecidableEq n] in
theorem sandwich_mul_right {V X Z : Matrix n n ℂ} [Fintype n] (h : Commute Z V) :
    V * (X * Z) * V = V * X * V * Z := by
  rw [show V * (X * Z) * V = V * X * (Z * V) by simp only [Matrix.mul_assoc], h.eq]
  simp only [Matrix.mul_assoc]

/-- The derivative of a real power is a right module map over the commutant. -/
theorem rpowDeriv_mul_right {C Z : Matrix n n ℂ} (hC : C.PosDef) (hZ : Commute Z C) {p : ℝ}
    (hp : p ∈ Icc (0 : ℝ) 1) (X : Matrix n n ℂ) :
    rpowDeriv p C (X * Z) = rpowDeriv p C X * Z := by
  unfold rpowDeriv
  split_ifs with h0 h1
  · simp
  · rfl
  · have hp' : p ∈ Ioo (0 : ℝ) 1 := ⟨lt_of_le_of_ne hp.1 (Ne.symm h0), lt_of_le_of_ne hp.2 h1⟩
    rw [rpowFDeriv_apply hC hp', rpowFDeriv_apply hC hp', smul_mul_assoc]
    congr 1
    have hint := (integrableOn_rpowFDerivIntegrand hC hp').apply_continuousLinearMap X
    have hR : ∀ t : ℝ, Commute Z (Ring.inverse (t • (1 : Matrix n n ℂ) + C)) := fun t =>
      commute_ringInverse_right (((Commute.one_right Z).smul_right t).add_right hZ)
    have hpt : ∀ t : ℝ, t ^ p • (Ring.inverse (t • (1 : Matrix n n ℂ) + C) * (X * Z) *
        Ring.inverse (t • (1 : Matrix n n ℂ) + C)) =
        (ContinuousLinearMap.mul ℂ (Matrix n n ℂ)).flip Z (rpowFDerivIntegrand p C t X) := by
      intro t
      rw [ContinuousLinearMap.flip_apply, ContinuousLinearMap.mul_apply',
        rpowFDerivIntegrand_apply, sandwich_mul_right (hR t), smul_mul_assoc]
    simp_rw [hpt]
    rw [ContinuousLinearMap.integral_comp_comm _ hint]
    rfl

/-- The partial derivative of the mean in its second argument is a right module map over the
commutant of both arguments. -/
theorem geomMeanDerivRight_mul_right {A B Z : Matrix n n ℂ} (hA : A.PosDef) (hB : B.PosDef)
    (hZA : Commute Z A) (hZB : Commute Z B) {p : ℝ} (hp : p ∈ Icc (0 : ℝ) 1)
    (X : Matrix n n ℂ) :
    geomMeanDerivRight p A B (X * Z) = geomMeanDerivRight p A B X * Z := by
  have h1 : Commute Z (A ^ (1 / 2 : ℝ)) := (PosDef.commute_rpow_left hA hZA.symm _).symm
  have h2 : Commute Z (A ^ (-(1 / 2) : ℝ)) := (PosDef.commute_rpow_left hA hZA.symm _).symm
  have hC : Commute Z (A ^ (-(1 / 2) : ℝ) * B * A ^ (-(1 / 2) : ℝ)) :=
    (h2.mul_right hZB).mul_right h2
  simp only [geomMeanDerivRight, ContinuousLinearMap.comp_apply, sandwichL_apply]
  rw [sandwich_mul_right h2, rpowDeriv_mul_right (hA.whiten hB) hC hp, sandwich_mul_right h1]

/-- The partial derivative of the mean in its first argument is a right module map over the
commutant of both arguments. -/
theorem geomMeanDerivLeft_mul_right {A B Z : Matrix n n ℂ} (hA : A.PosDef) (hB : B.PosDef)
    (hZA : Commute Z A) (hZB : Commute Z B) {p : ℝ} (hp : p ∈ Icc (0 : ℝ) 1)
    (X : Matrix n n ℂ) :
    geomMeanDerivLeft p A B (X * Z) = geomMeanDerivLeft p A B X * Z :=
  geomMeanDerivRight_mul_right hB hA hZB hZA ⟨by linarith [hp.2], by linarith [hp.1]⟩ X

namespace MeanTree

variable {ι : Type*} [DecidableEq ι] {A : ι → Matrix n n ℂ}

/-- The derivative of the root in one input is a right module map over the commutant of the
inputs. -/
theorem derivLabel_mul_right (hA : ∀ i, (A i).PosDef) {Z : Matrix n n ℂ}
    (hZ : ∀ i, Commute Z (A i)) (T : MeanTree ι) (j : ι) (X : Matrix n n ℂ) :
    T.derivLabel A j (X * Z) = T.derivLabel A j X * Z := by
  induction T with
  | leaf i =>
    unfold derivLabel
    split_ifs <;> simp
  | node p l r ihl ihr =>
    simp only [derivLabel, _root_.add_apply, ContinuousLinearMap.comp_apply, ihl, ihr,
      Matrix.add_mul]
    rw [geomMeanDerivLeft_mul_right (posDef_eval hA l) (posDef_eval hA r)
        (commute_eval_right hA hZ l) (commute_eval_right hA hZ r) p.2,
      geomMeanDerivRight_mul_right (posDef_eval hA l) (posDef_eval hA r)
        (commute_eval_right hA hZ l) (commute_eval_right hA hZ r) p.2]

/-- **The leaf map is a right module map over the commutant of the inputs**:
`Φ_j(X Z) = Φ_j(X) Z`. -/
theorem leafMap_mul_right (hA : ∀ i, (A i).PosDef) {Z : Matrix n n ℂ}
    (hZ : ∀ i, Commute Z (A i)) (T : MeanTree ι) (j : ι) (X : Matrix n n ℂ) :
    T.leafMap A j (X * Z) = T.leafMap A j X * Z := by
  have hM : Commute Z (T.eval A ^ (-(1 / 2) : ℝ)) :=
    (PosDef.commute_rpow_left (posDef_eval hA T) (commute_eval_right hA hZ T).symm _).symm
  have hAj : Commute Z (A j ^ (1 / 2 : ℝ)) :=
    (PosDef.commute_rpow_left (hA j) (hZ j).symm _).symm
  simp only [leafMap, normalizedDerivMap, FunLike.coe_smul, Pi.smul_apply,
    ContinuousLinearMap.comp_apply, sandwichL_apply]
  rw [sandwich_mul_right hAj, derivLabel_mul_right hA hZ, sandwich_mul_right hM, smul_mul_assoc]

end MeanTree

omit [DecidableEq n] in
/-- The trace adjoint of a right module map over `Z` is a left module map over `Z`. -/
theorem traceAdjointMap_mul_left {Φ : Matrix n n ℂ →ₗ[ℂ] Matrix n n ℂ} {Z : Matrix n n ℂ}
    (h : ∀ X, Φ (X * Z) = Φ X * Z) (Y : Matrix n n ℂ) :
    traceAdjointMap Φ (Z * Y) = Z * traceAdjointMap Φ Y := by
  refine ext_iff_trace_mul_right.mpr fun X => ?_
  have h2 : (Z * traceAdjointMap Φ Y * X).trace = (traceAdjointMap Φ Y * (X * Z)).trace := by
    rw [Matrix.mul_assoc, trace_mul_comm, Matrix.mul_assoc]
  rw [h2, trace_traceAdjointMap_mul, trace_traceAdjointMap_mul, h, ← Matrix.mul_assoc,
    trace_mul_comm, Matrix.mul_assoc, ← Matrix.mul_assoc, trace_mul_comm]

namespace Transport

/-- A matrix commuting with `M` commutes with `M^{-iu}`. -/
theorem commute_imagPow {M Z : Matrix n n ℂ} (h : Commute Z M) (u : ℝ) :
    Commute Z (imagPow M u) := by
  have hlog : Commute Z (CFC.log M) := (Commute.cfc_real h.symm _).symm
  exact (((hlog.smul_right Complex.I).smul_right (-u))).exp_right

/-- **The transport states are fixed by the commutant**: if `Z` commutes with every input
and fixes the root vector `v`, then `Z σ_{j,u} = σ_{j,u}` (`06-transport.tex`, display
`transport:states`). -/
theorem mul_transportState {J : Type*} [DecidableEq J] {T' : MeanTree J}
    {A : J → Matrix n n ℂ} (hA : ∀ j, (A j).PosDef) {Z : Matrix n n ℂ}
    (hZ : ∀ j, Commute Z (A j)) {v : n → ℂ} (hv : Z *ᵥ v = v) (j : J) (u : ℝ) :
    Z * transportState T' A v j u = transportState T' A v j u := by
  have hw : Z *ᵥ (imagPow (T'.eval A) u *ᵥ v) = imagPow (T'.eval A) u *ᵥ v := by
    rw [mulVec_mulVec, (commute_imagPow (MeanTree.commute_eval_right hA hZ T') u).eq,
      ← mulVec_mulVec, hv]
  simp only [transportState]
  rw [← traceAdjointMap_mul_left (fun X => MeanTree.leafMap_mul_right hA hZ T' j X),
    mul_vecMulVec, hw]

/-- A matrix commuting with `M` and fixing `pre` fixes the filtered vector. -/
theorem mulVec_filteredVector {M Z : Matrix n n ℂ} (hM : M.PosDef) (h : Commute Z M)
    {pre : n → ℂ} (hpre : Z *ᵥ pre = pre) : Z *ᵥ filteredVector M pre = filteredVector M pre := by
  have hc : Commute Z (M ^ (-(1 / 4) : ℝ)) := (PosDef.commute_rpow_left hM h.symm _).symm
  rw [filteredVector, mulVec_smul, filteredRaw, mulVec_mulVec, hc.eq, ← mulVec_mulVec, hpre]

end Transport

end Matrix
