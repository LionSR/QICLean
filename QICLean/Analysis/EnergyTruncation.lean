/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.ShiftedDensityTruncation
import QICLean.Analysis.GroundEnergyBounds
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Restrict
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Truncating the high spectrum of a Hermitian matrix

For a Hermitian matrix `A` and an energy `τ`, the truncation replaces every eigenvalue above `τ`
by `τ` and keeps the others:
`Ã = A P_{(-∞, τ)} + τ P_{[τ, ∞)}`, where `P_{[τ, ∞)}` is the spectral projection of `A` onto
eigenvalues at least `τ`. In the functional calculus, `Ã = min (A, τ)`.

This is the truncation of a local term in Arad, Kuwahara and Landau, *Connecting global and
local energy distributions in quantum spin models on a lattice* (arXiv:1406.3898,
`low70.tex`, Definition `def:Ht`, lines 684–697), and the hard truncation of Arad, Landau,
Vazirani and Vidick (arXiv:1602.08828v2, `local_alg_arxiv_v2.tex`, Definition
`def:hard-trunc`, lines 873–886), where `A = H_J` and `τ = ε_J + t`.

The truncation is Hermitian, commutes with `A`, lies below `A` and below `τ`, and lies above
every lower bound of the spectrum of `A` that is at most `τ`.

## Main statements

* `Matrix.energyTruncation`: the truncation `min (A, τ)`.
* `Matrix.IsHermitian.energyTruncation_eq`: the form `A (1 - P_{[τ, ∞)}) + τ P_{[τ, ∞)}`.
* `Matrix.IsHermitian.energyTruncation_le`, `energyTruncation_le_smul_one`,
  `smul_one_le_energyTruncation`: the order bounds.
-/

open scoped Matrix ComplexOrder MatrixOrder

noncomputable section

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n] {A : Matrix n n ℂ}

/-- The truncation of `A` at the energy `τ`: every eigenvalue above `τ` is replaced by `τ`.
Arad, Kuwahara and Landau, arXiv:1406.3898, Definition `def:Ht`; Arad, Landau, Vazirani and
Vidick, arXiv:1602.08828v2, Definition `def:hard-trunc`. -/
def energyTruncation (A : Matrix n n ℂ) (τ : ℝ) : Matrix n n ℂ :=
  cfc (fun t : ℝ ↦ min t τ) A

/-- The truncation in the form of the sources: `A P_{(-∞, τ)} + τ P_{[τ, ∞)}`. -/
theorem IsHermitian.energyTruncation_eq (hA : A.IsHermitian) (τ : ℝ) :
    energyTruncation A τ =
      A * (1 - spectralProjectionGE A τ) + (τ : ℂ) • spectralProjectionGE A τ := by
  have hc (f : ℝ → ℝ) : ContinuousOn f (spectrum ℝ A) := A.finite_real_spectrum.continuousOn f
  have hP : spectralProjectionGE A τ = cfc (fun t : ℝ ↦ if τ ≤ t then 1 else 0) A := rfl
  have h1 : (1 : Matrix n n ℂ) = cfc (fun _ : ℝ ↦ (1 : ℝ)) A := by
    rw [cfc_const (1 : ℝ) A hA.isSelfAdjoint, map_one]
  have hid : A = cfc (fun t : ℝ ↦ t) A := (cfc_id' ℝ A hA.isSelfAdjoint).symm
  have hτ : (τ : ℂ) • spectralProjectionGE A τ =
      cfc (fun t : ℝ ↦ τ * if τ ≤ t then 1 else 0) A := by
    rw [cfc_const_mul τ _ A (hc _), hP, ← Complex.coe_smul]
  rw [hτ, hP, h1]
  conv_rhs => lhs; lhs; rw [hid]
  rw [← cfc_sub (fun _ : ℝ ↦ (1 : ℝ)) _ A (hc _) (hc _), ← _root_.cfc_mul _ _ A (hc _) (hc _),
    ← _root_.cfc_add (a := A) (fun t : ℝ ↦ t * (1 - if τ ≤ t then 1 else 0))
      (fun t : ℝ ↦ τ * if τ ≤ t then 1 else 0) (hc _) (hc _), energyTruncation]
  congr 1
  funext t
  split_ifs with h
  · simp [min_eq_right h]
  · push Not at h
    simp [min_eq_left h.le]

/-- The truncation is Hermitian. -/
theorem isHermitian_energyTruncation (A : Matrix n n ℂ) (τ : ℝ) :
    (energyTruncation A τ).IsHermitian :=
  (cfc_predicate _ A : IsSelfAdjoint (energyTruncation A τ))

/-- The truncation commutes with `A`. -/
theorem IsHermitian.commute_energyTruncation (hA : A.IsHermitian) (τ : ℝ) :
    Commute A (energyTruncation A τ) := by
  change A * energyTruncation A τ = energyTruncation A τ * A
  conv_lhs => lhs; rw [← cfc_id' ℝ A hA.isSelfAdjoint]
  conv_rhs => rhs; rw [← cfc_id' ℝ A hA.isSelfAdjoint]
  rw [energyTruncation, ← _root_.cfc_mul (fun t : ℝ ↦ t) (fun t ↦ min t τ) A,
    ← _root_.cfc_mul (fun t ↦ min t τ) (fun t : ℝ ↦ t) A]
  congr 1
  funext t
  exact mul_comm _ _

/-- The truncation lies below `A`. -/
theorem IsHermitian.energyTruncation_le (hA : A.IsHermitian) (τ : ℝ) :
    energyTruncation A τ ≤ A := by
  conv_rhs => rw [← cfc_id' ℝ A hA.isSelfAdjoint]
  exact cfc_mono fun t _ => min_le_left t τ

/-- The truncation lies below `τ`. -/
theorem IsHermitian.energyTruncation_le_smul_one (hA : A.IsHermitian) (τ : ℝ) :
    energyTruncation A τ ≤ (τ : ℂ) • 1 := by
  have h : (τ : ℂ) • (1 : Matrix n n ℂ) = cfc (fun _ : ℝ ↦ τ) A := by
    rw [cfc_const τ A hA.isSelfAdjoint, Algebra.algebraMap_eq_smul_one, ← Complex.coe_smul]
  rw [h]
  exact cfc_mono fun t _ => min_le_right t τ

/-- If every eigenvalue of `A` is at least `ε` and `ε ≤ τ`, the truncation lies above `ε`. -/
theorem IsHermitian.smul_one_le_energyTruncation (hA : A.IsHermitian) {ε τ : ℝ} (hετ : ε ≤ τ)
    (hspec : ∀ t ∈ spectrum ℝ A, ε ≤ t) :
    (ε : ℂ) • 1 ≤ energyTruncation A τ := by
  have h : (ε : ℂ) • (1 : Matrix n n ℂ) = cfc (fun _ : ℝ ↦ ε) A := by
    rw [cfc_const ε A hA.isSelfAdjoint, Algebra.algebraMap_eq_smul_one, ← Complex.coe_smul]
  rw [h]
  exact cfc_mono fun t ht => le_min (hspec t ht) hετ

end Matrix

section

open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace Matrix

/-- Upper clipping at `e+t` preserves a vector at the lower energy `e`.
Auxiliary to ALVV, arXiv:1602.08828v2, `def:hard-trunc`, lines 873–886.
The spectral lower bound is derived from the ambient operator inequality. -/
private theorem cfc_min_mulVec_eq_smul_of_ground_lower_bound
    {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℂ) (hA : A.IsHermitian) (e t : ℝ) (x : n → ℂ)
    (hEA : (e : ℂ) • (1 : Matrix n n ℂ) ≤ A)
    (hx : A *ᵥ x = (e : ℂ) • x) (ht : 0 ≤ t) :
    cfc (fun r : ℝ ↦ min r (e + t)) A *ᵥ x = (e : ℂ) • x ∧
      (e : ℂ) • (1 : Matrix n n ℂ) ≤ cfc (fun r : ℝ ↦ min r (e + t)) A ∧
      cfc (fun r : ℝ ↦ min r (e + t)) A ≤ A := by
  have hspec : ∀ r ∈ spectrum ℝ A, e ≤ r :=
    (algebraMap_le_iff_le_spectrum hA.isSelfAdjoint).mp (by
      simpa only [Algebra.algebraMap_eq_smul_one, Complex.coe_smul] using hEA)
  have he : (e : ℂ) • (1 : Matrix n n ℂ) = cfc (fun _ : ℝ ↦ e) A := by
    rw [cfc_const e A hA.isSelfAdjoint, Algebra.algebraMap_eq_smul_one,
      ← Complex.coe_smul]
  have hlow : (e : ℂ) • (1 : Matrix n n ℂ) ≤
      cfc (fun r : ℝ ↦ min r (e + t)) A := by
    rw [he]
    exact cfc_mono fun r hr ↦ le_min (hspec r hr) (le_add_of_nonneg_right ht)
  have hupp : cfc (fun r : ℝ ↦ min r (e + t)) A ≤ A := by
    conv_rhs => rw [← cfc_id' ℝ A hA.isSelfAdjoint]
    exact cfc_mono fun r _ ↦ min_le_left r (e + t)
  exact ⟨mulVec_eq_smul_of_order_sandwich A _ e x hlow hupp hx, hlow, hupp⟩
end Matrix

open scoped BigOperators ComplexOrder MatrixOrder

namespace Matrix

/-- A common ground vector of the original regional matrices remains in
the kernel of every energy-centered partially clipped sum. This applies
clipping on the full chain and requires no identification of functional
calculus through tensor products. Auxiliary to ALVV,
arXiv:1602.08828v2, `def:hard-trunc`, lines 873–886, and Theorem `t:ais`,
lines 1010–1024. -/
theorem centered_partially_clipped_sum_posSemidef_and_mulVec_eq_zero
    {ι n : Type*} [Fintype ι] [DecidableEq ι] [Fintype n] [DecidableEq n]
    (A : ι → Matrix n n ℂ) (e : ι → ℝ) (t : ℝ) (T : Finset ι)
    (hA : ∀ i, (A i).IsHermitian)
    (he : ∀ i, (e i : ℂ) • (1 : Matrix n n ℂ) ≤ A i)
    (x : n → ℂ) (hx : ∀ i, A i *ᵥ x = (e i : ℂ) • x) (ht : 0 ≤ t) :
    let X := ∑ i, ((if i ∈ T then cfc (fun r : ℝ ↦ min r (e i + t)) (A i)
      else A i) - (e i : ℂ) • (1 : Matrix n n ℂ))
    X.PosSemidef ∧ X *ᵥ x = 0 := by
  intro X
  let F : ι → Matrix n n ℂ := fun i ↦
    if i ∈ T then cfc (fun r : ℝ ↦ min r (e i + t)) (A i) else A i
  have hF (i : ι) : F i *ᵥ x = (e i : ℂ) • x ∧
      (e i : ℂ) • (1 : Matrix n n ℂ) ≤ F i := by
    by_cases hi : i ∈ T
    · obtain ⟨hground, hlow, _⟩ := cfc_min_mulVec_eq_smul_of_ground_lower_bound
        (A i) (hA i) (e i) t x (he i) (hx i) ht
      simpa only [F, ite_eq_left hi] using And.intro hground hlow
    · simpa only [F, ite_eq_right hi] using And.intro (hx i) (he i)
  have hpos : X.PosSemidef :=
    posSemidef_sum Finset.univ fun i _ ↦ le_iff.mp (hF i).2
  have hzero (i : ι) : (F i - (e i : ℂ) • (1 : Matrix n n ℂ)) *ᵥ x = 0 := by
    rw [sub_mulVec, smul_mulVec, one_mulVec, (hF i).1, sub_self]
  exact ⟨hpos, by
    change (∑ i, (F i - (e i : ℂ) • (1 : Matrix n n ℂ))) *ᵥ x = 0
    rw [sum_mulVec]
    exact Finset.sum_eq_zero fun i _ ↦ hzero i⟩
end Matrix

section

open scoped Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator BigOperators

namespace Matrix

/-- A partially clipped centered regional sum has the sum of the clipped
and original unit-bond budgets as an operator-norm bound. Auxiliary to ALVV,
arXiv:1602.08828v2, `def:hard-trunc`, lines 873–886, and `t:ais`, lines 1010–1024.
The separate attained regional minima need not share an eigenvector. -/
theorem centered_partially_clipped_sum_norm_le_budget
    {ι n : Type*} [Fintype ι] [DecidableEq ι] [Fintype n] [DecidableEq n]
    (A : ι → Matrix n n ℂ) (e : ι → ℝ) (c : ι → ℕ) (t : ℝ) (T : Finset ι)
    (hpos : ∀ i, (A i).PosSemidef)
    (hlow : ∀ i, (e i : ℂ) • (1 : Matrix n n ℂ) ≤ A i)
    (hcap : ∀ i, A i ≤ (c i : ℝ) • (1 : Matrix n n ℂ))
    (x : ι → n → ℂ) (hx : ∀ i, A i *ᵥ x i = (e i : ℂ) • x i)
    (hunit : ∀ i, star (x i) ⬝ᵥ x i = 1) (ht : 0 ≤ t)
    (Y : Matrix n n ℂ) (C : ℕ) (hY : Y.PosSemidef)
    (hYC : Y ≤ (C : ℝ) • (1 : Matrix n n ℂ)) :
    let X := (∑ i, ((if i ∈ T then energyTruncation (A i) (e i + t) else A i) -
      (e i : ℂ) • (1 : Matrix n n ℂ))) + Y
    X.PosSemidef ∧
      X ≤ ((∑ i, if i ∈ T then t else (c i : ℝ)) + (C : ℝ)) • 1 ∧
      ‖X‖ ≤ (∑ i, if i ∈ T then t else (c i : ℝ)) + (C : ℝ) := by
  intro X
  let F : ι → Matrix n n ℂ := fun i ↦
    (if i ∈ T then energyTruncation (A i) (e i + t) else A i) -
      (e i : ℂ) • (1 : Matrix n n ℂ)
  let b : ι → ℝ := fun i ↦ if i ∈ T then t else (c i : ℝ)
  have he0 (i : ι) : 0 ≤ e i :=
    (hpos i).nonneg_of_normalized_eigenvector (e i) (x i) (hx i) (hunit i)
  have hspec (i : ι) : ∀ r ∈ spectrum ℝ (A i), e i ≤ r :=
    (algebraMap_le_iff_le_spectrum (hpos i).isHermitian.isSelfAdjoint).mp (by
      simpa only [Algebra.algebraMap_eq_smul_one, Complex.coe_smul] using hlow i)
  have hF (i : ι) : 0 ≤ F i ∧ F i ≤ b i • (1 : Matrix n n ℂ) := by
    by_cases hi : i ∈ T
    · have hmin := (hpos i).isHermitian.smul_one_le_energyTruncation
        (le_add_of_nonneg_right ht) (hspec i)
      have hmax := (hpos i).isHermitian.energyTruncation_le_smul_one (e i + t)
      refine ⟨?_, ?_⟩
      · simpa only [F, ite_eq_left hi] using sub_nonneg.mpr hmin
      · have hshift := sub_le_sub_right hmax ((e i : ℂ) • (1 : Matrix n n ℂ))
        simpa only [F, b, ite_eq_left hi, Complex.coe_smul, add_smul,
          add_sub_cancel_left] using hshift
    · have hei : 0 ≤ (e i : ℂ) • (1 : Matrix n n ℂ) := by
        rw [Complex.coe_smul]
        exact smul_nonneg (he0 i) zero_le_one
      refine ⟨?_, ?_⟩
      · simpa only [F, ite_eq_right hi] using sub_nonneg.mpr (hlow i)
      · simpa only [F, b, ite_eq_right hi] using
          (sub_le_self (A i) hei).trans (hcap i)
  have hb (i : ι) : 0 ≤ b i := by
    dsimp only [b]
    split_ifs
    · exact ht
    · exact Nat.cast_nonneg (c i)
  have hX0 : 0 ≤ X := by
    change 0 ≤ (∑ i, F i) + Y
    exact add_nonneg (Finset.sum_nonneg fun i _ ↦ (hF i).1) hY.nonneg
  have hXcap : X ≤ ((∑ i, b i) + (C : ℝ)) • (1 : Matrix n n ℂ) := by
    change (∑ i, F i) + Y ≤ _
    calc
      _ ≤ (∑ i, b i • (1 : Matrix n n ℂ)) +
          (C : ℝ) • (1 : Matrix n n ℂ) :=
        add_le_add (Finset.sum_le_sum fun i _ ↦ (hF i).2) hYC
      _ = _ := by rw [← Finset.sum_smul, ← add_smul]
  have hbudget : 0 ≤ (∑ i, b i) + (C : ℝ) :=
    add_nonneg (Finset.sum_nonneg fun i _ ↦ hb i) (Nat.cast_nonneg C)
  have hnorm : ‖X‖ ≤ (∑ i, b i) + (C : ℝ) :=
    (CStarAlgebra.norm_le_iff_le_algebraMap X hbudget hX0).mpr (by
      simpa only [Algebra.algebraMap_eq_smul_one] using hXcap)
  exact ⟨nonneg_iff_posSemidef.mp hX0, hXcap, hnorm⟩
end Matrix
end

section

open scoped BigOperators Matrix.Norms.L2Operator

namespace Matrix

/-- Every partially clipped, energy-centered sum commutes with each original
regional matrix when the original matrices commute pairwise. Auxiliary to
the successive truncation argument in ALVV, arXiv:1602.08828v2,
Theorem t:ais, lines 1010–1024. No current-operator or weight commutation
hypothesis, norm estimate or spectral gap is assumed. -/
theorem commute_centered_partially_clipped_sum
    {ι n : Type*} [Fintype ι] [DecidableEq ι] [Fintype n] [DecidableEq n]
    (A : ι → Matrix n n ℂ) (e : ι → ℝ) (t : ℝ) (T : Finset ι)
    (hcomm : Pairwise fun i j ↦ Commute (A i) (A j)) (j : ι) :
    let X := ∑ i, ((if i ∈ T then cfc (fun x : ℝ ↦ min x (e i + t)) (A i)
      else A i) - (e i : ℂ) • (1 : Matrix n n ℂ))
    Commute X (A j) := by
  intro X
  change Commute (∑ i, ((if i ∈ T then
    cfc (fun x : ℝ ↦ min x (e i + t)) (A i) else A i) -
      (e i : ℂ) • (1 : Matrix n n ℂ))) (A j)
  refine Commute.sum_left Finset.univ _ (A j) ?_
  intro i _
  have hij : Commute (A i) (A j) := by
    by_cases heq : i = j
    · simpa only [heq] using Commute.refl (A j)
    · exact hcomm heq
  refine Commute.sub_left ?_ ?_
  · by_cases hi : i ∈ T
    · simpa only [ite_eq_left hi] using
        hij.cfc_real (fun x : ℝ ↦ min x (e i + t))
    · simpa only [ite_eq_right hi] using hij
  · exact (Commute.one_left (A j)).smul_left (e i : ℂ)
end Matrix
end

section

open scoped Matrix ComplexOrder MatrixOrder

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n] {A : Matrix n n ℂ}

/-- A shifted clipping dominates the original high-threshold projection.
Supporting ALVV, arXiv:1602.08828v2, `def:hard-trunc`, lines 873–886,
and Theorem `t:ais`, lines 1010–1024. This is an auxiliary inequality. -/
private theorem IsHermitian.smul_spectralProjectionGE_le_shifted_cfc_min
    (hA : A.IsHermitian) {e0 u t : ℝ} (hu : 0 ≤ u) (hut : u ≤ t)
    (hspec : ∀ x ∈ spectrum ℝ A, e0 ≤ x) :
    (u : ℂ) • spectralProjectionGE A (e0 + u) ≤
      cfc (fun x : ℝ ↦ min x (e0 + t)) A - (e0 : ℂ) • 1 := by
  have hc (f : ℝ → ℝ) : ContinuousOn f (spectrum ℝ A) :=
    A.finite_real_spectrum.continuousOn f
  have hleft : (u : ℂ) • spectralProjectionGE A (e0 + u) =
      cfc (fun x : ℝ ↦ u * if e0 + u ≤ x then 1 else 0) A := by
    rw [cfc_const_mul u _ A (hc _), spectralProjectionGE, ← Complex.coe_smul]
  have hconst : (e0 : ℂ) • (1 : Matrix n n ℂ) =
      cfc (fun _ : ℝ ↦ e0) A := by
    rw [cfc_const e0 A hA.isSelfAdjoint, Algebra.algebraMap_eq_smul_one,
      ← Complex.coe_smul]
  rw [hleft, hconst, ← cfc_sub (fun x : ℝ ↦ min x (e0 + t))
    (fun _ : ℝ ↦ e0) A (hc _) (hc _)]
  apply cfc_mono (hf := hc _) (hg := hc _)
  intro x hx
  by_cases h : e0 + u ≤ x
  · simp only [ite_eq_left h, mul_one]
    have hm : e0 + u ≤ min x (e0 + t) :=
      le_min h (add_le_add le_rfl hut)
    linarith
  · simp only [ite_eq_right h, mul_zero]
    exact sub_nonneg.mpr (le_min (hspec x hx) (by linarith))

/-- The analogous bound for the untruncated shifted regional operator.
Supporting ALVV, arXiv:1602.08828v2, `def:hard-trunc`, lines 873–886,
and Theorem `t:ais`, lines 1010–1024. -/
private theorem IsHermitian.smul_spectralProjectionGE_le_shifted_self
    (hA : A.IsHermitian) {e0 u : ℝ} (hu : 0 ≤ u)
    (hspec : ∀ x ∈ spectrum ℝ A, e0 ≤ x) :
    (u : ℂ) • spectralProjectionGE A (e0 + u) ≤ A - (e0 : ℂ) • 1 := by
  have hc (f : ℝ → ℝ) : ContinuousOn f (spectrum ℝ A) :=
    A.finite_real_spectrum.continuousOn f
  apply (hA.smul_spectralProjectionGE_le_shifted_cfc_min hu le_rfl hspec).trans
  apply sub_le_sub_right
  conv_rhs => rw [← cfc_id' ℝ A hA.isSelfAdjoint]
  exact cfc_mono (fun x _ ↦ min_le_left x (e0 + u)) (hc _) (hc _)
end Matrix

open scoped BigOperators ComplexOrder MatrixOrder

namespace Matrix

/-- A centered sum of original regional operators and their upper clippings
dominates the original high-energy projection of any selected region.
All spectral lower bounds are derived from the original matrix inequalities.
Auxiliary to ALVV, arXiv:1602.08828v2, Definition `def:hard-trunc`,
lines 873–886, and Theorem `t:ais`, lines 1010–1024. -/
theorem spectralProjectionGE_le_centered_partially_clipped_sum
    {ι n : Type*} [Fintype ι] [DecidableEq ι] [Fintype n] [DecidableEq n]
    (A : ι → Matrix n n ℂ) (e : ι → ℝ) (t u : ℝ) (T : Finset ι)
    (hA : ∀ i, (A i).IsHermitian)
    (he : ∀ i, (e i : ℂ) • (1 : Matrix n n ℂ) ≤ A i)
    (hu : 0 ≤ u) (hut : u ≤ t) (j : ι) :
    u • spectralProjectionGE (A j) (e j + u) ≤
      ∑ i, ((if i ∈ T then cfc (fun x : ℝ ↦ min x (e i + t)) (A i)
        else A i) - (e i : ℂ) • (1 : Matrix n n ℂ)) := by
  have ht : 0 ≤ t := hu.trans hut
  have hspec (i : ι) : ∀ x ∈ spectrum ℝ (A i), e i ≤ x :=
    (algebraMap_le_iff_le_spectrum (hA i).isSelfAdjoint).mp (by
      simpa only [Algebra.algebraMap_eq_smul_one, Complex.coe_smul] using he i)
  let F : ι → Matrix n n ℂ := fun i ↦
    (if i ∈ T then cfc (fun x : ℝ ↦ min x (e i + t)) (A i) else A i) -
      (e i : ℂ) • (1 : Matrix n n ℂ)
  have hnonneg (i : ι) : 0 ≤ F i := by
    by_cases hi : i ∈ T
    · have h := (hA i).smul_spectralProjectionGE_le_shifted_cfc_min
        (e0 := e i) (u := 0) (t := t) le_rfl ht (hspec i)
      simpa only [F, ite_eq_left hi, Complex.ofReal_zero, zero_smul] using h
    · simpa only [F, ite_eq_right hi] using sub_nonneg.mpr (he i)
  have hselected : (u : ℂ) • spectralProjectionGE (A j) (e j + u) ≤ F j := by
    by_cases hj : j ∈ T
    · simpa only [F, ite_eq_left hj] using
        (hA j).smul_spectralProjectionGE_le_shifted_cfc_min hu hut (hspec j)
    · simpa only [F, ite_eq_right hj] using
        (hA j).smul_spectralProjectionGE_le_shifted_self hu (hspec j)
  have hsum : F j ≤ ∑ i, F i :=
    Finset.single_le_sum (fun i _ ↦ hnonneg i) (Finset.mem_univ j)
  simpa only [Complex.coe_smul, F] using hselected.trans hsum
end Matrix
end
end

section

open scoped BigOperators

/-- Common energy shifts cancel from the difference of an original finite
sum and its partially replaced sum. The discrepancy is precisely the sum
of excesses on the replaced indices. Auxiliary to ALVV,
arXiv:1602.08828v2, Corollary c:goodagsphardtrunc, lines 979–1005;
this is an additive identity, not a norm or truncation estimate. -/
private theorem sum_centered_sub_partially_replaced_eq
    {ι M : Type*} [Fintype ι] [DecidableEq ι] [AddCommGroup M]
    (A F C : ι → M) (T : Finset ι) :
    (∑ i, (A i - C i)) - (∑ i, ((if i ∈ T then F i else A i) - C i)) =
      ∑ i ∈ T, (A i - F i) := by
  rw [← Finset.sum_sub_distrib]
  calc
    (∑ i, ((A i - C i) - ((if i ∈ T then F i else A i) - C i))) =
        ∑ i, if i ∈ T then A i - F i else 0 := by
      refine Finset.sum_congr rfl ?_
      intro i _
      by_cases hi : i ∈ T
      · simp only [sub_sub_sub_cancel_right, ite_eq_left hi]
      · simp only [ite_eq_right hi, sub_self]
    _ = ∑ i ∈ T, (A i - F i) := Finset.sum_ite_mem_eq T (fun i ↦ A i - F i)

open scoped BigOperators Matrix.Norms.L2Operator

namespace Matrix

/-- The discrepancy on any actual subspace is bounded by the sum of the
restricted excess norms on precisely the clipped indices. Common scalar
energy shifts cancel algebraically. Auxiliary to ALVV,
arXiv:1602.08828v2, Corollary c:goodagsphardtrunc, lines 979–1005.
Neither a total discrepancy identity nor a norm bound is supplied. -/
theorem norm_centered_clipping_discrepancy_domRestrict_le_sum
    {ι n : Type*} [Fintype ι] [DecidableEq ι] [Fintype n] [DecidableEq n]
    (A F : ι → Matrix n n ℂ) (C : ι → ℂ) (T : Finset ι)
    (G : Submodule ℂ (EuclideanSpace ℂ n)) :
    let φ := Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ)
    ‖(φ ((∑ i, (A i - C i • 1)) -
      (∑ i, ((if i ∈ T then F i else A i) - C i • 1)))).domRestrict G‖ ≤
      ∑ i ∈ T, ‖(φ (A i - F i)).domRestrict G‖ := by
  intro φ
  rw [sum_centered_sub_partially_replaced_eq A F (fun i ↦ C i • 1) T]
  simpa only [map_sum, ContinuousLinearMap.domRestrict,
    ContinuousLinearMap.finsetSum_comp] using
      (norm_sum_le T (fun i ↦ (φ (A i - F i)).domRestrict G))
end Matrix
end
