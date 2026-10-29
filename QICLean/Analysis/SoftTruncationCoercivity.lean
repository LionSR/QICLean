/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.ShiftedSoftHardTruncation

/-!
# Centered soft truncation and high-energy projections

Replacing one centered regional term by its actual soft truncation preserves
the hard high-projection lower bound, up to the scalar error
`(t / 2) * (1 / 2) ^ m`. The argument uses the checked shifted soft/hard
comparison and the original hard projection order theorem.

These are matrix-order auxiliaries to ALVV, arXiv:1602.08828v2,
`def:hard-trunc` and `def:soft-trunc`, lines 873–886 and 1178–1185.
They do not assert a physical spectral comparison. In the later physical
application with scale equal to order, the condition
`m / 2 ≥ 17 + eta + alpha` is retained explicitly.
-/

open scoped BigOperators Matrix ComplexOrder MatrixOrder

namespace Matrix

/-- One actual soft replacement dominates the original selected high-energy
projection after adding its scalar order error. Positivity is obtained from
the same hard comparison. No commutativity or attained-minimum hypothesis
is needed for this order assertion. Auxiliary to ALVV,
arXiv:1602.08828v2, `def:soft-trunc`, lines 1178–1185. -/
theorem softTruncation_centered_coercivity
    {ι n : Type*} [Fintype ι] [DecidableEq ι] [Fintype n] [DecidableEq n]
    (A : ι → Matrix n n ℂ) (e : ι → ℝ) (j : ι) (eps t u : ℝ) (m : ℕ)
    (hA : ∀ i, (A i).IsHermitian)
    (he : ∀ i, (e i : ℂ) • (1 : Matrix n n ℂ) ≤ A i)
    (hepslo : e j - 10 ≤ eps) (hepshi : eps ≤ e j)
    (ht : 0 < t) (hm : 1 ≤ m) (hu : 0 ≤ u) (hut : u ≤ t / 2 - 10) :
    let alpha : ℝ := (t / 2) * (1 / 2 : ℝ) ^ m
    let F := (eps : ℂ) • (1 : Matrix n n ℂ) +
      cfc (Real.softTruncation t m) (A j - (eps : ℂ) • 1)
    let X := ∑ i, ((if i = j then F else A i) - (e i : ℂ) • 1)
    (X + (alpha : ℂ) • 1).PosSemidef ∧
      u • spectralProjectionGE (A j) (e j + u) ≤ X + (alpha : ℂ) • 1 := by
  intro alpha F X
  classical
  have hmin : (e j : ℝ) • (1 : Matrix n n ℂ) ≤ A j := by
    simpa only [Complex.coe_smul] using he j
  have heps : eps • (1 : Matrix n n ℂ) ≤ (e j : ℝ) • 1 :=
    smul_le_smul_of_nonneg_right hepshi zero_le_one
  have hpos : (A j - (eps : ℂ) • 1).PosSemidef := by
    apply Matrix.le_iff.mp
    simpa only [Complex.coe_smul] using heps.trans hmin
  have hsoft := ((hA j).softTruncation_shifted_hard_bounds
    (e j) eps t m hpos hepslo ht hm).1
  have hcut : e j + (t / 2 - 10) = e j + t / 2 - 10 := by ring
  rw [← hcut] at hsoft
  change energyTruncation (A j) (e j + (t / 2 - 10)) - (alpha : ℂ) • 1 ≤ F at hsoft
  let B := ∑ i, ((if i ∈ ({j} : Finset ι) then
    cfc (fun x : ℝ ↦ min x (e i + (t / 2 - 10))) (A i) else A i) - (e i : ℂ) • 1)
  have hcompare : B ≤ X + (alpha : ℂ) • 1 := by
    have hterm (i : ι) :
        ((if i ∈ ({j} : Finset ι) then
          cfc (fun x : ℝ ↦ min x (e i + (t / 2 - 10))) (A i) else A i) -
            (e i : ℂ) • 1) ≤
        ((if i = j then F else A i) - (e i : ℂ) • 1) +
          (if i = j then (alpha : ℂ) • (1 : Matrix n n ℂ) else 0) := by
      by_cases hij : i = j
      · subst i
        simp only [Finset.mem_singleton, ite_true]
        have hc : energyTruncation (A j) (e j + (t / 2 - 10)) ≤
            F + (alpha : ℂ) • 1 := sub_le_iff_le_add.mp hsoft
        change energyTruncation (A j) (e j + (t / 2 - 10)) - (e j : ℂ) • 1 ≤ _
        exact (sub_le_sub_right hc _).trans_eq (by abel)
      · simp [hij]
    have hsum := Finset.sum_le_sum fun i (_hi : i ∈ (Finset.univ : Finset ι)) ↦ hterm i
    simpa only [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, ite_true, B, X]
      using hsum
  have hzero := spectralProjectionGE_le_centered_partially_clipped_sum
    A e (t / 2 - 10) 0 {j} hA he le_rfl (hu.trans hut) j
  have hnonneg : 0 ≤ B := by simpa only [zero_smul] using hzero
  refine ⟨Matrix.nonneg_iff_posSemidef.mp (hnonneg.trans hcompare), ?_⟩
  exact (spectralProjectionGE_le_centered_partially_clipped_sum
    A e (t / 2 - 10) u {j} hA he hu hut j).trans hcompare

end Matrix

namespace Real

/-- The explicit cutoff for a reverse soft-window weight lies below the hard
comparator cutoff when the scale condition is retained. The bounds on the
actual centered soft ground energy and the boundary constant are inputs to
this scalar auxiliary; they must be derived from the physical Hamiltonian.
Supporting ALVV, arXiv:1602.08828v2, `lem:exp-approx`, lines 1195–1255. -/
theorem softTruncation_reverse_cutoff_bounds
    (m : ℕ) (E eta C : ℝ)
    (hElow : -((m : ℝ) / 2 * (1 / 2 : ℝ) ^ m) ≤ E) (hEhigh : E ≤ 2)
    (heta : 0 ≤ eta) (hC0 : 0 ≤ C) (hC4 : C ≤ 4)
    (hscale : 17 + eta + (m : ℝ) / 2 * (1 / 2 : ℝ) ^ m ≤ (m : ℝ) / 2) :
    let alpha := (m : ℝ) / 2 * (1 / 2 : ℝ) ^ m
    let u := E + alpha + eta + C + 1
    0 ≤ u ∧ u ≤ (m : ℝ) / 2 - 10 ∧ u ≤ 7 + eta + alpha ∧
      C < u - (E + alpha + eta) ∧ u - (E + alpha + eta) - C = 1 := by
  intro alpha u
  have hu : u ≤ 7 + eta + alpha := by
    dsimp only [u]
    linarith only [hEhigh, hC4]
  refine ⟨?_, ?_, hu, ?_, ?_⟩
  · dsimp only [u, alpha]
    linarith only [hElow, heta, hC0]
  · dsimp only [alpha] at hu
    linarith only [hu, hscale]
  · dsimp only [u]
    linarith
  · dsimp only [u]
    ring

end Real
