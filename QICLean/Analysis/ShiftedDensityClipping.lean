/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.CfcConjugation
import QICLean.Analysis.CommutingHermitian
import QICLean.Analysis.FloorKKT

/-!
# Clipped joint eigenvalues from first-order density inequalities

A commuting pair of density matrices satisfying the first-order inequalities
for a shifted inverse has the clipped eigenvalue form in a common orthonormal
basis.

Source: OpenAI, *Polynomial PEPS approximation of gapped square-grid ground
states*, September 24, 2026, `03-patches.tex`, lines 170–200,
`eq:patch-kkt` and `eq:patch-clipped-eigenvalues`; revision
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace Matrix

variable {k : Type*} [Fintype k] [DecidableEq k]

/-- If the first-order trace inequality holds against every density commuting
with `x`, then `x` and `ρ` have a common unitary eigenbasis in which
`s_i + b = max (p_i / lam) b` for one scalar `0 < lam ≤ 1`.
Both matrices have trace one; no nonsingularity of either density is required.

Source: polynomial-PEPS Proposition 4.1, `03-patches.tex`, lines 170–200,
`eq:patch-kkt` and `eq:patch-clipped-eigenvalues`. -/
theorem PosSemidef.exists_unitary_diagonal_clipped_of_forall_density
    {x ρ : Matrix k k ℂ} (hx : x.PosSemidef) (hρ : ρ.PosSemidef)
    (hxt : x.trace = 1) (hρt : ρ.trace = 1) (hxρ : Commute x ρ)
    {b : ℝ} (hb : 0 < b)
    (hvar : ∀ y : Matrix k k ℂ, y.PosSemidef → y.trace = 1 → Commute x y →
      (ρ * (x + b • (1 : Matrix k k ℂ)) ^ (-1 : ℝ) * y).trace.re ≤
        (ρ * (x + b • (1 : Matrix k k ℂ)) ^ (-1 : ℝ) * x).trace.re) :
    ∃ (U : Matrix k k ℂ) (s p : k → ℝ) (lam : ℝ),
      Uᴴ * U = 1 ∧ U * Uᴴ = 1 ∧
      x = U * diagonal (fun i ↦ (s i : ℂ)) * Uᴴ ∧
      ρ = U * diagonal (fun i ↦ (p i : ℂ)) * Uᴴ ∧
      0 < lam ∧ lam ≤ 1 ∧ ∀ i, s i + b = max (p i / lam) b := by
  obtain ⟨U, s, p, hU, hU', hxs, hρp⟩ :=
    Matrix.exists_unitary_diagonal_of_commute hx.isHermitian hρ.isHermitian hxρ.eq
  let Uu : unitary (Matrix k k ℂ) := ⟨U, by
    simpa only [Unitary.mem_iff, star_eq_conjTranspose] using And.intro hU hU'⟩
  have hdiag (q : k → ℝ) :
      (U * diagonal (fun i ↦ (q i : ℂ)) * Uᴴ).PosSemidef ↔ ∀ i, 0 ≤ q i := by
    simpa only [star_eq_conjTranspose, posSemidef_diagonal_iff, Complex.zero_le_real]
      using Matrix.IsUnit.posSemidef_star_right_conjugate_iff
        (x := diagonal fun i ↦ (q i : ℂ)) (Unitary.isUnit_coe (U := Uu))
  obtain ⟨hs, hp⟩ : (∀ i, 0 ≤ s i) ∧ (∀ i, 0 ≤ p i) :=
    ⟨(hdiag s).mp (hxs ▸ hx), (hdiag p).mp (hρp ▸ hρ)⟩
  have htrace (A : Matrix k k ℂ) : (U * A * Uᴴ).trace = A.trace := by
    rw [trace_mul_cycle, hU, one_mul]
  obtain ⟨hs1, hp1⟩ : (∑ i, s i = 1) ∧ (∑ i, p i = 1) := by
    simpa only [hxs, hρp, htrace, trace_diagonal, Complex.re_sum, Complex.ofReal_re,
      Complex.one_re] using And.intro (congrArg Complex.re hxt) (congrArg Complex.re hρt)
  let Φ := Unitary.conjStarAlgAut ℝ (Matrix k k ℂ) Uu
  have hΦ (A : Matrix k k ℂ) : Φ A = U * A * Uᴴ := rfl
  have hshiftDiag : diagonal (fun i ↦ ((s i + b : ℝ) : ℂ)) =
      diagonal (fun i ↦ (s i : ℂ)) + b • (1 : Matrix k k ℂ) := by
    simpa only [diagonal_smul, diagonal_one', Pi.smul_apply, Pi.one_apply,
      Complex.real_smul, mul_one, Complex.ofReal_add] using
      (diagonal_add (fun i ↦ (s i : ℂ)) (b • (1 : k → ℂ))).symm
  have hshift : x + b • (1 : Matrix k k ℂ) =
      Φ (diagonal (fun i ↦ ((s i + b : ℝ) : ℂ))) := by
    rw [hshiftDiag, map_add, map_smul, map_one, hΦ, ← hxs]
  have hD : (diagonal (fun i ↦ ((s i + b : ℝ) : ℂ))).PosSemidef :=
    posSemidef_diagonal_iff.mpr fun i ↦ Complex.zero_le_real.mpr (add_nonneg (hs i) hb.le)
  have hpowD : (diagonal (fun i ↦ ((s i + b : ℝ) : ℂ))) ^ (-1 : ℝ) =
      diagonal (fun i ↦ (((s i + b)⁻¹ : ℝ) : ℂ)) := by
    simpa only [CFC.rpow_eq_cfc_real hD.nonneg, Real.rpow_neg_one] using
      cfc_diagonal (fun i ↦ s i + b) (fun t : ℝ ↦ t ^ (-1 : ℝ))
        ((Set.finite_range _).continuousOn _)
  have hpow : (x + b • (1 : Matrix k k ℂ)) ^ (-1 : ℝ) =
      Φ (diagonal (fun i ↦ (((s i + b)⁻¹ : ℝ) : ℂ))) := by
    simpa only [hshift, hΦ, Uu, star_eq_conjTranspose, hpowD] using
      rpow_conj_unitary hD (-1) Uu
  have hpair (q : k → ℝ) :
      (ρ * (x + b • (1 : Matrix k k ℂ)) ^ (-1 : ℝ) *
        Φ (diagonal (fun i ↦ (q i : ℂ)))).trace.re =
      ∑ i, p i / (s i + b) * q i := by
    rw [hρp, hpow, ← hΦ, ← map_mul, ← map_mul, hΦ, htrace,
      diagonal_mul_diagonal, diagonal_mul_diagonal, trace_diagonal]
    simp only [← Complex.ofReal_mul, Complex.re_sum,
      Complex.ofReal_re, div_eq_mul_inv]
  have hscalar (q : k → ℝ) (hq : ∀ i, 0 ≤ q i) (hq1 : ∑ i, q i = 1) :
      (∑ i, p i / (s i + b) * q i) ≤ ∑ i, p i / (s i + b) * s i := by
    have hqpos : (Φ (diagonal (fun i ↦ (q i : ℂ)))).PosSemidef := by
      rw [hΦ]
      exact (hdiag q).mpr hq
    have hqt : (Φ (diagonal (fun i ↦ (q i : ℂ)))).trace = 1 := by
      rw [hΦ, htrace, trace_diagonal, ← Complex.ofReal_sum, hq1, Complex.ofReal_one]
    have hqc : Commute x (Φ (diagonal (fun i ↦ (q i : ℂ)))) := by
      rw [hxs, ← hΦ]
      exact (commute_diagonal (fun i ↦ (s i : ℂ)) (fun i ↦ (q i : ℂ))).map Φ
    have hpairx : (ρ * (x + b • (1 : Matrix k k ℂ)) ^ (-1 : ℝ) * x).trace.re =
        ∑ i, p i / (s i + b) * s i := by
      simpa only [hΦ, ← hxs] using hpair s
    simpa only [hpair, hpairx] using hvar _ hqpos hqt hqc
  let g : k → ℝ := fun i ↦ p i / (s i + b)
  let lam := ∑ i, s i * g i
  have hgle (i : k) : g i ≤ lam := by
    simpa [g, lam, mul_comm] using
      hscalar (fun j ↦ if j = i then 1 else 0)
        (fun j ↦ by split <;> norm_num) (by simp)
  have hden (i : k) : 0 < s i + b := add_pos_of_nonneg_of_pos (hs i) hb
  have hg (i : k) : 0 ≤ g i := div_nonneg (hp i) (hden i).le
  have hgp (i : k) : g i * (s i + b) = p i := div_mul_cancel₀ _ (hden i).ne'
  have hcomp (i : k) : s i * g i = s i * lam := by
    exact (Finset.sum_eq_sum_iff_of_le
      (fun j _ ↦ mul_le_mul_of_nonneg_left (hgle j) (hs j))).mp
        (by rw [← Finset.sum_mul, hs1, one_mul]) i (Finset.mem_univ i)
  have hlampos : 0 < lam := by
    obtain ⟨i, _, hi⟩ := (Finset.sum_pos_iff_of_nonneg (fun i _ ↦ hp i)).mp
      (show 0 < ∑ i, p i by rw [hp1]; norm_num)
    exact (div_pos hi (hden i)).trans_le (hgle i)
  have hlamle : lam ≤ 1 := by
    calc
      lam ≤ ∑ i, p i := Finset.sum_le_sum fun i _ ↦ by
        have := hgp i
        have := mul_nonneg (hg i) hb.le
        nlinarith
      _ = 1 := hp1
  refine ⟨U, s, p, lam, hU, hU', hxs, hρp, hlampos, hlamle, ?_⟩
  intro i
  by_cases hi : s i = 0
  · have hgi : g i * b = p i := by simpa only [hi, zero_add] using hgp i
    have hpi : p i / lam ≤ b := (div_le_iff₀ hlampos).mpr (by
      have := mul_le_mul_of_nonneg_right (hgle i) hb.le
      nlinarith)
    rw [hi, zero_add, max_eq_right hpi]
  · have hgi : g i = lam := mul_left_cancel₀ hi (hcomp i)
    have hpi : p i / lam = s i + b := (div_eq_iff hlampos.ne').mpr (by
      simpa only [hgi, mul_comm] using (hgp i).symm)
    rw [hpi, max_eq_left (le_add_of_nonneg_left (hs i))]

end Matrix
