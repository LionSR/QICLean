/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.FunctionalCalculus.CfcConjugation
import QICLean.Spectral.Filter.SoftTruncationHardResidual

/-!
# A high-energy floor for the actual soft truncation

Monotonicity and the polynomial remainder give a quantitative lower bound above a chosen
energy threshold. The resulting same-matrix projection order is an input to a reverse
low-energy estimate; no reverse residual or spectral gap is assumed or asserted here.
This auxiliary supports ALVV, arXiv:1602.08828v2, `lem:exp-approx`, lines 1195–1255.
The independent soft scale and order remain explicit.

It also contains the following results.

* `Matrix.IsHermitian.softTruncation_estimated_center_bounds`,
  `Matrix.softTruncation_commuting_family_bounds`: estimated-center soft replacements of commuting
  regional matrices.
-/

section SoftTruncationHighProjection

namespace Real

/-- Above a nonnegative threshold, the soft function is bounded below by that threshold
minus its actual polynomial remainder bound. Auxiliary to ALVV, arXiv:1602.08828v2,
`lem:exp-approx`, lines 1195–1255. -/
theorem softTruncation_high_energy_floor
    (t : ℝ) (m : ℕ) (T x : ℝ) (ht : 0 < t) (hm : 1 ≤ m)
    (hT : 0 ≤ T) (hTx : T ≤ x) :
    T - (t / (m : ℝ)) * (T / t) ^ m ≤ softTruncation t m x := by
  have hband := (softTruncation_bounds t m T ht hm hT).2.2.1
  have hmono := monotoneOn_softTruncation t m ht hT (hT.trans hTx) hTx
  linarith only [hband, hmono]

/-- At scale at least twice the low-energy width plus sixteen, every order at least two
leaves a positive reverse Sylvester denominator. The energy and bond-count bounds are
explicit inputs to this scalar auxiliary; a physical application must derive them.
ALVV, arXiv:1602.08828v2, `lem:exp-approx`, lines 1195–1255. -/
theorem softTruncation_reverse_barrier_margin
    (t : ℝ) (m : ℕ) (eta E : ℝ) (c : ℕ)
    (hm : 2 ≤ m) (heta : 0 ≤ eta) (hE : E ≤ 2) (hc : c ≤ 2)
    (hscale : 2 * (eta + 8) ≤ t) :
    let U := 2 * (eta + 8)
    let b := U - (t / (m : ℝ)) * (U / t) ^ m
    0 ≤ U ∧ eta + 8 ≤ b ∧
      (∀ x, U ≤ x → b ≤ softTruncation t m x) ∧
      2 ≤ b - (E + eta) - 2 * (c : ℝ) := by
  intro U b
  have hU : 0 ≤ U := by dsimp only [U]; linarith only [heta]
  have ht : 0 < t := by linarith only [hscale, heta]
  have hUt : U ≤ t := hscale
  have hm' : 1 ≤ m := by omega
  have hmcast : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hb0 : 0 ≤ U / t := div_nonneg hU ht.le
  have hb1 : U / t ≤ 1 := (div_le_one ht).mpr hUt
  have hp : (U / t) ^ m ≤ U / t := by
    simpa only [pow_one] using pow_le_pow_of_le_one hb0 hb1 hm'
  have herror : (t / (m : ℝ)) * (U / t) ^ m ≤ U / 2 := by
    calc
      _ ≤ (t / (m : ℝ)) * (U / t) :=
        mul_le_mul_of_nonneg_left hp (by positivity)
      _ = U / (m : ℝ) := by field_simp
      _ ≤ U / 2 := div_le_div_of_nonneg_left hU (by norm_num) hmcast
  have hfloor : eta + 8 ≤ b := by dsimp only [b, U] at *; linarith only [herror]
  have hc' : (c : ℝ) ≤ 2 := by exact_mod_cast hc
  refine ⟨hU, hfloor,
    fun x hx ↦ softTruncation_high_energy_floor t m U x ht hm' hU hx, ?_⟩
  linarith only [hfloor, hE, hc']

end Real

open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder

namespace Matrix

/-- The actual soft function of an energy-centered Hermitian matrix dominates the original
high-energy projection with the derived floor. The lower regional energy is explicit;
no commutativity or high-projection inequality is supplied. Auxiliary to ALVV,
arXiv:1602.08828v2, `lem:exp-approx`, lines 1195–1255. -/
theorem IsHermitian.smul_spectralProjectionGE_le_softTruncation
    {ι : Type*} [Fintype ι] [DecidableEq ι] {A : Matrix ι ι ℂ}
    (hA : A.IsHermitian) (e t T : ℝ) (m : ℕ)
    (he : (e : ℂ) • (1 : Matrix ι ι ℂ) ≤ A)
    (ht : 0 < t) (hm : 1 ≤ m) (hT : 0 ≤ T) :
    (T - (t / (m : ℝ)) * (T / t) ^ m) • spectralProjectionGE A (e + T) ≤
      cfc (Real.softTruncation t m) (A - (e : ℂ) • 1) := by
  have hc (f : ℝ → ℝ) : ContinuousOn f (spectrum ℝ A) :=
    A.finite_real_spectrum.continuousOn f
  have hspec : ∀ x ∈ spectrum ℝ A, e ≤ x :=
    (algebraMap_le_iff_le_spectrum hA.isSelfAdjoint).mp (by
      simpa only [Algebra.algebraMap_eq_smul_one, Complex.coe_smul] using he)
  rw [hA.cfc_sub_smul_one (Real.softTruncation t m) e]
  change (T - (t / (m : ℝ)) * (T / t) ^ m) •
    cfc (fun x : ℝ ↦ if e + T ≤ x then 1 else 0) A ≤ _
  rw [← cfc_smul _ _ A (hc _)]
  refine cfc_mono (fun x hx ↦ ?_) (hc _) (hc _)
  by_cases hhigh : e + T ≤ x
  · simp only [hhigh, ite_true, smul_eq_mul, mul_one]
    exact Real.softTruncation_high_energy_floor t m T (x - e) ht hm hT (by linarith)
  · simp only [hhigh, ite_false, smul_zero]
    exact (Real.softTruncation_bounds t m (x - e) ht hm
      (sub_nonneg.mpr (hspec x hx))).1

end Matrix

end SoftTruncationHighProjection

section SoftTruncationCommutingFamily

/-!
## Estimated-center soft replacements of commuting regional matrices

Every soft replacement is constructed from the original matrix and an estimated lower
energy in the source's ten-unit interval. A scalar correction restores positivity and the
actual high-projection floor. These generic order results support the physical simultaneous
regional construction in ALVV, arXiv:1602.08828v2, `def:soft-trunc`, lines 1178–1185,
and `t:aisefficient`, lines 1373–1392. They do not supply or assume a reverse residual,
physical boundary estimate, gap or efficient-filter conclusion.
-/

open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder

namespace Matrix

/-- A literal estimated-center soft replacement has a derived ten-unit positive correction,
order below the original centered matrix, preserved commutation and an actual high-energy
projection floor. Auxiliary to ALVV, arXiv:1602.08828v2, `def:soft-trunc`, lines 1178–1185. -/
theorem IsHermitian.softTruncation_estimated_center_bounds
    {n : Type*} [Fintype n] [DecidableEq n] {A : Matrix n n ℂ}
    (hA : A.IsHermitian) (e p t : ℝ) (m : ℕ)
    (he : (e : ℂ) • (1 : Matrix n n ℂ) ≤ A)
    (hpl : e - 10 ≤ p) (hpu : p ≤ e) (ht : 0 < t) (hm : 1 ≤ m) :
    let F := (p : ℂ) • 1 + cfc (Real.softTruncation t m) (A - (p : ℂ) • 1) -
      (e : ℂ) • 1
    (F + (10 : ℂ) • 1).PosSemidef ∧ F ≤ A - (e : ℂ) • 1 ∧
      (∀ C : Matrix n n ℂ, Commute A C → Commute F C) ∧
      ∀ U : ℝ, 0 ≤ U →
        (U - (t / (m : ℝ)) * (U / t) ^ m) • spectralProjectionGE A (p + U) ≤
          F + (10 : ℂ) • 1 := by
  intro F
  have hp : (p : ℂ) • (1 : Matrix n n ℂ) ≤ A := by
    have hpe : (p : ℂ) • (1 : Matrix n n ℂ) ≤ (e : ℂ) • 1 := by
      simpa only [Complex.coe_smul] using smul_le_smul_of_nonneg_right hpu
        (zero_le_one : (0 : Matrix n n ℂ) ≤ 1)
    exact hpe.trans he
  let X := A - (p : ℂ) • 1
  have hX : X.PosSemidef := le_iff.mp hp
  have hf0 : 0 ≤ cfc (Real.softTruncation t m) X :=
    cfc_nonneg fun x hx ↦ (Real.softTruncation_bounds t m x ht hm
      (spectrum_nonneg_of_nonneg hX.nonneg hx)).1
  have hfX : cfc (Real.softTruncation t m) X ≤ X := by
    conv_rhs => rw [← cfc_id' ℝ X hX.isHermitian.isSelfAdjoint]
    exact cfc_mono (fun x hx ↦ (Real.softTruncation_bounds t m x ht hm
      (spectrum_nonneg_of_nonneg hX.nonneg hx)).2.1)
      (X.finite_real_spectrum.continuousOn _) (X.finite_real_spectrum.continuousOn _)
  have hsc : 0 ≤ (((p - e + 10 : ℝ) : ℂ) • (1 : Matrix n n ℂ)) := by
    rw [Complex.coe_smul]
    exact smul_nonneg (by linarith only [hpl]) zero_le_one
  have hcorr : F + (10 : ℂ) • 1 = cfc (Real.softTruncation t m) X +
      ((p - e + 10 : ℝ) : ℂ) • 1 := by
    dsimp only [F]
    simp only [Complex.ofReal_add, Complex.ofReal_sub, Complex.ofReal_ofNat,
      add_smul, sub_smul]
    abel
  have hfF : cfc (Real.softTruncation t m) X ≤ F + (10 : ℂ) • 1 := by
    rw [hcorr]
    exact le_add_of_nonneg_right hsc
  have hFpos : (F + (10 : ℂ) • 1).PosSemidef := by
    rw [hcorr]
    exact (nonneg_iff_posSemidef.mp hf0).add (nonneg_iff_posSemidef.mp hsc)
  refine ⟨hFpos, ?_, ?_, ?_⟩
  · have hsum : (p : ℂ) • 1 + cfc (Real.softTruncation t m) X ≤ A := by
      exact (_root_.add_le_add (le_refl ((p : ℂ) • (1 : Matrix n n ℂ))) hfX).trans_eq
        (by dsimp only [X]; abel)
    exact sub_le_sub_right hsum _
  · intro C hAC
    have hfc : Commute (cfc (Real.softTruncation t m) X) C := by
      rw [show X = A - (p : ℂ) • 1 from rfl,
        hA.cfc_sub_smul_one (Real.softTruncation t m) p]
      exact hAC.cfc_real (fun x : ℝ ↦ Real.softTruncation t m (x - p))
    exact (((Commute.one_left C).smul_left (p : ℂ)).add_left hfc).sub_left
      ((Commute.one_left C).smul_left (e : ℂ))
  · intro U hU
    exact (hA.smul_spectralProjectionGE_le_softTruncation p t U m hp ht hm hU).trans hfF

/-- A finite selected family of actual estimated-center soft replacements has a common
positive correction and simultaneous high-projection floors. Commutation with every
original block is derived from pairwise commutation of the original blocks, even after
several soft replacements. Auxiliary to ALVV, arXiv:1602.08828v2,
`def:soft-trunc` and `t:aisefficient`, lines 1178–1185 and 1373–1392. -/
theorem softTruncation_commuting_family_bounds
    {ι n : Type*} [Fintype ι] [DecidableEq ι] [Fintype n] [DecidableEq n]
    (A : ι → Matrix n n ℂ) (e p : ι → ℝ) (S : Finset ι)
    (hA : ∀ i, (A i).IsHermitian)
    (he : ∀ i, (e i : ℂ) • (1 : Matrix n n ℂ) ≤ A i)
    (hpl : ∀ i ∈ S, e i - 10 ≤ p i) (hpu : ∀ i ∈ S, p i ≤ e i)
    (hcomm : Pairwise fun i j ↦ Commute (A i) (A j))
    (t : ℝ) (m : ℕ) (ht : 0 < t) (hm : 1 ≤ m) :
    let F := fun i ↦ (if i ∈ S then (p i : ℂ) • 1 +
      cfc (Real.softTruncation t m) (A i - (p i : ℂ) • 1) else A i) - (e i : ℂ) • 1
    let B := ∑ i, F i
    let D := 10 * (S.card : ℝ)
    (B + (D : ℂ) • 1).PosSemidef ∧ B ≤ ∑ i, (A i - (e i : ℂ) • 1) ∧
      (∀ j, Commute B (A j)) ∧
      ∀ j ∈ S, ∀ U : ℝ, 0 ≤ U →
        (U - (t / (m : ℝ)) * (U / t) ^ m) • spectralProjectionGE (A j) (p j + U) ≤
          B + (D : ℂ) • 1 := by
  classical
  intro F B D
  let K := fun i ↦ F i + (if i ∈ S then (10 : ℂ) • 1 else 0)
  have hsel (i : ι) (hi : i ∈ S) :
      (F i + (10 : ℂ) • 1).PosSemidef ∧ F i ≤ A i - (e i : ℂ) • 1 ∧
        (∀ C : Matrix n n ℂ, Commute (A i) C → Commute (F i) C) ∧
        ∀ U : ℝ, 0 ≤ U →
          (U - (t / (m : ℝ)) * (U / t) ^ m) • spectralProjectionGE (A i) (p i + U) ≤
            F i + (10 : ℂ) • 1 := by
    simpa only [F, ite_eq_left hi] using (hA i).softTruncation_estimated_center_bounds
      (e i) (p i) t m (he i) (hpl i hi) (hpu i hi) ht hm
  have hK (i : ι) : (K i).PosSemidef := by
    by_cases hi : i ∈ S
    · simpa only [K, ite_eq_left hi] using (hsel i hi).1
    · simpa only [K, F, ite_eq_right hi, add_zero] using le_iff.mp (he i)
  have hFle (i : ι) : F i ≤ A i - (e i : ℂ) • 1 := by
    by_cases hi : i ∈ S
    · exact (hsel i hi).2.1
    · simp only [F, ite_eq_right hi, le_refl]
  have hsumK : (∑ i, K i) = B + (D : ℂ) • 1 := by
    dsimp only [K, B]
    rw [Finset.sum_add_distrib, Finset.sum_ite_mem_eq, Finset.sum_const,
      ← Nat.cast_smul_eq_nsmul ℂ, smul_smul]
    congr 1
    simp only [D, Complex.ofReal_mul, Complex.ofReal_ofNat, Complex.ofReal_natCast]
    congr 1
    exact mul_comm _ _
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← hsumK]
    exact posSemidef_sum _ (fun i _ ↦ hK i)
  · exact Finset.sum_le_sum (fun i _ ↦ hFle i)
  · intro j
    change Commute (∑ i, F i) (A j)
    refine Commute.sum_left Finset.univ _ (A j) ?_
    intro i _
    have hij : Commute (A i) (A j) := by
      by_cases heq : i = j
      · simpa only [heq] using Commute.refl (A j)
      · exact hcomm heq
    by_cases hi : i ∈ S
    · exact (hsel i hi).2.2.1 (A j) hij
    · simpa only [F, ite_eq_right hi] using
        hij.sub_left ((Commute.one_left (A j)).smul_left (e i : ℂ))
  · intro j hj U hU
    have hproj := (hsel j hj).2.2.2 U hU
    have hKj : F j + (10 : ℂ) • 1 = K j := by simp only [K, ite_eq_left hj]
    rw [hKj] at hproj
    have hsingle : K j ≤ ∑ i, K i :=
      Finset.single_le_sum (fun i _ ↦ (hK i).nonneg) (Finset.mem_univ j)
    exact hproj.trans (hsingle.trans_eq hsumK)

end Matrix

end SoftTruncationCommutingFamily
