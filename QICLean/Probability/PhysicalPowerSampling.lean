/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.PowerSamplingNormalization
import QICLean.Probability.JointWordSampling
import QICLean.Algebra.FiniteSumPowers
import QICLean.Analysis.PhysicalPowerFilterLowerGap
import Mathlib.Algebra.Order.BigOperators.Group.List

/-!
# Sampling the physical normalized Hamiltonian power

Let `H = ∑ i, h i` be a sum of positive contractions. Add one zero interaction,
so the alphabet is `Option κ`, with `n = card κ + 1` letters and complement
operators `P_none = 1`, `P_some i = 1 - h i`. Each ordered word product has norm
at most one. The exact finite average of the scaled word products is the
normalized Hamiltonian power, by the proved ordered expansion.

For a unit ground vector with lower gap `Δ > 0`, set
`C = (1 - E0 / n)⁻¹` and `m = ⌈(n - E0) / Δ * log Q⌉₊`, with `Q ≥ 1`.
The energy range `0 ≤ E0 ≤ n - 1` follows from the actual terms and eigenvector.
The normalization theorem gives `C^(2m) ≤ n² * exp (2 * E0 * log Q / Δ)`.

The joint sampling theorem yields one actual family of words whose average
approximates this power and whose letter counts are all controlled. The
lower-gap power estimate then gives approximation of the same ground
projection. An explicit positive sample count and logarithmic frequency
threshold are provided. Matrix-dimension nonemptiness follows from the unit
ground vector; the sample index set is explicitly nonempty or constructed so.

These are the norm and frequency estimates in the sampled-power construction
of LVV, arXiv:1307.5143v1, Section 2.3.1, with the ground-energy dependence
retained in the published Methods theorem and supplement, Proposition 1, p. 6:
https://people.eecs.berkeley.edu/~vazirani/pubs/1dalg.pdf.
The spatial operator-Schmidt-rank estimate uses further locality information.
-/

open scoped BigOperators Matrix Matrix.Norms.L2Operator ComplexOrder MatrixOrder InnerProductSpace

namespace Matrix

open Classical in
private theorem norm_complement_word_le_one
    {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (h : κ → Matrix ι ι ℂ) (hpos : ∀ i, (h i).PosSemidef) (hu : ∀ i, h i ≤ 1)
    {m : ℕ} (w : Fin m → Option κ) :
    ‖(List.ofFn fun j ↦ 1 - (w j).elim 0 h).prod‖ ≤ 1 := by
  classical
  have hp (i : Option κ) : ‖1 - i.elim 0 h‖ ≤ 1 := by
    cases i with
    | none => simp
    | some i =>
      exact (CStarAlgebra.norm_le_one_iff_of_nonneg _ (Matrix.le_iff.mp (hu i)).nonneg).mpr
        (sub_le_self _ (hpos i).nonneg)
  have hn : ‖(List.ofFn fun j ↦ 1 - (w j).elim 0 h).prod‖₊ ≤ 1 := by
    calc
      _ ≤ (List.ofFn fun j ↦ ‖1 - (w j).elim 0 h‖₊).prod := by
        simpa only [List.map_ofFn, Function.comp_def] using
          List.nnnorm_prod_le (List.ofFn fun j ↦ 1 - (w j).elim 0 h)
      _ ≤ (1 : NNReal) ^ m := by
        simpa only [List.length_ofFn] using List.prod_le_pow_length
          (List.ofFn fun j ↦ ‖1 - (w j).elim 0 h‖₊) 1 (by
            intro x hx
            obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hx
            exact_mod_cast hp (w j))
      _ = 1 := by simp
  exact_mod_cast hn

open Classical in
private theorem complement_word_actual_mean
    {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    (h : κ → Matrix ι ι ℂ) (c : ℝ) (m : ℕ) :
    (Fintype.card (Fin m → Option κ) : ℂ)⁻¹ •
        ∑ w : Fin m → Option κ,
          (c : ℂ) ^ m • (List.ofFn fun j ↦ 1 - (w j).elim 0 h).prod =
      ((c : ℂ) • (1 - (Fintype.card κ + 1 : ℂ)⁻¹ • ∑ i, h i)) ^ m := by
  have hh := Fintype.smul_sub_average_pow_eq_sum_ordered_words
    (fun i : Option κ ↦ i.elim (0 : Matrix ι ι ℂ) h) (c : ℂ) m
  simp only [Fintype.sum_option, Option.elim_none, Option.elim_some, zero_add,
    Fintype.card_option, Nat.cast_add, Nat.cast_one] at hh
  rw [hh, ← Finset.smul_sum, smul_smul, Fintype.card_fun, Fintype.card_fin, Nat.cast_pow,
    Fintype.card_option, Nat.cast_add, Nat.cast_one, div_pow, div_eq_mul_inv]
  congr 1
  ring

open Classical in
/-- Actual positive-contraction word samples approximate their normalized power
and simultaneously control every letter count. The mean identity and norm bound
are derived from the terms; the numerical budget retains `c^(2m)`.
Supporting LVV, equation `eq:a-exp` and Corollary 2.14. -/
theorem exists_sampled_complement_power_approximation_and_word_counts
    {ι κ β : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι] [Fintype κ]
    [Fintype β] [Nonempty β]
    (h : κ → Matrix ι ι ℂ) (hpos : ∀ i, (h i).PosSemidef) (hu : ∀ i, h i ≤ 1)
    {c η : ℝ} (hc : 0 ≤ c) (hη : 0 < η) (m : ℕ) {p : ℕ} (hp : 0 < p) (u : ℕ)
    (hsmall : (Fintype.card ι : ℝ) *
        (4 * (p : ℝ) ^ 2 * c ^ (2 * m) / ((Fintype.card β : ℝ) * η ^ 2)) ^ p +
      ((Fintype.card κ : ℝ) + 1) * Fintype.card β *
        Real.exp ((m : ℝ) / ((Fintype.card κ : ℝ) + 1) - u * Real.log 2) < 1) :
    ∃ σ : β → Fin m → Option κ,
      ‖(Fintype.card β : ℂ)⁻¹ • ∑ b,
          (c : ℂ) ^ m • (List.ofFn fun j ↦ 1 - (σ b j).elim 0 h).prod -
        ((c : ℂ) • (1 - (Fintype.card κ + 1 : ℂ)⁻¹ • ∑ i, h i)) ^ m‖ < η ∧
      ∀ b a, WordMultiplicity.countsFinsupp (σ b) a < u := by
  classical
  let Y (w : Fin m → Option κ) : Matrix ι ι ℂ :=
    (c : ℂ) ^ m • (List.ofFn fun j ↦ 1 - (w j).elim 0 h).prod
  have hY (w : Fin m → Option κ) : ‖Y w‖ ≤ c ^ m := by
    calc
      _ = c ^ m * ‖(List.ofFn fun j ↦ 1 - (w j).elim 0 h).prod‖ := by
        simp only [Y, norm_smul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg hc]
      _ ≤ c ^ m * 1 := mul_le_mul_of_nonneg_left
        (norm_complement_word_le_one h hpos hu w) (pow_nonneg hc _)
      _ = _ := mul_one _
  have hcPow : (c ^ m) ^ 2 = c ^ (2 * m) := by rw [← pow_mul, Nat.mul_comm m 2]
  have hs : (Fintype.card ι : ℝ) *
        (4 * (p : ℝ) ^ 2 * (c ^ m) ^ 2 / ((Fintype.card β : ℝ) * η ^ 2)) ^ p +
      (Fintype.card (Option κ) : ℝ) * Fintype.card β *
        Real.exp ((m : ℝ) / Fintype.card (Option κ) - u * Real.log 2) < 1 := by
    simpa only [hcPow, Fintype.card_option, Nat.cast_add, Nat.cast_one] using hsmall
  obtain ⟨σ, hσ, hfreq⟩ := exists_average_sub_mean_norm_lt_and_word_counts_lt Y hη hY hp u hs
  refine ⟨σ, ?_, hfreq⟩
  simpa only [Y, complement_word_actual_mean] using hσ


private theorem physical_power_ground_energy_bounds
    {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    (h : κ → Matrix ι ι ℂ) (hpos : ∀ i, (h i).PosSemidef) (hu : ∀ i, h i ≤ 1)
    {E0 : ℝ} {Ω : EuclideanSpace ℂ ι} (hΩ : ‖Ω‖ = 1)
    (hHΩ : (∑ i, h i) *ᵥ WithLp.ofLp Ω = (E0 : ℂ) • WithLp.ofLp Ω) :
    0 ≤ E0 ∧ E0 ≤ (Fintype.card κ : ℝ) := by
  have hn : star (WithLp.ofLp Ω) ⬝ᵥ WithLp.ofLp Ω = (1 : ℂ) := by
    rw [dotProduct_comm, ← EuclideanSpace.inner_eq_star_dotProduct,
      inner_self_eq_norm_sq_to_K, hΩ]
    norm_num
  have hHpos := posSemidef_sum Finset.univ fun i _ ↦ hpos i
  have hlow := (Complex.nonneg_iff.mp
    (hHpos.dotProduct_mulVec_nonneg (WithLp.ofLp Ω))).1
  rw [hHΩ, dotProduct_smul, hn, smul_eq_mul, mul_one, Complex.ofReal_re] at hlow
  have hHu : (∑ i, h i) ≤ (Fintype.card κ : ℝ) • (1 : Matrix ι ι ℂ) := by
    simpa only [Finset.sum_const, Finset.card_univ, Nat.cast_smul_eq_nsmul] using
      (show (∑ i, h i) ≤ ∑ _ : κ, (1 : Matrix ι ι ℂ) from
        Finset.sum_le_sum fun i _ ↦ hu i)
  have hupper := (Complex.nonneg_iff.mp
    ((Matrix.le_iff.mp hHu).dotProduct_mulVec_nonneg (WithLp.ofLp Ω))).1
  rw [sub_mulVec, smul_mulVec, one_mulVec, hHΩ, dotProduct_sub] at hupper
  simp only [dotProduct_smul, hn] at hupper
  have hupper' : 0 ≤ (Fintype.card κ : ℝ) - E0 := by
    simpa only [Complex.real_smul, smul_eq_mul, mul_one,
      Complex.sub_re, Complex.ofReal_re] using hupper
  exact ⟨hlow, sub_nonneg.mp hupper'⟩


open Classical in
/-- Sampling the actual physical normalized power with the published energy-dependent
budget gives one operator approximating both that power and the canonical ground
projection, with simultaneous word-frequency control. The ground-energy range,
normalization bound, mean identity and matrix norm estimate are derived.
Supporting the norm estimates of LVV, published supplement, Proposition 1, p. 6. -/
theorem exists_sampled_power_approximation_with_energy_dependent_budget
    {ι κ β : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    [Fintype β] [Nonempty β]
    (h : κ → Matrix ι ι ℂ) (hpos : ∀ i, (h i).PosSemidef) (hu : ∀ i, h i ≤ 1)
    {E0 Δ : ℝ} {Ω : EuclideanSpace ℂ ι} (hΩ : ‖Ω‖ = 1)
    (hHΩ : (∑ i, h i) *ᵥ WithLp.ofLp Ω = (E0 : ℂ) • WithLp.ofLp Ω)
    (hgap : ((∑ i, h i) - (E0 : ℂ) • 1 - (Δ : ℂ) •
      (1 - vecMulVec (WithLp.ofLp Ω) (star (WithLp.ofLp Ω)))).PosSemidef)
    (hΔ : 0 < Δ) {Q η : ℝ} (hQ : 1 ≤ Q) (hη : 0 < η)
    {p : ℕ} (hp : 0 < p) (u : ℕ) :
    let N := Fintype.card κ + 1
    let m := ⌈((N : ℝ) - E0) / Δ * Real.log Q⌉₊
    let C := (1 - E0 / N)⁻¹
    ((Fintype.card ι : ℝ) *
        (4 * (p : ℝ) ^ 2 * (N : ℝ) ^ 2 * Real.exp (2 * E0 * Real.log Q / Δ) /
          ((Fintype.card β : ℝ) * η ^ 2)) ^ p +
      (N : ℝ) * Fintype.card β *
        Real.exp ((m : ℝ) / N - u * Real.log 2) < 1) →
    ∃ σ : β → Fin m → Option κ,
      let K := (Fintype.card β : ℂ)⁻¹ • ∑ b,
        (C : ℂ) ^ m • (List.ofFn fun j ↦ 1 - (σ b j).elim 0 h).prod
      ‖K - ((C : ℂ) • (1 - (Fintype.card κ + 1 : ℂ)⁻¹ • ∑ i, h i)) ^ m‖ < η ∧
      ‖K - vecMulVec (WithLp.ofLp Ω) (star (WithLp.ofLp Ω))‖ < η + 1 / Q ∧
        ∀ b a, WordMultiplicity.countsFinsupp (σ b) a < u := by
  classical
  intro N m C hsmall
  let : Nonempty ι := by
    by_contra hn
    let : IsEmpty ι := ⟨fun i ↦ hn ⟨i⟩⟩
    have hz : Ω = 0 := Subsingleton.elim _ _
    simp [hz] at hΩ
  obtain ⟨hE0, hEupper⟩ := physical_power_ground_energy_bounds h hpos hu hΩ hHΩ
  have hEN : E0 ≤ (N : ℝ) - 1 := by simpa only [N, Nat.cast_add, Nat.cast_one,
    add_sub_cancel_right] using hEupper
  obtain ⟨hC1, _, _⟩ := Real.power_sampling_normalization_bounds hE0 hEN
  change 1 ≤ C at hC1
  have hCpos : 0 < C := lt_of_lt_of_le zero_lt_one hC1
  have hNormC := Real.power_sampling_normalization_pow_ceil_le hE0 hEN hΔ hQ
  change C ^ (2 * m) ≤ (N : ℝ) ^ 2 * Real.exp (2 * E0 * Real.log Q / Δ) at hNormC
  have hnum : 4 * (p : ℝ) ^ 2 * C ^ (2 * m) ≤
      4 * (p : ℝ) ^ 2 * (N : ℝ) ^ 2 * Real.exp (2 * E0 * Real.log Q / Δ) := by
    calc
      _ ≤ (4 * (p : ℝ) ^ 2) *
          ((N : ℝ) ^ 2 * Real.exp (2 * E0 * Real.log Q / Δ)) :=
        mul_le_mul_of_nonneg_left hNormC (by positivity)
      _ = _ := by ring
  have hM : (Fintype.card ι : ℝ) *
      (4 * (p : ℝ) ^ 2 * C ^ (2 * m) / ((Fintype.card β : ℝ) * η ^ 2)) ^ p ≤
      (Fintype.card ι : ℝ) *
        (4 * (p : ℝ) ^ 2 * (N : ℝ) ^ 2 * Real.exp (2 * E0 * Real.log Q / Δ) /
          ((Fintype.card β : ℝ) * η ^ 2)) ^ p :=
    mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (by positivity)
        (div_le_div_of_nonneg_right hnum (by positivity)) p) (Nat.cast_nonneg _)
  have hsC : (Fintype.card ι : ℝ) *
      (4 * (p : ℝ) ^ 2 * C ^ (2 * m) / ((Fintype.card β : ℝ) * η ^ 2)) ^ p +
      (N : ℝ) * Fintype.card β * Real.exp ((m : ℝ) / N - u * Real.log 2) < 1 :=
    (add_le_add hM (le_refl _)).trans_lt hsmall
  obtain ⟨σ, hσ, hfreq⟩ := exists_sampled_complement_power_approximation_and_word_counts
    h hpos hu hCpos.le hη m hp u (by
      simpa only [N, Nat.cast_add, Nat.cast_one] using hsC)
  have hQpos : 0 < Q := lt_of_lt_of_le zero_lt_one hQ
  have hm : (((Fintype.card κ + 1 : ℕ) : ℝ) - E0) / Δ *
      Real.log (1 / (1 / Q)) ≤ (m : ℝ) := by
    simpa only [one_div, inv_inv, N] using
      (Nat.le_ceil (((N : ℝ) - E0) / Δ * Real.log Q))
  have hpower := norm_power_filter_sub_ground_le_of_lower_gap_log_threshold
    h hpos hu hΩ hHΩ hgap hΔ (one_div_pos.mpr hQpos) m hm
  have hpower' :
      ‖((C : ℂ) • (1 - (Fintype.card κ + 1 : ℂ)⁻¹ • ∑ i, h i)) ^ m -
        vecMulVec (WithLp.ofLp Ω) (star (WithLp.ofLp Ω))‖ ≤ 1 / Q := by
    change ‖(C • (1 - (N : ℝ)⁻¹ • ∑ i, h i)) ^ m -
      vecMulVec (WithLp.ofLp Ω) (star (WithLp.ofLp Ω))‖ ≤ 1 / Q at hpower
    simpa only [N, Nat.cast_add, Nat.cast_one, ← Complex.coe_smul, Complex.ofReal_inv,
      Complex.ofReal_add, Complex.ofReal_natCast, Complex.ofReal_one] using hpower
  refine ⟨σ, hσ, ?_, hfreq⟩
  exact (norm_sub_le_norm_sub_add_norm_sub _ _ _).trans_lt (add_lt_add_of_lt_of_le hσ hpower')


open Classical in
/-- Explicit positive sample count and logarithmic letter-count threshold for the
physical normalized-power sampler. For `2 * dim < 4^p`, choose the displayed
natural-ceiling count. The joint failure budget is then strictly below one.
The sample count contains `exp (2 * E0 * log Q / Δ)`, as in the published LVV
supplement, Proposition 1, p. 6. -/
theorem exists_sampled_power_approximation_with_explicit_count
    {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    (h : κ → Matrix ι ι ℂ) (hpos : ∀ i, (h i).PosSemidef) (hu : ∀ i, h i ≤ 1)
    {E0 Δ : ℝ} {Ω : EuclideanSpace ℂ ι} (hΩ : ‖Ω‖ = 1)
    (hHΩ : (∑ i, h i) *ᵥ WithLp.ofLp Ω = (E0 : ℂ) • WithLp.ofLp Ω)
    (hgap : ((∑ i, h i) - (E0 : ℂ) • 1 - (Δ : ℂ) •
      (1 - vecMulVec (WithLp.ofLp Ω) (star (WithLp.ofLp Ω)))).PosSemidef)
    (hΔ : 0 < Δ) {Q η : ℝ} (hQ : 1 ≤ Q) (hη : 0 < η)
    {p : ℕ} (hp : 0 < p) (hpD : 2 * (Fintype.card ι : ℝ) < (4 : ℝ) ^ p) :
    let N := Fintype.card κ + 1
    let m := ⌈((N : ℝ) - E0) / Δ * Real.log Q⌉₊
    let C := (1 - E0 / N)⁻¹
    let ℓ := ⌈16 * (p : ℝ) ^ 2 * (N : ℝ) ^ 2 *
      Real.exp (2 * E0 * Real.log Q / Δ) / η ^ 2⌉₊ + 1
    let u := ⌈((m : ℝ) / N + Real.log (2 * (N : ℝ) * ℓ)) / Real.log 2⌉₊
    0 < ℓ ∧ ∃ σ : Fin ℓ → Fin m → Option κ,
      let K := (ℓ : ℂ)⁻¹ • ∑ b,
        (C : ℂ) ^ m • (List.ofFn fun j ↦ 1 - (σ b j).elim 0 h).prod
      ‖K - ((C : ℂ) • (1 - (Fintype.card κ + 1 : ℂ)⁻¹ • ∑ i, h i)) ^ m‖ < η ∧
      ‖K - vecMulVec (WithLp.ofLp Ω) (star (WithLp.ofLp Ω))‖ < η + 1 / Q ∧
        ∀ b a, WordMultiplicity.countsFinsupp (σ b) a < u := by
  classical
  intro N m C ℓ u
  have hℓ : 0 < ℓ := Nat.succ_pos _
  let : Nonempty (Fin ℓ) := ⟨⟨0, hℓ⟩⟩
  have hℓR : (0 : ℝ) < ℓ := by exact_mod_cast hℓ
  have hN : (0 : ℝ) < N := by exact_mod_cast Nat.succ_pos (Fintype.card κ)
  let S := (N : ℝ) ^ 2 * Real.exp (2 * E0 * Real.log Q / Δ)
  have hS : 0 ≤ S := by positivity
  have hη2 : 0 < η ^ 2 := sq_pos_of_pos hη
  have hℓeq : ℓ = ⌈16 * (p : ℝ) ^ 2 * S / η ^ 2⌉₊ + 1 := by
    dsimp only [ℓ, S]
    congr 2
    ring
  have hlarge : 16 * (p : ℝ) ^ 2 * S ≤ (ℓ : ℝ) * η ^ 2 := by
    apply (div_le_iff₀ hη2).mp
    calc
      _ ≤ (⌈16 * (p : ℝ) ^ 2 * S / η ^ 2⌉₊ : ℝ) := Nat.le_ceil _
      _ ≤ (ℓ : ℝ) := by
        rw [hℓeq, Nat.cast_add, Nat.cast_one]
        exact le_add_of_nonneg_right zero_le_one
  have hbase : 4 * (p : ℝ) ^ 2 * S / ((ℓ : ℝ) * η ^ 2) ≤ 1 / 4 := by
    apply (div_le_iff₀ (mul_pos hℓR hη2)).mpr
    nlinarith only [hlarge]
  have hM : (Fintype.card ι : ℝ) *
      (4 * (p : ℝ) ^ 2 * S / ((ℓ : ℝ) * η ^ 2)) ^ p < 1 / 2 := by
    calc
      _ ≤ (Fintype.card ι : ℝ) * (1 / 4 : ℝ) ^ p :=
        mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (by positivity) hbase p) (Nat.cast_nonneg _)
      _ = (Fintype.card ι : ℝ) / (4 : ℝ) ^ p := by
        simp only [div_eq_mul_inv, one_mul, inv_pow]
      _ < 1 / 2 := (div_lt_iff₀ (by positivity : (0 : ℝ) < 4 ^ p)).mpr (by
        nlinarith only [hpD])
  have huLog : (m : ℝ) / N + Real.log (2 * (N : ℝ) * ℓ) ≤ u * Real.log 2 :=
    (div_le_iff₀ (Real.log_pos (by norm_num : (1 : ℝ) < 2))).mp (Nat.le_ceil _)
  have harg : (m : ℝ) / N - u * Real.log 2 ≤ -Real.log (2 * (N : ℝ) * ℓ) := by
    linarith
  have hF : (N : ℝ) * ℓ * Real.exp ((m : ℝ) / N - u * Real.log 2) ≤ 1 / 2 := by
    calc
      _ ≤ (N : ℝ) * ℓ * Real.exp (-Real.log (2 * (N : ℝ) * ℓ)) :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr harg) (by positivity)
      _ = 1 / 2 := by
        rw [Real.exp_neg, Real.exp_log (by positivity : (0 : ℝ) < 2 * (N : ℝ) * ℓ)]
        field_simp
  have hsmall : (Fintype.card ι : ℝ) *
      (4 * (p : ℝ) ^ 2 * S / ((ℓ : ℝ) * η ^ 2)) ^ p +
      (N : ℝ) * ℓ * Real.exp ((m : ℝ) / N - u * Real.log 2) < 1 := by
    calc
      _ < 1 / 2 + 1 / 2 := add_lt_add_of_lt_of_le hM hF
      _ = 1 := by norm_num
  refine ⟨hℓ, ?_⟩
  have hres := exists_sampled_power_approximation_with_energy_dependent_budget
    (β := Fin ℓ) h hpos hu hΩ hHΩ hgap hΔ hQ hη hp u
  have hres' := hres (by simpa only [Fintype.card_fin, S, mul_assoc] using hsmall)
  simpa only [Fintype.card_fin] using hres'

end Matrix
