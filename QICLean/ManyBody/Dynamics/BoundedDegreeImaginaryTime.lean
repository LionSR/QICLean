/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.Fintype.Sigma
import QICLean.Algebra.IncidenceCount
import QICLean.Analysis.ExpConjugation
import QICLean.ManyBody.Dynamics.Interaction

/-!
# Imaginary-time conjugation for interactions of bounded support and degree

Let `Φ` be an interaction whose terms are positive contractions `0 ≤ hᵢ ≤ 1`, each supported
on at most `k` sites, and let `H = ∑_{i ∈ s} hᵢ` for a finite set `s` of indices such that
every site lies in the supports of at most `g` of the terms with index in `s`. For an
observable `O` supported on at most `k` sites,
`‖ad_H^m O‖ ≤ (g k)^m m! ‖O‖`, and hence
`‖e^{t(H - z)} O e^{-t(H - z)}‖ ≤ 2 ‖O‖` for every `z ∈ ℂ` and `0 ≤ t` with `2 g k t ≤ 1`.
The same conjugation of a sum of `J` terms of `Φ` has norm at most `2 |J|`.

The commutator iterate is a sum of nested commutators along sequences of terms. After `j`
commutators a piece is supported on at most `|S| + j k` sites, so at most `g (|S| + j k)`
terms fail to commute with it, and each commutator with a positive contraction costs at most
the norm of the piece. The Hamiltonian `Φ.hamiltonian` is the case `s = univ`.

**Scope restriction (contractions, count degree, observables on at most `k` sites):** the
printed lemma assumes positive terms with `∑_{X ∋ i} ‖h_X‖ ≤ g` at every site, allows an
observable `A` with `R = ∑_{X ∈ E_A} ‖h_X‖`, and concludes
`‖e^{sH} A e^{-sH}‖ ≤ ‖A‖ (1 - g k s)^{-R/(g k)}` for `0 ≤ s < 1/(g k)`. Here the terms are
contractions, the degree counts terms, the observable lies on at most `k` sites (so
`R ≤ g k`), and only the consequence `2 ‖O‖` at `s ≤ 1/(2 g k)` is stated. See
`docs/paper-gaps/akl14_hadamard_bound_scope.tex`.

Moved from TNLean, `TNLean/Lattice/BoundedDegreeImaginaryTime.lean` at commit `e41c3b63`,
restated for an interaction on a system of sites; the hypotheses `0 < k` and `0 < g` are
dropped.

## Main results

* `ManyBody.Interaction.norm_commutator_sum_le_card` — only the terms meeting the support
  contribute to a commutator, each at most the norm of the observable.
* `ManyBody.Interaction.exists_commutator_iterate_decomposition` — the commutator iterate as
  a sum of few pieces of bounded support and norm.
* `ManyBody.Interaction.norm_commutator_iterate_le` — factorial growth of commutator iterates.
* `ManyBody.Interaction.norm_exp_conjugation_shift_le_two` — the short imaginary-time bound.
* `ManyBody.Interaction.norm_exp_conjugation_shift_sum_le` — its sum over a set of terms.

## References

* Arad, Kuwahara and Landau, arXiv:1406.3898, Lemma `lem:Hadamard-bound` and its proof,
  `low70.tex`, lines 795–880; the setting of `sec:settings`, lines 400–445.
-/

open Matrix
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace ManyBody.Interaction

variable {V : Type*} [Fintype V] [DecidableEq V] {X : V → Type*} [∀ v, Fintype (X v)]
  [∀ v, DecidableEq (X v)] {ι : Type*} {T : ι → Finset V}

/-- If the terms of `Φ` are positive contractions and `O` is supported on `S`, then
`‖[∑_{i ∈ s} hᵢ, O]‖` is at most the number of indices `i ∈ s` with `T i` meeting `S`,
times `‖O‖`. AKL14, arXiv:1406.3898, proof of `lem:Hadamard-bound`, `low70.tex`,
lines 817–837. -/
theorem norm_commutator_sum_le_card (Φ : Interaction X T) (s : Finset ι)
    (hpos : ∀ i, 0 ≤ Φ.term i) (hle : ∀ i, Φ.term i ≤ 1)
    {O : Matrix (Config X) (Config X) ℂ} {S : Finset V} (hO : O ∈ supportedOperators X S) :
    ‖(∑ i ∈ s, Φ.term i) * O - O * (∑ i ∈ s, Φ.term i)‖ ≤
      ((s.filter fun i ↦ ¬Disjoint (T i) S).card : ℝ) * ‖O‖ := by
  classical
  let active := s.filter fun i ↦ ¬Disjoint (T i) S
  have hsum : (∑ i ∈ s, (Φ.term i * O - O * Φ.term i)) =
      ∑ i ∈ active, (Φ.term i * O - O * Φ.term i) := by
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro i hi hia
    by_cases hd : Disjoint (T i) S
    · exact sub_eq_zero.mpr (commute_of_mem_supportedOperators_of_disjoint (Φ.mem i) hO hd).eq
    · exact False.elim (hia (Finset.mem_filter.mpr ⟨hi, hd⟩))
  calc
    ‖(∑ i ∈ s, Φ.term i) * O - O * (∑ i ∈ s, Φ.term i)‖ =
        ‖∑ i ∈ s, (Φ.term i * O - O * Φ.term i)‖ := by
      rw [Finset.sum_mul, Finset.mul_sum, Finset.sum_sub_distrib]
    _ = ‖∑ i ∈ active, (Φ.term i * O - O * Φ.term i)‖ := congrArg (‖·‖) hsum
    _ ≤ ∑ i ∈ active, ‖Φ.term i * O - O * Φ.term i‖ := norm_sum_le _ _
    _ ≤ ∑ _i ∈ active, ‖O‖ := Finset.sum_le_sum fun i _ ↦
      Matrix.norm_commutator_le_of_nonneg_le_one _ O (hpos i) (hle i)
    _ = (active.card : ℝ) * ‖O‖ := by simp only [Finset.sum_const, nsmul_eq_mul]

/-- Let the terms of `Φ` be positive contractions on at most `k` sites, and let every site lie
in the supports of at most `g` terms with index in `s`. For `O` supported on `S₀`, the
iterate `ad_H^m O` of `H = ∑_{i ∈ s} hᵢ` is a sum of at most `∏_{j < m} g (|S₀| + j k)`
pieces, each of norm at most `‖O‖` and supported on at most `|S₀| + m k` sites.
AKL14, arXiv:1406.3898, proof of `lem:Hadamard-bound`, eq. `Kell`, `low70.tex`,
lines 804–877. -/
theorem exists_commutator_iterate_decomposition (Φ : Interaction X T) (s : Finset ι)
    {k g : ℕ} (hpos : ∀ i, 0 ≤ Φ.term i) (hle : ∀ i, Φ.term i ≤ 1)
    (hk : ∀ i, (T i).card ≤ k) (hg : ∀ v, (s.filter fun i ↦ v ∈ T i).card ≤ g)
    {O : Matrix (Config X) (Config X) ℂ} {S₀ : Finset V} (hO : O ∈ supportedOperators X S₀)
    (m : ℕ) :
    ∃ (N : ℕ) (Y : Fin N → Matrix (Config X) (Config X) ℂ) (S : Fin N → Finset V),
      (GaussianFilter.commutatorCLM (∑ i ∈ s, Φ.term i) ^ m) O = ∑ a, Y a ∧
      (∀ a, Y a ∈ supportedOperators X (S a)) ∧
      (∀ a, ‖Y a‖ ≤ ‖O‖) ∧ (∀ a, (S a).card ≤ S₀.card + m * k) ∧
      N ≤ ∏ j ∈ Finset.range m, g * (S₀.card + j * k) := by
  classical
  set H := ∑ i ∈ s, Φ.term i
  induction m with
  | zero =>
    exact ⟨1, fun _ ↦ O, fun _ ↦ S₀, by simp, fun _ ↦ hO, fun _ ↦ le_rfl,
      fun _ ↦ by simp, by simp⟩
  | succ m ih =>
    obtain ⟨N, Y, S, hsum, hsupp, hnorm, hcard, hN⟩ := ih
    let A : Fin N → Finset ι := fun a ↦ s.filter fun i ↦ ¬Disjoint (T i) (S a)
    let σ := Σ a : Fin N, ↥(A a)
    let e := Fintype.equivFin σ
    let f : σ → Matrix (Config X) (Config X) ℂ := fun p ↦
      Φ.term p.2.1 * Y p.1 - Y p.1 * Φ.term p.2.1
    let R : σ → Finset V := fun p ↦ S p.1 ∪ T p.2.1
    refine ⟨Fintype.card σ, fun j ↦ f (e.symm j), fun j ↦ R (e.symm j), ?_, ?_, ?_, ?_, ?_⟩
    · have hterm (a : Fin N) :
          H * Y a - Y a * H = ∑ i ∈ A a, (Φ.term i * Y a - Y a * Φ.term i) := by
        rw [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]
        symm
        apply Finset.sum_subset (Finset.filter_subset _ _)
        intro i hi hiA
        by_cases hd : Disjoint (T i) (S a)
        · exact sub_eq_zero.mpr
            (commute_of_mem_supportedOperators_of_disjoint (Φ.mem i) (hsupp a) hd).eq
        · exact False.elim (hiA (Finset.mem_filter.mpr ⟨hi, hd⟩))
      rw [pow_succ', mul_apply_eq_comp,
        GaussianFilter.commutatorCLM_apply, hsum,
        Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib]
      calc
        ∑ a, (H * Y a - Y a * H) =
            ∑ a, ∑ i : ↥(A a), (Φ.term i.1 * Y a - Y a * Φ.term i.1) := by
          refine Finset.sum_congr rfl fun a _ ↦ ?_
          rw [hterm a, ← Finset.sum_coe_sort (A a)]
        _ = ∑ p : σ, f p := (Fintype.sum_sigma f).symm
        _ = ∑ j, f (e.symm j) := (Equiv.sum_comp e.symm f).symm
    · intro j
      have hh : Φ.term (e.symm j).2.1 ∈ supportedOperators X (R (e.symm j)) :=
        supportedOperators_mono Finset.subset_union_right (Φ.mem _)
      have hY : Y (e.symm j).1 ∈ supportedOperators X (R (e.symm j)) :=
        supportedOperators_mono Finset.subset_union_left (hsupp _)
      exact sub_mem (mul_mem hh hY) (mul_mem hY hh)
    · intro j
      exact (Matrix.norm_commutator_le_of_nonneg_le_one _ _ (hpos _) (hle _)).trans (hnorm _)
    · intro j
      calc
        (R (e.symm j)).card ≤ (S (e.symm j).1).card + (T (e.symm j).2.1).card :=
          Finset.card_union_le _ _
        _ ≤ (S₀.card + m * k) + k := add_le_add (hcard _) (hk _)
        _ = S₀.card + (m + 1) * k := by ring
    · calc
        Fintype.card σ = ∑ a, (A a).card := by
          simp only [σ, Fintype.card_sigma, Fintype.card_coe]
        _ ≤ ∑ _a : Fin N, g * (S₀.card + m * k) := by
          refine Finset.sum_le_sum fun a _ ↦ ?_
          exact (Finset.card_filter_not_disjoint_le T hg (S a)).trans
            (Nat.mul_le_mul_left _ (hcard a))
        _ = N * (g * (S₀.card + m * k)) := by simp
        _ ≤ (∏ j ∈ Finset.range m, g * (S₀.card + j * k)) * (g * (S₀.card + m * k)) :=
          Nat.mul_le_mul_right _ hN
        _ = ∏ j ∈ Finset.range (m + 1), g * (S₀.card + j * k) :=
          (Finset.prod_range_succ _ _).symm

/-- Let the terms of `Φ` be positive contractions on at most `k` sites, and let every site lie
in the supports of at most `g` terms with index in `s`. If `O` is supported on at most `k`
sites, then `‖ad_H^m O‖ ≤ (g k)^m m! ‖O‖` for `H = ∑_{i ∈ s} hᵢ`.
AKL14, arXiv:1406.3898, proof of `lem:Hadamard-bound`, `low70.tex`, lines 804–877, with
`R ≤ g k`. -/
theorem norm_commutator_iterate_le (Φ : Interaction X T) (s : Finset ι)
    {k g : ℕ} (hpos : ∀ i, 0 ≤ Φ.term i) (hle : ∀ i, Φ.term i ≤ 1)
    (hk : ∀ i, (T i).card ≤ k) (hg : ∀ v, (s.filter fun i ↦ v ∈ T i).card ≤ g)
    {O : Matrix (Config X) (Config X) ℂ} {S₀ : Finset V} (hO : O ∈ supportedOperators X S₀)
    (hS₀ : S₀.card ≤ k) (m : ℕ) :
    ‖(GaussianFilter.commutatorCLM (∑ i ∈ s, Φ.term i) ^ m) O‖ ≤
      ((g * k : ℕ) : ℝ) ^ m * (m.factorial : ℝ) * ‖O‖ := by
  obtain ⟨N, Y, S, hsum, -, hnorm, -, hN⟩ :=
    exists_commutator_iterate_decomposition Φ s hpos hle hk hg hO m
  have hprod : ∏ j ∈ Finset.range m, g * (S₀.card + j * k) ≤ (g * k) ^ m * m.factorial := by
    calc
      ∏ j ∈ Finset.range m, g * (S₀.card + j * k) ≤
          ∏ j ∈ Finset.range m, (g * k) * (j + 1) := by
        refine Finset.prod_le_prod fun j _ ↦ ?_
        calc
          g * (S₀.card + j * k) ≤ g * (k + j * k) := Nat.mul_le_mul_left _ (by omega)
          _ = (g * k) * (j + 1) := by ring
      _ = (g * k) ^ m * m.factorial := by
        rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range,
          Finset.prod_range_add_one_eq_factorial]
  have hNreal : (N : ℝ) ≤ ((g * k : ℕ) : ℝ) ^ m * (m.factorial : ℝ) := by
    exact_mod_cast hN.trans hprod
  rw [hsum]
  calc
    ‖∑ a, Y a‖ ≤ ∑ a, ‖Y a‖ := norm_sum_le _ _
    _ ≤ ∑ _a : Fin N, ‖O‖ := Finset.sum_le_sum fun a _ ↦ hnorm a
    _ = (N : ℝ) * ‖O‖ := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right hNreal (norm_nonneg O)

/-- **Short imaginary-time conjugation for bounded support and degree.** Let the terms of `Φ`
be positive contractions on at most `k` sites, and let every site lie in the supports of at
most `g` terms with index in `s`. If `O` is supported on at most `k` sites, then for every
`z ∈ ℂ` and `0 ≤ t` with `2 g k t ≤ 1`, with `H = ∑_{i ∈ s} hᵢ`,
`‖e^{t(H - z)} O e^{-t(H - z)}‖ ≤ 2 ‖O‖`.
AKL14, arXiv:1406.3898, `lem:Hadamard-bound`, `low70.tex`, lines 795–880, within the scope
restriction of the module docstring. -/
theorem norm_exp_conjugation_shift_le_two (Φ : Interaction X T) (s : Finset ι)
    {k g : ℕ} (hpos : ∀ i, 0 ≤ Φ.term i) (hle : ∀ i, Φ.term i ≤ 1)
    (hk : ∀ i, (T i).card ≤ k) (hg : ∀ v, (s.filter fun i ↦ v ∈ T i).card ≤ g)
    {O : Matrix (Config X) (Config X) ℂ} {S₀ : Finset V} (hO : O ∈ supportedOperators X S₀)
    (hS₀ : S₀.card ≤ k) (z : ℂ) {t : ℝ} (ht0 : 0 ≤ t) (ht : 2 * ((g * k : ℕ) : ℝ) * t ≤ 1) :
    ‖NormedSpace.exp ((t : ℂ) • ((∑ i ∈ s, Φ.term i) - z • 1)) * O *
      NormedSpace.exp (-((t : ℂ) • ((∑ i ∈ s, Φ.term i) - z • 1)))‖ ≤ 2 * ‖O‖ := by
  set H := ∑ i ∈ s, Φ.term i
  apply Matrix.norm_exp_conjugation_le_two_of_growth (H - z • 1) O ((g * k : ℕ) : ℝ) t ht0
    (by linarith)
  intro m
  have had : GaussianFilter.commutatorCLM (H - z • 1) = GaussianFilter.commutatorCLM H := by
    refine ContinuousLinearMap.ext fun Z ↦ ?_
    simp only [GaussianFilter.commutatorCLM_apply, sub_mul, mul_sub, smul_mul_assoc,
      mul_smul_comm, one_mul, mul_one]
    abel
  rw [had]
  exact norm_commutator_iterate_le Φ s hpos hle hk hg hO hS₀ m

/-- In the setting of `norm_exp_conjugation_shift_le_two`, the conjugation of the sum of the
terms with index in a finite set `J` has norm at most `2 |J|`.
AKL14, arXiv:1406.3898, `lem:Hadamard-bound`, `low70.tex`, lines 795–880, applied to each
term. -/
theorem norm_exp_conjugation_shift_sum_le (Φ : Interaction X T) (s J : Finset ι)
    {k g : ℕ} (hpos : ∀ i, 0 ≤ Φ.term i) (hle : ∀ i, Φ.term i ≤ 1)
    (hk : ∀ i, (T i).card ≤ k) (hg : ∀ v, (s.filter fun i ↦ v ∈ T i).card ≤ g)
    (z : ℂ) {t : ℝ} (ht0 : 0 ≤ t) (ht : 2 * ((g * k : ℕ) : ℝ) * t ≤ 1) :
    ‖NormedSpace.exp ((t : ℂ) • ((∑ i ∈ s, Φ.term i) - z • 1)) * (∑ j ∈ J, Φ.term j) *
      NormedSpace.exp (-((t : ℂ) • ((∑ i ∈ s, Φ.term i) - z • 1)))‖ ≤ 2 * (J.card : ℝ) := by
  have hnorm1 : ‖(1 : Matrix (Config X) (Config X) ℂ)‖ ≤ 1 :=
    IsStarProjection.norm_le _ (IsStarProjection.one _)
  have hterm (j : ι) :
      ‖NormedSpace.exp ((t : ℂ) • ((∑ i ∈ s, Φ.term i) - z • 1)) * Φ.term j *
        NormedSpace.exp (-((t : ℂ) • ((∑ i ∈ s, Φ.term i) - z • 1)))‖ ≤ 2 := by
    have hj : ‖Φ.term j‖ ≤ 1 :=
      (CStarAlgebra.norm_le_norm_of_le_of_nonneg (hle j) (hpos j)).trans hnorm1
    calc
      _ ≤ 2 * ‖Φ.term j‖ :=
        norm_exp_conjugation_shift_le_two Φ s hpos hle hk hg (Φ.mem j) (hk j) z ht0 ht
      _ ≤ 2 := by linarith
  rw [Finset.mul_sum, Finset.sum_mul]
  calc
    _ ≤ ∑ j ∈ J, ‖NormedSpace.exp ((t : ℂ) • ((∑ i ∈ s, Φ.term i) - z • 1)) * Φ.term j *
        NormedSpace.exp (-((t : ℂ) • ((∑ i ∈ s, Φ.term i) - z • 1)))‖ := norm_sum_le _ _
    _ ≤ ∑ _j ∈ J, (2 : ℝ) := Finset.sum_le_sum fun j _ ↦ hterm j
    _ = 2 * (J.card : ℝ) := by rw [Finset.sum_const, nsmul_eq_mul, mul_comm]

end ManyBody.Interaction
