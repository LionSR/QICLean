/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.Fintype.Sigma
import QICLean.Algebra.Combinatorics.GateIncidence
import QICLean.Analysis.Exponential.ExpConjugation
import QICLean.Spectral.Eigenvalue.VariationalBound
import QICLean.ManyBody.Dynamics.Interaction

/-!
# Imaginary-time conjugation for interactions of bounded support and degree

Let `Φ` be an interaction whose terms are positive, `hᵢ ≥ 0`, each supported on at most `k`
sites, and let `H = ∑_{i ∈ s} hᵢ` for a finite set `s` of indices such that, at every site, the
norms of the terms with index in `s` whose support contains the site sum to at most `g`. Let
every term with index in `s \ E` commute with an operator `A`, and put `R = ∑_{i ∈ E} ‖hᵢ‖`.
Then `‖ad_H^m A‖ ≤ R (R + g k) ⋯ (R + (m - 1) g k) ‖A‖`, and hence
`‖e^{tH} A e^{-tH}‖ ≤ ‖A‖ (1 - g k t)^{-R/(g k)}` for `0 ≤ t < 1/(g k)`: this is the Hadamard
bound of Arad, Kuwahara and Landau.

The commutator iterate is a sum of nested commutators `[h_{X_m}, [⋯, [h_{X_1}, A]]]` along
sequences of terms, with `X_{j+1}` in `E` or meeting `X_1 ∪ ⋯ ∪ X_j`. A commutator with a
positive term costs at most its norm, and the norms of the terms meeting `j` supports of at
most `k` sites sum to at most `j g k`.

For terms that are positive contractions, every site in the supports of at most `g` terms, and
an observable `O` on at most `k` sites, the terms meeting the support of `O` are a set `E` with
`R ≤ g k`; this gives `‖ad_H^m O‖ ≤ (g k)^m m! ‖O‖` and
`‖e^{t(H - z)} O e^{-t(H - z)}‖ ≤ 2 ‖O‖` for every `z ∈ ℂ` and `0 ≤ t` with `2 g k t ≤ 1`. The
same conjugation of a sum of `J` terms of `Φ` has norm at most `2 |J|`. The Hamiltonian
`Φ.hamiltonian` is the case `s = univ`.

**Local fix (the set `E_A`):** in `norm_exp_conjugation_le` and the commutator growth behind
it, every term outside `E` commutes with the operator, where the printed lemma assumes only
`[H, A] = ∑_{X ∈ E_A} [h_X, A]`; the printed proof uses the stronger form. See
`docs/paper-gaps/akl14_hadamard_bound_scope.tex`.

Moved from TNLean, `TNLean/Lattice/BoundedDegreeImaginaryTime.lean` at commit `e41c3b63`,
restated for an interaction on a system of sites; the hypotheses `0 < k` and `0 < g` are
dropped. The norm-weighted degree, the set `E` and the binomial bound are added here.

## Main results

* `ManyBody.Interaction.commutator_sum_eq_sum_filter_not_disjoint`,
  `ManyBody.Interaction.norm_commutator_sum_le_card` — only the terms meeting the support
  contribute to a commutator, each at most the norm of the observable.
* `ManyBody.Interaction.exists_commutator_iterate_decomposition` — the commutator iterate as
  a sum of nested commutators of bounded total norm.
* `ManyBody.Interaction.norm_commutator_iterate_le_prod`,
  `ManyBody.Interaction.norm_commutator_iterate_le` — growth of commutator iterates.
* `ManyBody.Interaction.norm_exp_conjugation_le` — the Hadamard bound.
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

/-- Only the terms meeting the support of `O` contribute to its commutator with a sum of
terms: `[∑_{i ∈ s} hᵢ, O] = ∑ [hᵢ, O]` over the `i ∈ s` with `T i` meeting `S`, for `O`
supported on `S`. AKL14, arXiv:1406.3898, proof of `lem:Hadamard-bound`, `low70.tex`,
lines 817–837. -/
theorem commutator_sum_eq_sum_filter_not_disjoint (Φ : Interaction X T) (s : Finset ι)
    {O : Matrix (Config X) (Config X) ℂ} {S : Finset V} (hO : O ∈ supportedOperators X S) :
    (∑ i ∈ s, Φ.term i) * O - O * (∑ i ∈ s, Φ.term i) =
      ∑ i ∈ s.filter (fun i ↦ ¬Disjoint (T i) S), (Φ.term i * O - O * Φ.term i) := by
  classical
  rw [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]
  symm
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro i hi hia
  by_cases hd : Disjoint (T i) S
  · exact sub_eq_zero.mpr (commute_of_mem_supportedOperators_of_disjoint (Φ.mem i) hO hd).eq
  · exact False.elim (hia (Finset.mem_filter.mpr ⟨hi, hd⟩))

/-- A positive contraction has norm at most `1`. -/
private theorem norm_le_one_of_nonneg_le_one {A : Matrix (Config X) (Config X) ℂ} (h0 : 0 ≤ A)
    (h1 : A ≤ 1) : ‖A‖ ≤ 1 :=
  (CStarAlgebra.norm_le_norm_of_le_of_nonneg h1 h0).trans
    (IsStarProjection.norm_le _ (IsStarProjection.one _))

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
  rw [commutator_sum_eq_sum_filter_not_disjoint Φ s hO]
  calc
    ‖∑ i ∈ active, (Φ.term i * O - O * Φ.term i)‖ ≤
        ∑ i ∈ active, ‖Φ.term i * O - O * Φ.term i‖ := norm_sum_le _ _
    _ ≤ ∑ _i ∈ active, ‖O‖ := Finset.sum_le_sum fun i _ ↦
      (Matrix.norm_commutator_le_of_nonneg _ O (hpos i)).trans
        (mul_le_of_le_one_left (norm_nonneg O) (norm_le_one_of_nonneg_le_one (hpos i) (hle i)))
    _ = (active.card : ℝ) * ‖O‖ := by simp only [Finset.sum_const, nsmul_eq_mul]

/-- Let the terms of `Φ` be positive and supported on at most `k` sites, and let the norms of
the terms with index in `s` whose support contains any given site sum to at most `g ≥ 0`. Let
every term with index in `s \ E` commute with `O`, and let `R = ∑_{i ∈ E} ‖hᵢ‖`. Then the
iterate `ad_H^m O` of `H = ∑_{i ∈ s} hᵢ` is a sum of pieces `Y_a` with
`∑ₐ ‖Y_a‖ ≤ R (R + g k) ⋯ (R + (m - 1) g k) ‖O‖`, each attached to a set `S_a` of at most
`m k` sites such that every term with index in `s \ E` and support disjoint from `S_a`
commutes with `Y_a`.

The pieces are the nested commutators `[h_{X_m}, [⋯, [h_{X_1}, O]]]` with `X_{j+1}` in `E` or
meeting `S = X_1 ∪ ⋯ ∪ X_j`; the norms of the terms meeting `S` sum to at most `|S| g ≤ j g k`.
AKL14, arXiv:1406.3898, proof of `lem:Hadamard-bound`, eq. `Kell`, `low70.tex`,
lines 804–868. -/
theorem exists_commutator_iterate_decomposition (Φ : Interaction X T) (s : Finset ι)
    {k : ℕ} {g : ℝ} (hpos : ∀ i, 0 ≤ Φ.term i) (hk : ∀ i, (T i).card ≤ k)
    (hg : ∀ v, ∑ i ∈ s with v ∈ T i, ‖Φ.term i‖ ≤ g) (hg0 : 0 ≤ g)
    {O : Matrix (Config X) (Config X) ℂ} (E : Finset ι)
    (hE : ∀ i ∈ s, i ∉ E → Commute (Φ.term i) O) (m : ℕ) :
    ∃ (N : ℕ) (Y : Fin N → Matrix (Config X) (Config X) ℂ) (S : Fin N → Finset V),
      (GaussianFilter.commutatorCLM (∑ i ∈ s, Φ.term i) ^ m) O = ∑ a, Y a ∧
      (∀ a, ∀ i ∈ s, i ∉ E → Disjoint (T i) (S a) → Commute (Φ.term i) (Y a)) ∧
      (∀ a, (S a).card ≤ m * k) ∧
      ∑ a, ‖Y a‖ ≤ (∏ j ∈ Finset.range m, (∑ i ∈ E, ‖Φ.term i‖ + j * (g * k))) * ‖O‖ := by
  classical
  set H := ∑ i ∈ s, Φ.term i
  set R := ∑ i ∈ E, ‖Φ.term i‖
  have hR : 0 ≤ R := Finset.sum_nonneg fun i _ ↦ norm_nonneg _
  induction m with
  | zero =>
    exact ⟨1, fun _ ↦ O, fun _ ↦ ∅, by simp, fun _ i hi hiE _ ↦ hE i hi hiE,
      fun _ ↦ by simp, by simp⟩
  | succ m ih =>
    obtain ⟨N, Y, S, hsum, hcomm, hcard, hnorm⟩ := ih
    let A : Fin N → Finset ι := fun a ↦ s.filter fun i ↦ i ∈ E ∨ ¬Disjoint (T i) (S a)
    let σ := Σ a : Fin N, ↥(A a)
    let e := Fintype.equivFin σ
    let f : σ → Matrix (Config X) (Config X) ℂ := fun p ↦
      Φ.term p.2.1 * Y p.1 - Y p.1 * Φ.term p.2.1
    let S' : σ → Finset V := fun p ↦ S p.1 ∪ T p.2.1
    have hterm (a : Fin N) :
        H * Y a - Y a * H = ∑ i ∈ A a, (Φ.term i * Y a - Y a * Φ.term i) := by
      rw [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]
      symm
      refine Finset.sum_subset (Finset.filter_subset _ _) fun i hi hiA ↦ ?_
      have hiE : i ∉ E := fun h ↦ hiA (Finset.mem_filter.mpr ⟨hi, Or.inl h⟩)
      have hd : Disjoint (T i) (S a) := by
        by_contra hd
        exact hiA (Finset.mem_filter.mpr ⟨hi, Or.inr hd⟩)
      exact sub_eq_zero.mpr (hcomm a i hi hiE hd).eq
    have hweight (a : Fin N) : ∑ i ∈ A a, ‖Φ.term i‖ ≤ R + m * (g * k) := by
      have hsplit : A a = (s.filter fun i ↦ i ∈ E) ∪ s.filter fun i ↦ ¬Disjoint (T i) (S a) :=
        Finset.filter_or _ _ _
      have hE' : ∑ i ∈ s with i ∈ E, ‖Φ.term i‖ ≤ R :=
        Finset.sum_le_sum_of_subset_of_nonneg (fun i hi ↦ (Finset.mem_filter.mp hi).2)
          fun i _ _ ↦ norm_nonneg _
      have hS : ∑ i ∈ s with ¬Disjoint (T i) (S a), ‖Φ.term i‖ ≤ m * (g * k) := by
        refine (Finset.sum_filter_not_disjoint_le T (fun i ↦ norm_nonneg _) hg (S a)).trans ?_
        have : ((S a).card : ℝ) ≤ m * k := by exact_mod_cast hcard a
        nlinarith
      have hinter := Finset.sum_union_inter (s₁ := s.filter fun i ↦ i ∈ E)
        (s₂ := s.filter fun i ↦ ¬Disjoint (T i) (S a)) (f := fun i ↦ ‖Φ.term i‖)
      have hnn : 0 ≤ ∑ i ∈ (s.filter fun i ↦ i ∈ E) ∩ s.filter fun i ↦ ¬Disjoint (T i) (S a),
          ‖Φ.term i‖ := Finset.sum_nonneg fun i _ ↦ norm_nonneg _
      rw [hsplit]
      linarith
    refine ⟨Fintype.card σ, fun j ↦ f (e.symm j), fun j ↦ S' (e.symm j), ?_, ?_, ?_, ?_⟩
    · rw [Matrix.commutatorCLM_pow_succ_apply, hsum, Finset.mul_sum, Finset.sum_mul,
        ← Finset.sum_sub_distrib]
      calc
        ∑ a, (H * Y a - Y a * H) =
            ∑ a, ∑ i : ↥(A a), (Φ.term i.1 * Y a - Y a * Φ.term i.1) := by
          refine Finset.sum_congr rfl fun a _ ↦ ?_
          rw [hterm a, ← Finset.sum_coe_sort (A a)]
        _ = ∑ p : σ, f p := (Fintype.sum_sigma f).symm
        _ = ∑ j, f (e.symm j) := (Equiv.sum_comp e.symm f).symm
    · intro j i hi hiE hd
      have hd' := Finset.disjoint_union_right.mp hd
      have hY := hcomm (e.symm j).1 i hi hiE hd'.1
      have hh : Commute (Φ.term i) (Φ.term (e.symm j).2.1) :=
        commute_of_mem_supportedOperators_of_disjoint (Φ.mem i) (Φ.mem _) hd'.2
      exact (hh.mul_right hY).sub_right (hY.mul_right hh)
    · intro j
      calc
        (S' (e.symm j)).card ≤ (S (e.symm j).1).card + (T (e.symm j).2.1).card :=
          Finset.card_union_le _ _
        _ ≤ m * k + k := add_le_add (hcard _) (hk _)
        _ = (m + 1) * k := by ring
    · calc
        ∑ j, ‖f (e.symm j)‖ = ∑ p : σ, ‖f p‖ := Equiv.sum_comp e.symm (fun p ↦ ‖f p‖)
        _ = ∑ a, ∑ i : ↥(A a), ‖Φ.term i.1 * Y a - Y a * Φ.term i.1‖ :=
          Fintype.sum_sigma _
        _ ≤ ∑ a, ∑ i : ↥(A a), ‖Φ.term i.1‖ * ‖Y a‖ :=
          Finset.sum_le_sum fun a _ ↦ Finset.sum_le_sum fun i _ ↦
            Matrix.norm_commutator_le_of_nonneg _ _ (hpos _)
        _ = ∑ a, (∑ i ∈ A a, ‖Φ.term i‖) * ‖Y a‖ := by
          refine Finset.sum_congr rfl fun a _ ↦ ?_
          rw [Finset.sum_mul, ← Finset.sum_coe_sort (A a)]
        _ ≤ ∑ a, (R + m * (g * k)) * ‖Y a‖ :=
          Finset.sum_le_sum fun a _ ↦ mul_le_mul_of_nonneg_right (hweight a) (norm_nonneg _)
        _ = (R + m * (g * k)) * ∑ a, ‖Y a‖ := (Finset.mul_sum _ _ _).symm
        _ ≤ (R + m * (g * k)) * ((∏ j ∈ Finset.range m, (R + j * (g * k))) * ‖O‖) :=
          mul_le_mul_of_nonneg_left hnorm (by positivity)
        _ = (∏ j ∈ Finset.range (m + 1), (R + j * (g * k))) * ‖O‖ := by
          rw [Finset.prod_range_succ]
          ring

/-- **Commutator growth for a norm-weighted degree.** In the setting of
`exists_commutator_iterate_decomposition`,
`‖ad_H^m O‖ ≤ R (R + g k) ⋯ (R + (m - 1) g k) ‖O‖`.
AKL14, arXiv:1406.3898, proof of `lem:Hadamard-bound`, `low70.tex`, lines 838–868. -/
theorem norm_commutator_iterate_le_prod (Φ : Interaction X T) (s : Finset ι)
    {k : ℕ} {g : ℝ} (hpos : ∀ i, 0 ≤ Φ.term i) (hk : ∀ i, (T i).card ≤ k)
    (hg : ∀ v, ∑ i ∈ s with v ∈ T i, ‖Φ.term i‖ ≤ g) (hg0 : 0 ≤ g)
    {O : Matrix (Config X) (Config X) ℂ} (E : Finset ι)
    (hE : ∀ i ∈ s, i ∉ E → Commute (Φ.term i) O) (m : ℕ) :
    ‖(GaussianFilter.commutatorCLM (∑ i ∈ s, Φ.term i) ^ m) O‖ ≤
      (∏ j ∈ Finset.range m, (∑ i ∈ E, ‖Φ.term i‖ + j * (g * k))) * ‖O‖ := by
  obtain ⟨N, Y, S, hsum, -, -, hnorm⟩ :=
    exists_commutator_iterate_decomposition Φ s hpos hk hg hg0 E hE m
  rw [hsum]
  exact (norm_sum_le _ _).trans hnorm

/-- Let the terms of `Φ` be positive contractions on at most `k` sites, and let every site lie
in the supports of at most `g` terms with index in `s`. If `O` is supported on at most `k`
sites, then `‖ad_H^m O‖ ≤ (g k)^m m! ‖O‖` for `H = ∑_{i ∈ s} hᵢ`.
AKL14, arXiv:1406.3898, proof of `lem:Hadamard-bound`, `low70.tex`, lines 804–877, with
`R ≤ g k`: the case of `norm_commutator_iterate_le_prod` where the terms meeting the support
of `O` are taken for `E`. -/
theorem norm_commutator_iterate_le (Φ : Interaction X T) (s : Finset ι)
    {k g : ℕ} (hpos : ∀ i, 0 ≤ Φ.term i) (hle : ∀ i, Φ.term i ≤ 1)
    (hk : ∀ i, (T i).card ≤ k) (hg : ∀ v, (s.filter fun i ↦ v ∈ T i).card ≤ g)
    {O : Matrix (Config X) (Config X) ℂ} {S₀ : Finset V} (hO : O ∈ supportedOperators X S₀)
    (hS₀ : S₀.card ≤ k) (m : ℕ) :
    ‖(GaussianFilter.commutatorCLM (∑ i ∈ s, Φ.term i) ^ m) O‖ ≤
      ((g * k : ℕ) : ℝ) ^ m * (m.factorial : ℝ) * ‖O‖ := by
  classical
  set E := s.filter fun i ↦ ¬Disjoint (T i) S₀
  have hgw (v : V) : ∑ i ∈ s with v ∈ T i, ‖Φ.term i‖ ≤ g := by
    calc
      _ ≤ ∑ i ∈ s with v ∈ T i, (1 : ℝ) :=
        Finset.sum_le_sum fun i _ ↦ norm_le_one_of_nonneg_le_one (hpos i) (hle i)
      _ ≤ g := by simpa using (Nat.cast_le (α := ℝ)).mpr (hg v)
  have hE : ∀ i ∈ s, i ∉ E → Commute (Φ.term i) O := fun i hi hiE ↦
    commute_of_mem_supportedOperators_of_disjoint (Φ.mem i) hO
      (not_not.mp fun hd ↦ hiE (Finset.mem_filter.mpr ⟨hi, hd⟩))
  have hR : ∑ i ∈ E, ‖Φ.term i‖ ≤ g * k := by
    refine (Finset.sum_filter_not_disjoint_le T (fun i ↦ norm_nonneg _) hgw S₀).trans ?_
    have : (S₀.card : ℝ) ≤ k := by exact_mod_cast hS₀
    nlinarith [(Nat.cast_nonneg g : (0 : ℝ) ≤ g)]
  refine (norm_commutator_iterate_le_prod Φ s hpos hk hgw (Nat.cast_nonneg g) E hE m).trans
    (mul_le_mul_of_nonneg_right ?_ (norm_nonneg O))
  have hprod : ∏ j ∈ Finset.range m, ((g : ℝ) * k + j * (g * k)) =
      ((g * k : ℕ) : ℝ) ^ m * m.factorial := by
    induction m with
    | zero => simp
    | succ m ih =>
      rw [Finset.prod_range_succ, ih, pow_succ, Nat.factorial_succ]
      push_cast
      ring
  rw [← hprod]
  exact Finset.prod_le_prod₀ (fun j _ ↦ by positivity) fun j _ ↦ by linarith

/-- **The Hadamard bound** (AKL14, Lemma `lem:Hadamard-bound`). Let the terms of `Φ` be
positive and supported on at most `k` sites, and let the norms of the terms with index in `s`
whose support contains any given site sum to at most `g`. For an operator `A` and a finite set
`E` of indices such that every term with index in `s \ E` commutes with `A`, put
`R = ∑_{i ∈ E} ‖hᵢ‖` and `H = ∑_{i ∈ s} hᵢ`. Then for `0 ≤ t < 1/(g k)`,
`‖e^{tH} A e^{-tH}‖ ≤ ‖A‖ (1 - g k t)^{-R/(g k)}`.

**Local fix (the set `E_A`):** the printed lemma assumes `[H, A] = ∑_{X ∈ E_A} [h_X, A]`; its
proof uses that every term outside `E_A` commutes with `A`, which is the hypothesis here. See
`docs/paper-gaps/akl14_hadamard_bound_scope.tex`.

AKL14, arXiv:1406.3898, `lem:Hadamard-bound`, `low70.tex`, lines 795–880, in the setting of
`sec:settings`, lines 400–445. -/
theorem norm_exp_conjugation_le (Φ : Interaction X T) (s : Finset ι)
    {k : ℕ} {g : ℝ} (hpos : ∀ i, 0 ≤ Φ.term i) (hk : ∀ i, (T i).card ≤ k)
    (hg : ∀ v, ∑ i ∈ s with v ∈ T i, ‖Φ.term i‖ ≤ g)
    {A : Matrix (Config X) (Config X) ℂ} (E : Finset ι)
    (hE : ∀ i ∈ s, i ∉ E → Commute (Φ.term i) A) {t : ℝ} (ht0 : 0 ≤ t)
    (ht : t < 1 / (g * k)) :
    ‖NormedSpace.exp ((t : ℂ) • ∑ i ∈ s, Φ.term i) * A *
      NormedSpace.exp (-((t : ℂ) • ∑ i ∈ s, Φ.term i))‖ ≤
      ‖A‖ * (1 - g * k * t) ^ (-((∑ i ∈ E, ‖Φ.term i‖) / (g * k))) := by
  have hgk : 0 < g * k := one_div_pos.mp (ht0.trans_lt ht)
  have hg0 : 0 ≤ g := by
    by_contra h
    exact absurd hgk (not_lt.mpr (mul_nonpos_of_nonpos_of_nonneg (le_of_not_ge h)
      (Nat.cast_nonneg k)))
  exact Matrix.norm_exp_conjugation_le_of_growth _ A hgk ht0
    (by rw [lt_div_iff₀ hgk] at ht; linarith)
    (norm_commutator_iterate_le_prod Φ s hpos hk hg hg0 E hE)

/-- **Short imaginary-time conjugation for bounded support and degree.** Let the terms of `Φ`
be positive contractions on at most `k` sites, and let every site lie in the supports of at
most `g` terms with index in `s`. If `O` is supported on at most `k` sites, then for every
`z ∈ ℂ` and `0 ≤ t` with `2 g k t ≤ 1`, with `H = ∑_{i ∈ s} hᵢ`,
`‖e^{t(H - z)} O e^{-t(H - z)}‖ ≤ 2 ‖O‖`.
AKL14, arXiv:1406.3898, `lem:Hadamard-bound`, `low70.tex`, lines 795–880, in the case
`R ≤ g k`, through the factorial growth `(g k)^m m!`. -/
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
