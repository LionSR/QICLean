/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Algebra.Combinatorics.GateIncidence
import QICLean.ManyBody.Dynamics.GraphPropagation
import QICLean.ManyBody.Sites.Placement.Basic
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Comparison of Hamiltonian evolutions

The interaction-picture derivative compares two canonical Heisenberg evolutions through
commutators with the Hamiltonian difference. This yields finite-dimensional bounds
for spatial Hamiltonian truncation.

Two forms of the truncation bound are proved. Evolving under the full Hamiltonian, every term
outside the simulated region `L` enters with the Lieb–Robinson factor at distance `d`, so the
bound carries the total norm of the deleted terms. Evolving under the terms inside `L`, the
evolved observable stays in `L` and commutes with the deleted terms disjoint from `L`; only the
terms crossing the boundary of `L` enter. Their total norm is at most `b` times the number of
sites of `L` lying in a crossing term, a bound independent of the sites outside `L`.

## Main results

* `ManyBody.norm_heisenbergEvolution_sub_spatial_truncation_le` — the deleted-term form.
* `ManyBody.norm_heisenbergEvolution_sub_spatial_truncation_le_boundary` — the boundary form.
* `ManyBody.Interaction.sum_norm_term_crossing_le` — the total norm of the crossing terms.
-/

open NormedSpace Matrix
open scoped Matrix.Norms.L2Operator

namespace ManyBody

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The interaction-picture derivative for two Hamiltonians. No Hermiticity is needed
for this algebraic differentiation identity. -/
theorem hasDerivAt_relative_heisenberg (H K A : Matrix n n ℂ) (t : ℝ) :
    HasDerivAt (fun s ↦ heisenbergEvolution H (-s) (heisenbergEvolution K s A))
      (heisenbergEvolution H (-t)
        (Complex.I • ((K - H) * heisenbergEvolution K t A -
          heisenbergEvolution K t A * (K - H)))) t := by
  have hinner := hasDerivAt_exp_conjugation_variable (Complex.I • K)
    (hasDerivAt_const t A)
  have houter := hasDerivAt_exp_conjugation_variable (-(Complex.I • H)) hinner
  have hc (s : ℝ) : Commute K (exp (s • (Complex.I • K))) :=
    (((Commute.refl K).smul_right Complex.I).smul_right s).exp_right
  have hc' (s : ℝ) (B : Matrix n n ℂ) :
      K * (exp (s • (Complex.I • K)) * B) = exp (s • (Complex.I • K)) * (K * B) := by
    rw [← mul_assoc, (hc s).eq, mul_assoc]
  have hcneg (B : Matrix n n ℂ) :
      K * (exp (-(t • (Complex.I • K))) * B) = exp (-(t • (Complex.I • K))) * (K * B) := by
    simpa only [neg_smul] using hc' (-t) B
  convert houter using 1
  · simp only [heisenbergEvolution_def, smul_neg, neg_smul, neg_neg]
  · simp only [heisenbergEvolution_def, smul_neg, neg_smul, neg_neg, mul_smul_comm,
      smul_mul_assoc, smul_sub, sub_mul, mul_sub, add_zero]
    simp only [mul_add, add_mul, mul_sub, sub_mul, mul_neg, neg_mul,
      mul_smul_comm, smul_mul_assoc, mul_assoc, hc', hcneg]
    module

/-- A uniform commutator bound controls the difference of two exact evolutions,
including at negative time. The observable need not be Hermitian. -/
theorem norm_heisenbergEvolution_sub_le_of_commutator_bound
    {H K : Matrix n n ℂ} (hH : H.IsHermitian) (A : Matrix n n ℂ) (t ε : ℝ)
    (hbound : ∀ s ∈ Set.uIcc 0 t,
      ‖(K - H) * heisenbergEvolution K s A -
        heisenbergEvolution K s A * (K - H)‖ ≤ ε) :
    ‖heisenbergEvolution K t A - heisenbergEvolution H t A‖ ≤ ε * |t| := by
  let F := fun s ↦ heisenbergEvolution H (-s) (heisenbergEvolution K s A)
  have hd := hasDerivAt_relative_heisenberg H K A
  have hle := Convex.norm_image_sub_le_of_norm_deriv_le
    (fun s _ ↦ (hd s).differentiableAt) (fun s hs ↦ by
      rw [(hd s).deriv, norm_heisenbergEvolution hH, norm_smul, Complex.norm_I, one_mul]
      exact hbound s hs) (convex_uIcc (𝕜 := ℝ) 0 t) (Set.left_mem_uIcc) (Set.right_mem_uIcc)
  have hcancel (s : ℝ) : Matrix.hermitianUnitaryPath H (-s) *
      Matrix.hermitianUnitaryPath H s = 1 := by
    rw [← Matrix.hermitianUnitaryPath_add, neg_add_cancel, Matrix.hermitianUnitaryPath_zero]
  have hinv : heisenbergEvolution H (-t) (heisenbergEvolution H t A) = A := by
    simp only [heisenbergEvolution, neg_neg, mul_assoc]
    rw [← mul_assoc (Matrix.hermitianUnitaryPath H (-t)), hcancel, one_mul, mul_one]
  have heq : F t - F 0 = heisenbergEvolution H (-t)
      (heisenbergEvolution K t A - heisenbergEvolution H t A) := by
    simp only [F, heisenbergEvolution, neg_zero, Matrix.hermitianUnitaryPath,
      zero_smul, exp_zero, one_mul, mul_one] at *
    rw [mul_sub, sub_mul, hinv]
  rw [heq, norm_heisenbergEvolution hH] at hle
  simpa [Real.norm_eq_abs] using hle

/-- Termwise commutator estimates for a finite Hamiltonian perturbation add without
introducing a factor depending on the dimension of the Hilbert space. -/
theorem norm_heisenbergEvolution_sub_le_of_sum_commutator_bound
    {ι : Type*} (D : Finset ι) (B : ι → Matrix n n ℂ)
    {H K : Matrix n n ℂ} (hH : H.IsHermitian) (hDiff : K - H = ∑ j ∈ D, B j)
    (A : Matrix n n ℂ) (t : ℝ) (ε : ι → ℝ)
    (hbound : ∀ j ∈ D, ∀ s ∈ Set.uIcc 0 t,
      ‖heisenbergEvolution K s A * B j - B j * heisenbergEvolution K s A‖ ≤ ε j) :
    ‖heisenbergEvolution K t A - heisenbergEvolution H t A‖ ≤ (∑ j ∈ D, ε j) * |t| := by
  apply norm_heisenbergEvolution_sub_le_of_commutator_bound hH
  intro s hs
  rw [hDiff, Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]
  exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun j hj ↦ by
    rw [norm_sub_rev]
    exact hbound j hj s hs)

section Sites

variable {V : Type*} [Fintype V] [DecidableEq V] {X : V → Type*}
  [∀ v, Fintype (X v)] [∀ v, DecidableEq (X v)]
  {ι : Type*} [Fintype ι] {T : ι → Finset V}

/-- Deleting terms distant from the observable gives an exponential distance bound.
The explicit sum of norms of the deleted terms is retained: no volume-uniform bound
on this sum is assumed or proved. -/
theorem norm_heisenbergEvolution_sub_le_graphDistance
    (G : SimpleGraph V) (Φ : Interaction X T)
    (hHerm : ∀ j, (Φ.term j).IsHermitian)
    (R : ℕ) (hDiam : ∀ j, ∀ x ∈ T j, ∀ y ∈ T j, G.edist x y ≤ R)
    (vR : ℕ) (hCard : ∀ j, (T j).card ≤ vR)
    (b : ℝ) (hBudget : ∀ x, ∑ j ∈ Finset.univ.filter (fun j ↦ x ∈ T j), ‖Φ.term j‖ ≤ b)
    (D : Finset ι) {H : Matrix (Config X) (Config X) ℂ} (hH : H.IsHermitian)
    (hDiff : Φ.hamiltonian - H = ∑ j ∈ D, Φ.term j)
    (S : Finset V) {A : Matrix (Config X) (Config X) ℂ}
    (hA : A ∈ supportedOperators X S) (μ : ℝ) (hμ : 0 ≤ μ) (d : ℕ)
    (hd : ∀ j ∈ D, ∀ x ∈ S, ∀ y ∈ T j, (d : ℕ∞) ≤ G.edist x y) (t : ℝ) :
    ‖heisenbergEvolution Φ.hamiltonian t A - heisenbergEvolution H t A‖ ≤
      (4 * (S.card : ℝ) * ‖A‖ * (∑ j ∈ D, ‖Φ.term j‖) *
        Real.exp ((4 * vR * |b| * Real.exp (2 * μ * R)) * |t| - μ * d)) * |t| := by
  let c := 4 * (S.card : ℝ) * ‖A‖
  let v := 4 * (vR : ℝ) * |b| * Real.exp (2 * μ * R)
  have hv : 0 ≤ v := by dsimp [v]; positivity
  have htime {s : ℝ} (hs : s ∈ Set.uIcc 0 t) : |s| ≤ |t| := by
    simpa only [sub_zero] using Set.abs_sub_left_of_mem_uIcc hs
  have h := norm_heisenbergEvolution_sub_le_of_sum_commutator_bound D Φ.term hH hDiff A t
    (fun j ↦ c * ‖Φ.term j‖ * Real.exp (v * |t| - μ * d)) (by
      intro j hj s hs
      have hb := norm_heisenberg_commutator_le_graphDistance_finsets_numeric G Φ hHerm
        R hDiam vR hCard b hBudget S hA (T j) (Φ.mem j) μ hμ d (hd j hj) s
      exact hb.trans (mul_le_mul_of_nonneg_left
        (Real.exp_le_exp.mpr (sub_le_sub_right (mul_le_mul_of_nonneg_left (htime hs) hv) _))
        (by positivity)))
  simpa only [← Finset.sum_mul, ← Finset.mul_sum, c, v] using h

omit [Fintype V] [DecidableEq V] [Fintype ι] in
/-- A term not inside `L` is at distance at least `d` from `S` when every site outside `L` is at
distance at least `d + R` from `S` and the terms have diameter at most `R`. -/
private theorem le_edist_of_not_subset (G : SimpleGraph V) (R : ℕ)
    (hDiam : ∀ j, ∀ x ∈ T j, ∀ y ∈ T j, G.edist x y ≤ R) (L S : Finset V) (d : ℕ)
    (hd : ∀ x ∈ S, ∀ z ∉ L, (d : ℕ∞) + R ≤ G.edist x z) {j : ι} (hj : ¬ T j ⊆ L)
    {x y : V} (hx : x ∈ S) (hy : y ∈ T j) : (d : ℕ∞) ≤ G.edist x y := by
  obtain ⟨z, hz, hzL⟩ := Finset.not_subset.mp hj
  have hdist : (d : ℕ∞) + R ≤ G.edist x y + R :=
    (hd x hx z hzL).trans ((G.edist_triangle (u := x) (v := y) (w := z)).trans
      (add_le_add_right (hDiam j y hy z hz) _))
  by_cases htop : G.edist x y = ⊤
  · simp [htop]
  · lift G.edist x y to ℕ using htop with k hk
    exact_mod_cast (Nat.le_of_add_le_add_right (by exact_mod_cast hdist) : d ≤ k)

/-- The exact evolution generated by the terms wholly inside `L` approximates the full
Hamiltonian on `S`, provided every site outside `L` is at distance at least `d + R`
from `S`. The interaction range accounts for the loss of `R` at the boundary.
The deleted-term norm sum is explicit; no infinite-system limit is asserted. -/
theorem norm_heisenbergEvolution_sub_spatial_truncation_le
    (G : SimpleGraph V) (Φ : Interaction X T)
    (hHerm : ∀ j, (Φ.term j).IsHermitian)
    (R : ℕ) (hDiam : ∀ j, ∀ x ∈ T j, ∀ y ∈ T j, G.edist x y ≤ R)
    (vR : ℕ) (hCard : ∀ j, (T j).card ≤ vR)
    (b : ℝ) (hBudget : ∀ x, ∑ j ∈ Finset.univ.filter (fun j ↦ x ∈ T j), ‖Φ.term j‖ ≤ b)
    (L S : Finset V) {A : Matrix (Config X) (Config X) ℂ}
    (hA : A ∈ supportedOperators X S) (μ : ℝ) (hμ : 0 ≤ μ) (d : ℕ)
    (hd : ∀ x ∈ S, ∀ z ∉ L, (d : ℕ∞) + R ≤ G.edist x z) (t : ℝ) :
    ‖heisenbergEvolution Φ.hamiltonian t A -
      heisenbergEvolution (∑ j ∈ Finset.univ.filter (fun j ↦ T j ⊆ L), Φ.term j) t A‖ ≤
      (4 * (S.card : ℝ) * ‖A‖ *
        (∑ j ∈ Finset.univ.filter (fun j ↦ ¬ T j ⊆ L), ‖Φ.term j‖) *
        Real.exp ((4 * vR * |b| * Real.exp (2 * μ * R)) * |t| - μ * d)) * |t| := by
  classical
  apply norm_heisenbergEvolution_sub_le_graphDistance G Φ hHerm R hDiam vR hCard b hBudget
    (Finset.univ.filter (fun j ↦ ¬ T j ⊆ L))
    ((isSelfAdjoint_sum _ fun j _ ↦ (hHerm j).isSelfAdjoint).isHermitian) ?_ S hA μ hμ d ?_ t
  · apply sub_eq_iff_eq_add.mpr
    simpa [Interaction.hamiltonian, add_comm] using
      (Finset.sum_filter_add_sum_filter_not Finset.univ (fun j ↦ T j ⊆ L) Φ.term).symm
  · intro j hj x hx y hy
    exact le_edist_of_not_subset G R hDiam L S d hd (Finset.mem_filter.mp hj).2 hx hy

/-- The total norm of the terms crossing the boundary of `L`, meeting `L` without lying in it,
is at most `b` times the number of sites of `L` that lie in a crossing term. -/
theorem Interaction.sum_norm_term_crossing_le (Φ : Interaction X T) (b : ℝ)
    (hBudget : ∀ x, ∑ j ∈ Finset.univ.filter (fun j ↦ x ∈ T j), ‖Φ.term j‖ ≤ b)
    (L : Finset V) :
    ∑ j ∈ Finset.univ.filter (fun j ↦ ¬ T j ⊆ L ∧ ¬ Disjoint (T j) L), ‖Φ.term j‖ ≤
      b * (L.filter fun x ↦ ∃ j, x ∈ T j ∧ ¬ T j ⊆ L).card := by
  classical
  refine le_trans ?_ (Finset.sum_filter_not_disjoint_le T (fun j ↦ norm_nonneg (Φ.term j))
    hBudget _)
  refine Finset.sum_le_sum_of_subset_of_nonneg (fun j hj ↦ ?_) fun j _ _ ↦ norm_nonneg _
  obtain ⟨-, hjL, hjD⟩ := Finset.mem_filter.mp hj
  obtain ⟨x, hxT, hxL⟩ := Finset.not_disjoint_iff.mp hjD
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, Finset.not_disjoint_iff.mpr
    ⟨x, hxT, Finset.mem_filter.mpr ⟨hxL, j, hxT, hjL⟩⟩⟩

/-- **Spatial truncation, boundary form.** The exact evolution generated by the terms wholly
inside `L` approximates the full Hamiltonian evolution of an observable on `S ⊆ L`, provided
every site outside `L` is at distance at least `d + R` from `S`. Only the terms crossing the
boundary of `L` enter, with total norm at most `b` times the number of sites of `L` lying in a
crossing term (`Interaction.sum_norm_term_crossing_le`), independently of the sites outside
`L`. The evolution under the kept terms leaves the operators on `L` in place, so it commutes
with every deleted term disjoint from `L`. -/
theorem norm_heisenbergEvolution_sub_spatial_truncation_le_boundary
    (G : SimpleGraph V) (Φ : Interaction X T)
    (hHerm : ∀ j, (Φ.term j).IsHermitian)
    (R : ℕ) (hDiam : ∀ j, ∀ x ∈ T j, ∀ y ∈ T j, G.edist x y ≤ R)
    (vR : ℕ) (hCard : ∀ j, (T j).card ≤ vR)
    (b : ℝ) (hBudget : ∀ x, ∑ j ∈ Finset.univ.filter (fun j ↦ x ∈ T j), ‖Φ.term j‖ ≤ b)
    (L S : Finset V) (hSL : S ⊆ L) {A : Matrix (Config X) (Config X) ℂ}
    (hA : A ∈ supportedOperators X S) (μ : ℝ) (hμ : 0 ≤ μ) (d : ℕ)
    (hd : ∀ x ∈ S, ∀ z ∉ L, (d : ℕ∞) + R ≤ G.edist x z) (t : ℝ) :
    ‖heisenbergEvolution Φ.hamiltonian t A -
      heisenbergEvolution (∑ j ∈ Finset.univ.filter (fun j ↦ T j ⊆ L), Φ.term j) t A‖ ≤
      (4 * (S.card : ℝ) * ‖A‖ *
        (∑ j ∈ Finset.univ.filter (fun j ↦ ¬ T j ⊆ L ∧ ¬ Disjoint (T j) L), ‖Φ.term j‖) *
        Real.exp ((4 * vR * |b| * Real.exp (2 * μ * R)) * |t| - μ * d)) * |t| := by
  classical
  -- The interaction of the kept terms, the others replaced by `0`.
  let Ψ : Interaction X T := ⟨fun j ↦ if T j ⊆ L then Φ.term j else 0, fun j ↦ by
    split_ifs
    exacts [Φ.mem j, zero_mem _]⟩
  have hΨ : Ψ.hamiltonian = ∑ j ∈ Finset.univ.filter (fun j ↦ T j ⊆ L), Φ.term j := by
    simp only [Interaction.hamiltonian, Ψ, Finset.sum_filter]
  have hΨHerm (j : ι) : (Ψ.term j).IsHermitian := by
    change (if T j ⊆ L then Φ.term j else 0).IsHermitian
    split_ifs
    exacts [hHerm j, isHermitian_zero]
  have hΨBudget (x : V) :
      ∑ j ∈ Finset.univ.filter (fun j ↦ x ∈ T j), ‖Ψ.term j‖ ≤ b :=
    (Finset.sum_le_sum fun j _ ↦ by
      change ‖if T j ⊆ L then Φ.term j else 0‖ ≤ ‖Φ.term j‖
      split_ifs <;> simp).trans (hBudget x)
  have hKL : Ψ.hamiltonian ∈ supportedOperators X L := by
    rw [hΨ]
    exact sum_mem fun j hj ↦ supportedOperators_mono (Finset.mem_filter.mp hj).2 (Φ.mem j)
  have hAL : A ∈ supportedOperators X L := supportedOperators_mono hSL hA
  let c := 4 * (S.card : ℝ) * ‖A‖
  let v := 4 * (vR : ℝ) * |b| * Real.exp (2 * μ * R)
  have hv : 0 ≤ v := by dsimp [v]; positivity
  have htime {s : ℝ} (hs : s ∈ Set.uIcc 0 t) : |s| ≤ |t| := by
    simpa only [sub_zero] using Set.abs_sub_left_of_mem_uIcc hs
  let D := Finset.univ.filter (fun j ↦ ¬ T j ⊆ L)
  have hDiff : Ψ.hamiltonian - Φ.hamiltonian = ∑ j ∈ D, -Φ.term j := by
    rw [Finset.sum_neg_distrib, hΨ, Interaction.hamiltonian,
      ← Finset.sum_filter_add_sum_filter_not Finset.univ (fun j ↦ T j ⊆ L) Φ.term]
    abel
  have h := norm_heisenbergEvolution_sub_le_of_sum_commutator_bound D (fun j ↦ -Φ.term j)
    (isSelfAdjoint_sum _ fun j _ ↦ (hHerm j).isSelfAdjoint).isHermitian hDiff A t
    (fun j ↦ if Disjoint (T j) L then 0 else c * ‖Φ.term j‖ * Real.exp (v * |t| - μ * d)) (by
      intro j hj s hs
      have hneg : heisenbergEvolution Ψ.hamiltonian s A * -Φ.term j -
          -Φ.term j * heisenbergEvolution Ψ.hamiltonian s A =
          -(heisenbergEvolution Ψ.hamiltonian s A * Φ.term j -
            Φ.term j * heisenbergEvolution Ψ.hamiltonian s A) := by
        rw [Matrix.mul_neg, Matrix.neg_mul]
        abel
      rw [hneg, norm_neg]
      split_ifs with hdisj
      · have hev : heisenbergEvolution Ψ.hamiltonian s A ∈ supportedOperators X L :=
          mul_mem (mul_mem (hermitianUnitaryPath_mem_supportedOperators hKL s) hAL)
            (hermitianUnitaryPath_mem_supportedOperators hKL (-s))
        rw [(commute_of_mem_supportedOperators_of_disjoint hev (Φ.mem j) hdisj.symm).eq,
          sub_self, norm_zero]
      · have hb := norm_heisenberg_commutator_le_graphDistance_finsets_numeric G Ψ hΨHerm
          R hDiam vR hCard b hΨBudget S hA (T j) (Φ.mem j) μ hμ d
          (fun x hx y hy ↦ le_edist_of_not_subset G R hDiam L S d hd
            (Finset.mem_filter.mp hj).2 hx hy) s
        exact hb.trans (mul_le_mul_of_nonneg_left
          (Real.exp_le_exp.mpr (sub_le_sub_right (mul_le_mul_of_nonneg_left (htime hs) hv) _))
          (by positivity)))
  rw [norm_sub_rev, ← hΨ]
  refine h.trans_eq ?_
  congr 1
  rw [Finset.mul_sum, Finset.sum_mul, ← Finset.filter_filter,
    Finset.sum_filter (p := fun j ↦ ¬ Disjoint (T j) L)]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [ite_not]

end Sites
end ManyBody
