/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Algebra.Combinatorics.FinSum
import QICLean.ManyBody.Dynamics.BoundedDegreeImaginaryTime
import QICLean.ManyBody.Hamiltonian.Models
import QICLean.Spectral.Eigenvalue.GroundEnergyBounds
import Mathlib.Tactic.FinCases

/-!
# Consecutive regions of a chain and the bond Hamiltonians on them

For a bond interaction on the chain of `L` sites, the bonds `{i, i + 1}` internal to an interval
`[lo, hi)` (those with `lo ≤ i` and `i + 1 < hi`) sum to an operator supported on the interval.
The internal sums of consecutive intervals with ordered endpoints therefore commute. Four cuts
`k1 ≤ k2 ≤ k3 ≤ k4 ≤ L` divide the chain into five intervals and the bonds into five internal
families and at most four crossing bonds. For positive bond terms of norm at most one, each of
these sums is positive and bounded by its number of terms, and together they make up the
Hamiltonian. Coincident cuts, empty intervals and the empty chain are included.

For a sum `H` of positive bond terms of norm at most one, an operator supported on two adjacent
sites satisfies `‖exp(tH) O exp(-tH)‖ ≤ 2 ‖O‖` for `0 ≤ t ≤ 1/8`, also after a scalar shift of
`H`: it is the case `k = g = 2` of `ManyBody.Interaction.norm_exp_conjugation_shift_le_two`,
since every bond has two sites and every site lies in at most two bonds.

## Main results

* `ManyBody.BondInteraction.isSupportedOn_sum_internal_bonds` — the support of the sum of the
  internal bonds.
* `ManyBody.BondInteraction.pairwise_commute_sum_internal_consecutive_regions` — the internal sums
  of consecutive intervals commute.
* `ManyBody.BondInteraction.five_region_original_bond_data` — the five internal sums and the
  crossing bonds at four cuts.
* `ManyBody.BondInteraction.norm_exp_conjugation_shift_le_two` — the imaginary-time conjugation
  bound.

## References

* I. Arad, Z. Landau, U. Vazirani and T. Vidick, arXiv:1602.08828v2, `def:hard-trunc`,
  lines 873–886, `c:goodagsphardtrunc`, lines 979–1005, and Theorem `t:ais`, lines 1010–1024.
* I. Arad, T. Kuwahara and Z. Landau, arXiv:1406.3898, Lemma `lem:Hadamard-bound`,
  `low70.tex`, lines 795–880.
-/

open scoped Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace ManyBody

/-- The sum of the bond terms internal to the interval `[lo, hi)` is supported on the interval.
Arad–Landau–Vazirani–Vidick, arXiv:1602.08828v2, `def:hard-trunc`, lines 873–886. -/
theorem BondInteraction.isSupportedOn_sum_internal_bonds (L q lo hi : ℕ)
    (Φ : BondInteraction L q) :
    IsSupportedOn (X := fun _ ↦ Fin q)
      (∑ i ∈ (Finset.univ : Finset (Fin (L - 1))).filter
        (fun j ↦ lo ≤ j.val ∧ j.val + 1 < hi), Φ.term i) (interval L lo hi) := by
  change _ ∈ supportedOperators _ _
  exact sum_mem fun i hiI ↦
    (Φ.mem i).mono (internal_bond_support_subset hiI)

/-- Consecutive half-open intervals with ordered endpoints are pairwise disjoint, including
empty intervals. -/
private theorem pairwise_disjoint_consecutive_intervals
    {L m : ℕ} (k : Fin (m + 1) → ℕ) (hk : Monotone k) :
    Pairwise fun i j : Fin m ↦
      Disjoint (interval L (k i.castSucc) (k i.succ))
        (interval L (k j.castSucc) (k j.succ)) := by
  have hlt (i j : Fin m) (hij : i < j) :
      Disjoint (interval L (k i.castSucc) (k i.succ))
        (interval L (k j.castSucc) (k j.succ)) := by
    have hs : i.succ ≤ j.castSucc := by
      change i.val + 1 ≤ j.val
      exact hij
    have hends := hk hs
    apply Finset.disjoint_left.mpr
    intro x hx hy
    have hx' := mem_interval.mp hx
    have hy' := mem_interval.mp hy
    omega
  intro i j hij
  rcases lt_or_gt_of_ne hij with hij | hji
  · exact hlt i j hij
  · exact (hlt j i hji).symm

/-- The sums of the bond terms internal to consecutive intervals commute, since they are
supported on disjoint intervals. Arad–Landau–Vazirani–Vidick, arXiv:1602.08828v2,
`def:hard-trunc`, lines 873–886, and Theorem `t:ais`, lines 1010–1024. -/
theorem BondInteraction.pairwise_commute_sum_internal_consecutive_regions
    {L q m : ℕ} (k : Fin (m + 1) → ℕ) (hk : Monotone k)
    (Φ : BondInteraction L q) :
    Pairwise fun i j : Fin m ↦
      Commute
        (∑ r ∈ (Finset.univ : Finset (Fin (L - 1))).filter
          (fun r ↦ k i.castSucc ≤ r.val ∧ r.val + 1 < k i.succ), Φ.term r)
        (∑ r ∈ (Finset.univ : Finset (Fin (L - 1))).filter
          (fun r ↦ k j.castSucc ≤ r.val ∧ r.val + 1 < k j.succ), Φ.term r) := by
  intro i j hij
  refine commute_of_mem_supportedOperators_of_disjoint ?_ ?_
    (pairwise_disjoint_consecutive_intervals k hk hij)
  · exact (BondInteraction.isSupportedOn_sum_internal_bonds L q (k i.castSucc) (k i.succ) Φ)
  · exact (BondInteraction.isSupportedOn_sum_internal_bonds L q (k j.castSucc) (k j.succ) Φ)

/-- At most four bonds cross four cuts. -/
private theorem card_four_cut_crossing_le (L k1 k2 k3 k4 : ℕ) :
    ((Finset.univ : Finset (Fin (L - 1))).filter
      (fun i ↦ i.val + 1 ∈ ({k1, k2, k3, k4} : Finset ℕ))).card ≤ 4 := by
  let J := (Finset.univ : Finset (Fin (L - 1))).filter
    (fun i ↦ i.val + 1 ∈ ({k1, k2, k3, k4} : Finset ℕ))
  have hcard : J.card ≤ ({k1, k2, k3, k4} : Finset ℕ).card := by
    apply Finset.card_le_card_of_injOn (fun i : Fin (L - 1) ↦ i.val + 1)
    · intro i hi
      exact (Finset.mem_filter.mp hi).2
    · intro i _ j _ hij
      exact Fin.ext (Nat.add_right_cancel hij)
  exact hcard.trans Finset.card_le_four

/-- **Five consecutive regions.** For cuts `k1 ≤ k2 ≤ k3 ≤ k4 ≤ L` and positive bond terms of
norm at most one, the sums `A_j` of the bond terms internal to the five intervals are supported
on disjoint intervals, positive and at most their number of terms; the sum `Y` of the at most
four crossing bonds is positive and at most its number of terms; and `H = ∑_j A_j + Y`.
Coincident cuts, empty regions and the empty chain are included.
Arad–Landau–Vazirani–Vidick, arXiv:1602.08828v2, `def:hard-trunc`, lines 873–886, and
`c:goodagsphardtrunc`, lines 979–1005. -/
theorem BondInteraction.five_region_original_bond_data
    (L q k1 k2 k3 k4 : ℕ) (h12 : k1 ≤ k2) (h23 : k2 ≤ k3)
    (h34 : k3 ≤ k4) (h4L : k4 ≤ L)
    (Φ : BondInteraction L q)
    (h0 : ∀ i, 0 ≤ Φ.term i) (h1 : ∀ i, Φ.term i ≤ 1) :
    let k : Fin 6 → ℕ := ![0, k1, k2, k3, k4, L]
    let R : Fin 5 → Finset (Fin L) := fun j ↦ interval L (k j.castSucc) (k j.succ)
    let I : Fin 5 → Finset (Fin (L - 1)) := fun j ↦
      Finset.univ.filter (fun i ↦ k j.castSucc ≤ i.val ∧ i.val + 1 < k j.succ)
    let A : Fin 5 → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ :=
      fun j ↦ ∑ i ∈ I j, Φ.term i
    let J : Finset (Fin (L - 1)) := Finset.univ.filter
      (fun i ↦ i.val + 1 ∈ ({k1, k2, k3, k4} : Finset ℕ))
    let Y : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ := ∑ i ∈ J, Φ.term i
    Monotone k ∧ (Pairwise fun i j ↦ Disjoint (R i) (R j)) ∧
      (∀ j, IsSupportedOn (X := fun _ ↦ Fin q) (A j) (R j)) ∧
      (∀ j, (A j).PosSemidef ∧
        A j ≤ ((I j).card : ℝ) • (1 : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)) ∧
      Y.PosSemidef ∧
      Y ≤ (J.card : ℝ) • (1 : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ) ∧
      J.card ≤ 4 ∧ Φ.hamiltonian = (∑ j, A j) + Y := by
  intro k R I A J Y
  have hk : Monotone k := by
    apply Fin.monotone_iff_le_succ.mpr
    intro i
    fin_cases i <;> simp [k] <;> omega
  have hRordered (i j : Fin 5) (hij : i < j) : Disjoint (R i) (R j) := by
    apply Finset.disjoint_left.mpr
    intro v hvi hvj
    have hends := hk (Fin.succ_le_castSucc_iff.mpr hij)
    change v ∈ interval L (k i.castSucc) (k i.succ) at hvi
    change v ∈ interval L (k j.castSucc) (k j.succ) at hvj
    rw [mem_interval] at hvi hvj
    omega
  have hR : Pairwise fun i j ↦ Disjoint (R i) (R j) := by
    intro i j hij
    rcases lt_or_gt_of_ne hij with hij' | hji
    · exact hRordered i j hij'
    · exact (hRordered j i hji).symm
  have hAs (j : Fin 5) :
      IsSupportedOn (X := fun _ ↦ Fin q) (A j) (R j) :=
    BondInteraction.isSupportedOn_sum_internal_bonds L q (k j.castSucc) (k j.succ) Φ
  have hA (j : Fin 5) : (A j).PosSemidef ∧
      A j ≤ ((I j).card : ℝ) •
        (1 : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ) :=
    Matrix.sum_posSemidef_and_le_card_of_positive_unit_terms (I j) Φ.term
      (fun i _ ↦ h0 i) (fun i _ ↦ h1 i)
  have hY : Y.PosSemidef ∧
      Y ≤ (J.card : ℝ) • (1 : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ) :=
    Matrix.sum_posSemidef_and_le_card_of_positive_unit_terms J Φ.term
      (fun i _ ↦ h0 i) (fun i _ ↦ h1 i)
  have hJ : J.card ≤ 4 := card_four_cut_crossing_le L k1 k2 k3 k4
  refine ⟨hk, hR, hAs, hA, hY.1, hY.2, hJ, ?_⟩
  rw [Fin.sum_univ_five]
  change (∑ i : Fin (L - 1), Φ.term i) =
    (∑ i ∈ (Finset.univ : Finset (Fin (L - 1))).filter
      (fun i ↦ 0 ≤ i.val ∧ i.val + 1 < k1), Φ.term i) +
    (∑ i ∈ (Finset.univ : Finset (Fin (L - 1))).filter
      (fun i ↦ k1 ≤ i.val ∧ i.val + 1 < k2), Φ.term i) +
    (∑ i ∈ (Finset.univ : Finset (Fin (L - 1))).filter
      (fun i ↦ k2 ≤ i.val ∧ i.val + 1 < k3), Φ.term i) +
    (∑ i ∈ (Finset.univ : Finset (Fin (L - 1))).filter
      (fun i ↦ k3 ≤ i.val ∧ i.val + 1 < k4), Φ.term i) +
    (∑ i ∈ (Finset.univ : Finset (Fin (L - 1))).filter
      (fun i ↦ k4 ≤ i.val ∧ i.val + 1 < L), Φ.term i) +
    (∑ i ∈ (Finset.univ : Finset (Fin (L - 1))).filter
      (fun i ↦ i.val + 1 ∈ ({k1, k2, k3, k4} : Finset ℕ)), Φ.term i)
  exact Fin.sum_eq_five_internal_add_crossings h12 h23 h34 Φ.term

/-- **Imaginary-time conjugation by a sum of bond terms.** For a set `I` of bonds with positive
terms of norm at most one, `H = ∑_{i ∈ I} h_i` and an operator `O` supported on two adjacent
sites, `‖exp(t(H - z)) O exp(-t(H - z))‖ ≤ 2 ‖O‖` for `0 ≤ t ≤ 1/8` and every scalar `z`.
Arad–Kuwahara–Landau, arXiv:1406.3898, `low70.tex`, lines 795–880. -/
theorem BondInteraction.norm_exp_conjugation_shift_le_two {L q c : ℕ}
    (I : Finset (Fin (L - 1)))
    (Φ : BondInteraction L q)
    (h0 : ∀ i ∈ I, 0 ≤ Φ.term i) (h1 : ∀ i ∈ I, Φ.term i ≤ 1)
    (O : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (hO : IsSupportedOn (X := fun _ ↦ Fin q) O (interval L c (c + 2)))
    (z : ℂ) (t : ℝ) (ht0 : 0 ≤ t) (ht : t ≤ 1 / 8) :
    let H : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ := Φ.partialHamiltonian I
    ‖NormedSpace.exp ((t : ℂ) • (H - z • 1)) * O *
      NormedSpace.exp (-((t : ℂ) • (H - z • 1)))‖ ≤ 2 * ‖O‖ := by
  classical
  intro H
  have hH : H = ∑ i ∈ I, (Φ.restrict (· ∈ I)).term i :=
    (Interaction.partialHamiltonian_restrict_of_forall fun _ hi ↦ hi).symm
  rw [hH]
  exact (Φ.restrict (· ∈ I)).norm_exp_conjugation_shift_le_two I (k := 2) (g := 2)
    (fun i ↦ by by_cases hi : i ∈ I <;> simp [hi, h0])
    (fun i ↦ by by_cases hi : i ∈ I <;> simp [hi, h1])
    (fun i ↦ by simpa using card_interval_le (L := L) i.val (i.val + 2))
    (card_filter_mem_bond_le_two I) hO
    (by simpa using card_interval_le (L := L) c (c + 2)) z ht0 (by push_cast; linarith)

end ManyBody
