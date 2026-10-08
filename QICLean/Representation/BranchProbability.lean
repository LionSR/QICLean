/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Representation.StarOperator

/-!
# Removable-row branches and their probabilities

Let `S_{m+1}` act by a permutation representation, and let `S_m` permute the first `m`
copies. This file proves the branch statements of Lemma 6.1(6) of the area-law paper
(*A two-dimensional area law from a global spectral gap*, `05-replicas.tex`, lines
132–145, proof lines 237–249):

* the label `λ` of all copies and the label `ν` of the first `m` copies are compatible
  (their projectors have nonzero product) exactly when `π^λ ≠ 0` and `ν = λ - e_i` for a
  removable row `i`;
* in any state commuting with the representation, conditional on `λ`, the probability of
  the branch `ν = λ - e_i` is `d_ν / d_λ`;
* `d_{λ - e_i} / d_λ = (l_i / k) ∏_{j ≠ i} (l_i - 1 - l_j)/(l_i - l_j) ≤ 2^q l_i / k` for a
  padding length `q` at least the number of rows of `λ`.

## Main declarations

* `PermutationRepresentation.labelProj_mul_labelProj_firstCopies_ne_zero_iff`.
* `PermutationRepresentation.trace_mul_labelProj_mul_labelProj_firstCopies`.
* `TensorPower.dim_div_dim_eq`, `TensorPower.dim_div_dim_le`.
-/

open Finset Matrix PermutationRepresentation TensorPower

namespace IrrepLabel

variable {G : Type*} [Group G] [Fintype G]

theorem eq_zero_of_mul_self_of_trace_eq_zero {d : ℕ} {M : Matrix (Fin d) (Fin d) ℂ}
    (hM : M * M = M) (htr : M.trace = 0) : M = 0 := by
  rw [trace_eq_finrank_range_of_mul_self hM, Nat.cast_eq_zero, Submodule.finrank_eq_zero,
    LinearMap.range_eq_bot] at htr
  exact (LinearEquiv.map_eq_zero_iff Matrix.toLin').mp htr

end IrrepLabel

namespace PermutationRepresentation

variable {m : ℕ} {X : Type*} [Fintype X] [DecidableEq X]
  (φ : Equiv.Perm (Fin (m + 1)) →* Equiv.Perm X)

theorem labelProj_firstCopies (n : IrrepLabel (Equiv.Perm (Fin m))) :
    labelProj (φ.comp (firstCopies m)) n =
      groupAlgebraRep φ (IrrepLabel.restrictHom (firstCopies m) (IrrepLabel.centralIdem n)) :=
  groupAlgebraRep_comp φ _ _

theorem block_restrict_centralIdem_eq_zero_iff (l : IrrepLabel (Equiv.Perm (Fin (m + 1))))
    (n : IrrepLabel (Equiv.Perm (Fin m))) :
    IrrepLabel.block l (IrrepLabel.restrictHom (firstCopies m) (IrrepLabel.centralIdem n)) = 0 ↔
      ¬∃ i, labelPart l = Function.update (labelPart n) i (labelPart n i + 1) := by
  rw [← branchMult_eq_zero_iff]
  constructor
  · intro h
    have := IrrepLabel.trace_block_centralIdem (firstCopies m) l n
    rw [h, trace_zero] at this
    have hd : (n.dim : ℂ) ≠ 0 := by exact_mod_cast n.dim_pos.ne'
    exact_mod_cast (mul_eq_zero.mp this.symm).resolve_left hd
  · intro h
    refine IrrepLabel.eq_zero_of_mul_self_of_trace_eq_zero ?_ ?_
    · rw [← IrrepLabel.block_mul, ← map_mul, IrrepLabel.centralIdem_mul_self]
    · rw [IrrepLabel.trace_block_centralIdem, h]
      simp

/-- **Compatible branches** (`05-replicas.tex`, Lemma 6.1(6), lines 132–134): the full label
`λ` and the first-`m` label `ν` are compatible exactly when `π^λ ≠ 0` and `ν = λ - e_i` for
some row `i`. -/
theorem labelProj_mul_labelProj_firstCopies_ne_zero_iff
    (l : IrrepLabel (Equiv.Perm (Fin (m + 1)))) (n : IrrepLabel (Equiv.Perm (Fin m))) :
    labelProj φ l * labelProj (φ.comp (firstCopies m)) n ≠ 0 ↔
      labelProj φ l ≠ 0 ∧
        ∃ i, labelPart l = Function.update (labelPart n) i (labelPart n i + 1) := by
  rw [(commute_labelProj_comp φ (firstCopies m) n l).symm.eq, labelProj_firstCopies, Ne,
    groupAlgebraRep_mul_labelProj_eq_zero_iff, block_restrict_centralIdem_eq_zero_iff]
  tauto

/-- **Branch probability** (`05-replicas.tex`, Lemma 6.1(6), equation
`replicas:branch-probability`): for an operator `M` commuting with the representation (for
instance a permutation-invariant density matrix), on the branch `ν = λ - e_i`,
`d_λ Tr(M π^λ π^ν) = d_ν Tr(M π^λ)`. -/
theorem trace_mul_labelProj_mul_labelProj_firstCopies {M : Matrix X X ℂ}
    (hM : ∀ g, Commute (permOp φ g) M) {l : IrrepLabel (Equiv.Perm (Fin (m + 1)))}
    {n : IrrepLabel (Equiv.Perm (Fin m))}
    (h : ∃ i, labelPart l = Function.update (labelPart n) i (labelPart n i + 1)) :
    (l.dim : ℂ) * (M * (labelProj φ l * labelProj (φ.comp (firstCopies m)) n)).trace =
      n.dim * (M * labelProj φ l).trace := by
  rw [(commute_labelProj_comp φ (firstCopies m) n l).symm.eq, labelProj_firstCopies,
    trace_mul_groupAlgebraRep_mul_labelProj φ hM, IrrepLabel.trace_block_centralIdem,
    (branchMult_eq_one_iff l n).mpr h]
  simp

end PermutationRepresentation

namespace TensorPower

variable {m : ℕ}

theorem sum_labelPart_of_rows {k : ℕ} (l : IrrepLabel (Equiv.Perm (Fin k))) {N : ℕ}
    (hN : ∀ a, N ≤ a → labelPart l a = 0) : ∑ a : Fin N, labelPart l a = k := by
  rcases le_total k N with hkN | hNk
  · exact sum_labelPart l hkN
  · calc ∑ a : Fin N, labelPart l a = ∑ a ∈ range N, labelPart l a :=
          Fin.sum_univ_eq_sum_range _ N
      _ = ∑ a ∈ range k, labelPart l a :=
          sum_subset (range_subset_range.mpr hNk) fun a _ ha => hN a (by simpa using ha)
      _ = ∑ a : Fin k, labelPart l a := (Fin.sum_univ_eq_sum_range _ k).symm
      _ = k := sum_labelPart l le_rfl

/-- The branch probability `d_{λ - e_i}/d_λ = (l_i/k) ∏_{j ≠ i} (l_i - 1 - l_j)/(l_i - l_j)`
(`05-replicas.tex`, equation `replicas:branch-probability`), for a padding length `q` at
least the number of rows of `λ`, with `l = shiftedPart`. -/
theorem dim_div_dim_eq {l : IrrepLabel (Equiv.Perm (Fin (m + 1)))}
    {n : IrrepLabel (Equiv.Perm (Fin m))} {i : ℕ}
    (h : labelPart l = Function.update (labelPart n) i (labelPart n i + 1)) {q : ℕ}
    (hq : ∀ a, q ≤ a → labelPart l a = 0) (hi : i < q) :
    (n.dim : ℝ) / l.dim = (Partition.shiftedPart (part q l) ⟨i, hi⟩ / (m + 1 : ℕ)) *
      ∏ j ∈ univ.erase (⟨i, hi⟩ : Fin q),
        ((Partition.shiftedPart (part q l) ⟨i, hi⟩ : ℝ) - 1 -
          Partition.shiftedPart (part q l) j) /
        ((Partition.shiftedPart (part q l) ⟨i, hi⟩ : ℝ) - Partition.shiftedPart (part q l) j) := by
  set p := part q l
  set i' : Fin q := ⟨i, hi⟩
  have hp : Antitone p := fun a b hab => labelPart_antitone l hab
  have hli : labelPart l i = labelPart n i + 1 := by rw [h, Function.update_self]
  have h1 : 1 ≤ p i' := by simp [p, i', hli]
  have hn : part q n = Function.update p i' (p i' - 1) := by
    funext a
    by_cases ha : a = i'
    · subst ha; simp [p, part, i', hli]
    · have ha' : (a : ℕ) ≠ i := fun e => ha (Fin.ext e)
      simp [p, part, Function.update_of_ne ha, h, Function.update_of_ne ha']
  have hqn : ∀ a, q ≤ a → labelPart n a = 0 := by
    intro a ha
    have hai : a ≠ i := by omega
    have := hq a ha
    rwa [h, Function.update_of_ne hai] at this
  have hdl := dim_eq_hookFormula_of_rows l hq
  have hdn := dim_eq_hookFormula_of_rows n hqn
  rw [hn] at hdn
  have hsum : ∑ a, p a = m + 1 := sum_labelPart_of_rows l hq
  have key := Partition.hookFormula_update_sub_mul p h1
  rw [hsum, ← hdn, ← hdl] at key
  set L : Fin q → ℝ := fun j => (Partition.shiftedPart p j : ℝ)
  have hinj := Partition.shiftedPart_injective hp
  have hD : ∏ j ∈ univ.erase i', (L i' - L j) ≠ 0 := prod_ne_zero_iff.mpr fun j hj =>
    sub_ne_zero.mpr fun e => (mem_erase.mp hj).1 (hinj e).symm
  have hl0 : (l.dim : ℝ) ≠ 0 := by exact_mod_cast l.dim_pos.ne'
  simp only [L] at hD
  rw [prod_div_distrib, div_eq_iff hl0]
  field_simp
  push_cast at key ⊢
  linear_combination key

theorem sub_one_div_le_two {d : ℝ} (hd : 1 ≤ |d|) : 0 ≤ (d - 1) / d ∧ (d - 1) / d ≤ 2 := by
  rcases le_or_gt 0 d with h | h
  · rw [abs_of_nonneg h] at hd
    refine ⟨div_nonneg (by linarith) h, ?_⟩
    rw [div_le_iff₀ (by linarith)]
    linarith
  · rw [abs_of_neg h] at hd
    refine ⟨div_nonneg_of_nonpos (by linarith) h.le, ?_⟩
    rw [div_le_iff_of_neg h]
    linarith

/-- **The branch-probability bound** (`05-replicas.tex`, equation
`replicas:branch-probability`): `d_{λ - e_i}/d_λ ≤ 2^q l_i/k`. -/
theorem dim_div_dim_le {l : IrrepLabel (Equiv.Perm (Fin (m + 1)))}
    {n : IrrepLabel (Equiv.Perm (Fin m))} {i : ℕ}
    (h : labelPart l = Function.update (labelPart n) i (labelPart n i + 1)) {q : ℕ}
    (hq : ∀ a, q ≤ a → labelPart l a = 0) (hi : i < q) :
    (n.dim : ℝ) / l.dim ≤
      2 ^ q * (Partition.shiftedPart (part q l) ⟨i, hi⟩ / (m + 1 : ℕ)) := by
  rw [dim_div_dim_eq h hq hi, mul_comm (2 ^ q : ℝ)]
  set p := part q l
  set i' : Fin q := ⟨i, hi⟩
  have hp : Antitone p := fun a b hab => labelPart_antitone l hab
  have hinj := Partition.shiftedPart_injective hp
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  have hfac : ∀ j ∈ univ.erase i',
      0 ≤ ((Partition.shiftedPart p i' : ℝ) - 1 - Partition.shiftedPart p j) /
        ((Partition.shiftedPart p i' : ℝ) - Partition.shiftedPart p j) ∧
      ((Partition.shiftedPart p i' : ℝ) - 1 - Partition.shiftedPart p j) /
        ((Partition.shiftedPart p i' : ℝ) - Partition.shiftedPart p j) ≤ 2 := by
    intro j hj
    have hne : (Partition.shiftedPart p i' : ℝ) ≠ Partition.shiftedPart p j := fun e =>
      (mem_erase.mp hj).1 (hinj e).symm
    have h1 : (1 : ℝ) ≤ |(Partition.shiftedPart p i' : ℝ) - Partition.shiftedPart p j| := by
      rcases lt_or_gt_of_ne hne with hlt | hlt
      · have : (Partition.shiftedPart p i' : ℝ) + 1 ≤ Partition.shiftedPart p j := by
          exact_mod_cast (by exact_mod_cast hlt : Partition.shiftedPart p i' < _)
        rw [abs_of_neg (by linarith)]; linarith
      · have : (Partition.shiftedPart p j : ℝ) + 1 ≤ Partition.shiftedPart p i' := by
          exact_mod_cast (by exact_mod_cast hlt : Partition.shiftedPart p j < _)
        rw [abs_of_pos (by linarith)]; linarith
    rw [show (Partition.shiftedPart p i' : ℝ) - 1 - Partition.shiftedPart p j =
      (Partition.shiftedPart p i' : ℝ) - Partition.shiftedPart p j - 1 by ring]
    exact sub_one_div_le_two h1
  calc ∏ j ∈ univ.erase i', _ ≤ ∏ _j ∈ univ.erase i', (2 : ℝ) :=
        prod_le_prod₀ (fun j hj => (hfac j hj).1) fun j hj => (hfac j hj).2
    _ = 2 ^ (q - 1) := by rw [prod_const, card_erase_of_mem (mem_univ _), card_univ,
          Fintype.card_fin]
    _ ≤ 2 ^ q := pow_le_pow_right₀ (by norm_num) (Nat.sub_le q 1)

end TensorPower
