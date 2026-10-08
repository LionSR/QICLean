/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Representation.BranchProbability

/-!
# Lemma 6.1, parts 1 and 6, on `(ℂ^q)^{⊗k}`

This file assembles, for the copy permutations of `Q^{⊗k}` with `Q = ℂ^q`, the statements of
Lemma 6.1 (`lem:schur`) of the area-law paper (*A two-dimensional area law from a global
spectral gap*, `05-replicas.tex`, lines 85–151) that concern the identification of the
labels with partitions:

* part 1: the labels occurring in `Q^{⊗k}` are the partitions with at most `q` rows; for
  them `d_λ = k! ∏_{i<j}(l_i - l_j)/∏_i l_i!` with `l_i = λ_i + q - 1 - i` (rows indexed
  from `0`), and `|log d_λ - k H(λ/k)| ≤ (q² + q + 1)(log(k + q + 2) + 1)`;
* part 6: the full label `λ` and the first-`(k-1)` label `ν` are compatible precisely along
  the removable-row branches `ν = λ - e_i`; in any permutation-invariant state, conditional
  on `λ`, the branch has probability `d_ν / d_λ = (l_i/k) ∏_{j ≠ i} (l_i - 1 - l_j)/(l_i - l_j)
  ≤ 2^q l_i / k`; and the star operator has eigenvalue `(λ_i - 1 - i)/k` on the branch.

The remaining assertion of part 1, `dim V^{(q)}_λ = ∏_{i<j} (l_i - l_j)/(j - i)`, is
`TensorPower.schur_multiplicity_eq_weylFormula`; the polynomial bounds on the number of
labels and on the total multiplicity are `TensorPower.card_labelProj_ne_zero_le` and
`TensorPower.sum_multiplicity_le`.

## Main declarations

* `TensorPower.labelPart_eq_zero_of_labelProj_ne_zero` — at most `q` rows.
* `TensorPower.schur_dim_eq_hookFormula`, `TensorPower.schur_abs_log_dim_sub_le`.
* `TensorPower.schur_branch_compatible_iff`, `TensorPower.schur_branch_probability`,
  `TensorPower.schur_starOp_eigenvalue`.
-/

open Finset Matrix PermutationRepresentation

namespace TensorPower

variable {q k m : ℕ}

/-- A label occurring in `(ℂ^q)^{⊗k}` has at most `q` rows. -/
theorem labelPart_eq_zero_of_labelProj_ne_zero {l : IrrepLabel (Equiv.Perm (Fin k))}
    (hl : labelProj (copyPerm (Fin q) k) l ≠ 0) : ∀ a, q ≤ a → labelPart l a = 0 := by
  intro a ha
  rw [labelProj_ne_zero_iff] at hl
  simp only [labelPart]
  split_ifs with hak
  · exact hl ⟨a, hak⟩ ha
  · rfl

/-- **Lemma 6.1(1), dimension of the symmetric-group factor**: for a label occurring in
`(ℂ^q)^{⊗k}`, `d_λ = k! ∏_{i<j} (l_i - l_j)/∏_i l_i!` with the partition padded to length
`q`. -/
theorem schur_dim_eq_hookFormula {l : IrrepLabel (Equiv.Perm (Fin k))}
    (hl : labelProj (copyPerm (Fin q) k) l ≠ 0) :
    (l.dim : ℝ) = Partition.hookFormula (part q l) :=
  dim_eq_hookFormula_of_rows l (labelPart_eq_zero_of_labelProj_ne_zero hl)

/-- **Lemma 6.1(1), entropy asymptotics**: for a label occurring in `(ℂ^q)^{⊗k}`,
`|log d_λ - k H(λ/k)| ≤ (q² + q + 1)(log(k + q + 2) + 1)`. -/
theorem schur_abs_log_dim_sub_le {l : IrrepLabel (Equiv.Perm (Fin k))}
    (hl : labelProj (copyPerm (Fin q) k) l ≠ 0) :
    |Real.log l.dim - Partition.entropyTerm (part q l)| ≤
      (q ^ 2 + q + 1) * (Real.log (k + q + 2) + 1) := by
  have hrows := labelPart_eq_zero_of_labelProj_ne_zero hl
  have hsum : ∑ a, part q l a = k := sum_labelPart_of_rows l hrows
  have := Partition.abs_log_hookFormula_sub_le (p := part q l)
    (fun a b hab => labelPart_antitone l hab)
  rw [hsum] at this
  rwa [schur_dim_eq_hookFormula hl]

/-- **Lemma 6.1(6), compatible branches**: on `(ℂ^q)^{⊗(m+1)}`, the full label `λ` and the
label `ν` of the first `m` copies are compatible exactly when `λ` occurs and `ν = λ - e_i`
for some row `i`. -/
theorem schur_branch_compatible_iff (l : IrrepLabel (Equiv.Perm (Fin (m + 1))))
    (n : IrrepLabel (Equiv.Perm (Fin m))) :
    labelProj (copyPerm (Fin q) (m + 1)) l *
        labelProj ((copyPerm (Fin q) (m + 1)).comp (firstCopies m)) n ≠ 0 ↔
      labelProj (copyPerm (Fin q) (m + 1)) l ≠ 0 ∧
        ∃ i, labelPart l = Function.update (labelPart n) i (labelPart n i + 1) :=
  labelProj_mul_labelProj_firstCopies_ne_zero_iff _ l n

/-- **Lemma 6.1(6), branch probabilities** (`05-replicas.tex`, equation
`replicas:branch-probability`): for any operator `ρ` on `(ℂ^q)^{⊗(m+1)}` commuting with the
copy permutations (for instance a permutation-invariant density matrix), on the branch
`ν = λ - e_i` of an occurring label, `d_λ Tr(ρ π^λ π^ν) = d_ν Tr(ρ π^λ)`, and
`d_ν / d_λ = (l_i/k) ∏_{j ≠ i} (l_i - 1 - l_j)/(l_i - l_j) ≤ 2^q l_i/k` with `k = m + 1`,
`l_i = λ_i + q - 1 - i`. -/
theorem schur_branch_probability {ρ : Matrix (Fin (m + 1) → Fin q) (Fin (m + 1) → Fin q) ℂ}
    (hρ : ∀ σ, Commute (permOp (copyPerm (Fin q) (m + 1)) σ) ρ)
    {l : IrrepLabel (Equiv.Perm (Fin (m + 1)))} {n : IrrepLabel (Equiv.Perm (Fin m))} {i : ℕ}
    (hl : labelProj (copyPerm (Fin q) (m + 1)) l ≠ 0)
    (h : labelPart l = Function.update (labelPart n) i (labelPart n i + 1)) :
    ∃ hi : i < q,
      (l.dim : ℂ) * (ρ * (labelProj (copyPerm (Fin q) (m + 1)) l *
          labelProj ((copyPerm (Fin q) (m + 1)).comp (firstCopies m)) n)).trace =
        n.dim * (ρ * labelProj (copyPerm (Fin q) (m + 1)) l).trace ∧
      (n.dim : ℝ) / l.dim = (Partition.shiftedPart (part q l) ⟨i, hi⟩ / (m + 1 : ℕ)) *
        ∏ j ∈ univ.erase (⟨i, hi⟩ : Fin q),
          ((Partition.shiftedPart (part q l) ⟨i, hi⟩ : ℝ) - 1 -
            Partition.shiftedPart (part q l) j) /
          ((Partition.shiftedPart (part q l) ⟨i, hi⟩ : ℝ) -
            Partition.shiftedPart (part q l) j) ∧
      (n.dim : ℝ) / l.dim ≤
        2 ^ q * (Partition.shiftedPart (part q l) ⟨i, hi⟩ / (m + 1 : ℕ)) := by
  have hrows := labelPart_eq_zero_of_labelProj_ne_zero hl
  have hi : i < q := by
    by_contra hiq
    have hli : labelPart l i = labelPart n i + 1 := by rw [h, Function.update_self]
    rw [hrows i (not_lt.mp hiq)] at hli
    omega
  exact ⟨hi, trace_mul_labelProj_mul_labelProj_firstCopies _ hρ ⟨i, h⟩,
    dim_div_dim_eq h hrows hi, dim_div_dim_le h hrows hi⟩

/-- **Lemma 6.1(6), star operator** (`05-replicas.tex`, equation `replicas:star-definition`):
on the branch `ν = λ - e_i`, the normalized star operator `J = (1/k) ∑_{j<k} U((j k))` acts
on `(ℂ^q)^{⊗k}`, `k = m + 1`, by `(λ_i - 1 - i)/k` (rows indexed from `0`). -/
theorem schur_starOp_eigenvalue {l : IrrepLabel (Equiv.Perm (Fin (m + 1)))}
    {n : IrrepLabel (Equiv.Perm (Fin m))} {i : ℕ}
    (h : labelPart l = Function.update (labelPart n) i (labelPart n i + 1)) :
    starOp (copyPerm (Fin q) (m + 1)) *
        (labelProj (copyPerm (Fin q) (m + 1)) l *
          labelProj ((copyPerm (Fin q) (m + 1)).comp (firstCopies m)) n) =
      (((labelPart l i : ℂ) - 1 - i) / (m + 1 : ℕ)) •
        (labelProj (copyPerm (Fin q) (m + 1)) l *
          labelProj ((copyPerm (Fin q) (m + 1)).comp (firstCopies m)) n) :=
  starOp_mul_branch _ h

end TensorPower
