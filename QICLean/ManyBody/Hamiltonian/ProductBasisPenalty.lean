/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.ManyBody.Hamiltonian.KroneckerSum
import QICLean.ManyBody.Sites.Placement.PlaceAlong

/-!
# Onsite penalties selecting a basis configuration

For a basis configuration `b` of a system, the onsite penalty at a site `s` is the diagonal
projection `1 - |b s⟩⟨b s|` of the basis of `s`, and their sum over the sites, each placed on its
site, counts the sites at which a configuration differs from `b`. The sum is gapped at energy
`0` with gap `1`, and its zero-energy space is the line through `|b⟩`; the empty system is
included, where the orthogonal complement of the line is zero.

The declarations restate `TNLean/Circuit/ProductBasisPenalty.lean` (Apache-2.0). The changes:
any finite site type and any finite basis at each site instead of one local dimension; the
onsite matrices are placed at their sites with `ManyBody.placeAt`.

## Main definitions

* `ManyBody.siteBasisPenalty` — the penalty `1 - |a⟩⟨a|` of one basis.
* `ManyBody.productBasisPenalty` — the sum of the placed penalties.

## Main results

* `ManyBody.siteBasisPenalty_posSemidef`, `ManyBody.siteBasisPenalty_le_one`.
* `ManyBody.productBasisPenalty_eq_diagonal` — the count of differing sites.
* `ManyBody.isHermitian_productBasisPenalty`,
  `ManyBody.isGapped_productBasisPenalty`,
  `ManyBody.groundSpace_productBasisPenalty` — the gap and the zero-energy space.

## References

* arXiv:1307.5143v1 (Landau, Vazirani, Vidick), final induction, lines 652--678: the padding by
  product ancillas, an auxiliary reduction rather than an additional hypothesis on the
  interaction.
-/

open Matrix
open scoped ComplexOrder MatrixOrder

namespace ManyBody

section Site

variable {α : Type} [DecidableEq α]

/-- The onsite penalty vanishing exactly at the basis vector `a`: the diagonal projection
`1 - |a⟩⟨a|`. -/
def siteBasisPenalty (a : α) : Matrix α α ℂ :=
  diagonal fun x ↦ if x = a then 0 else 1

/-- The onsite penalty is positive semidefinite. -/
theorem siteBasisPenalty_posSemidef (a : α) : (siteBasisPenalty a).PosSemidef := by
  refine PosSemidef.diagonal fun x ↦ ?_
  change (0 : ℂ) ≤ if x = a then 0 else 1
  split_ifs <;> norm_num

/-- The onsite penalty is at most the identity. -/
theorem siteBasisPenalty_le_one (a : α) : siteBasisPenalty a ≤ 1 := by
  refine Matrix.le_iff.mpr ?_
  have hid : 1 - siteBasisPenalty a = diagonal fun x ↦ if x = a then (1 : ℂ) else 0 := by
    rw [siteBasisPenalty, ← diagonal_one, diagonal_sub]
    congr 1
    funext x
    split_ifs <;> simp
  rw [hid]
  refine PosSemidef.diagonal fun x ↦ ?_
  change (0 : ℂ) ≤ if x = a then 1 else 0
  split_ifs <;> norm_num

end Site

variable {S : Type} [Fintype S] [DecidableEq S] {X : S → Type} [∀ s, DecidableEq (X s)]

/-- The sum over the sites of the onsite penalties selecting the basis configuration `b`, each
placed on its site. -/
noncomputable def productBasisPenalty (b : Config X) : Matrix (Config X) (Config X) ℂ :=
  ∑ s, placeAt s (siteBasisPenalty (b s))

/-- The sum of the penalties is the diagonal matrix counting the sites at which a configuration
differs from `b`. -/
theorem productBasisPenalty_eq_diagonal (b : Config X) :
    productBasisPenalty b = diagonal fun x ↦ ∑ s, if x s = b s then (0 : ℂ) else 1 := by
  have hsite : ∀ s, placeAt s (siteBasisPenalty (b s)) =
      diagonal fun x ↦ if x s = b s then (0 : ℂ) else 1 := fun s ↦ by
    ext y x
    rw [placeAt_apply, siteBasisPenalty, diagonal_apply, diagonal_apply]
    by_cases hxy : y = x
    · subst hxy
      simp
    · rw [ite_eq_right_iff.mpr fun h ↦ absurd h hxy]
      by_cases hout : ∀ v, v ≠ s → y v = x v
      · rw [ite_eq_left_iff.mpr fun h ↦ absurd hout h]
        refine ite_eq_right_iff.mpr fun hs ↦ absurd ?_ hxy
        refine funext fun v ↦ ?_
        by_cases hv : v = s
        · exact hv ▸ hs
        · exact hout v hv
      · rw [ite_eq_right_iff.mpr fun h ↦ absurd h hout]
  rw [productBasisPenalty, Finset.sum_congr rfl fun s _ ↦ hsite s]
  ext y x
  by_cases hxy : y = x
  · subst hxy
    simp [Matrix.sum_apply]
  · simp [Matrix.sum_apply, hxy]

/-- The sum of the penalties as the diagonal matrix of a real count. -/
private theorem productBasisPenalty_eq_diagonal_real (b : Config X) :
    productBasisPenalty b =
      diagonal fun x ↦ ((∑ s, if x s = b s then (0 : ℝ) else 1 : ℝ) : ℂ) := by
  rw [productBasisPenalty_eq_diagonal]
  congr 1
  funext x
  rw [Complex.ofReal_sum]
  exact Finset.sum_congr rfl fun s _ ↦ by split_ifs <;> simp

omit [DecidableEq S] in
/-- A configuration other than `b` differs from it at some site. -/
private theorem one_le_count_of_ne {b x : Config X} (hx : x ≠ b) :
    1 ≤ ∑ s, if x s = b s then (0 : ℝ) else 1 := by
  obtain ⟨s, hs⟩ : ∃ s, x s ≠ b s := by
    by_contra h
    push Not at h
    exact hx (funext h)
  have h := Finset.single_le_sum
    (fun t _ ↦ (show (0 : ℝ) ≤ if x t = b t then 0 else 1 by split_ifs <;> norm_num))
    (Finset.mem_univ s)
  simpa only [hs, ite_false] using h

/-- The sum of the penalties is Hermitian. -/
theorem isHermitian_productBasisPenalty (b : Config X) : (productBasisPenalty b).IsHermitian := by
  rw [productBasisPenalty_eq_diagonal_real]
  exact isHermitian_diagonal_of_self_adjoint _ (funext fun x ↦ Complex.conj_ofReal _)

/-- The sum of the penalties is gapped at energy `0` with gap `1`, including on the empty
system. -/
theorem isGapped_productBasisPenalty [∀ s, Fintype (X s)] (b : Config X) :
    IsGapped (productBasisPenalty b) 0 1 := by
  rw [productBasisPenalty_eq_diagonal_real, isGapped_diagonal_iff]
  refine ⟨⟨b, by simp⟩, fun x ↦ ?_⟩
  by_cases hx : x = b
  · exact Or.inl (by simp [hx])
  · exact Or.inr (by simpa only [zero_add] using one_le_count_of_ne hx)

/-- The zero-energy space of the sum of the penalties is the line through `|b⟩`. -/
theorem groundSpace_productBasisPenalty [∀ s, Fintype (X s)] (b : Config X) :
    groundSpace (productBasisPenalty b) 0 =
      Submodule.span ℂ {WithLp.toLp 2 (Pi.single b (1 : ℂ))} := by
  ext ψ
  rw [productBasisPenalty_eq_diagonal_real, mem_groundSpace_diagonal_iff,
    Submodule.mem_span_singleton]
  constructor
  · intro h
    refine ⟨ψ b, ?_⟩
    ext x
    by_cases hx : x = b
    · subst hx
      simp
    · have hne : ((∑ s, if x s = b s then (0 : ℝ) else 1 : ℝ) : ℂ) ≠ ((0 : ℝ) : ℂ) :=
        Complex.ofReal_injective.ne (one_pos.trans_le (one_le_count_of_ne hx)).ne'
      simp [hx, h x hne]
  · rintro ⟨c, rfl⟩ x hx
    have hxb : x ≠ b := by
      rintro rfl
      exact hx (by simp)
    simp [hxb]

end ManyBody
