/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Entropy.SupportedMarginalTails

/-!
# Three-way cut coordinates

For regions `A ⊆ B` of a finite set of sites, a configuration splits into its parts on `A`, on
`B \ A` and on `Bᶜ`. In these coordinates `((x, y), z)`, an operator supported inside `B` is a
matrix on the first two parts tensored with the identity on `Bᶜ`, and an operator supported
outside `A` is, after reassociating to `(x, (y, z))`, the identity on `A` tensored with a matrix
on `(B \ A) × Bᶜ`.

For a chain cut at site `i`, with `A` the sites left of `i` and `B` the sites up to `i`, this is
the setting of the gluing lemma of Landau, Vazirani and Vidick: the left part `H_L` of the
Hamiltonian is supported inside `B` and the rest `H_i + H_R` outside `A`.

## Main definitions

* `Entropy.threeCutEquiv`: the coordinates `((x, y), z)` of a configuration.
* `Entropy.regionSplitEquiv`: the split of a configuration on `B` into its parts on `A` and
  `B \ A`.

## Main results

* `Entropy.threeCutEquiv_eq_trans`: the three-way coordinates refine the two-way cut at `B`.
* `Entropy.IsSupportedOn.reindex_threeCutEquiv_eq_kronecker_one`: an operator supported
  inside `B` is `M ⊗ 1`.
* `Entropy.IsSupportedOn.reindex_threeCutEquiv_eq_one_kronecker`: an operator supported outside
  `A` is `1 ⊗ K` after reassociation.

## References

* Z. Landau, U. Vazirani, T. Vidick, *A polynomial-time algorithm for the ground state of
  1D gapped local Hamiltonians*, arXiv:1307.5143v1, `algo53.tex`, lines 409–417.
-/

open Matrix
open scoped Kronecker

namespace Entropy

variable {V : Type*} [Fintype V] [DecidableEq V] {n : V → ℕ}

/-- The coordinates `((x, y), z)` of a configuration, with `x` its part on `A`, `y` its part on
`B \ A` and `z` its part on `Bᶜ`, for regions `A ⊆ B`. -/
def threeCutEquiv (n : V → ℕ) {A B : Finset V} (hAB : A ⊆ B) :
    SiteConfig n ≃
      ((((v : {v // v ∈ A}) → Fin (n v)) × ((v : {v // v ∈ B \ A}) → Fin (n v))) ×
        ((v : {v // v ∉ B}) → Fin (n v))) where
  toFun σ := ((fun v ↦ σ v, fun v ↦ σ v), fun v ↦ σ v)
  invFun p v :=
    if hA : v ∈ A then p.1.1 ⟨v, hA⟩
    else if hB : v ∈ B then p.1.2 ⟨v, Finset.mem_sdiff.2 ⟨hB, hA⟩⟩
    else p.2 ⟨v, hB⟩
  left_inv σ := by
    funext v
    by_cases hA : v ∈ A
    · simp [hA]
    · by_cases hB : v ∈ B <;> simp [hA, hB]
  right_inv p := by
    obtain ⟨⟨x, y⟩, z⟩ := p
    refine Prod.ext (Prod.ext ?_ ?_) ?_
    · funext v; simp [v.2]
    · funext v
      have h := Finset.mem_sdiff.1 v.2
      simp [h.1, h.2]
    · funext v
      have hA : v.1 ∉ A := fun h ↦ v.2 (hAB h)
      simp [hA, v.2]

variable {A B : Finset V} (hAB : A ⊆ B)

omit [Fintype V] in
theorem threeCutEquiv_symm_apply_of_mem {p} {v : V} (hv : v ∈ A) :
    (threeCutEquiv n hAB).symm p v = p.1.1 ⟨v, hv⟩ := by
  simp [threeCutEquiv, hv]

omit [Fintype V] in
theorem threeCutEquiv_symm_apply_of_mem_sdiff {p} {v : V} (hv : v ∈ B \ A) :
    (threeCutEquiv n hAB).symm p v = p.1.2 ⟨v, hv⟩ := by
  have h := Finset.mem_sdiff.1 hv
  simp [threeCutEquiv, h.1, h.2]

omit [Fintype V] in
theorem threeCutEquiv_symm_apply_of_not_mem {p} {v : V} (hv : v ∉ B) :
    (threeCutEquiv n hAB).symm p v = p.2 ⟨v, hv⟩ := by
  have hA : v ∉ A := fun h ↦ hv (hAB h)
  simp [threeCutEquiv, hA, hv]

/-- The split of a configuration on `B` into its parts on `A` and on `B \ A`, for `A ⊆ B`. -/
def regionSplitEquiv (n : V → ℕ) {A B : Finset V} (hAB : A ⊆ B) :
    ((v : {v // v ∈ B}) → Fin (n v)) ≃
      ((v : {v // v ∈ A}) → Fin (n v)) × ((v : {v // v ∈ B \ A}) → Fin (n v)) where
  toFun c := (fun v ↦ c ⟨v, hAB v.2⟩, fun v ↦ c ⟨v, (Finset.mem_sdiff.1 v.2).1⟩)
  invFun p v :=
    if hA : v.1 ∈ A then p.1 ⟨v, hA⟩ else p.2 ⟨v, Finset.mem_sdiff.2 ⟨v.2, hA⟩⟩
  left_inv c := by
    funext v
    by_cases hA : v.1 ∈ A <;> simp [hA]
  right_inv p := by
    obtain ⟨x, y⟩ := p
    refine Prod.ext ?_ ?_
    · funext v; simp [v.2]
    · funext v
      simp [(Finset.mem_sdiff.1 v.2).2]

omit [Fintype V] in
/-- **The three-way coordinates refine the two-way cut at `B`**: they are the cut coordinates at
`B` followed by the split of the part on `B` into its parts on `A` and `B \ A`. -/
theorem threeCutEquiv_eq_trans :
    threeCutEquiv n hAB =
      (cutEquiv n B).trans ((regionSplitEquiv n hAB).prodCongr (Equiv.refl _)) := by
  ext σ <;> rfl

/-- **An operator supported inside `B`** is, in three-way cut coordinates, a matrix on the parts
in `A` and `B \ A` tensored with the identity on `Bᶜ`: its slice at any configuration `z₀`
of `Bᶜ`. -/
theorem IsSupportedOn.reindex_threeCutEquiv_eq_kronecker_one
    {X : Matrix (SiteConfig n) (SiteConfig n) ℂ} {D : Finset V} (hX : IsSupportedOn X D)
    (hDB : D ⊆ B) (z₀ : (v : {v // v ∉ B}) → Fin (n v)) :
    reindex (threeCutEquiv n hAB) (threeCutEquiv n hAB) X =
      (fun p p' ↦ reindex (threeCutEquiv n hAB) (threeCutEquiv n hAB) X (p, z₀) (p', z₀)) ⊗ₖ
        (1 : Matrix _ _ ℂ) := by
  classical
  ext ⟨p, z⟩ ⟨p', z'⟩
  change X ((threeCutEquiv n hAB).symm (p, z)) ((threeCutEquiv n hAB).symm (p', z')) =
    X ((threeCutEquiv n hAB).symm (p, z₀)) ((threeCutEquiv n hAB).symm (p', z₀)) *
      (1 : Matrix _ _ ℂ) z z'
  simp only [one_apply, mul_ite, mul_one, mul_zero]
  split_ifs with hz
  · subst hz
    refine hX.apply_eq (fun v hv ↦ ?_) (fun v hv ↦ ?_) (fun v hv ↦ ?_)
    · by_cases hA : v ∈ A
      · simp only [threeCutEquiv_symm_apply_of_mem hAB hA]
      · simp only [threeCutEquiv_symm_apply_of_mem_sdiff hAB
          (Finset.mem_sdiff.2 ⟨hDB hv, hA⟩)]
    · by_cases hA : v ∈ A
      · simp only [threeCutEquiv_symm_apply_of_mem hAB hA]
      · simp only [threeCutEquiv_symm_apply_of_mem_sdiff hAB
          (Finset.mem_sdiff.2 ⟨hDB hv, hA⟩)]
    · by_cases hvB : v ∈ B
      · by_cases hA : v ∈ A
        · simp only [threeCutEquiv_symm_apply_of_mem hAB hA]
        · simp only [threeCutEquiv_symm_apply_of_mem_sdiff hAB
            (Finset.mem_sdiff.2 ⟨hvB, hA⟩)]
      · simp only [threeCutEquiv_symm_apply_of_not_mem hAB hvB]
  · obtain ⟨w, hw⟩ := Function.ne_iff.mp hz
    refine hX.1 _ _ ⟨w.1, fun h ↦ w.2 (hDB h), ?_⟩
    rwa [threeCutEquiv_symm_apply_of_not_mem hAB w.2,
      threeCutEquiv_symm_apply_of_not_mem hAB w.2]

omit [Fintype V] in
/-- **An operator supported outside `A`** is, in three-way cut coordinates reassociated to
`(x, (y, z))`, the identity on `A` tensored with a matrix on `(B \ A) × Bᶜ`: its slice at any
configuration `x₀` of `A`. -/
theorem IsSupportedOn.reindex_threeCutEquiv_eq_one_kronecker
    {X : Matrix (SiteConfig n) (SiteConfig n) ℂ} {D : Finset V} (hX : IsSupportedOn X D)
    (hDA : Disjoint D A) (x₀ : (v : {v // v ∈ A}) → Fin (n v)) :
    reindex (threeCutEquiv n hAB) (threeCutEquiv n hAB) X =
      reindex (Equiv.prodAssoc _ _ _).symm (Equiv.prodAssoc _ _ _).symm
        ((1 : Matrix _ _ ℂ) ⊗ₖ fun q q' ↦
          reindex (threeCutEquiv n hAB) (threeCutEquiv n hAB) X ((x₀, q.1), q.2)
            ((x₀, q'.1), q'.2)) := by
  classical
  have hnot : ∀ v ∈ D, v ∉ A := fun v hv hvA ↦ Finset.disjoint_left.mp hDA hv hvA
  ext ⟨⟨x, y⟩, z⟩ ⟨⟨x', y'⟩, z'⟩
  change X ((threeCutEquiv n hAB).symm ((x, y), z)) ((threeCutEquiv n hAB).symm ((x', y'), z')) =
    (1 : Matrix _ _ ℂ) x x' *
      X ((threeCutEquiv n hAB).symm ((x₀, y), z)) ((threeCutEquiv n hAB).symm ((x₀, y'), z'))
  simp only [one_apply, ite_mul, one_mul, zero_mul]
  -- On the sites outside `A`, the coordinates do not depend on the part on `A`.
  have hout (x₁ x₂ : (v : {v // v ∈ A}) → Fin (n v)) (q : _) (r : _) {v : V} (hv : v ∉ A) :
      (threeCutEquiv n hAB).symm ((x₁, q), r) v = (threeCutEquiv n hAB).symm ((x₂, q), r) v := by
    by_cases hvB : v ∈ B
    · simp only [threeCutEquiv_symm_apply_of_mem_sdiff hAB (Finset.mem_sdiff.2 ⟨hvB, hv⟩)]
    · simp only [threeCutEquiv_symm_apply_of_not_mem hAB hvB]
  split_ifs with hx
  · subst hx
    refine hX.apply_eq (fun v hv ↦ hout _ _ _ _ (hnot v hv))
      (fun v hv ↦ hout _ _ _ _ (hnot v hv)) (fun v hv ↦ ?_)
    by_cases hvA : v ∈ A
    · simp only [threeCutEquiv_symm_apply_of_mem hAB hvA]
    · rw [hout x x₀ y z hvA, hout x x₀ y' z' hvA]
  · obtain ⟨w, hw⟩ := Function.ne_iff.mp hx
    refine hX.1 _ _ ⟨w.1, fun h ↦ hnot _ h w.2, ?_⟩
    rwa [threeCutEquiv_symm_apply_of_mem hAB w.2, threeCutEquiv_symm_apply_of_mem hAB w.2]

end Entropy
