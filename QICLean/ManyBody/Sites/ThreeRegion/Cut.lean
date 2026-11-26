/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.ManyBody.Sites.SupportedDecomposition
import QICLean.ManyBody.Sites.Placement.Basic
import QICLean.Algebra.OperatorSchmidt.Basic

/-!
# Three regions of a system of sites

For regions `A ⊆ B` of a finite set of sites, a configuration splits into its parts on `A`, on
`B \ A` and on `Bᶜ`. In these coordinates `((x, y), z)` an operator supported inside `B` is a
matrix on the first two parts tensored with the identity on `Bᶜ`, an operator supported inside
`A`, inside `B \ A` or outside `B` acts on that part alone, and an operator supported outside `A`
is, after reassociating to `(x, (y, z))`, the identity on `A` tensored with a matrix on
`(B \ A) × Bᶜ`. For one local dimension `q`, the factor of an operator supported on `D` has
operator Schmidt rank at most `q ^ (2 |D ∩ A|)` across `A | B \ A`, and the factor on
`(B \ A) × Bᶜ` of an operator supported outside `A` has rank at most `q ^ (2 |D ∩ (B \ A)|)`.

For two disjoint regions `T` and `E` the coordinates are those of `A = T`, `B = T ∪ E`, whose
middle region `(T ∪ E) \ T` is `E` (`Finset.union_sdiff_cancel_left`). For a chain cut at site
`i`, with `A` the sites left of `i` and `B` the sites up to `i`, this is the setting of the
gluing lemma of Landau, Vazirani and Vidick: the left part `H_L` of the Hamiltonian is supported
inside `B` and the rest `H_i + H_R` outside `A`.

Empty regions, empty basis types and zero local dimension are included throughout.

## Main definitions

* `ManyBody.threeCutEquiv`: the coordinates `((x, y), z)` of a configuration.
* `ManyBody.subsetSplitEquiv`: the split of a configuration on `B` into its parts on `A` and
  `B \ A`.

## Main results

* `ManyBody.threeCutEquiv_eq_trans`: the three-way coordinates refine the two-way cut at `B`.
* `ManyBody.reindex_threeCutEquiv_piKronecker`: a product operator is the Kronecker product of
  its parts on the three regions.
* `ManyBody.IsSupportedOn.reindex_threeCutEquiv_eq_kronecker_one`,
  `ManyBody.IsSupportedOn.reindex_threeCutEquiv_eq_one_kronecker`: the two forms with the
  factor written as a slice of the operator.
* `ManyBody.exists_reindex_threeCutEquiv_eq_kronecker_one`,
  `ManyBody.exists_reindex_threeCutEquiv_eq_kronecker_one_kronecker_one`,
  `ManyBody.exists_reindex_threeCutEquiv_eq_one_kronecker_kronecker_one`,
  `ManyBody.exists_reindex_threeCutEquiv_eq_one_kronecker`,
  `ManyBody.exists_reindex_threeCutEquiv_eq_reindex_one_kronecker`: the five product forms of a
  supported operator, with no nonemptiness assumption.
* `ManyBody.exists_reindex_threeCutEquiv_eq_kronecker_one_operatorSchmidtRank_le`,
  `ManyBody.exists_reindex_threeCutEquiv_eq_reindex_one_kronecker_operatorSchmidtRank_le`: the
  support-intersection bounds on the operator Schmidt rank of the factors.

## References

* Z. Landau, U. Vazirani, T. Vidick, *A polynomial-time algorithm for the ground state of
  1D gapped local Hamiltonians*, arXiv:1307.5143v1, `algo53.tex`, lines 409–417.
* AKLV, arXiv:1301.1162v1, Lemma 4.2 (`l:agsp`), lines 646–654; ALVV, arXiv:1602.08828v2,
  `eq:H-mid-cut`, lines 810–821, and Proposition 5.7 (`prop:Cheby-AGSP-eff`), lines 1324–1332:
  the product forms and rank bounds are supporting locality algebra for these passages; the
  coefficient identifications, frequency counts and cut movements there are separate
  assertions.
* Polynomial-PEPS manuscript (September 24, 2026), §6.4, `05-frames.tex`, lines 352–394: the
  partition of a set of sites into `T`, `E` and `U = Λ ∖ (T ∪ E)`.
-/

open Matrix
open scoped Kronecker Matrix.Norms.L2Operator

namespace ManyBody

variable {V : Type*} [DecidableEq V]

/-! ### Coordinates -/

section Coordinates

variable (X : V → Type*) {A B : Finset V}

/-- The coordinates `((x, y), z)` of a configuration, with `x` its part on `A`, `y` its part on
`B \ A` and `z` its part on `Bᶜ`, for regions `A ⊆ B`. -/
def threeCutEquiv (hAB : A ⊆ B) :
    Config X ≃ (RegionConfig X A × RegionConfig X (B \ A)) × ComplConfig X B where
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

variable {X} (hAB : A ⊆ B)

/-- The part on `A` of a configuration is its restriction to `A`. -/
@[simp]
theorem threeCutEquiv_apply_fst_fst (σ : Config X) (v : {v // v ∈ A}) :
    (threeCutEquiv X hAB σ).1.1 v = σ v :=
  rfl

/-- The part on `B \ A` of a configuration is its restriction to `B \ A`. -/
@[simp]
theorem threeCutEquiv_apply_fst_snd (σ : Config X) (v : {v // v ∈ B \ A}) :
    (threeCutEquiv X hAB σ).1.2 v = σ v :=
  rfl

/-- The part outside `B` of a configuration is its restriction to the sites outside `B`. -/
@[simp]
theorem threeCutEquiv_apply_snd (σ : Config X) (v : {v // v ∉ B}) :
    (threeCutEquiv X hAB σ).2 v = σ v :=
  rfl

/-- At a site of `A`, the configuration glued from `((x, y), z)` takes the value of `x`. -/
theorem threeCutEquiv_symm_apply_of_mem {p} {v : V} (hv : v ∈ A) :
    (threeCutEquiv X hAB).symm p v = p.1.1 ⟨v, hv⟩ := by
  simp [threeCutEquiv, hv]

/-- At a site of `B \ A`, the configuration glued from `((x, y), z)` takes the value of `y`. -/
theorem threeCutEquiv_symm_apply_of_mem_sdiff {p} {v : V} (hv : v ∈ B \ A) :
    (threeCutEquiv X hAB).symm p v = p.1.2 ⟨v, hv⟩ := by
  have h := Finset.mem_sdiff.1 hv
  simp [threeCutEquiv, h.1, h.2]

/-- At a site outside `B`, the configuration glued from `((x, y), z)` takes the value of `z`. -/
theorem threeCutEquiv_symm_apply_of_not_mem {p} {v : V} (hv : v ∉ B) :
    (threeCutEquiv X hAB).symm p v = p.2 ⟨v, hv⟩ := by
  have hA : v ∉ A := fun h ↦ hv (hAB h)
  simp [threeCutEquiv, hA, hv]

variable (X) in
/-- The split of a configuration on `B` into its parts on `A` and on `B \ A`, for `A ⊆ B`. -/
def subsetSplitEquiv (hAB : A ⊆ B) :
    RegionConfig X B ≃ RegionConfig X A × RegionConfig X (B \ A) where
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

/-- **The three-way coordinates refine the two-way cut at `B`**: they are the cut coordinates at
`B` followed by the split of the part on `B` into its parts on `A` and `B \ A`. -/
theorem threeCutEquiv_eq_trans :
    threeCutEquiv X hAB =
      (cutEquiv X B).trans ((subsetSplitEquiv X hAB).prodCongr (Equiv.refl _)) := by
  ext σ <;> rfl

end Coordinates

/-! ### Supported operators in three-way coordinates -/

section Operators

variable [Fintype V] {X : V → Type*} [∀ v, DecidableEq (X v)] {A B : Finset V}
  (hAB : A ⊆ B)

/-- **An operator supported inside `B`** is, in three-way cut coordinates, a matrix on the parts
in `A` and `B \ A` tensored with the identity on `Bᶜ`: its slice at any configuration `z₀`
of `Bᶜ`. -/
theorem IsSupportedOn.reindex_threeCutEquiv_eq_kronecker_one
    {M : Matrix (Config X) (Config X) ℂ} {D : Finset V} (hM : IsSupportedOn M D)
    (hDB : D ⊆ B) (z₀ : ComplConfig X B) :
    reindex (threeCutEquiv X hAB) (threeCutEquiv X hAB) M =
      (fun p p' ↦ reindex (threeCutEquiv X hAB) (threeCutEquiv X hAB) M (p, z₀) (p', z₀)) ⊗ₖ
        (1 : Matrix _ _ ℂ) := by
  ext ⟨p, z⟩ ⟨p', z'⟩
  change M ((threeCutEquiv X hAB).symm (p, z)) ((threeCutEquiv X hAB).symm (p', z')) =
    M ((threeCutEquiv X hAB).symm (p, z₀)) ((threeCutEquiv X hAB).symm (p', z₀)) *
      (1 : Matrix _ _ ℂ) z z'
  simp only [one_apply, mul_ite, mul_one, mul_zero]
  split_ifs with hz
  · subst hz
    refine hM.apply_eq (fun v hv ↦ ?_) (fun v hv ↦ ?_) (fun v hv ↦ ?_)
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
    refine hM.1 _ _ ⟨w.1, fun h ↦ w.2 (hDB h), ?_⟩
    rwa [threeCutEquiv_symm_apply_of_not_mem hAB w.2,
      threeCutEquiv_symm_apply_of_not_mem hAB w.2]

omit [Fintype V] in
/-- **An operator supported outside `A`** is, in three-way cut coordinates reassociated to
`(x, (y, z))`, the identity on `A` tensored with a matrix on `(B \ A) × Bᶜ`: its slice at any
configuration `x₀` of `A`. -/
theorem IsSupportedOn.reindex_threeCutEquiv_eq_one_kronecker
    {M : Matrix (Config X) (Config X) ℂ} {D : Finset V} (hM : IsSupportedOn M D)
    (hDA : Disjoint D A) (x₀ : RegionConfig X A) :
    reindex (threeCutEquiv X hAB) (threeCutEquiv X hAB) M =
      reindex (Equiv.prodAssoc _ _ _).symm (Equiv.prodAssoc _ _ _).symm
        ((1 : Matrix _ _ ℂ) ⊗ₖ fun q q' ↦
          reindex (threeCutEquiv X hAB) (threeCutEquiv X hAB) M ((x₀, q.1), q.2)
            ((x₀, q'.1), q'.2)) := by
  have hnot : ∀ v ∈ D, v ∉ A := fun v hv hvA ↦ Finset.disjoint_left.mp hDA hv hvA
  ext ⟨⟨x, y⟩, z⟩ ⟨⟨x', y'⟩, z'⟩
  change M ((threeCutEquiv X hAB).symm ((x, y), z))
      ((threeCutEquiv X hAB).symm ((x', y'), z')) =
    (1 : Matrix _ _ ℂ) x x' *
      M ((threeCutEquiv X hAB).symm ((x₀, y), z)) ((threeCutEquiv X hAB).symm ((x₀, y'), z'))
  simp only [one_apply, ite_mul, one_mul, zero_mul]
  -- On the sites outside `A`, the coordinates do not depend on the part on `A`.
  have hout (x₁ x₂ : RegionConfig X A) (q : RegionConfig X (B \ A)) (r : ComplConfig X B)
      {v : V} (hv : v ∉ A) :
      (threeCutEquiv X hAB).symm ((x₁, q), r) v = (threeCutEquiv X hAB).symm ((x₂, q), r) v := by
    by_cases hvB : v ∈ B
    · simp only [threeCutEquiv_symm_apply_of_mem_sdiff hAB (Finset.mem_sdiff.2 ⟨hvB, hv⟩)]
    · simp only [threeCutEquiv_symm_apply_of_not_mem hAB hvB]
  split_ifs with hx
  · subst hx
    refine hM.apply_eq (fun v hv ↦ hout _ _ _ _ (hnot v hv))
      (fun v hv ↦ hout _ _ _ _ (hnot v hv)) (fun v hv ↦ ?_)
    by_cases hvA : v ∈ A
    · simp only [threeCutEquiv_symm_apply_of_mem hAB hvA]
    · rw [hout x x₀ y z hvA, hout x x₀ y' z' hvA]
  · obtain ⟨w, hw⟩ := Function.ne_iff.mp hx
    refine hM.1 _ _ ⟨w.1, fun h ↦ hnot _ h w.2, ?_⟩
    rwa [threeCutEquiv_symm_apply_of_mem hAB w.2, threeCutEquiv_symm_apply_of_mem hAB w.2]

omit [∀ v, DecidableEq (X v)] in
/-- In three-way cut coordinates, a product operator is the Kronecker product of its parts on
`A`, on `B \ A` and on `Bᶜ`. -/
theorem reindex_threeCutEquiv_piKronecker (m : (v : V) → Matrix (X v) (X v) ℂ) :
    reindex (threeCutEquiv X hAB) (threeCutEquiv X hAB) (piKronecker m) =
      (piKronecker (ι := fun w : {v // v ∈ A} ↦ X w.1) (κ := fun w ↦ X w.1) (fun w ↦ m w.1) ⊗ₖ
        piKronecker (ι := fun w : {v // v ∈ B \ A} ↦ X w.1) (κ := fun w ↦ X w.1)
          (fun w ↦ m w.1)) ⊗ₖ
        piKronecker (ι := fun w : {v // v ∉ B} ↦ X w.1) (κ := fun w ↦ X w.1) (fun w ↦ m w.1) := by
  ext ⟨⟨x, y⟩, z⟩ ⟨⟨x', y'⟩, z'⟩
  simp only [reindex_apply, submatrix_apply, kroneckerMap_apply, piKronecker_apply]
  rw [← Finset.prod_mul_prod_compl B, ← Finset.prod_sdiff hAB,
    Finset.prod_subtype (F := inferInstance) (B \ A) (fun _ ↦ Iff.rfl),
    Finset.prod_subtype (F := inferInstance) A (fun _ ↦ Iff.rfl),
    Finset.prod_subtype (F := inferInstance) Bᶜ (fun _ ↦ Finset.mem_compl), mul_comm
      (∏ w : {v // v ∈ B \ A}, _)]
  congr 1
  · congr 1
    · refine Finset.prod_congr rfl fun w _ ↦ ?_
      rw [threeCutEquiv_symm_apply_of_mem hAB w.2, threeCutEquiv_symm_apply_of_mem hAB w.2]
    · refine Finset.prod_congr rfl fun w _ ↦ ?_
      rw [threeCutEquiv_symm_apply_of_mem_sdiff hAB w.2,
        threeCutEquiv_symm_apply_of_mem_sdiff hAB w.2]
  · refine Finset.prod_congr rfl fun w _ ↦ ?_
    rw [threeCutEquiv_symm_apply_of_not_mem hAB w.2, threeCutEquiv_symm_apply_of_not_mem hAB w.2]

omit [DecidableEq V] [Fintype V] in
/-- On the sites of a set `S`, the parts of a product operator that is the identity outside `D`
are the identity when `S` misses `D`. -/
private theorem piKronecker_restrict_eq_one {S : Finset V} {D : Finset V}
    {m : (v : V) → Matrix (X v) (X v) ℂ} (hm : ∀ v ∉ D, m v = 1) (hS : ∀ v ∈ S, v ∉ D) :
    piKronecker (ι := fun w : {v // v ∈ S} ↦ X w.1) (κ := fun w ↦ X w.1) (fun w ↦ m w.1) = 1 := by
  rw [show (fun w : {v // v ∈ S} ↦ m w.1) = fun w : {v // v ∈ S} ↦ (1 : Matrix (X w.1) (X w.1) ℂ)
    from funext fun w ↦ hm w.1 (hS w.1 w.2), piKronecker_one]

/-- The same for the sites outside `B`, when `D ⊆ B`. -/
private theorem piKronecker_compl_eq_one {D : Finset V} (hDB : D ⊆ B)
    {m : (v : V) → Matrix (X v) (X v) ℂ} (hm : ∀ v ∉ D, m v = 1) :
    piKronecker (ι := fun w : {v // v ∉ B} ↦ X w.1) (κ := fun w ↦ X w.1) (fun w ↦ m w.1) = 1 := by
  rw [show (fun w : {v // v ∉ B} ↦ m w.1) = fun w : {v // v ∉ B} ↦ (1 : Matrix (X w.1) (X w.1) ℂ)
    from funext fun w ↦ hm w.1 fun h ↦ w.2 (hDB h), piKronecker_one]

variable [∀ v, Fintype (X v)]

/-- If every product operator acting on `D` has the form `Φ K` in the coordinates `e`, for a
linear map `Φ`, then so does every operator acting on `D`. -/
theorem exists_reindex_eq_of_mem_supportedOperators {κ N : Type*} [AddCommMonoid N]
    [Module ℂ N] {D : Finset V} (e : Config X ≃ κ) (Φ : N →ₗ[ℂ] Matrix κ κ ℂ)
    (hgen : ∀ m : (v : V) → Matrix (X v) (X v) ℂ, (∀ v ∉ D, m v = 1) →
      ∃ K, reindex e e (piKronecker m) = Φ K)
    {M : Matrix (Config X) (Config X) ℂ} (hM : M ∈ supportedOperators X D) :
    ∃ K, reindex e e M = Φ K := by
  induction hM using supportedOperators_induction with
  | prod m hm => exact hgen m hm
  | add M₁ M₂ _ _ h₁ h₂ =>
    obtain ⟨K₁, hK₁⟩ := h₁
    obtain ⟨K₂, hK₂⟩ := h₂
    exact ⟨K₁ + K₂, by rw [map_add Φ, ← hK₁, ← hK₂]; rfl⟩
  | smul c M₁ _ h₁ =>
    obtain ⟨K₁, hK₁⟩ := h₁
    exact ⟨c • K₁, by rw [map_smul Φ, ← hK₁]; rfl⟩

/-- **An operator supported inside `B`** is `K ⊗ 1_{Bᶜ}` in three-way cut coordinates, with no
nonemptiness assumption. -/
theorem exists_reindex_threeCutEquiv_eq_kronecker_one {M : Matrix (Config X) (Config X) ℂ}
    (hM : M ∈ supportedOperators X B) :
    ∃ K : Matrix (RegionConfig X A × RegionConfig X (B \ A))
        (RegionConfig X A × RegionConfig X (B \ A)) ℂ,
      reindex (threeCutEquiv X hAB) (threeCutEquiv X hAB) M =
        K ⊗ₖ (1 : Matrix (ComplConfig X B) (ComplConfig X B) ℂ) := by
  refine exists_reindex_eq_of_mem_supportedOperators (threeCutEquiv X hAB)
    ((kroneckerBilinear (R := ℂ)).flip (1 : Matrix (ComplConfig X B) (ComplConfig X B) ℂ))
    (fun m hm ↦ ⟨piKronecker (ι := fun w : {v // v ∈ A} ↦ X w.1) (κ := fun w ↦ X w.1)
      (fun w ↦ m w.1) ⊗ₖ
      piKronecker (ι := fun w : {v // v ∈ B \ A} ↦ X w.1) (κ := fun w ↦ X w.1)
      (fun w ↦ m w.1), ?_⟩) hM
  rw [reindex_threeCutEquiv_piKronecker hAB m, piKronecker_compl_eq_one subset_rfl hm]
  rfl

/-- **An operator supported inside `A`** is `(K ⊗ 1_{B \ A}) ⊗ 1_{Bᶜ}` in three-way cut
coordinates. ALVV, arXiv:1602.08828v2, `eq:H-mid-cut`, lines 810–821. -/
theorem exists_reindex_threeCutEquiv_eq_kronecker_one_kronecker_one {D : Finset V}
    (hD : D ⊆ A) {M : Matrix (Config X) (Config X) ℂ} (hM : M ∈ supportedOperators X D) :
    ∃ K : Matrix (RegionConfig X A) (RegionConfig X A) ℂ,
      reindex (threeCutEquiv X hAB) (threeCutEquiv X hAB) M =
        (K ⊗ₖ (1 : Matrix (RegionConfig X (B \ A)) (RegionConfig X (B \ A)) ℂ)) ⊗ₖ
          (1 : Matrix (ComplConfig X B) (ComplConfig X B) ℂ) := by
  refine exists_reindex_eq_of_mem_supportedOperators (threeCutEquiv X hAB)
    (((kroneckerBilinear (R := ℂ)).flip
      (1 : Matrix (ComplConfig X B) (ComplConfig X B) ℂ)).comp
      ((kroneckerBilinear (R := ℂ)).flip
        (1 : Matrix (RegionConfig X (B \ A)) (RegionConfig X (B \ A)) ℂ)))
    (fun m hm ↦ ⟨piKronecker (ι := fun w : {v // v ∈ A} ↦ X w.1) (κ := fun w ↦ X w.1)
      (fun w ↦ m w.1), ?_⟩) hM
  rw [reindex_threeCutEquiv_piKronecker hAB m, piKronecker_compl_eq_one (hD.trans hAB) hm,
    piKronecker_restrict_eq_one hm fun v hv hvD ↦ (Finset.mem_sdiff.1 hv).2 (hD hvD)]
  rfl

/-- **An operator supported inside `B \ A`** is `(1_A ⊗ K) ⊗ 1_{Bᶜ}` in three-way cut
coordinates. Polynomial-PEPS manuscript, proof of Lemma 6.5, `05-frames.tex`, lines 434–437. -/
theorem exists_reindex_threeCutEquiv_eq_one_kronecker_kronecker_one {D : Finset V}
    (hD : D ⊆ B \ A) {M : Matrix (Config X) (Config X) ℂ} (hM : M ∈ supportedOperators X D) :
    ∃ K : Matrix (RegionConfig X (B \ A)) (RegionConfig X (B \ A)) ℂ,
      reindex (threeCutEquiv X hAB) (threeCutEquiv X hAB) M =
        ((1 : Matrix (RegionConfig X A) (RegionConfig X A) ℂ) ⊗ₖ K) ⊗ₖ
          (1 : Matrix (ComplConfig X B) (ComplConfig X B) ℂ) := by
  refine exists_reindex_eq_of_mem_supportedOperators (threeCutEquiv X hAB)
    (((kroneckerBilinear (R := ℂ)).flip
      (1 : Matrix (ComplConfig X B) (ComplConfig X B) ℂ)).comp
      (kroneckerBilinear (R := ℂ) (1 : Matrix (RegionConfig X A) (RegionConfig X A) ℂ)))
    (fun m hm ↦ ⟨piKronecker (ι := fun w : {v // v ∈ B \ A} ↦ X w.1) (κ := fun w ↦ X w.1)
      (fun w ↦ m w.1), ?_⟩) hM
  rw [reindex_threeCutEquiv_piKronecker hAB m,
    piKronecker_compl_eq_one (hD.trans Finset.sdiff_subset) hm,
    piKronecker_restrict_eq_one hm fun v hv hvD ↦ (Finset.mem_sdiff.1 (hD hvD)).2 hv]
  rfl

/-- **An operator supported outside `B`** is `1_{A × (B \ A)} ⊗ K` in three-way cut
coordinates. ALVV, arXiv:1602.08828v2, `eq:H-mid-cut`, lines 810–821. -/
theorem exists_reindex_threeCutEquiv_eq_one_kronecker {D : Finset V} (hD : D ⊆ Bᶜ)
    {M : Matrix (Config X) (Config X) ℂ} (hM : M ∈ supportedOperators X D) :
    ∃ K : Matrix (ComplConfig X B) (ComplConfig X B) ℂ,
      reindex (threeCutEquiv X hAB) (threeCutEquiv X hAB) M =
        (1 : Matrix (RegionConfig X A × RegionConfig X (B \ A))
          (RegionConfig X A × RegionConfig X (B \ A)) ℂ) ⊗ₖ K := by
  refine exists_reindex_eq_of_mem_supportedOperators (threeCutEquiv X hAB)
    (kroneckerBilinear (R := ℂ) (1 : Matrix (RegionConfig X A × RegionConfig X (B \ A))
      (RegionConfig X A × RegionConfig X (B \ A)) ℂ))
    (fun m hm ↦ ⟨piKronecker (ι := fun w : {v // v ∉ B} ↦ X w.1) (κ := fun w ↦ X w.1)
      (fun w ↦ m w.1), ?_⟩) hM
  rw [reindex_threeCutEquiv_piKronecker hAB m,
    piKronecker_restrict_eq_one hm fun v hv hvD ↦ Finset.mem_compl.1 (hD hvD) (hAB hv),
    piKronecker_restrict_eq_one hm fun v hv hvD ↦
      Finset.mem_compl.1 (hD hvD) (Finset.mem_sdiff.1 hv).1, one_kronecker_one]
  rfl

/-- **An operator supported outside `A`** is the identity on `A` tensored with a matrix on
`(B \ A) × Bᶜ` in three-way cut coordinates reassociated to `(x, (y, z))`, with no nonemptiness
assumption. AKLV, arXiv:1301.1162v1, Lemma 4.2 (`l:agsp`), lines 646–654; ALVV,
arXiv:1602.08828v2, `eq:H-mid-cut`, lines 810–821, and `prop:Cheby-AGSP-eff`, lines
1324–1332. -/
theorem exists_reindex_threeCutEquiv_eq_reindex_one_kronecker {D : Finset V}
    (hD : Disjoint D A) {M : Matrix (Config X) (Config X) ℂ} (hM : M ∈ supportedOperators X D) :
    ∃ K : Matrix (RegionConfig X (B \ A) × ComplConfig X B)
        (RegionConfig X (B \ A) × ComplConfig X B) ℂ,
      reindex (threeCutEquiv X hAB) (threeCutEquiv X hAB) M =
        reindex (Equiv.prodAssoc _ _ _).symm (Equiv.prodAssoc _ _ _).symm
          ((1 : Matrix (RegionConfig X A) (RegionConfig X A) ℂ) ⊗ₖ K) := by
  refine exists_reindex_eq_of_mem_supportedOperators (threeCutEquiv X hAB)
    ((reindexLinearEquiv ℂ ℂ (Equiv.prodAssoc _ _ _).symm (Equiv.prodAssoc _ _ _).symm).toLinearMap
      ∘ₗ kroneckerBilinear (R := ℂ) (1 : Matrix (RegionConfig X A) (RegionConfig X A) ℂ))
    (fun m hm ↦ ⟨piKronecker (ι := fun w : {v // v ∈ B \ A} ↦ X w.1) (κ := fun w ↦ X w.1)
      (fun w ↦ m w.1) ⊗ₖ
      piKronecker (ι := fun w : {v // v ∉ B} ↦ X w.1) (κ := fun w ↦ X w.1)
      (fun w ↦ m w.1), ?_⟩) hM
  rw [reindex_threeCutEquiv_piKronecker hAB m,
    piKronecker_restrict_eq_one hm fun v hv hvD ↦ Finset.disjoint_left.1 hD hvD hv]
  change _ = reindex (Equiv.prodAssoc _ _ _).symm (Equiv.prodAssoc _ _ _).symm
    ((1 : Matrix (RegionConfig X A) (RegionConfig X A) ℂ) ⊗ₖ _)
  ext ⟨⟨x, y⟩, z⟩ ⟨⟨x', y'⟩, z'⟩
  simp [kroneckerMap_apply, mul_assoc]

end Operators

/-! ### Operator Schmidt rank of the factors -/

section SchmidtRank

variable [Fintype V] {q : ℕ} {A B D : Finset V} (hAB : A ⊆ B)

/-- The number of configurations of `Fin q` on the sites of `D` inside a region `R`. -/
private theorem card_innerConfig_const (R : Finset V) :
    Fintype.card (InnerConfig (fun _ : V ↦ q) R D) = q ^ (D ∩ R).card := by
  rw [card_innerConfig]
  simp only [Finset.prod_const]

/-- **A supported operator inside `B` has the support-intersection rank bound across
`A | B \ A`.** For one local dimension `q`, an operator supported on `D ⊆ B` is `K ⊗ 1_{Bᶜ}`
with operator Schmidt rank of `K` at most `q ^ (2 |D ∩ A|)`. No state, positivity or positive
local dimension is assumed; the bound is restricted from the matrix-unit decomposition at the
cut at `A`, read at one configuration of `Bᶜ`. Supporting locality algebra for AKLV,
arXiv:1301.1162v1, Lemma 4.2 (`l:agsp`), lines 646–654, and ALVV, arXiv:1602.08828v2,
`eq:H-mid-cut`, lines 810–821, and `prop:Cheby-AGSP-eff`, lines 1324–1332. -/
theorem exists_reindex_threeCutEquiv_eq_kronecker_one_operatorSchmidtRank_le (hDB : D ⊆ B)
    {M : Matrix (V → Fin q) (V → Fin q) ℂ} (hM : M ∈ supportedOperators (fun _ ↦ Fin q) D) :
    ∃ K : Matrix (RegionConfig (fun _ : V ↦ Fin q) A × RegionConfig (fun _ : V ↦ Fin q) (B \ A))
        (RegionConfig (fun _ : V ↦ Fin q) A × RegionConfig (fun _ : V ↦ Fin q) (B \ A)) ℂ,
      reindex (threeCutEquiv (fun _ ↦ Fin q) hAB) (threeCutEquiv (fun _ ↦ Fin q) hAB) M =
        K ⊗ₖ (1 : Matrix (ComplConfig (fun _ : V ↦ Fin q) B)
          (ComplConfig (fun _ : V ↦ Fin q) B) ℂ) ∧
      operatorSchmidtRank K ≤ q ^ (2 * (D ∩ A).card) := by
  classical
  set e := threeCutEquiv (fun _ : V ↦ Fin q) hAB
  by_cases hconfig : Nonempty (V → Fin q)
  · let σ₀ : V → Fin q := Classical.choice hconfig
    let x₀ : RegionConfig (fun _ : V ↦ Fin q) A := fun v ↦ σ₀ v
    let z₀ : ComplConfig (fun _ : V ↦ Fin q) B := fun v ↦ σ₀ v
    obtain ⟨K, hK⟩ := exists_reindex_threeCutEquiv_eq_kronecker_one hAB
      (supportedOperators_mono hDB hM)
    let γ : RegionConfig (fun _ : V ↦ Fin q) (B \ A) → ComplConfig (fun _ : V ↦ Fin q) A :=
      fun y v ↦ e.symm ((x₀, y), z₀) v
    have houtside (x : RegionConfig (fun _ : V ↦ Fin q) A)
        (y : RegionConfig (fun _ : V ↦ Fin q) (B \ A)) (v : {v // v ∉ A}) :
        e.symm ((x, y), z₀) v = γ y v := by
      dsimp only [γ]
      by_cases hvB : v.val ∈ B
      · rw [threeCutEquiv_symm_apply_of_mem_sdiff hAB (Finset.mem_sdiff.2 ⟨hvB, v.2⟩),
          threeCutEquiv_symm_apply_of_mem_sdiff hAB (Finset.mem_sdiff.2 ⟨hvB, v.2⟩)]
      · rw [threeCutEquiv_symm_apply_of_not_mem hAB hvB,
          threeCutEquiv_symm_apply_of_not_mem hAB hvB]
    have hglue (x : RegionConfig (fun _ : V ↦ Fin q) A)
        (y : RegionConfig (fun _ : V ↦ Fin q) (B \ A)) :
        (cutEquiv (fun _ ↦ Fin q) A).symm (x, γ y) = e.symm ((x, y), z₀) := by
      apply (cutEquiv (fun _ ↦ Fin q) A).injective
      rw [Equiv.apply_symm_apply]
      refine Prod.ext (funext fun v ↦ ?_) (funext fun v ↦ ?_)
      · exact (threeCutEquiv_symm_apply_of_mem hAB (p := ((x, y), z₀)) v.2).symm
      · exact (houtside x y v).symm
    have hslice (x x' : RegionConfig (fun _ : V ↦ Fin q) A)
        (y y' : RegionConfig (fun _ : V ↦ Fin q) (B \ A)) :
        M (e.symm ((x, y), z₀)) (e.symm ((x', y'), z₀)) = K (x, y) (x', y') := by
      have hentry := congrFun (congrFun hK ((x, y), z₀)) ((x', y'), z₀)
      change M (e.symm ((x, y), z₀)) (e.symm ((x', y'), z₀)) =
        K (x, y) (x', y') * (1 : Matrix (ComplConfig (fun _ : V ↦ Fin q) B)
          (ComplConfig (fun _ : V ↦ Fin q) B) ℂ) z₀ z₀ at hentry
      simpa only [one_apply_eq, mul_one] using hentry
    obtain ⟨N, L, R, hN, hdec, _⟩ :=
      IsSupportedOn.hasProductDecomposition_inner (n := fun _ ↦ q) (B := A) hM σ₀
        (c₀ := ‖M‖) le_rfl
    have hKdec : HasOperatorSchmidtDecomposition K N := by
      refine ⟨L, fun s ↦ (R s).submatrix γ γ, ?_⟩
      ext ⟨x, y⟩ ⟨x', y'⟩
      have hentry := congrFun (congrFun hdec (x, γ y)) (x', γ y')
      change M ((cutEquiv (fun _ ↦ Fin q) A).symm (x, γ y))
          ((cutEquiv (fun _ ↦ Fin q) A).symm (x', γ y')) = _ at hentry
      rw [hglue x y, hglue x' y', hslice x x' y y'] at hentry
      simpa only [Matrix.sum_apply, kronecker_apply, submatrix_apply] using hentry
    refine ⟨K, hK, (operatorSchmidtRank_le_of_hasOperatorSchmidtDecomposition hKdec).trans ?_⟩
    calc N ≤ Fintype.card (InnerConfig (fun _ : V ↦ q) A D) ^ 2 := hN
      _ = q ^ (2 * (D ∩ A).card) := by
        rw [card_innerConfig_const, ← pow_mul, Nat.mul_comm (D ∩ A).card 2]
  · have : IsEmpty (V → Fin q) := ⟨fun σ ↦ hconfig ⟨σ⟩⟩
    refine ⟨0, Matrix.ext fun p ↦ isEmptyElim (e.symm p), ?_⟩
    exact (operatorSchmidtRank_le_of_hasOperatorSchmidtDecomposition
      ⟨Fin.elim0, Fin.elim0, by simp⟩).trans (Nat.zero_le _)

/-- **An operator supported outside `A` has the support-intersection rank bound across
`B \ A | Bᶜ`.** For one local dimension `q`, an operator supported on `D` disjoint from `A` is
the identity on `A` tensored with a matrix `K` on `(B \ A) × Bᶜ` whose operator Schmidt rank is
at most `q ^ (2 |D ∩ (B \ A)|)`. No state, positivity or positive local dimension is assumed;
the bound is restricted from the matrix-unit decomposition at the cut at `B \ A`, read at one
configuration of `A`. Supporting locality algebra for AKLV, arXiv:1301.1162v1, `l:agsp`,
lines 646–654, and ALVV, arXiv:1602.08828v2, `eq:H-mid-cut`, lines 810–821, and Proposition
5.7 (`prop:Cheby-AGSP-eff`), lines 1324–1332. -/
theorem exists_reindex_threeCutEquiv_eq_reindex_one_kronecker_operatorSchmidtRank_le
    (hDA : Disjoint D A) {M : Matrix (V → Fin q) (V → Fin q) ℂ}
    (hM : M ∈ supportedOperators (fun _ ↦ Fin q) D) :
    ∃ K : Matrix (RegionConfig (fun _ : V ↦ Fin q) (B \ A) × ComplConfig (fun _ : V ↦ Fin q) B)
        (RegionConfig (fun _ : V ↦ Fin q) (B \ A) × ComplConfig (fun _ : V ↦ Fin q) B) ℂ,
      reindex (threeCutEquiv (fun _ ↦ Fin q) hAB) (threeCutEquiv (fun _ ↦ Fin q) hAB) M =
        reindex (Equiv.prodAssoc _ _ _).symm (Equiv.prodAssoc _ _ _).symm
          ((1 : Matrix (RegionConfig (fun _ : V ↦ Fin q) A)
            (RegionConfig (fun _ : V ↦ Fin q) A) ℂ) ⊗ₖ K) ∧
        operatorSchmidtRank K ≤ q ^ (2 * (D ∩ (B \ A)).card) := by
  classical
  set e := threeCutEquiv (fun _ : V ↦ Fin q) hAB
  by_cases hconfig : Nonempty (V → Fin q)
  · let σ₀ : V → Fin q := Classical.choice hconfig
    let x₀ : RegionConfig (fun _ : V ↦ Fin q) A := fun v ↦ σ₀ v
    let y₀ : RegionConfig (fun _ : V ↦ Fin q) (B \ A) := fun v ↦ σ₀ v
    obtain ⟨K, hK⟩ := exists_reindex_threeCutEquiv_eq_reindex_one_kronecker hAB hDA hM
    let γ : ComplConfig (fun _ : V ↦ Fin q) B → ComplConfig (fun _ : V ↦ Fin q) (B \ A) :=
      fun z v ↦ e.symm ((x₀, y₀), z) v
    have houtside (y : RegionConfig (fun _ : V ↦ Fin q) (B \ A))
        (z : ComplConfig (fun _ : V ↦ Fin q) B) (v : {v // v ∉ B \ A}) :
        e.symm ((x₀, y), z) v = γ z v := by
      dsimp only [γ]
      by_cases hvA : v.val ∈ A
      · rw [threeCutEquiv_symm_apply_of_mem hAB hvA, threeCutEquiv_symm_apply_of_mem hAB hvA]
      · have hvB : v.val ∉ B := fun hvB ↦ v.2 (Finset.mem_sdiff.2 ⟨hvB, hvA⟩)
        rw [threeCutEquiv_symm_apply_of_not_mem hAB hvB,
          threeCutEquiv_symm_apply_of_not_mem hAB hvB]
    have hglue (y : RegionConfig (fun _ : V ↦ Fin q) (B \ A))
        (z : ComplConfig (fun _ : V ↦ Fin q) B) :
        (cutEquiv (fun _ ↦ Fin q) (B \ A)).symm (y, γ z) = e.symm ((x₀, y), z) := by
      apply (cutEquiv (fun _ ↦ Fin q) (B \ A)).injective
      rw [Equiv.apply_symm_apply]
      refine Prod.ext (funext fun v ↦ ?_) (funext fun v ↦ ?_)
      · exact (threeCutEquiv_symm_apply_of_mem_sdiff hAB (p := ((x₀, y), z)) v.2).symm
      · exact (houtside y z v).symm
    have hslice (y y' : RegionConfig (fun _ : V ↦ Fin q) (B \ A))
        (z z' : ComplConfig (fun _ : V ↦ Fin q) B) :
        M (e.symm ((x₀, y), z)) (e.symm ((x₀, y'), z')) = K (y, z) (y', z') := by
      have hentry := congrFun (congrFun hK ((x₀, y), z)) ((x₀, y'), z')
      change M (e.symm ((x₀, y), z)) (e.symm ((x₀, y'), z')) =
        (1 : Matrix (RegionConfig (fun _ : V ↦ Fin q) A)
          (RegionConfig (fun _ : V ↦ Fin q) A) ℂ) x₀ x₀ * K (y, z) (y', z') at hentry
      simpa only [one_apply_eq, one_mul] using hentry
    obtain ⟨N, L, R, hN, hdec, _⟩ :=
      IsSupportedOn.hasProductDecomposition_inner (n := fun _ ↦ q) (B := B \ A) hM σ₀
        (c₀ := ‖M‖) le_rfl
    have hKdec : HasOperatorSchmidtDecomposition K N := by
      refine ⟨L, fun s ↦ (R s).submatrix γ γ, ?_⟩
      ext ⟨y, z⟩ ⟨y', z'⟩
      have hentry := congrFun (congrFun hdec (y, γ z)) (y', γ z')
      change M ((cutEquiv (fun _ ↦ Fin q) (B \ A)).symm (y, γ z))
          ((cutEquiv (fun _ ↦ Fin q) (B \ A)).symm (y', γ z')) = _ at hentry
      rw [hglue y z, hglue y' z', hslice y y' z z'] at hentry
      simpa only [Matrix.sum_apply, kronecker_apply, submatrix_apply] using hentry
    refine ⟨K, hK, (operatorSchmidtRank_le_of_hasOperatorSchmidtDecomposition hKdec).trans ?_⟩
    calc N ≤ Fintype.card (InnerConfig (fun _ : V ↦ q) (B \ A) D) ^ 2 := hN
      _ = q ^ (2 * (D ∩ (B \ A)).card) := by
        rw [card_innerConfig_const, ← pow_mul, Nat.mul_comm (D ∩ (B \ A)).card 2]
  · have : IsEmpty (V → Fin q) := ⟨fun σ ↦ hconfig ⟨σ⟩⟩
    refine ⟨0, Matrix.ext fun p ↦ isEmptyElim (e.symm p), ?_⟩
    exact (operatorSchmidtRank_le_of_hasOperatorSchmidtDecomposition
      ⟨Fin.elim0, Fin.elim0, by simp⟩).trans (Nat.zero_le _)

end SchmidtRank

end ManyBody
