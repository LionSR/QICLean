/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.ManyBody.Sites.Support
import QICLean.Algebra.HermitianHelpers
import Mathlib.Analysis.CStarAlgebra.Hom
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Matrix.Order
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# Placement of a regional matrix

For a region `D` of a system of sites `X`, the placement `ManyBody.place D K` of a matrix `K`
on the configurations of `D` is the operator `K ⊗ 1` on `⊗_v ℂ^{X v}`, which acts as `K` on
the sites of `D` and as the identity elsewhere. Placement is a unital `*`-homomorphism of the
matrix algebra of the region into that of the system, and its range is exactly the
subalgebra of operators supported on `D`. When every basis type is nonempty it is injective,
preserves the operator norm, and reflects the order.

## Main definitions

* `ManyBody.place` — the placement `K ↦ K ⊗ 1` of a regional matrix.
* `ManyBody.placeHom` — the placement as a `*`-homomorphism.

## Implementation notes

A statement whose left side or hypotheses compute in the matrix algebra of the region (a
product, a power, an inverse, positivity, the order) takes the finiteness and decidability of
`RegionConfig X D` as instance arguments of its own, instead of the instances derived from
those of the basis types. Any instance on the region then matches, so these lemmas rewrite
terms in which `X` is a specific family, such as `fun _ ↦ Fin d` or `fun v ↦ Fin (n v)`;
with the derived instances the unifier would have to solve for the family of instances from
its restriction to the region.

## Main results

* `ManyBody.place_apply` — the entries of a placed matrix.
* `ManyBody.place_mul`, `ManyBody.place_one`, `ManyBody.place_conjTranspose` and the linear
  lemmas.
* `ManyBody.place_mem_supportedOperators`, `ManyBody.exists_eq_place_of_mem_supportedOperators`,
  `ManyBody.range_placeHom` — the placed matrices are the supported operators.
* `ManyBody.place_injective`, `ManyBody.norm_place`, `ManyBody.norm_place_le`.
* `ManyBody.posSemidef_place`, `ManyBody.posSemidef_place_iff`, `ManyBody.place_le_place_iff`.
-/

open Matrix
open scoped Kronecker Matrix.Norms.L2Operator MatrixOrder ComplexOrder

namespace ManyBody

variable {V : Type*} [Fintype V] [DecidableEq V] {X : V → Type*} [∀ v, DecidableEq (X v)]
  {D : Finset V}

/-- The placement `K ↦ K ⊗ 1` of a matrix on the configurations of the region `D`: the
operator on the whole system that acts as `K` on the sites of `D` and as the identity on the
other sites. -/
noncomputable def place (D : Finset V) (K : Matrix (RegionConfig X D) (RegionConfig X D) ℂ) :
    Matrix (Config X) (Config X) ℂ :=
  reindex (cutEquiv X D).symm (cutEquiv X D).symm
    (K ⊗ₖ (1 : Matrix (ComplConfig X D) (ComplConfig X D) ℂ))

/-- Entries of a placed matrix: `(K ⊗ 1)_{στ}` is the entry of `K` at the parts of `σ` and
`τ` on `D` when `σ` and `τ` agree outside `D`, and zero otherwise. -/
theorem place_apply (D : Finset V) (K : Matrix (RegionConfig X D) (RegionConfig X D) ℂ)
    (σ τ : Config X) :
    place D K σ τ = if ∀ v ∉ D, σ v = τ v then K (fun v ↦ σ v) (fun v ↦ τ v) else 0 := by
  simp only [place, reindex_apply, submatrix_apply, Equiv.symm_symm, kroneckerMap_apply,
    one_apply, cutEquiv_snd_eq_iff, mul_ite, mul_one, mul_zero]
  rfl

/-- In the coordinates of the cut along `D`, a placed matrix is `K ⊗ 1`. -/
theorem reindex_cutEquiv_place (K : Matrix (RegionConfig X D) (RegionConfig X D) ℂ) :
    reindex (cutEquiv X D) (cutEquiv X D) (place D K) =
      K ⊗ₖ (1 : Matrix (ComplConfig X D) (ComplConfig X D) ℂ) := by
  ext a b
  simp [place]

/-- A matrix on a region is recovered from its placement, at any configuration `y` of the
other sites. -/
theorem place_apply_cutEquiv_symm (K : Matrix (RegionConfig X D) (RegionConfig X D) ℂ)
    (a b : RegionConfig X D) (y : ComplConfig X D) :
    place D K ((cutEquiv X D).symm (a, y)) ((cutEquiv X D).symm (b, y)) = K a b := by
  simp [place]

/-! ### Algebraic properties -/

section Algebra

variable (K K' : Matrix (RegionConfig X D) (RegionConfig X D) ℂ)

@[simp]
theorem place_zero : place D (0 : Matrix (RegionConfig X D) (RegionConfig X D) ℂ) = 0 := by
  simp [place]

theorem place_add : place D (K + K') = place D K + place D K' := by
  simp [place, add_kronecker, submatrix_add]

theorem place_smul (c : ℂ) : place D (c • K) = c • place D K := by
  simp [place, smul_kronecker, submatrix_smul]

theorem place_neg : place D (-K) = -place D K := by
  rw [← neg_one_smul ℂ K, place_smul, neg_one_smul]

theorem place_sub : place D (K - K') = place D K - place D K' := by
  rw [sub_eq_add_neg, place_add, place_neg, sub_eq_add_neg]

theorem place_sum {ι : Type*} (s : Finset ι)
    (K : ι → Matrix (RegionConfig X D) (RegionConfig X D) ℂ) :
    place D (∑ i ∈ s, K i) = ∑ i ∈ s, place D (K i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, place_add, ih]

theorem place_conjTranspose : place D Kᴴ = (place D K)ᴴ := by
  simp [place, conjTranspose_kronecker, conjTranspose_submatrix]

/-- The placement of a Hermitian matrix is Hermitian. -/
theorem isHermitian_place {K : Matrix (RegionConfig X D) (RegionConfig X D) ℂ}
    (hK : K.IsHermitian) : (place D K).IsHermitian :=
  hK.apply_of_map_conjTranspose place_conjTranspose

@[simp]
theorem place_one [DecidableEq (RegionConfig X D)] :
    place D (1 : Matrix (RegionConfig X D) (RegionConfig X D) ℂ) = 1 := by
  obtain rfl : ‹DecidableEq (RegionConfig X D)› = Fintype.decidablePiFintype :=
    Subsingleton.elim _ _
  simp [place]

variable [∀ v, Fintype (X v)]

theorem place_mul [Fintype (RegionConfig X D)] : place D (K * K') = place D K * place D K' := by
  obtain rfl : ‹Fintype (RegionConfig X D)› = Pi.instFintype := Subsingleton.elim _ _
  simp only [place, reindex_apply, submatrix_mul_equiv, ← mul_kronecker_mul, Matrix.one_mul]

theorem place_pow [Fintype (RegionConfig X D)] [DecidableEq (RegionConfig X D)] (k : ℕ) :
    place D (K ^ k) = place D K ^ k := by
  induction k with
  | zero => rw [pow_zero, pow_zero, place_one]
  | succ k ih => rw [pow_succ, pow_succ, place_mul, ih]

/-- The placement of the inverse is a right inverse of the placement. -/
theorem place_mul_place_inv [Fintype (RegionConfig X D)] [DecidableEq (RegionConfig X D)]
    {K : Matrix (RegionConfig X D) (RegionConfig X D) ℂ} (hK : IsUnit K.det) :
    place D K * place D K⁻¹ = 1 := by
  rw [← place_mul, mul_nonsing_inv _ hK, place_one]

/-- The placement of the inverse is a left inverse of the placement. -/
theorem place_inv_mul_place [Fintype (RegionConfig X D)] [DecidableEq (RegionConfig X D)]
    {K : Matrix (RegionConfig X D) (RegionConfig X D) ℂ} (hK : IsUnit K.det) :
    place D K⁻¹ * place D K = 1 := by
  rw [← place_mul, nonsing_inv_mul _ hK, place_one]

/-- The trace of a placed matrix is the trace of the matrix times the number of
configurations outside the region. -/
theorem trace_place [Fintype (RegionConfig X D)] :
    (place D K).trace = Fintype.card (ComplConfig X D) * K.trace := by
  obtain rfl : ‹Fintype (RegionConfig X D)› = Pi.instFintype := Subsingleton.elim _ _
  have h : ∀ M : Matrix (RegionConfig X D × ComplConfig X D) (RegionConfig X D × ComplConfig X D) ℂ,
      (M.submatrix (cutEquiv X D) (cutEquiv X D)).trace = M.trace := fun M ↦ by
    simp only [Matrix.trace, diag_apply, submatrix_apply]
    exact (cutEquiv X D).sum_comp fun j ↦ M j j
  rw [place, reindex_apply, Equiv.symm_symm, h, trace_kronecker, trace_one, mul_comm]

/-- The placement `K ↦ K ⊗ 1` as a unital `*`-homomorphism from the matrix algebra of a
region to the matrix algebra of the system. -/
noncomputable def placeHom (D : Finset V) :
    Matrix (RegionConfig X D) (RegionConfig X D) ℂ →⋆ₐ[ℂ] Matrix (Config X) (Config X) ℂ where
  toFun := place D
  map_one' := place_one
  map_mul' K K' := place_mul K K'
  map_zero' := place_zero
  map_add' K K' := place_add K K'
  commutes' c := by
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, place_smul, place_one]
  map_star' K := by
    rw [star_eq_conjTranspose, star_eq_conjTranspose, place_conjTranspose]

@[simp]
theorem placeHom_apply : placeHom D K = place D K :=
  rfl

end Algebra

/-! ### Placed matrices are the supported operators -/

section Support

variable [∀ v, Fintype (X v)]

/-- A placed matrix is supported on its region. -/
theorem place_mem_supportedOperators (K : Matrix (RegionConfig X D) (RegionConfig X D) ℂ) :
    place D K ∈ supportedOperators X D := by
  refine ⟨fun σ τ ⟨v, hv, hne⟩ ↦ ?_, fun σ τ σ' τ' h1 h2 h3 h4 ↦ ?_⟩
  · rw [place_apply, ite_eq_right fun h ↦ hne (h v hv)]
  · rw [place_apply, place_apply, ite_eq_left h3, ite_eq_left h4,
      show (fun v : {v // v ∈ D} ↦ σ v) = fun v : {v // v ∈ D} ↦ σ' v from
        funext fun v ↦ h1 v.1 v.2,
      show (fun v : {v // v ∈ D} ↦ τ v) = fun v : {v // v ∈ D} ↦ τ' v from
        funext fun v ↦ h2 v.1 v.2]

/-- Every operator supported on a region is the placement of a matrix on that region. -/
theorem exists_eq_place_of_mem_supportedOperators {A : Matrix (Config X) (Config X) ℂ}
    (hA : A ∈ supportedOperators X D) :
    ∃ K : Matrix (RegionConfig X D) (RegionConfig X D) ℂ, A = place D K := by
  cases isEmpty_or_nonempty (Config X) with
  | inl _ => exact ⟨0, Subsingleton.elim _ _⟩
  | inr h =>
    obtain ⟨σ₀⟩ := h
    refine ⟨Matrix.of fun a b ↦ A ((cutEquiv X D).symm (a, (cutEquiv X D σ₀).2))
      ((cutEquiv X D).symm (b, (cutEquiv X D σ₀).2)), ?_⟩
    ext σ τ
    rw [place_apply, of_apply]
    split_ifs with h
    · refine apply_eq_of_mem_supportedOperators hA (fun v hv ↦ ?_) (fun v hv ↦ ?_)
        fun v hv ↦ ?_
      · rw [cutEquiv_symm_apply_mem _ _ hv]
      · rw [cutEquiv_symm_apply_mem _ _ hv]
      · rw [cutEquiv_symm_apply_not_mem _ _ hv, cutEquiv_symm_apply_not_mem _ _ hv]
        exact iff_of_true (h v hv) rfl
    · push Not at h
      obtain ⟨v, hv, hne⟩ := h
      exact apply_eq_zero_of_mem_supportedOperators hA hv hne

/-- An operator is supported on a region exactly when it is the placement of a matrix on that
region. -/
theorem mem_supportedOperators_iff_exists_eq_place {A : Matrix (Config X) (Config X) ℂ} :
    A ∈ supportedOperators X D ↔
      ∃ K : Matrix (RegionConfig X D) (RegionConfig X D) ℂ, A = place D K :=
  ⟨exists_eq_place_of_mem_supportedOperators, by
    rintro ⟨K, rfl⟩
    exact place_mem_supportedOperators K⟩

/-- The range of the placement is the subalgebra of operators supported on the region. -/
theorem range_placeHom (D : Finset V) :
    (placeHom (X := X) D).range = supportedOperators X D := by
  refine StarSubalgebra.ext fun A ↦ ?_
  rw [mem_supportedOperators_iff_exists_eq_place]
  exact ⟨fun ⟨K, hK⟩ ↦ ⟨K, hK.symm⟩, fun ⟨K, hK⟩ ↦ ⟨K, hK.symm⟩⟩

end Support

/-! ### Product operators -/

section Product

variable [∀ v, Fintype (X v)]

/-- The product operator `⊗_v m_v` of a family of on-site matrices, with matrix elements
`∏_v m_v(σ_v, τ_v)`. -/
def prodOp (m : (v : V) → Matrix (X v) (X v) ℂ) : Matrix (Config X) (Config X) ℂ :=
  Matrix.of fun σ τ ↦ ∏ v, m v (σ v) (τ v)

omit [DecidableEq V] [∀ v, DecidableEq (X v)] [∀ v, Fintype (X v)] in
@[simp]
theorem prodOp_apply (m : (v : V) → Matrix (X v) (X v) ℂ) (σ τ : Config X) :
    prodOp m σ τ = ∏ v, m v (σ v) (τ v) :=
  rfl

omit [∀ v, DecidableEq (X v)] in
/-- Product operators multiply sitewise. -/
theorem prodOp_mul (m m' : (v : V) → Matrix (X v) (X v) ℂ) :
    prodOp m * prodOp m' = prodOp fun v ↦ m v * m' v := by
  ext σ τ
  simp only [prodOp, Matrix.mul_apply, Matrix.of_apply, Fintype.prod_sum,
    Finset.prod_mul_distrib]

omit [DecidableEq V] [∀ v, Fintype (X v)] in
@[simp]
theorem prodOp_one : prodOp (fun v ↦ (1 : Matrix (X v) (X v) ℂ)) = 1 := by
  ext σ τ
  simp only [prodOp, Matrix.of_apply, Matrix.one_apply]
  by_cases h : σ = τ
  · subst h
    simp
  · obtain ⟨v, hv⟩ := Function.ne_iff.mp h
    rw [ite_eq_right h]
    exact Finset.prod_eq_zero (Finset.mem_univ v) (ite_eq_right hv)

omit [DecidableEq V] [∀ v, Fintype (X v)] [∀ v, DecidableEq (X v)] in
/-- The adjoint of a product operator is the product of the adjoints. -/
theorem conjTranspose_prodOp (m : (v : V) → Matrix (X v) (X v) ℂ) :
    (prodOp m)ᴴ = prodOp fun v ↦ (m v)ᴴ := by
  ext σ τ
  simp [prodOp, Matrix.conjTranspose_apply]

omit [DecidableEq V] [∀ v, Fintype (X v)] [∀ v, DecidableEq (X v)] in
theorem star_prodOp (m : (v : V) → Matrix (X v) (X v) ℂ) :
    star (prodOp m) = prodOp fun v ↦ star (m v) :=
  conjTranspose_prodOp m

/-- A product of unitaries is unitary. -/
theorem prodOp_mem_unitary {m : (v : V) → Matrix (X v) (X v) ℂ}
    (hm : ∀ v, m v ∈ unitary (Matrix (X v) (X v) ℂ)) :
    prodOp m ∈ unitary (Matrix (Config X) (Config X) ℂ) := by
  refine Matrix.mem_unitaryGroup_iff.mpr ?_
  rw [star_prodOp, prodOp_mul]
  simp only [fun v ↦ Unitary.mul_star_self_of_mem (hm v)]
  exact prodOp_one

/-- A product operator `⊗_v m_v` with `m_v = 1` outside `D` is supported on `D`. -/
theorem prodOp_mem_supportedOperators {m : (v : V) → Matrix (X v) (X v) ℂ}
    (hm : ∀ v ∉ D, m v = 1) : prodOp m ∈ supportedOperators X D := by
  refine ⟨fun σ τ ⟨v, hv, hne⟩ ↦ ?_, fun σ τ σ' τ' h1 h2 h3 h4 ↦ ?_⟩
  · rw [prodOp_apply]
    exact Finset.prod_eq_zero (Finset.mem_univ v) (by rw [hm v hv, one_apply_ne hne])
  · simp only [prodOp_apply]
    refine Finset.prod_congr rfl fun v _ ↦ ?_
    by_cases hv : v ∈ D
    · rw [h1 v hv, h2 v hv]
    · rw [hm v hv, h3 v hv, h4 v hv, one_apply_eq, one_apply_eq]

omit [∀ v, Fintype (X v)] in
/-- The placement of a matrix unit of a region is the product of the matrix units at the sites
of the region and the identity at the other sites. -/
theorem place_single (a b : RegionConfig X D) :
    place D (single a b (1 : ℂ)) =
      prodOp fun v ↦ if h : v ∈ D then single (a ⟨v, h⟩) (b ⟨v, h⟩) (1 : ℂ) else 1 := by
  ext σ τ
  have hf : ∀ v, (if h : v ∈ D then single (a ⟨v, h⟩) (b ⟨v, h⟩) (1 : ℂ) else 1) (σ v) (τ v) =
      if (if h : v ∈ D then a ⟨v, h⟩ = σ v ∧ b ⟨v, h⟩ = τ v else σ v = τ v) then 1 else 0 := by
    intro v
    by_cases h : v ∈ D <;> simp [h, single_apply, one_apply]
  rw [place_apply, prodOp_apply, Finset.prod_congr rfl fun v _ ↦ hf v, Fintype.prod_boole]
  by_cases hout : ∀ v ∉ D, σ v = τ v
  · rw [ite_eq_left hout, single_apply]
    refine if_congr ⟨fun ⟨ha, hb⟩ v ↦ ?_, fun h ↦ ⟨funext fun v ↦ ?_, funext fun v ↦ ?_⟩⟩ rfl rfl
    · by_cases hv : v ∈ D
      · rw [dite_eq_left hv]
        exact ⟨congrFun ha ⟨v, hv⟩, congrFun hb ⟨v, hv⟩⟩
      · rw [dite_eq_right hv]
        exact hout v hv
    · have hv := h v.1
      rw [dite_eq_left v.2] at hv
      exact hv.1
    · have hv := h v.1
      rw [dite_eq_left v.2] at hv
      exact hv.2
  · push Not at hout
    obtain ⟨v, hv, hne⟩ := hout
    rw [ite_eq_right fun h ↦ hne (h v hv), ite_eq_right fun h ↦ hne (by simpa [hv] using h v)]

/-- **Supported operators are spanned by product operators.** The operators supported on `D`
are the linear combinations of the product operators `⊗_v m_v` with `m_v = 1` outside `D`. -/
theorem supportedOperators_toSubmodule_eq_span (D : Finset V) :
    Subalgebra.toSubmodule (supportedOperators X D).toSubalgebra =
      Submodule.span ℂ {A | ∃ m : (v : V) → Matrix (X v) (X v) ℂ, (∀ v ∉ D, m v = 1) ∧
        A = prodOp m} := by
  refine le_antisymm (fun A hA ↦ ?_) (Submodule.span_le.mpr ?_)
  · obtain ⟨K, rfl⟩ := exists_eq_place_of_mem_supportedOperators hA
    rw [matrix_eq_sum_single K, place_sum]
    refine Submodule.sum_mem _ fun a _ ↦ ?_
    rw [place_sum]
    refine Submodule.sum_mem _ fun b _ ↦ ?_
    rw [show single a b (K a b) = K a b • single a b (1 : ℂ) by rw [smul_single, smul_eq_mul,
      mul_one], place_smul]
    refine Submodule.smul_mem _ _ (Submodule.subset_span ⟨fun v ↦
      if h : v ∈ D then single (a ⟨v, h⟩) (b ⟨v, h⟩) (1 : ℂ) else 1,
      fun v hv ↦ dite_eq_right hv, place_single a b⟩)
  · rintro _ ⟨m, hm, rfl⟩
    exact prodOp_mem_supportedOperators hm

/-- **Induction over product operators.** A property of the operators supported on `D` holds
for all of them if it holds for the product operators `⊗_v m_v` with `m_v = 1` outside `D` and
is closed under sums and scalar multiples. -/
@[elab_as_elim]
theorem supportedOperators_induction {D : Finset V}
    {p : (A : Matrix (Config X) (Config X) ℂ) → A ∈ supportedOperators X D → Prop}
    (prod : ∀ (m : (v : V) → Matrix (X v) (X v) ℂ) (hm : ∀ v ∉ D, m v = 1),
      p (prodOp m) (prodOp_mem_supportedOperators hm))
    (add : ∀ A B hA hB, p A hA → p B hB → p (A + B) (add_mem hA hB))
    (smul : ∀ (c : ℂ) A hA, p A hA → p (c • A) (SMulMemClass.smul_mem c hA))
    {A : Matrix (Config X) (Config X) ℂ} (hA : A ∈ supportedOperators X D) : p A hA := by
  have hiff (B : Matrix (Config X) (Config X) ℂ) : B ∈ supportedOperators X D ↔
      B ∈ Submodule.span ℂ {A | ∃ m : (v : V) → Matrix (X v) (X v) ℂ, (∀ v ∉ D, m v = 1) ∧
        A = prodOp m} := by
    rw [← supportedOperators_toSubmodule_eq_span]
    rfl
  refine Submodule.span_induction (p := fun B _ ↦ ∀ hB : B ∈ supportedOperators X D, p B hB)
    ?_ ?_ ?_ ?_ ((hiff A).mp hA) hA
  · rintro _ ⟨m, hm, rfl⟩ _
    exact prod m hm
  · intro h0
    have h := smul 0 _ _ (prod (fun _ ↦ 1) fun _ _ ↦ rfl)
    simp only [zero_smul] at h
    exact h
  · intro B C hB hC ihB ihC _
    exact add B C _ _ (ihB ((hiff B).mpr hB)) (ihC ((hiff C).mpr hC))
  · intro c B hB ihB _
    exact smul c B _ (ihB ((hiff B).mpr hB))

/-- Two bilinear maps that agree on pairs of product operators agree on all pairs of supported
operators. -/
theorem eq_of_mem_supportedOperators₂ {M : Type*} [AddCommMonoid M] [Module ℂ M]
    {D D' : Finset V}
    (f g : Matrix (Config X) (Config X) ℂ →ₗ[ℂ] Matrix (Config X) (Config X) ℂ →ₗ[ℂ] M)
    (h : ∀ m m' : (v : V) → Matrix (X v) (X v) ℂ, (∀ v ∉ D, m v = 1) → (∀ v ∉ D', m' v = 1) →
      f (prodOp m) (prodOp m') = g (prodOp m) (prodOp m'))
    {A B : Matrix (Config X) (Config X) ℂ} (hA : A ∈ supportedOperators X D)
    (hB : B ∈ supportedOperators X D') : f A B = g A B := by
  induction hA using supportedOperators_induction with
  | prod m hm =>
    induction hB using supportedOperators_induction with
    | prod m' hm' => exact h m m' hm hm'
    | add B C _ _ ihB ihC => rw [map_add, map_add, ihB, ihC]
    | smul c B _ ihB => rw [map_smul, map_smul, ihB]
  | add A C _ _ ihA ihC => rw [map_add, map_add, LinearMap.add_apply, LinearMap.add_apply, ihA, ihC]
  | smul c A _ ihA => rw [map_smul, map_smul, LinearMap.smul_apply, LinearMap.smul_apply, ihA]

end Product

/-! ### Injectivity, norm and order -/

section Order

variable [∀ v, Fintype (X v)]

/-- Placement does not increase the operator norm. -/
theorem norm_place_le (K : Matrix (RegionConfig X D) (RegionConfig X D) ℂ) :
    ‖place D K‖ ≤ ‖K‖ :=
  NonUnitalStarAlgHom.norm_apply_le (placeHom D) K

omit [∀ v, Fintype (X v)] in
/-- The placement of a positive semidefinite matrix is positive semidefinite. -/
theorem posSemidef_place [∀ v, Finite (X v)]
    {K : Matrix (RegionConfig X D) (RegionConfig X D) ℂ} (hK : K.PosSemidef) :
    (place D K).PosSemidef :=
  (hK.kronecker PosSemidef.one).submatrix _

omit [∀ v, Fintype (X v)] in
/-- Placement is monotone. -/
theorem place_le_place [∀ v, Finite (X v)]
    {K K' : Matrix (RegionConfig X D) (RegionConfig X D) ℂ} (h : K ≤ K') :
    place D K ≤ place D K' := by
  rw [Matrix.le_iff, ← place_sub]
  exact posSemidef_place (Matrix.le_iff.mp h)

variable [∀ v, Nonempty (X v)]

omit [∀ v, Fintype (X v)] in
/-- When every basis type is nonempty, placement is injective. -/
theorem place_injective (D : Finset V) :
    Function.Injective (place (X := X) D) := by
  intro K K' h
  ext a b
  have y : ComplConfig X D := fun v ↦ Classical.arbitrary (X v)
  rw [← place_apply_cutEquiv_symm K a b y, ← place_apply_cutEquiv_symm K' a b y, h]

omit [∀ v, Fintype (X v)] in
@[simp]
theorem place_inj {K K' : Matrix (RegionConfig X D) (RegionConfig X D) ℂ} :
    place D K = place D K' ↔ K = K' :=
  (place_injective D).eq_iff

/-- When every basis type is nonempty, placement preserves the operator norm. -/
theorem norm_place (K : Matrix (RegionConfig X D) (RegionConfig X D) ℂ) :
    ‖place D K‖ = ‖K‖ :=
  NonUnitalStarAlgHom.norm_map (placeHom D) (place_injective D) K

omit [∀ v, Fintype (X v)] in
/-- When every basis type is nonempty, a matrix is positive semidefinite exactly when its
placement is. -/
theorem posSemidef_place_iff [∀ v, Finite (X v)]
    {K : Matrix (RegionConfig X D) (RegionConfig X D) ℂ} :
    (place D K).PosSemidef ↔ K.PosSemidef := by
  refine ⟨fun h ↦ ?_, posSemidef_place⟩
  have y : ComplConfig X D := fun v ↦ Classical.arbitrary (X v)
  have e : K = (place D K).submatrix (fun a ↦ (cutEquiv X D).symm (a, y))
      (fun a ↦ (cutEquiv X D).symm (a, y)) := by
    ext a b
    rw [submatrix_apply, place_apply_cutEquiv_symm]
  rw [e]
  exact h.submatrix _

omit [∀ v, Fintype (X v)] in
/-- When every basis type is nonempty, placement reflects the order. -/
theorem place_le_place_iff [∀ v, Finite (X v)]
    {K K' : Matrix (RegionConfig X D) (RegionConfig X D) ℂ} :
    place D K ≤ place D K' ↔ K ≤ K' := by
  rw [Matrix.le_iff, Matrix.le_iff, ← place_sub, posSemidef_place_iff]

end Order

end ManyBody
