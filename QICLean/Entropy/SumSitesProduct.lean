/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.EntropyDecomposition
import QICLean.Entropy.RegionEntropy

/-!
# Regional entropies of a product over two systems of sites

Let `f` be a vector on the sites `A` and `g` a vector on the sites `B`. Their product `f ⊗ g`
lives on the sites `A ⊕ B`, and the reduction of `f ⊗ g` to a region `R ⊔ T`, with `R ⊆ A` and
`T ⊆ B`, is the Kronecker product of the reductions of `f` to `R` and of `g` to `T`. For unit
vectors the entropy of `R ⊔ T` is therefore `S_f(R) + S_g(T)`. Consequently the mutual
information of two regions of `A` does not change when the sites `B` are adjoined in a product
state, and a region of `B` has no mutual information with a region of `A`.

The local alphabets form one family on `A ⊕ B`; identical sites are the constant family.

Moved from TNLean, `TNLean/Lattice/SiteRelabelEntropy.lean` at commit `e41c3b63` (its second
half), restated for an arbitrary family of local alphabets. Relabelling the sites along a
bijection is `ManyBody.relabelVector`, with `ManyBody.regionEntropy_relabel`.

## Main definitions

* `ManyBody.sumSitesProduct` — the product vector `f ⊗ g` on the sites `A ⊕ B`.
* `ManyBody.disjSumEquiv` — configurations of `R ⊔ T` as pairs of configurations.

## Main results

* `ManyBody.norm_sumSitesProduct` — the norm of a product vector.
* `ManyBody.regionState_sumSitesProduct` — the reduction to `R ⊔ T` is a Kronecker
  product.
* `ManyBody.regionEntropy_sumSitesProduct` — `S_{f ⊗ g}(R ⊔ T) = S_f(R) + S_g(T)`.
* `ManyBody.regionMutualInformation_sumSitesProduct_inl`,
  `ManyBody.regionMutualInformation_sumSitesProduct_inr_inl` — mutual information after
  adjoining sites in a product state.

## References

* OpenAI, *A two-dimensional area law from a global spectral gap*, September 24, 2026,
  proof of Proposition 10.2 (`prop:amplification`), `09-amplification.tex`, lines 342–347
  and 547–553.
-/

open Matrix
open scoped Kronecker ComplexOrder

namespace ManyBody

variable {A B : Type*} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
  {X : A ⊕ B → Type*} [∀ v, Fintype (X v)] [∀ v, DecidableEq (X v)]

/-- Configurations of a region `S` of `A ⊕ B` whose left part is `R` and right part is `T`, as
pairs of configurations. -/
private def sumConfigurationEquiv (S : Finset (A ⊕ B)) (R : Finset A) (T : Finset B)
    (hR : ∀ a, Sum.inl a ∈ S ↔ a ∈ R) (hT : ∀ b, Sum.inr b ∈ S ↔ b ∈ T) :
    ManyBody.RegionConfig X S ≃
      ManyBody.RegionConfig (fun a ↦ X (.inl a)) R × ManyBody.RegionConfig
          (fun b ↦ X (.inr b)) T where
  toFun c := (fun a ↦ c ⟨.inl a, (hR a).mpr a.2⟩, fun b ↦ c ⟨.inr b, (hT b).mpr b.2⟩)
  invFun p x := match x with
    | ⟨.inl a, h⟩ => p.1 ⟨a, (hR a).mp h⟩
    | ⟨.inr b, h⟩ => p.2 ⟨b, (hT b).mp h⟩
  left_inv c := by
    funext ⟨x, h⟩
    cases x <;> rfl
  right_inv _ := rfl

/-- Configurations of a region `R ⊔ T` of `A ⊕ B` as pairs of configurations of `R` and
of `T`. -/
def disjSumEquiv (R : Finset A) (T : Finset B) :
    ManyBody.RegionConfig X (R.disjSum T) ≃
      ManyBody.RegionConfig (fun a ↦ X (.inl a)) R × ManyBody.RegionConfig (fun b ↦ X (.inr b)) T :=
  sumConfigurationEquiv _ R T (fun _ ↦ Finset.inl_mem_disjSum) fun _ ↦ Finset.inr_mem_disjSum

/-- Configurations of the complement of `R ⊔ T` as pairs of configurations of `Rᶜ` and
of `Tᶜ`. -/
private def disjSumComplEquiv (R : Finset A) (T : Finset B) :
    ManyBody.RegionConfig X (R.disjSum T)ᶜ ≃
      ManyBody.RegionConfig (fun a ↦ X (.inl a)) Rᶜ × ManyBody.RegionConfig
          (fun b ↦ X (.inr b)) Tᶜ :=
  sumConfigurationEquiv _ Rᶜ Tᶜ (fun _ ↦ by simp) fun _ ↦ by simp

/-- The product vector `f ⊗ g` on the sites `A ⊕ B`. -/
noncomputable def sumSitesProduct (f : EuclideanSpace ℂ ((a : A) → X (.inl a)))
    (g : EuclideanSpace ℂ ((b : B) → X (.inr b))) : EuclideanSpace ℂ ((v : A ⊕ B) → X v) :=
  WithLp.toLp 2 fun c ↦ f (fun a ↦ c (.inl a)) * g (fun b ↦ c (.inr b))

omit [∀ v, DecidableEq (X v)] in
/-- The norm of a product vector is the product of the norms. -/
theorem norm_sumSitesProduct (f : EuclideanSpace ℂ ((a : A) → X (.inl a)))
    (g : EuclideanSpace ℂ ((b : B) → X (.inr b))) :
    ‖ManyBody.sumSitesProduct f g‖ = ‖f‖ * ‖g‖ := by
  rw [← sq_eq_sq₀ (norm_nonneg _) (by positivity), mul_pow, EuclideanSpace.norm_sq_eq,
    EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq, Finset.sum_mul_sum,
    ← Finset.sum_product']
  exact Fintype.sum_equiv (Equiv.sumPiEquivProdPi X) _ _ fun c ↦ by
    simp [ManyBody.sumSitesProduct, mul_pow]

omit [∀ v, Fintype (X v)] [∀ v, DecidableEq (X v)] in
private theorem splitEquiv_symm_inl (R : Finset A) (T : Finset B)
    (a : ManyBody.RegionConfig X (R.disjSum T)) (d : ManyBody.RegionConfig X (R.disjSum T)ᶜ) :
    (fun x ↦ (ManyBody.splitEquiv X (R.disjSum T)).symm (a, d) (.inl x)) =
      (ManyBody.splitEquiv (fun a ↦ X (.inl a)) R).symm
        ((ManyBody.disjSumEquiv R T a).1, (disjSumComplEquiv R T d).1) := by
  funext x
  by_cases hx : x ∈ R
  · rw [ManyBody.splitEquiv_symm_apply_of_mem _ _ _ _ _ (Finset.inl_mem_disjSum.mpr hx),
      ManyBody.splitEquiv_symm_apply_of_mem _ _ _ _ _ hx]
    rfl
  · rw
      [ManyBody.splitEquiv_symm_apply_of_notMem _ _ _ _ _
      (fun h ↦ hx (Finset.inl_mem_disjSum.mp h)),
      ManyBody.splitEquiv_symm_apply_of_notMem _ _ _ _ _ hx]
    rfl

omit [∀ v, Fintype (X v)] [∀ v, DecidableEq (X v)] in
private theorem splitEquiv_symm_inr (R : Finset A) (T : Finset B)
    (a : ManyBody.RegionConfig X (R.disjSum T)) (d : ManyBody.RegionConfig X (R.disjSum T)ᶜ) :
    (fun x ↦ (ManyBody.splitEquiv X (R.disjSum T)).symm (a, d) (.inr x)) =
      (ManyBody.splitEquiv (fun b ↦ X (.inr b)) T).symm
        ((ManyBody.disjSumEquiv R T a).2, (disjSumComplEquiv R T d).2) := by
  funext x
  by_cases hx : x ∈ T
  · rw [ManyBody.splitEquiv_symm_apply_of_mem _ _ _ _ _ (Finset.inr_mem_disjSum.mpr hx),
      ManyBody.splitEquiv_symm_apply_of_mem _ _ _ _ _ hx]
    rfl
  · rw
      [ManyBody.splitEquiv_symm_apply_of_notMem _ _ _ _ _
      (fun h ↦ hx (Finset.inr_mem_disjSum.mp h)),
      ManyBody.splitEquiv_symm_apply_of_notMem _ _ _ _ _ hx]
    rfl

omit [∀ v, DecidableEq (X v)] in
/-- The reduction of a product vector to `R ⊔ T` is the Kronecker product of the reductions of
the two factors. -/
theorem regionState_sumSitesProduct (f : EuclideanSpace ℂ ((a : A) → X (.inl a)))
    (g : EuclideanSpace ℂ ((b : B) → X (.inr b))) (R : Finset A) (T : Finset B) :
    ManyBody.regionState (ManyBody.sumSitesProduct f g) (R.disjSum T) =
      (ManyBody.regionState f R ⊗ₖ ManyBody.regionState g T).submatrix
        (ManyBody.disjSumEquiv R T) (ManyBody.disjSumEquiv R T) := by
  ext a b
  simp only
      [ManyBody.regionState_eq_regionMatrix, ManyBody.regionMatrix_apply, submatrix_apply,
      kroneckerMap_apply,
    vecMulVec_apply, Pi.star_apply, ManyBody.sumSitesProduct]
  rw [← (disjSumComplEquiv R T).symm.sum_comp, Fintype.sum_prod_type, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun d₁ _ ↦ Finset.sum_congr rfl fun d₂ _ ↦ ?_
  rw [splitEquiv_symm_inl, splitEquiv_symm_inl, splitEquiv_symm_inr, splitEquiv_symm_inr]
  simp only [Equiv.apply_symm_apply, star_mul]
  ring

/-- **The entropy of a region of a product vector.** For unit vectors `f` on the sites `A` and
`g` on the sites `B`, the region `R ⊔ T` of `f ⊗ g` has entropy `S_f(R) + S_g(T)`.
Two-dimensional area law, `09-amplification.tex`, lines 342–347. -/
theorem regionEntropy_sumSitesProduct {f : EuclideanSpace ℂ ((a : A) → X (.inl a))}
    {g : EuclideanSpace ℂ ((b : B) → X (.inr b))} (hf : ‖f‖ = 1) (hg : ‖g‖ = 1)
    (R : Finset A) (T : Finset B) :
    ManyBody.regionEntropy (ManyBody.sumSitesProduct f g) (R.disjSum T) =
      ManyBody.regionEntropy f R + ManyBody.regionEntropy g T := by
  unfold regionEntropy
  have hR := ManyBody.regionState_posSemidef R f
  have hT := ManyBody.regionState_posSemidef T g
  rw [vonNeumannEntropy_congr (ManyBody.regionState_sumSitesProduct f g R T) _
    (((hR.kronecker hT).submatrix _).isHermitian),
    vonNeumannEntropy_submatrix_equiv _ _ (hR.kronecker hT).isHermitian]
  exact vonNeumannEntropy_kronecker hR hT (ManyBody.trace_regionState_eq_one hf (D := R))
    (ManyBody.trace_regionState_eq_one hg (D := T))

/-- **Adjoining sites in a product state** does not change the mutual information of two
regions of `A`. Two-dimensional area law, `09-amplification.tex`, lines 547–553. -/
theorem regionMutualInformation_sumSitesProduct_inl {f : EuclideanSpace ℂ ((a : A) → X (.inl a))}
    {g : EuclideanSpace ℂ ((b : B) → X (.inr b))} (hf : ‖f‖ = 1) (hg : ‖g‖ = 1)
    (R T : Finset A) :
    ManyBody.regionMutualInformation (ManyBody.sumSitesProduct f g) (R.disjSum ∅) (T.disjSum ∅) =
      ManyBody.regionMutualInformation f R T := by
  have hunion : R.disjSum (∅ : Finset B) ∪ T.disjSum ∅ = (R ∪ T).disjSum ∅ := by
    ext x
    rcases x with x | x <;> simp
  simp only
      [regionMutualInformation, hunion, ManyBody.regionEntropy_sumSitesProduct hf hg,
      ManyBody.regionEntropy_empty _ g hg,
    add_zero]

/-- **A region of the adjoined sites** has no mutual information with a region of `A` in a
product vector. Two-dimensional area law, `09-amplification.tex`, lines 547–553. -/
theorem regionMutualInformation_sumSitesProduct_inr_inl
    {f : EuclideanSpace ℂ ((a : A) → X (.inl a))} {g : EuclideanSpace ℂ ((b : B) → X (.inr b))}
    (hf : ‖f‖ = 1) (hg : ‖g‖ = 1) (T : Finset B) (R : Finset A) :
    ManyBody.regionMutualInformation (ManyBody.sumSitesProduct f g) ((∅ : Finset A).disjSum T)
        (R.disjSum ∅) = 0 := by
  have hunion : (∅ : Finset A).disjSum T ∪ R.disjSum ∅ = R.disjSum T := by
    ext x
    rcases x with x | x <;> simp
  simp only
      [regionMutualInformation, hunion, ManyBody.regionEntropy_sumSitesProduct hf hg,
      ManyBody.regionEntropy_empty _ g hg,
    ManyBody.regionEntropy_empty _ f hf]
  ring

end ManyBody
