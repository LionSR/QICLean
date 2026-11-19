/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.ManyBody.Sites.Placement

/-!
# Matrix product form on a system of sites

For a system of sites with finite basis types `X v` and a locality relation `near` on the
sites, a matrix product form of an operator `ρ` is an expansion
`ρ = ∑_α (∏_i F_i(α)) • ⊗_j ρ_j(α_j)`
in which the coefficient `F_i` depends only on the indices `α_j` with `near i j`
(Hastings, arXiv:cond-mat/0508554v3, eq. `mpf`, lines 1024–1046). On a metric lattice the
relation is `dist i j ≤ l`; on a graph it may mean that a walk of length at most `l` joins
the sites. The index type may depend on the site.

Product forms with the same relation are closed under products and powers, and an operator
supported on a region near a centre has a product form with a matrix-unit index on its
support and none elsewhere (lines 1053–1075).

## Main definitions and results

* `ManyBody.ProductForm near ρ`, `ManyBody.HasProductForm near ρ`.
* `ManyBody.ProductForm.mul`, `ManyBody.ProductForm.pow`, `ManyBody.hasProductForm_list_prod`,
  with the index counts `card_index_mul`, `card_index_pow`.
* `ManyBody.ProductForm.ofSupported`, `ManyBody.ProductForm.card_index_ofSupported`,
  `ManyBody.hasProductForm_of_mem_supportedOperators_radius`.
* `ManyBody.ProductForm.restrict`: removing index values whose coefficient vanishes.

Moved from TNLean (`e113e005`): `TNLean/Lattice/ProductForm.lean`,
`ProductFormIndexRestriction.lean` and the supported factor of `TrotterIndexCount.lean`.
Changes: the configurations are `Config X` for any finite basis types, and the product operator
is `ManyBody.prodOp` (TNLean's `piKronecker`). The supported-operator form uses the indices of
`ofSupported` on the support only, so no common dimension and no relation `near i i` is
needed; TNLean's `apply_eq_apply_of_mem_supportedOperators` is
`ManyBody.apply_eq_of_mem_supportedOperators`.
-/

open Matrix

universe u

namespace ManyBody

variable {V : Type*} [Fintype V] [DecidableEq V] {X : V → Type u} [∀ v, Fintype (X v)]
  [∀ v, DecidableEq (X v)] {near : V → V → Prop}

/-- A coefficient function at site `i` that depends only on the indices at the sites `j`
with `near i j`. On a metric lattice of range `l`, this means `dist i j ≤ l`.
Hastings, arXiv:cond-mat/0508554v3, lines 1037–1039. -/
def IsLocalCoefficient (near : V → V → Prop) (i : V) {A : V → Type*} (f : (∀ j, A j) → ℂ) :
    Prop :=
  ∀ α β : (∀ j, A j), (∀ j, near i j → α j = β j) → f α = f β

variable (X) in
/-- **Matrix product form.** The data of eq. `mpf`: an index type at each site, operators
`siteOp j a` on the site `j`, and coefficient functions `coeff i` depending only on the
indices near `i`, with `ρ = ∑_α (∏ᵢ coeff i α) • ⊗ⱼ siteOp j (α j)`.
Hastings, arXiv:cond-mat/0508554v3, eq. `mpf`, lines 1024–1039. -/
structure ProductForm (near : V → V → Prop) (ρ : Matrix (Config X) (Config X) ℂ) where
  /-- The values of the index carried by each site; the type may vary with the site. -/
  Index : V → Type u
  /-- The index at each site takes finitely many values. -/
  [fintype : ∀ j, Fintype (Index j)]
  /-- The operator `ρⱼ(a)` acting only on site `j`. -/
  siteOp : (j : V) → Index j → Matrix (X j) (X j) ℂ
  /-- The coefficient function `Fᵢ` attached to site `i`. -/
  coeff : V → (∀ j, Index j) → ℂ
  /-- Each `Fᵢ` depends only on the indices at the sites `j` with `near i j`. -/
  coeff_local : ∀ i, IsLocalCoefficient near i (coeff i)
  /-- The expansion of eq. `mpf`. -/
  eq_sum : ρ = ∑ α : (∀ j, Index j), (∏ i, coeff i α) • prodOp fun j ↦ siteOp j (α j)

attribute [instance] ProductForm.fintype

variable (X) in
/-- An operator has a matrix product form with coefficient neighbourhoods `near`.
Hastings, arXiv:cond-mat/0508554v3, eq. `mpf`, lines 1024–1039. -/
def HasProductForm (near : V → V → Prop) (ρ : Matrix (Config X) (Config X) ℂ) : Prop :=
  Nonempty (ProductForm X near ρ)

omit [Fintype V] [DecidableEq V] in
/-- A coefficient depending only on `near i` also depends only on any larger set. -/
theorem IsLocalCoefficient.mono {near' : V → V → Prop}
    (hnear : ∀ i j, near i j → near' i j) {i : V} {A : V → Type*}
    {f : (∀ j, A j) → ℂ} (hf : IsLocalCoefficient near i f) : IsLocalCoefficient near' i f :=
  fun α β h ↦ hf α β fun j hj ↦ h j (hnear i j hj)

omit [∀ v, Fintype (X v)] [∀ v, DecidableEq (X v)] in
/-- Enlarging the coefficient neighbourhoods preserves a product form. -/
theorem HasProductForm.mono {near' : V → V → Prop} (hnear : ∀ i j, near i j → near' i j)
    {ρ : Matrix (Config X) (Config X) ℂ} (hρ : HasProductForm X near ρ) :
    HasProductForm X near' ρ := by
  obtain ⟨P⟩ := hρ
  exact ⟨{ P with coeff_local := fun i ↦ (P.coeff_local i).mono hnear }⟩

variable (X) in
/-- The product form of the identity, with one index value at every site.
Hastings, arXiv:cond-mat/0508554v3, eq. `mpf`, lines 1024–1039. -/
noncomputable def ProductForm.one (near : V → V → Prop) : ProductForm X near 1 where
  Index := fun _ ↦ PUnit
  siteOp := fun _ _ ↦ 1
  coeff := fun _ _ ↦ 1
  coeff_local := fun _ _ _ _ ↦ rfl
  eq_sum := by simp

omit [∀ v, Fintype (X v)] in
variable (X) in
/-- The identity has a product form for every locality relation. -/
theorem hasProductForm_one (near : V → V → Prop) : HasProductForm X near 1 :=
  ⟨ProductForm.one X near⟩

omit [∀ v, Fintype (X v)] [∀ v, DecidableEq (X v)] in
/-- Every operator has a product form when there are no configurations. -/
theorem hasProductForm_of_isEmpty [IsEmpty (Config X)] (near : V → V → Prop)
    (ρ : Matrix (Config X) (Config X) ℂ) : HasProductForm X near ρ :=
  ⟨{ Index := fun _ ↦ PUnit
     siteOp := fun _ _ ↦ 0
     coeff := fun _ _ ↦ 0
     coeff_local := fun _ _ _ _ ↦ rfl
     eq_sum := Subsingleton.elim _ _ }⟩

/-- **Products.** Product forms with the same coefficient neighbourhoods are closed under
multiplication: pair the two indices at each site and multiply the coefficient functions.
Hastings, arXiv:cond-mat/0508554v3, lines 1068–1077. -/
noncomputable def ProductForm.mul {ρ σ : Matrix (Config X) (Config X) ℂ}
    (P : ProductForm X near ρ) (Q : ProductForm X near σ) : ProductForm X near (ρ * σ) := by
  refine {
    Index := fun j ↦ P.Index j × Q.Index j
    siteOp := fun j a ↦ P.siteOp j a.1 * Q.siteOp j a.2
    coeff := fun i γ ↦ P.coeff i (fun j ↦ (γ j).1) * Q.coeff i (fun j ↦ (γ j).2)
    coeff_local := fun i α β h ↦ ?_
    eq_sum := ?_ }
  · dsimp only
    rw [P.coeff_local i _ _ fun j hj ↦ congrArg Prod.fst (h j hj),
      Q.coeff_local i _ _ fun j hj ↦ congrArg Prod.snd (h j hj)]
  · refine (congrArg₂ (· * ·) P.eq_sum Q.eq_sum).trans ?_
    rw [Finset.sum_mul_sum, ← Fintype.sum_prod_type']
    refine Fintype.sum_equiv (Equiv.arrowProdEquivProdArrow _ _ _).symm _ _ fun x ↦ ?_
    simp [prodOp_mul, Finset.prod_mul_distrib, Equiv.arrowProdEquivProdArrow, smul_smul,
      mul_comm]

omit [∀ v, DecidableEq (X v)] in
/-- Products preserve coefficient neighbourhoods. -/
theorem HasProductForm.mul {ρ σ : Matrix (Config X) (Config X) ℂ}
    (hρ : HasProductForm X near ρ) (hσ : HasProductForm X near σ) :
    HasProductForm X near (ρ * σ) := by
  classical
  obtain ⟨P⟩ := hρ
  obtain ⟨Q⟩ := hσ
  exact ⟨P.mul Q⟩

/-- Repeated multiplication groups the indices at each site in the product form of a power.
Hastings, arXiv:cond-mat/0508554v3, eq. `mplt`, lines 1303–1317. -/
noncomputable def ProductForm.pow {ρ : Matrix (Config X) (Config X) ℂ}
    (P : ProductForm X near ρ) : (n : ℕ) → ProductForm X near (ρ ^ n)
  | 0 => ProductForm.one X near
  | n + 1 => (P.pow n).mul P

omit [∀ v, Fintype (X v)] in
/-- The index of the identity product form has one value at each site. -/
@[simp] theorem ProductForm.card_index_one (near : V → V → Prop) (i : V) :
    Fintype.card ((ProductForm.one X near).Index i) = 1 := by
  change Fintype.card PUnit = 1
  exact Fintype.card_unique

/-- Multiplying product forms multiplies the numbers of index values at each site. -/
@[simp] theorem ProductForm.card_index_mul {ρ σ : Matrix (Config X) (Config X) ℂ}
    (P : ProductForm X near ρ) (Q : ProductForm X near σ) (i : V) :
    Fintype.card ((P.mul Q).Index i) = Fintype.card (P.Index i) * Fintype.card (Q.Index i) :=
  Fintype.card_prod _ _

/-- The index count of a power is the corresponding power of the count.
Hastings, arXiv:cond-mat/0508554v3, lines 1072–1075 and 1318–1320. -/
@[simp] theorem ProductForm.card_index_pow {ρ : Matrix (Config X) (Config X) ℂ}
    (P : ProductForm X near ρ) (n : ℕ) (i : V) :
    Fintype.card ((P.pow n).Index i) = Fintype.card (P.Index i) ^ n := by
  induction n with
  | zero => exact ProductForm.card_index_one near i
  | succ n ih =>
    change Fintype.card ((P.pow n).Index i × P.Index i) = _
    rw [Fintype.card_prod, ih, pow_succ]

/-- Finite ordered products preserve the coefficient neighbourhoods of a product form. -/
theorem hasProductForm_list_prod (L : List (Matrix (Config X) (Config X) ℂ))
    (hL : ∀ ρ ∈ L, HasProductForm X near ρ) : HasProductForm X near L.prod := by
  induction L with
  | nil => exact hasProductForm_one X near
  | cons ρ L ih =>
    rw [List.prod_cons]
    exact (hL ρ (by simp)).mul (ih fun σ hσ ↦ hL σ (by simp [hσ]))

/-- Powers preserve the coefficient neighbourhoods of a product form. -/
theorem HasProductForm.pow {ρ : Matrix (Config X) (Config X) ℂ}
    (hρ : HasProductForm X near ρ) (n : ℕ) : HasProductForm X near (ρ ^ n) := by
  obtain ⟨P⟩ := hρ
  exact ⟨P.pow n⟩

/-- The product form of an operator supported on `D`, with one matrix-unit label at each
site of `D` and no label off `D`. The configuration `z` supplies the labels off `D`, where
they do not affect the operator; the coefficient is attached to the centre `i₀`.
Hastings, arXiv:cond-mat/0508554v3, lines 1053–1075. -/
noncomputable def ProductForm.ofSupported {D : Finset V} (z : Config X) (i₀ : V)
    (hD : ∀ j ∈ D, near i₀ j) {ρ : Matrix (Config X) (Config X) ℂ}
    (hρ : ρ ∈ supportedOperators X D) : ProductForm X near ρ := by
  classical
  let labels (α : ∀ j, j ∈ D → X j × X j) (j : V) : X j × X j :=
    if hj : j ∈ D then α j hj else (z j, z j)
  refine {
    Index := fun j ↦ j ∈ D → X j × X j
    siteOp := fun j a ↦ if hj : j ∈ D then single (a hj).1 (a hj).2 1 else 1
    coeff := fun i α ↦ if i = i₀ then ρ (fun j ↦ (labels α j).1) (fun j ↦ (labels α j).2)
      else 1
    coeff_local := ?_
    eq_sum := ?_ }
  · intro i α β h
    by_cases hi : i = i₀
    · subst i
      have hlabels : labels α = labels β := by
        funext j
        dsimp only [labels]
        split_ifs with hj
        · exact congrFun (h j (hD j hj)) hj
        · rfl
      simp only [hlabels]
    · simp only [ite_eq_right hi]
  · ext u v
    simp only [Matrix.sum_apply, Matrix.smul_apply, prodOp_apply, smul_eq_mul,
      Fintype.prod_ite_eq']
    rw [Finset.sum_eq_single (fun j (_ : j ∈ D) ↦ (u j, v j))]
    · by_cases hoff : ∃ j ∉ D, u j ≠ v j
      · rw [hρ.1 u v hoff]
        obtain ⟨j, hj, huv⟩ := hoff
        refine (mul_eq_zero_of_right _ (Finset.prod_eq_zero (Finset.mem_univ j) ?_)).symm
        simp [hj, huv]
      · push Not at hoff
        rw [Finset.prod_eq_one fun j _ ↦ ?_, mul_one]
        · refine hρ.2 u v _ _ (fun j hj ↦ ?_) (fun j hj ↦ ?_) hoff fun j hj ↦ ?_
          · simp [labels, hj]
          · simp [labels, hj]
          · simp [labels, hj]
        · by_cases hj : j ∈ D
          · simp [hj]
          · simp [hj, Matrix.one_apply, hoff j hj]
    · intro α _ hα
      obtain ⟨j, hj⟩ := Function.ne_iff.mp hα
      by_cases hmem : j ∈ D
      · have hbad : α j hmem ≠ (u j, v j) := fun h ↦ hj (funext fun _ ↦ h)
        refine mul_eq_zero_of_right _ (Finset.prod_eq_zero (Finset.mem_univ j) ?_)
        rw [dite_eq_left hmem, single_apply]
        split_ifs with h
        · exact absurd (Prod.ext h.1 h.2) hbad
        · rfl
      · exact (hj (funext fun hk ↦ (hmem hk).elim)).elim
    · simp

/-- A supported factor has `|X j|²` index values at a site `j` of its support and one value
elsewhere. Hastings, arXiv:cond-mat/0508554v3, lines 1053–1075. -/
theorem ProductForm.card_index_ofSupported {D : Finset V} (z : Config X) (i₀ : V)
    (hD : ∀ j ∈ D, near i₀ j) {ρ : Matrix (Config X) (Config X) ℂ}
    (hρ : ρ ∈ supportedOperators X D) (j : V) :
    Fintype.card ((ProductForm.ofSupported z i₀ hD hρ).Index j) =
      if j ∈ D then Fintype.card (X j) * Fintype.card (X j) else 1 := by
  change Fintype.card (j ∈ D → X j × X j) = _
  by_cases hj : j ∈ D
  · rw [ite_eq_left hj]
    let e : (j ∈ D → X j × X j) ≃ X j × X j :=
      ⟨fun f ↦ f hj, fun a _ ↦ a, fun _ ↦ rfl, fun _ ↦ rfl⟩
    exact (Fintype.card_congr e).trans (by simp)
  · rw [ite_eq_right hj]
    let e : (j ∈ D → X j × X j) ≃ Unit :=
      ⟨fun _ ↦ (), fun _ h ↦ (hj h).elim, fun f ↦ funext fun h ↦ (hj h).elim, fun _ ↦ rfl⟩
    exact (Fintype.card_congr e).trans (by simp)

/-- A product of supported factors has exactly one matrix-unit index component for each
factor touching a site, so `|X j|^{2c}` index values at `j` when `c` factors touch `j`. When
there are no configurations, any index sets of these cardinalities serve.
Hastings, arXiv:cond-mat/0508554v3, lines 1068–1075. -/
theorem exists_productForm_list_prod_card_index {κ : Type*}
    (H : κ → Matrix (Config X) (Config X) ℂ) (D : κ → Finset V) (c : κ → V)
    (hD : ∀ k j, j ∈ D k → near (c k) j) (hH : ∀ k, H k ∈ supportedOperators X (D k))
    (seq : List κ) :
    ∃ P : ProductForm X near (seq.map H).prod, ∀ i,
      Fintype.card (P.Index i) =
        Fintype.card (X i) ^ (2 * seq.countP (fun k ↦ decide (i ∈ D k))) := by
  by_cases hconfig : Nonempty (Config X)
  · obtain ⟨z⟩ := hconfig
    induction seq with
    | nil => exact ⟨ProductForm.one X near, fun i ↦ by simp⟩
    | cons k seq ih =>
      obtain ⟨P, hP⟩ := ih
      refine ⟨(ProductForm.ofSupported z (c k) (hD k) (hH k)).mul P, fun i ↦ ?_⟩
      change Fintype.card ((ProductForm.ofSupported z (c k) (hD k) (hH k)).Index i ×
        P.Index i) = _
      rw [Fintype.card_prod, ProductForm.card_index_ofSupported, hP, List.countP_cons]
      by_cases hi : i ∈ D k <;> simp [hi, mul_add, pow_add, sq, mul_comm]
  · have : IsEmpty (Config X) := not_nonempty_iff.mp hconfig
    exact ⟨{ Index := fun i ↦
               ULift (Fin (Fintype.card (X i) ^ (2 * seq.countP (fun k ↦ decide (i ∈ D k)))))
             siteOp := fun _ _ ↦ 0
             coeff := fun _ _ ↦ 0
             coeff_local := fun _ _ _ _ ↦ rfl
             eq_sum := Subsingleton.elim _ _ }, fun i ↦ by simp⟩

/-- An operator supported on a region near a specified centre has a product form with those
coefficient neighbourhoods. The centre need not belong to the region, which may be empty.
Hastings, arXiv:cond-mat/0508554v3, lines 1053–1061. -/
theorem hasProductForm_of_mem_supportedOperators_radius {D : Finset V} (i₀ : V)
    (hD : ∀ j ∈ D, near i₀ j) {ρ : Matrix (Config X) (Config X) ℂ}
    (hρ : ρ ∈ supportedOperators X D) : HasProductForm X near ρ := by
  by_cases hconfig : Nonempty (Config X)
  · obtain ⟨z⟩ := hconfig
    exact ⟨ProductForm.ofSupported z i₀ hD hρ⟩
  · have : IsEmpty (Config X) := not_nonempty_iff.mp hconfig
    exact hasProductForm_of_isEmpty near ρ

/-- An operator on a nonempty region whose sites are pairwise related by `near` has the
corresponding product form, with any site of the region as its centre.
Hastings, arXiv:cond-mat/0508554v3, lines 1053–1061. -/
theorem hasProductForm_of_mem_supportedOperators {D : Finset V}
    (hD : D.Nonempty ∧ ∀ i ∈ D, ∀ j ∈ D, near i j) {ρ : Matrix (Config X) (Config X) ℂ}
    (hρ : ρ ∈ supportedOperators X D) : HasProductForm X near ρ := by
  obtain ⟨i₀, hi₀⟩ := hD.1
  exact hasProductForm_of_mem_supportedOperators_radius i₀ (hD.2 i₀ hi₀) hρ

/-- Removing index values that force the coefficient at their site to vanish preserves the
represented operator and the coefficient neighbourhoods.
Hastings, arXiv:cond-mat/0508554v3, lines 1259–1279. -/
noncomputable def ProductForm.restrict {ρ : Matrix (Config X) (Config X) ℂ}
    (P : ProductForm X near ρ) (s : ∀ i, Finset (P.Index i))
    (hs : ∀ i α, α i ∉ s i → P.coeff i α = 0) : ProductForm X near ρ := by
  classical
  refine {
    Index := fun i ↦ {a : P.Index i // a ∈ s i}
    siteOp := fun i a ↦ P.siteOp i a.1
    coeff := fun i α ↦ P.coeff i (fun j ↦ (α j).1)
    coeff_local := fun i α β h ↦ P.coeff_local i _ _ fun j hj ↦ congrArg Subtype.val (h j hj)
    eq_sum := ?_ }
  refine P.eq_sum.trans ?_
  let f (α : ∀ i, P.Index i) := (∏ i, P.coeff i α) • prodOp fun j ↦ P.siteOp j (α j)
  change (∑ α, f α) = ∑ α : (∀ i, {a : P.Index i // a ∈ s i}), f (fun i ↦ (α i).1)
  calc
    (∑ α, f α) = ∑ α ∈ Finset.univ.filter (fun α ↦ ∀ i, α i ∈ s i), f α := by
      symm
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro α _ hα
      have hbad : ¬ ∀ i, α i ∈ s i := by
        simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using hα
      obtain ⟨i, hi⟩ := not_forall.mp hbad
      have hz : ∏ j, P.coeff j α = 0 := Finset.prod_eq_zero (Finset.mem_univ i) (hs i α hi)
      simp only [f, hz, zero_smul]
    _ = ∑ α : {α : (∀ i, P.Index i) // ∀ i, α i ∈ s i}, f α.1 :=
      Finset.sum_subtype _ (by simp) f
    _ = _ := Fintype.sum_equiv Equiv.subtypePiEquivPi _ _ fun _ ↦ rfl

omit [∀ v, Fintype (X v)] [∀ v, DecidableEq (X v)] in
/-- The index count after restriction is the cardinality of the allowed set at that site. -/
theorem ProductForm.card_index_restrict {ρ : Matrix (Config X) (Config X) ℂ}
    (P : ProductForm X near ρ) (s : ∀ i, Finset (P.Index i))
    (hs : ∀ i α, α i ∉ s i → P.coeff i α = 0) (i : V) :
    Fintype.card ((P.restrict s hs).Index i) = (s i).card := by
  classical
  exact Fintype.card_coe (s i)

end ManyBody
