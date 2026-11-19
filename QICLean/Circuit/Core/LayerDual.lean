/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Circuit.Core.Layer
import QICLean.ManyBody.Sites.Partition

/-!
# The Heisenberg picture of a layer

The cells and the remaining sites of a layer are its *blocks*; they partition the sites, and a
Kraus operator of the layer is the product over the blocks of local entries. Along a union `D`
of blocks the Kraus operators therefore factor as `K_near ⊗ K_far`, and the Heisenberg picture
`A ↦ ∑ᵢ Kᵢᴴ A Kᵢ` of an operator `A₁ ⊗ 1` supported on `D` is
`(∑ K_nearᴴ A₁ K_near) ⊗ (∑ K_farᴴ K_far)`. When the families on the blocks outside `D` are
trace-preserving, the second factor is the identity.

Two consequences are proved from this one computation:

* a layer whose gates and onsite families are trace-preserving is trace-preserving (take `D`
  empty);
* the Heisenberg picture of such a layer maps an operator supported on `R` to an operator
  supported on the backward light cone of `R`: `R` together with every cell of the layer that
  meets it.

## Main definitions

* `QuantumCircuit.Layer.dual` — the Heisenberg picture `A ↦ ∑ᵢ Kᵢᴴ A Kᵢ`.

## Main results

* `QuantumCircuit.Layer.sum_prod_region` — a sum over the configurations of a product over the
  blocks factors.
* `QuantumCircuit.Layer.dual_kronecker`, `QuantumCircuit.Layer.dual_place` — the factorization
  along a union of blocks.
* `QuantumCircuit.Layer.dual_one`, `QuantumCircuit.Layer.isTP_krausFamily` — local trace
  preservation gives trace preservation.
* `QuantumCircuit.Layer.dual_mem_supportedOperators_lightCone` — the backward light cone of one
  layer.
* `QuantumCircuit.Layer.dual_mul_of_disjoint_lightCone` — the Heisenberg picture is
  multiplicative on operators with disjoint light cones.
* `QuantumCircuit.Layer.nonempty_index_of_forall_isTP`,
  `QuantumCircuit.Layer.nonempty_output_of_forall_isTP` — such a layer on nonempty bases has a
  Kraus index and nonempty output bases.
-/

open Matrix ManyBody
open scoped Kronecker

namespace QuantumCircuit

namespace Layer

variable {S : Type} [Fintype S] [DecidableEq S] {Γ : Geometry S}
  {G : Finset S → (S → Type) → (S → Type) → Type 1} [GateFamily G] {X Y : S → Type}

/-! ### Blocks -/

section Blocks

variable (L : Layer Γ G X Y)

/-- The blocks of a layer: its cells and the sites met by no cell. -/
abbrev Block : Type := L.cells ⊕ L.Free

/-- The sites of a block. -/
def region : L.Block → Finset S
  | .inl b => Γ.cell b
  | .inr s => {s.1}

/-- The outcomes of the family on a block. -/
def BlockIndex : L.Block → Type
  | .inl b => GateFamily.Outcome (L.gate b)
  | .inr s => (L.onsite s).Index

instance instFintypeBlockIndex : (β : L.Block) → Fintype (L.BlockIndex β)
  | .inl b => inferInstanceAs (Fintype (GateFamily.Outcome (L.gate b)))
  | .inr s => inferInstanceAs (Fintype (L.onsite s).Index)

/-- A Kraus index of the layer is an outcome on every block. -/
def indexEquiv : L.Index ≃ ((β : L.Block) → L.BlockIndex β) :=
  (Equiv.sumPiEquivProdPi L.BlockIndex).symm

omit [Fintype S] [GateFamily G] in
theorem region_disjoint {β β' : L.Block} (h : β ≠ β') :
    Disjoint (L.region β) (L.region β') := by
  have hfree : ∀ (b : L.cells) (s : L.Free), Disjoint (Γ.cell b) {s.1} := fun b s ↦
    Finset.disjoint_singleton_right.mpr fun hs ↦ s.2 (Finset.mem_biUnion.mpr ⟨b, b.2, hs⟩)
  match β, β' with
  | .inl b, .inl b' =>
    exact L.pairwiseDisjoint b.2 b'.2 fun e ↦ h (congrArg Sum.inl (Subtype.ext e))
  | .inl b, .inr s => exact hfree b s
  | .inr s, .inl b => exact (hfree b s).symm
  | .inr s, .inr s' =>
    exact Finset.disjoint_singleton.mpr fun e ↦ h (congrArg Sum.inr (Subtype.ext e))

open Classical in
/-- The block containing a site. -/
noncomputable def blockOf (v : S) : L.Block :=
  if h : ∃ b ∈ L.cells, v ∈ Γ.cell b then .inl ⟨h.choose, h.choose_spec.1⟩
  else .inr ⟨v, fun hv ↦ h (Finset.mem_biUnion.mp hv)⟩

omit [Fintype S] [GateFamily G] in
theorem mem_region_blockOf (v : S) : v ∈ L.region (L.blockOf v) := by
  unfold blockOf
  split_ifs with h
  · exact h.choose_spec.2
  · exact Finset.mem_singleton_self v

omit [Fintype S] [GateFamily G] in
theorem blockOf_eq_of_mem {v : S} {β : L.Block} (hv : v ∈ L.region β) : L.blockOf v = β := by
  by_contra h
  exact Finset.disjoint_left.mp (L.region_disjoint h) (L.mem_region_blockOf v) hv

omit [Fintype S] [GateFamily G] in
/-- The blocks partition the sites. -/
theorem isComplPartition_region :
    IsComplPartition (∅ : Finset S) L.region (fun v ↦ L.blockOf v.1) where
  disjoint _ := Finset.disjoint_empty_right _
  mem v := L.mem_region_blockOf v.1
  eq_of_mem _ _ hv := L.blockOf_eq_of_mem hv

omit [GateFamily G] in
/-- A sum over the configurations of a product over the blocks of functions of the restrictions
is the product over the blocks of the sums over their configurations. -/
theorem sum_prod_region {R : Type*} [CommSemiring R] {F : S → Type} [∀ s, Fintype (F s)]
    (g : (β : L.Block) → RegionConfig F (L.region β) → R) :
    ∑ f : Config F, ∏ β, g β (fun v ↦ f v) = ∏ β, ∑ z, g β z := by
  rw [← sum_prod_complPartition L.isComplPartition_region g]
  exact Fintype.sum_equiv (complEmptyEquiv F).symm _ _ fun _ ↦ rfl

variable [∀ s, Fintype (X s)] [∀ s, DecidableEq (X s)] [∀ s, Fintype (Y s)]
  [∀ s, DecidableEq (Y s)]

/-- The local entries of a layer on a block. -/
def blockKraus (ev : Interpretation G) :
    (β : L.Block) → L.BlockIndex β →
      Matrix (RegionConfig Y (L.region β)) (RegionConfig X (L.region β)) ℂ
  | .inl b, j => ev (L.gate b) j
  | .inr s, j => fun y x ↦
      (L.onsite s).op j (y ⟨s, Finset.mem_singleton_self _⟩) (x ⟨s, Finset.mem_singleton_self _⟩)

/-- A Kraus operator of a layer is the product of its local entries over the blocks. -/
theorem kraus_apply_eq_prod (ev : Interpretation G) (i : L.Index) (y : Config Y)
    (x : Config X) :
    L.kraus ev i y x =
      ∏ β, L.blockKraus ev β (L.indexEquiv i β) (fun v ↦ y v) (fun v ↦ x v) := by
  rw [kraus, Fintype.prod_sum_type]
  rfl

/-- The effect of the family on a block. -/
noncomputable def blockEffect (ev : Interpretation G) (β : L.Block) :
    Matrix (RegionConfig X (L.region β)) (RegionConfig X (L.region β)) ℂ :=
  ∑ j, (L.blockKraus ev β j)ᴴ * L.blockKraus ev β j

omit [Fintype S] in
/-- Local trace preservation: the effect on every block is the identity. -/
theorem blockEffect_eq_one (ev : Interpretation G) (h : L.Forall ev KrausFamily.IsTP)
    (β : L.Block) : L.blockEffect ev β = 1 := by
  match β with
  | .inl b => exact h.1 b
  | .inr s =>
    have hs : (L.onsite s).effect = 1 := h.2 s
    let : Unique {v // v ∈ L.region (.inr s)} :=
      ⟨⟨⟨s, Finset.mem_singleton_self _⟩⟩, fun v ↦ Subtype.ext (Finset.mem_singleton.mp v.2)⟩
    ext a c
    have hac : a = c ↔ a default = c default :=
      ⟨fun h ↦ h ▸ rfl, fun h ↦ funext fun v ↦ by rwa [Subsingleton.elim v default]⟩
    have key := congrFun (congrFun hs (a default)) (c default)
    simp only [KrausFamily.effect, Matrix.sum_apply, mul_apply, conjTranspose_apply] at key
    simp only [blockEffect, Matrix.sum_apply, mul_apply, conjTranspose_apply, one_apply,
      hac]
    rw [one_apply] at key
    rw [← key]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    exact (Equiv.piUnique fun v : {v // v ∈ L.region (.inr s)} ↦ Y v).sum_comp
      (fun z ↦ star ((L.onsite s).op j z (a default)) * (L.onsite s).op j z (c default))

end Blocks

/-! ### The factorization along a union of blocks -/

section Factorization

variable [∀ s, Fintype (X s)] [∀ s, DecidableEq (X s)] [∀ s, Fintype (Y s)]
  [∀ s, DecidableEq (Y s)] (L : Layer Γ G X Y) (ev : Interpretation G)
  (p : L.Block → Prop) [DecidablePred p]

/-- The union of the blocks satisfying `p`. -/
def unionRegion : Finset S := (Finset.univ.filter p).biUnion L.region

omit [GateFamily G] [∀ s, Fintype (X s)] [∀ s, DecidableEq (X s)] [∀ s, Fintype (Y s)]
  [∀ s, DecidableEq (Y s)] in
theorem region_subset_unionRegion {β : L.Block} (hβ : p β) :
    L.region β ⊆ L.unionRegion p :=
  Finset.subset_biUnion_of_mem L.region (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hβ⟩)

omit [GateFamily G] [∀ s, Fintype (X s)] [∀ s, DecidableEq (X s)] [∀ s, Fintype (Y s)]
  [∀ s, DecidableEq (Y s)] in
theorem disjoint_unionRegion (β : {β // ¬p β}) :
    Disjoint (L.region β) (L.unionRegion p) := by
  refine (Finset.disjoint_biUnion_right _ _ _).mpr fun β' hβ' ↦ L.region_disjoint ?_
  rintro rfl
  exact β.2 (Finset.mem_filter.mp hβ').2

omit [GateFamily G] [∀ s, Fintype (X s)] [∀ s, DecidableEq (X s)] [∀ s, Fintype (Y s)]
  [∀ s, DecidableEq (Y s)] in
/-- The blocks outside `p` partition the sites outside the union of the blocks in `p`. -/
theorem isComplPartition :
    IsComplPartition (L.unionRegion p) (fun β : {β // ¬p β} ↦ L.region β)
      (fun v ↦ ⟨L.blockOf v.1, fun h ↦ v.2
        (L.region_subset_unionRegion p h (L.mem_region_blockOf v.1))⟩) where
  disjoint := L.disjoint_unionRegion p
  mem v := L.mem_region_blockOf v.1
  eq_of_mem _ _ hv := Subtype.ext (L.blockOf_eq_of_mem hv)

/-- The Kraus operators of the blocks in `p`, on the configurations of their union. -/
def nearKraus (j : (β : {β // p β}) → L.BlockIndex β) :
    Matrix (RegionConfig Y (L.unionRegion p)) (RegionConfig X (L.unionRegion p)) ℂ :=
  fun u' u ↦ ∏ β : {β // p β}, L.blockKraus ev β (j β)
    (fun v ↦ u' ⟨v, L.region_subset_unionRegion p β.2 v.2⟩)
    (fun v ↦ u ⟨v, L.region_subset_unionRegion p β.2 v.2⟩)

/-- The Kraus operators of the blocks outside `p`, on the configurations outside their union. -/
def farKraus (j : (β : {β // ¬p β}) → L.BlockIndex β) :
    Matrix (ComplConfig Y (L.unionRegion p)) (ComplConfig X (L.unionRegion p)) ℂ :=
  fun w' w ↦ ∏ β : {β // ¬p β}, L.blockKraus ev β (j β)
    (complRestrict (L.disjoint_unionRegion p) w' β) (complRestrict (L.disjoint_unionRegion p) w β)

theorem farKraus_apply (j : (β : {β // ¬p β}) → L.BlockIndex β) (w' w) :
    L.farKraus ev p j w' w = ∏ β : {β // ¬p β}, L.blockKraus ev β (j β)
      (complRestrict (L.disjoint_unionRegion p) w' β)
      (complRestrict (L.disjoint_unionRegion p) w β) :=
  rfl

/-- An index of the layer as a pair of indices on the blocks in `p` and outside `p`. -/
def nearFarEquiv :
    L.Index ≃ ((β : {β // p β}) → L.BlockIndex β) × ((β : {β // ¬p β}) → L.BlockIndex β) :=
  L.indexEquiv.trans (Equiv.piEquivPiSubtypeProd p L.BlockIndex)

/-- Along the union of the blocks in `p`, a Kraus operator is the Kronecker product of its parts
on the blocks in `p` and outside `p`. -/
theorem kraus_eq_submatrix (i : L.Index) :
    L.kraus ev i =
      (L.nearKraus ev p (L.nearFarEquiv p i).1 ⊗ₖ
        L.farKraus ev p (L.nearFarEquiv p i).2).submatrix
        (cutEquiv Y (L.unionRegion p)) (cutEquiv X (L.unionRegion p)) := by
  ext y x
  rw [kraus_apply_eq_prod, submatrix_apply, kroneckerMap_apply,
    ← Fintype.prod_subtype_mul_prod_subtype p]
  rfl

/-- The effect of the blocks outside `p` is the identity when their families are
trace-preserving. -/
theorem sum_farKraus (hF : ∀ β, ¬p β → L.blockEffect ev β = 1) :
    ∑ j, (L.farKraus ev p j)ᴴ * L.farKraus ev p j = 1 := by
  have hP := L.isComplPartition p
  ext w' w
  have hterm : ∀ j, ((L.farKraus ev p j)ᴴ * L.farKraus ev p j) w' w =
      ∑ z, ∏ β : {β // ¬p β},
        star (L.blockKraus ev β (j β) (complRestrict hP.disjoint z β)
          (complRestrict hP.disjoint w' β)) *
        L.blockKraus ev β (j β) (complRestrict hP.disjoint z β)
          (complRestrict hP.disjoint w β) := by
    intro j
    rw [mul_apply]
    refine Finset.sum_congr rfl fun z _ ↦ ?_
    rw [conjTranspose_apply, farKraus_apply, farKraus_apply, star_prod,
      ← Finset.prod_mul_distrib]
  rw [Matrix.sum_apply, Finset.sum_congr rfl fun j _ ↦ hterm j]
  rw [Finset.sum_congr rfl fun j _ ↦ sum_prod_complPartition (X := Y) hP fun β zβ ↦
    star (L.blockKraus ev β (j β) zβ (complRestrict hP.disjoint w' β)) *
      L.blockKraus ev β (j β) zβ (complRestrict hP.disjoint w β)]
  rw [← Fintype.prod_sum (fun (β : {β // ¬p β}) j ↦ ∑ zβ, star (L.blockKraus ev β j zβ
    (complRestrict hP.disjoint w' β)) * L.blockKraus ev β j zβ (complRestrict hP.disjoint w β))]
  have hblock : ∀ β : {β // ¬p β}, ∑ j, ∑ z, star (L.blockKraus ev β j z
      (complRestrict hP.disjoint w' β)) * L.blockKraus ev β j z (complRestrict hP.disjoint w β) =
      if complRestrict hP.disjoint w' β = complRestrict hP.disjoint w β then 1 else 0 := by
    intro β
    have := congrFun (congrFun (hF β.1 β.2) (complRestrict hP.disjoint w' β))
      (complRestrict hP.disjoint w β)
    rw [blockEffect, Matrix.sum_apply, one_apply] at this
    refine (Finset.sum_congr rfl fun j _ ↦ ?_).trans this
    rw [mul_apply]
    rfl
  simp_rw [hblock]
  rw [prod_ite_complPartition hP, one_apply]

/-- The Heisenberg picture `A ↦ ∑ᵢ Kᵢᴴ A Kᵢ` of a layer. -/
noncomputable def dual (A : Matrix (Config Y) (Config Y) ℂ) : Matrix (Config X) (Config X) ℂ :=
  ∑ i, (L.kraus ev i)ᴴ * A * L.kraus ev i

omit [DecidablePred p] in
theorem dual_apply' (A : Matrix (Config Y) (Config Y) ℂ) :
    L.dual ev A = ∑ i, (L.kraus ev i)ᴴ * A * L.kraus ev i :=
  rfl

/-- The Heisenberg picture of a product `M ⊗ N` along the union of the blocks in `p`: that of
`M` through the Kraus operators of the blocks in `p`, tensored with that of `N` through the
Kraus operators of the other blocks. -/
theorem dual_kronecker
    (M : Matrix (RegionConfig Y (L.unionRegion p)) (RegionConfig Y (L.unionRegion p)) ℂ)
    (N : Matrix (ComplConfig Y (L.unionRegion p)) (ComplConfig Y (L.unionRegion p)) ℂ) :
    L.dual ev ((M ⊗ₖ N).submatrix (cutEquiv Y _) (cutEquiv Y _)) =
      ((∑ j, (L.nearKraus ev p j)ᴴ * M * L.nearKraus ev p j) ⊗ₖ
        ∑ k, (L.farKraus ev p k)ᴴ * N * L.farKraus ev p k).submatrix
        (cutEquiv X _) (cutEquiv X _) := by
  have hterm : ∀ i, (L.kraus ev i)ᴴ * (M ⊗ₖ N).submatrix (cutEquiv Y _) (cutEquiv Y _) *
      L.kraus ev i =
      (((L.nearKraus ev p (L.nearFarEquiv p i).1)ᴴ * M * L.nearKraus ev p (L.nearFarEquiv p i).1)
        ⊗ₖ ((L.farKraus ev p (L.nearFarEquiv p i).2)ᴴ * N *
          L.farKraus ev p (L.nearFarEquiv p i).2)).submatrix
        (cutEquiv X (L.unionRegion p)) (cutEquiv X (L.unionRegion p)) := by
    intro i
    rw [kraus_eq_submatrix L ev p i, conjTranspose_submatrix, submatrix_mul_equiv,
      submatrix_mul_equiv, conjTranspose_kronecker, ← mul_kronecker_mul, ← mul_kronecker_mul]
  rw [dual_apply', Finset.sum_congr rfl fun i _ ↦ hterm i]
  ext a c
  simp only [Matrix.sum_apply, submatrix_apply, kroneckerMap_apply, Finset.sum_mul_sum]
  rw [← Fintype.sum_prod_type']
  exact Fintype.sum_equiv (L.nearFarEquiv p) _ _ fun _ ↦ rfl

/-- The Heisenberg picture of an operator `A₁ ⊗ 1` on the union of the blocks in `p`, when the
blocks outside `p` are trace-preserving: only the blocks in `p` act. -/
theorem dual_place (hF : ∀ β, ¬p β → L.blockEffect ev β = 1)
    (A₁ : Matrix (RegionConfig Y (L.unionRegion p)) (RegionConfig Y (L.unionRegion p)) ℂ) :
    L.dual ev (place (L.unionRegion p) A₁) =
      place (L.unionRegion p) (∑ j, (L.nearKraus ev p j)ᴴ * A₁ * L.nearKraus ev p j) := by
  have := L.dual_kronecker ev p A₁ 1
  simp_rw [Matrix.mul_one, L.sum_farKraus ev p hF] at this
  exact this

/-- The Heisenberg picture of a layer whose gates and onsite families are trace-preserving fixes
the identity. -/
theorem dual_one (h : L.Forall ev KrausFamily.IsTP) : L.dual ev 1 = 1 := by
  have hD : ∀ v, v ∉ L.unionRegion (fun _ ↦ False) := fun v hv ↦ by
    obtain ⟨β, hβ, _⟩ := Finset.mem_biUnion.mp hv
    exact (Finset.mem_filter.mp hβ).2
  have hdual := L.dual_place ev (fun _ ↦ False) (fun β _ ↦ L.blockEffect_eq_one ev h β)
    (1 : Matrix (RegionConfig Y (L.unionRegion fun _ ↦ False)) _ ℂ)
  have hnear : ∑ j, (L.nearKraus ev (fun _ ↦ False) j)ᴴ *
      (1 : Matrix (RegionConfig Y (L.unionRegion fun _ ↦ False)) _ ℂ) *
        L.nearKraus ev (fun _ ↦ False) j = 1 := by
    have hX : ∀ z z' : RegionConfig X (L.unionRegion fun _ ↦ False), z = z' := fun _ _ ↦
      funext fun v ↦ absurd v.2 (hD v)
    let : Unique ((β : {β : L.Block // False}) → L.BlockIndex β) :=
      ⟨⟨fun β ↦ β.2.elim⟩, fun _ ↦ funext fun β ↦ β.2.elim⟩
    let : Unique (RegionConfig Y (L.unionRegion fun _ ↦ False)) :=
      ⟨⟨fun v ↦ absurd v.2 (hD v)⟩, fun _ ↦ funext fun v ↦ absurd v.2 (hD v)⟩
    ext a c
    rw [Fintype.sum_unique, Matrix.mul_one, mul_apply, Fintype.sum_unique, one_apply,
      ite_eq_left (hX a c)]
    simp [nearKraus]
  rw [hnear, place_one, place_one] at hdual
  exact hdual

/-- The effect of the blocks in `p` is the identity when the layer is trace-preserving.

The configuration `y` outside the union of the blocks is a witness that the configurations
outside the union are nonempty: the proof reads the identity off the Heisenberg picture of the
identity, `1 ⊗ (effect of the blocks in p)`, which determines the effect only when its second
factor has an index. A direct proof would need, for configurations of the union, the partition
lemma `sum_prod_complPartition` that the blocks outside `p` use. -/
private theorem sum_nearKraus (h : L.Forall ev KrausFamily.IsTP)
    (y : ComplConfig X (L.unionRegion p)) :
    ∑ j, (L.nearKraus ev p j)ᴴ * L.nearKraus ev p j = 1 := by
  have hF := L.sum_farKraus ev p fun β _ ↦ L.blockEffect_eq_one ev h β
  have h1 := L.dual_kronecker ev p 1 1
  simp_rw [Matrix.mul_one, hF] at h1
  have h2 : place (L.unionRegion p) (∑ j, (L.nearKraus ev p j)ᴴ * L.nearKraus ev p j) =
      place (L.unionRegion p) 1 := by
    rw [place_one, ← L.dual_one ev h, ← place_one (D := L.unionRegion p)]
    exact h1.symm
  ext a b
  rw [← place_apply_cutEquiv_symm (∑ j, (L.nearKraus ev p j)ᴴ * L.nearKraus ev p j) a b y, h2,
    place_apply_cutEquiv_symm]

/-- A layer whose gates and onsite families are trace-preserving is trace-preserving. -/
theorem isTP_krausFamily (h : L.Forall ev KrausFamily.IsTP) :
    (L.krausFamily ev).IsTP := by
  have hdual := L.dual_one ev h
  rw [dual_apply'] at hdual
  simp only [Matrix.mul_one] at hdual
  change ∑ i : L.Index, (L.kraus ev i)ᴴ * L.kraus ev i = 1
  convert hdual using 2

omit [GateFamily G] [∀ s, Fintype (X s)] [∀ s, DecidableEq (X s)] [∀ s, Fintype (Y s)]
  [∀ s, DecidableEq (Y s)] [DecidablePred p] in
/-- The blocks meeting `R` lie in the light cone of `R`. -/
private theorem unionRegion_subset_lightCone (R : Finset S) :
    L.unionRegion (fun β ↦ ¬Disjoint (L.region β) R) ⊆ L.lightCone R := by
  intro v hv
  obtain ⟨β, hβ, hvβ⟩ := Finset.mem_biUnion.mp hv
  obtain ⟨w, hwβ, hwR⟩ := Finset.not_disjoint_iff.mp (Finset.mem_filter.mp hβ).2
  match β with
  | .inl b =>
    refine Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨b, ?_, hvβ⟩)
    exact Finset.mem_filter.mpr ⟨b.2, ⟨w, Finset.mem_inter.mpr ⟨hwβ, hwR⟩⟩⟩
  | .inr s =>
    have hv' : v = s.1 := Finset.mem_singleton.mp hvβ
    have hw' : w = s.1 := Finset.mem_singleton.mp hwβ
    exact Finset.mem_union_left _ (hv' ▸ hw' ▸ hwR)

/-- The backward light cone of one layer: when its gates and onsite families are
trace-preserving, its Heisenberg picture maps an operator supported on `R` to an operator
supported on `R` together with the cells of the layer meeting `R`. -/
theorem dual_mem_supportedOperators_lightCone (h : L.Forall ev KrausFamily.IsTP)
    {R : Finset S} {A : Matrix (Config Y) (Config Y) ℂ} (hA : A ∈ supportedOperators Y R) :
    L.dual ev A ∈ supportedOperators X (L.lightCone R) := by
  let p : L.Block → Prop := fun β ↦ ¬Disjoint (L.region β) R
  have hRD : R ⊆ L.unionRegion p := fun v hv ↦
    L.region_subset_unionRegion p (Finset.not_disjoint_iff.mpr ⟨v, L.mem_region_blockOf v, hv⟩)
      (L.mem_region_blockOf v)
  obtain ⟨A₁, rfl⟩ :=
    exists_eq_place_of_mem_supportedOperators (supportedOperators_mono hRD hA)
  rw [L.dual_place ev p (fun β _ ↦ L.blockEffect_eq_one ev h β)]
  exact supportedOperators_mono (L.unionRegion_subset_lightCone R)
    (place_mem_supportedOperators _)

/-- The Heisenberg picture of a layer whose gates and onsite families are trace-preserving is
multiplicative on operators whose light cones through the layer are disjoint. -/
theorem dual_mul_of_disjoint_lightCone (hL : L.Forall ev KrausFamily.IsTP) {R R' : Finset S}
    (hRR' : Disjoint (L.lightCone R) (L.lightCone R'))
    {A B : Matrix (Config Y) (Config Y) ℂ} (hA : A ∈ supportedOperators Y R)
    (hB : B ∈ supportedOperators Y R') :
    L.dual ev (A * B) = L.dual ev A * L.dual ev B := by
  cases isEmpty_or_nonempty (Config X) with
  | inl _ => exact Subsingleton.elim _ _
  | inr hX =>
    obtain ⟨σ₀⟩ := hX
    let p : L.Block → Prop := fun β ↦ ¬Disjoint (L.region β) R
    have hRD : R ⊆ L.unionRegion p := fun v hv ↦
      L.region_subset_unionRegion p (Finset.not_disjoint_iff.mpr
        ⟨v, L.mem_region_blockOf v, hv⟩) (L.mem_region_blockOf v)
    have hR'D : Disjoint R' (L.unionRegion p) :=
      (hRR'.mono (L.unionRegion_subset_lightCone R) Finset.subset_union_left).symm
    obtain ⟨A₁, rfl⟩ :=
      exists_eq_place_of_mem_supportedOperators (supportedOperators_mono hRD hA)
    obtain ⟨B₂, rfl⟩ := exists_eq_one_kronecker_of_mem_supportedOperators hR'D hB
    have hF := L.sum_farKraus ev p fun β _ ↦ L.blockEffect_eq_one ev hL β
    have hN := L.sum_nearKraus ev p hL (cutEquiv X _ σ₀).2
    have hAB : place (L.unionRegion p) A₁ * (1 ⊗ₖ B₂).submatrix (cutEquiv Y _) (cutEquiv Y _) =
        (A₁ ⊗ₖ B₂).submatrix (cutEquiv Y _) (cutEquiv Y _) := by
      rw [place, reindex_apply, Equiv.symm_symm, submatrix_mul_equiv, ← mul_kronecker_mul,
        Matrix.mul_one, Matrix.one_mul]
    rw [hAB, place, reindex_apply, Equiv.symm_symm, L.dual_kronecker, L.dual_kronecker,
      L.dual_kronecker]
    simp_rw [Matrix.mul_one, hF, hN]
    rw [submatrix_mul_equiv, ← mul_kronecker_mul, Matrix.mul_one, Matrix.one_mul]

omit [Fintype S] in
/-- A layer whose gates and onsite families are trace-preserving, on nonempty bases, has a
Kraus index. -/
theorem nonempty_index_of_forall_isTP [Finite S] [∀ s, Nonempty (X s)]
    (h : L.Forall ev KrausFamily.IsTP) : Nonempty L.Index := by
  have := Fintype.ofFinite S
  exact (L.isTP_krausFamily ev h).nonempty_index

omit [Fintype S] in
/-- The output bases of a layer whose gates and onsite families are trace-preserving, on
nonempty bases, are nonempty. -/
theorem nonempty_output_of_forall_isTP [Finite S] [∀ s, Nonempty (X s)]
    (h : L.Forall ev KrausFamily.IsTP) (s : S) : Nonempty (Y s) := by
  have := Fintype.ofFinite S
  obtain ⟨y⟩ := (L.isTP_krausFamily ev h).nonempty_target
  exact ⟨y s⟩

end Factorization

end Layer

end QuantumCircuit
