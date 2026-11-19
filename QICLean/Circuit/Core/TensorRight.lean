/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Channel.KrausFamilyProd
import QICLean.Circuit.Core.Map

/-!
# Circuits tensored with an environment at every site

For a basis `W s` at every site, a circuit of plain gates from `X` to `Z` acts on the system
`fun s ↦ X s × W s` by the identity on the environments: every gate `g` on a cell `D` becomes
`g ⊗ 1` on `RegionConfig X D × RegionConfig W D`, carried to the region of the enlarged system by
Mathlib's `Equiv.arrowProdEquivProdArrow`, and every onsite family `K` becomes `K ⊗ 1`. The cells
do not change, so neither do the depth and the gate count. This is a layer map
(`LayerMap.tensorRight`), and the moved circuit `Circuit.tensorRight` inherits composition,
unbranchedness and the cost bounds from `Circuit.mapLayers`. Its Kraus operator along a branch is
that of the circuit tensored with the identity on the environments, and its map sends
`ρ ⊗ ω` to `c(ρ) ⊗ ω`.

## Main definitions

* `QuantumCircuit.Layer.tensorRight`, `QuantumCircuit.LayerMap.tensorRight`,
  `QuantumCircuit.Circuit.tensorRight` — the layer and the circuit on the enlarged system.

## Main results

* `QuantumCircuit.Layer.kraus_tensorRight`, `QuantumCircuit.Circuit.kraus_tensorRight` — the
  Kraus operators.
* `QuantumCircuit.Circuit.map_tensorRight` — the map on `ρ ⊗ ω`.
* `QuantumCircuit.Circuit.forall_isTP_tensorRight`,
  `QuantumCircuit.Circuit.forall_isUnitary_tensorRight` — trace preservation and unitarity of the
  gates and onsite families.
* `QuantumCircuit.Circuit.depth_tensorRight_le`, `QuantumCircuit.Circuit.gateCount_tensorRight_le`.
-/

open Matrix ManyBody
open scoped Kronecker

namespace QuantumCircuit

variable {S : Type} [Fintype S] [DecidableEq S] {Γ : Geometry S} (W : S → Type)
  [∀ s, Fintype (W s)] [∀ s, DecidableEq (W s)]

namespace Layer

variable {X Y : S → Type}

/-- The layer tensored with the identity on the environment `W s` at every site: the gates
`g ⊗ 1` on the same cells and the onsite families `K ⊗ 1`. -/
noncomputable def tensorRight (L : Layer Γ KrausGate X Y) :
    Layer Γ KrausGate (fun s ↦ X s × W s) (fun s ↦ Y s × W s) where
  cells := L.cells
  pairwiseDisjoint := L.pairwiseDisjoint
  gate b := ((L.gate b).tensorRight (RegionConfig W (Γ.cell b))).reindex
    (Equiv.arrowProdEquivProdArrow _ _ _) (Equiv.arrowProdEquivProdArrow _ _ _)
  onsite s := (L.onsite s).tensorRight (W s)

/-- The Kraus indices of the tensored layer are those of the layer. -/
noncomputable def tensorRightIndexEquiv (L : Layer Γ KrausGate X Y) :
    (L.tensorRight W).Index ≃ L.Index :=
  Equiv.prodCongr (Equiv.piCongrRight fun b ↦ Equiv.prodPUnit (L.gate b).Index)
    (Equiv.piCongrRight fun s ↦ Equiv.prodPUnit (L.onsite s).Index)

omit [Fintype S] [∀ s, Fintype (W s)] in
@[simp] theorem tensorRightIndexEquiv_apply (L : Layer Γ KrausGate X Y)
    (i : (L.tensorRight W).Index) :
    L.tensorRightIndexEquiv W i = (fun b ↦ (i.1 b).1, fun s ↦ (i.2 s).1) :=
  rfl

omit [∀ s, Fintype (W s)] in
/-- The identity on the environments is the product of its factors on the cells of a layer and
at its free sites. -/
private theorem prod_one_mul_prod_one {G : Finset S → (S → Type) → (S → Type) → Type 1}
    (L : Layer Γ G X Y) (y x : Config W) :
    (∏ b : L.cells, (1 : Matrix (RegionConfig W (Γ.cell b)) (RegionConfig W (Γ.cell b)) ℂ)
        (fun v ↦ y v) (fun v ↦ x v)) * ∏ s : L.Free, (1 : Matrix (W s) (W s) ℂ) (y s) (x s) =
      (1 : Matrix (Config W) (Config W) ℂ) y x := by
  by_cases h : y = x
  · subst h
    simp only [one_apply_eq, Finset.prod_const_one, mul_one]
  obtain ⟨v, hv⟩ := Function.ne_iff.mp h
  rw [one_apply_ne h]
  by_cases hmem : v ∈ L.cells.biUnion Γ.cell
  · obtain ⟨b, hb, hvb⟩ := Finset.mem_biUnion.mp hmem
    refine mul_eq_zero_of_left (Finset.prod_eq_zero (i := (⟨b, hb⟩ : L.cells))
      (Finset.mem_univ _) ?_) _
    exact one_apply_ne fun e ↦ hv (congrFun e ⟨v, hvb⟩)
  · exact mul_eq_zero_of_right _ (Finset.prod_eq_zero (Finset.mem_univ ⟨v, hmem⟩)
      (one_apply_ne hv))

variable [∀ s, Fintype (X s)] [∀ s, DecidableEq (X s)] [∀ s, Fintype (Y s)]
  [∀ s, DecidableEq (Y s)]

omit [Fintype S] [∀ s, Fintype (X s)] [∀ s, DecidableEq (X s)] [∀ s, Fintype (Y s)]
  [∀ s, DecidableEq (Y s)] [∀ s, Fintype (W s)] in
private theorem gate_tensorRight_op (L : Layer Γ KrausGate X Y) (b : (L.tensorRight W).cells)
    (o : ((L.tensorRight W).gate b).Index)
    (y : RegionConfig (fun s ↦ Y s × W s) (Γ.cell b))
    (x : RegionConfig (fun s ↦ X s × W s) (Γ.cell b)) :
    ((L.tensorRight W).gate b).op o y x =
      (L.gate b).op o.1 (fun v ↦ (y v).1) (fun v ↦ (x v).1) *
        if (fun v ↦ (y v).2) = (fun v ↦ (x v).2) then 1 else 0 := by
  rw [← one_apply]
  rfl

omit [Fintype S] [∀ s, Fintype (X s)] [∀ s, DecidableEq (X s)] [∀ s, Fintype (Y s)]
  [∀ s, DecidableEq (Y s)] [∀ s, Fintype (W s)] in
private theorem onsite_tensorRight_op (L : Layer Γ KrausGate X Y) (s : (L.tensorRight W).Free)
    (o : ((L.tensorRight W).onsite s).Index) (y : Y s × W s) (x : X s × W s) :
    ((L.tensorRight W).onsite s).op o y x =
      (L.onsite s).op o.1 y.1 x.1 * if y.2 = x.2 then 1 else 0 := by
  rw [← one_apply]
  rfl

/-- The Kraus operators of the tensored layer are those of the layer tensored with the identity
on the environments. -/
theorem kraus_tensorRight (L : Layer Γ KrausGate X Y) (i : (L.tensorRight W).Index) :
    (L.tensorRight W).kraus KrausGate.ev i =
      (L.kraus KrausGate.ev (L.tensorRightIndexEquiv W i) ⊗ₖ
        (1 : Matrix (Config W) (Config W) ℂ)).submatrix
          (Equiv.arrowProdEquivProdArrow S Y W) (Equiv.arrowProdEquivProdArrow S X W) := by
  ext y x
  rw [submatrix_apply, kronecker_apply, kraus_apply, kraus_apply, ← prod_one_mul_prod_one W L,
    tensorRightIndexEquiv_apply]
  simp only [KrausGate.ev_apply, gate_tensorRight_op, onsite_tensorRight_op,
    Finset.prod_mul_distrib, one_apply, Equiv.arrowProdEquivProdArrow_apply]
  rw [mul_mul_mul_comm]
  rfl

omit [Fintype S] in
/-- A local property held by `K ⊗ 1` and by every relabelling of a family holding it passes to
the tensored layer. -/
theorem forall_tensorRight
    {P : ∀ {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β],
      KrausFamily α β → Prop}
    (hT : ∀ {α β ω : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype ω]
      [DecidableEq ω] (K : KrausFamily α β), P K → P (K.tensorRight ω))
    (hR : ∀ {α β α' β' : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
      [Fintype α'] [DecidableEq α'] [Fintype β'] [DecidableEq β'] (K : KrausFamily α β)
      (e : α' ≃ α) (f : β' ≃ β), P K → P (K.reindex e f))
    {L : Layer Γ KrausGate X Y} (hL : L.Forall KrausGate.ev P) :
    (L.tensorRight W).Forall KrausGate.ev P :=
  ⟨fun b ↦ hR _ _ _ (hT _ (hL.1 b)), fun s ↦ hT _ (hL.2 s)⟩

end Layer

/-- The layer map tensoring every layer with the identity on the environment `W s` at every
site. -/
noncomputable abbrev LayerMap.tensorRight : LayerMap Γ KrausGate Γ KrausGate where
  system X := fun s ↦ X s × W s
  fintype _ _ _ := inferInstance
  decidableEq _ _ _ := inferInstance
  layer _ _ _ _ _ _ L := L.tensorRight W
  indexEquiv _ _ _ _ _ _ L := L.tensorRightIndexEquiv W

namespace Circuit

variable {X Z : S → Type} [∀ s, Fintype (X s)] [∀ s, DecidableEq (X s)]

/-- The circuit tensored with the identity on the environment `W s` at every site. -/
noncomputable def tensorRight (c : Circuit Γ KrausGate X Z) :
    Circuit Γ KrausGate (fun s ↦ X s × W s) (fun s ↦ Z s × W s) :=
  c.mapLayers (LayerMap.tensorRight W)

/-- The Kraus operators of the tensored circuit are those of the circuit tensored with the
identity on the environments. -/
theorem kraus_tensorRight (c : Circuit Γ KrausGate X Z) (p : (c.tensorRight W).Index) :
    (c.tensorRight W).kraus KrausGate.ev p =
      (c.kraus KrausGate.ev (c.mapIndexEquiv (LayerMap.tensorRight W) p) ⊗ₖ
        (1 : Matrix (Config W) (Config W) ℂ)).submatrix
          (Equiv.arrowProdEquivProdArrow S Z W) (Equiv.arrowProdEquivProdArrow S X W) := by
  refine kraus_mapLayers (LayerMap.tensorRight W)
    (fun _ _ K ↦ (K ⊗ₖ (1 : Matrix (Config W) (Config W) ℂ)).submatrix
      (Equiv.arrowProdEquivProdArrow S _ W) (Equiv.arrowProdEquivProdArrow S _ W))
    (fun _ _ ↦ ?_) (fun _ _ _ _ A B ↦ ?_)
    (fun _ _ _ _ _ _ L i ↦ Layer.kraus_tensorRight W L i) c p
  · rw [one_kronecker_one, submatrix_one_equiv]
  · have := submatrix_mul_equiv (A ⊗ₖ (1 : Matrix (Config W) (Config W) ℂ)) (B ⊗ₖ 1)
      (Equiv.arrowProdEquivProdArrow S _ W) (Equiv.arrowProdEquivProdArrow S _ W)
      (Equiv.arrowProdEquivProdArrow S _ W)
    rw [← mul_kronecker_mul, Matrix.mul_one] at this
    exact this.symm

/-- The map of the tensored circuit sends `ρ ⊗ ω` to `c(ρ) ⊗ ω`. -/
theorem map_tensorRight [∀ s, Fintype (Z s)] (c : Circuit Γ KrausGate X Z)
    (ρ : Matrix (Config X) (Config X) ℂ) (ω : Matrix (Config W) (Config W) ℂ) :
    (c.tensorRight W).map KrausGate.ev
        ((ρ ⊗ₖ ω).submatrix (Equiv.arrowProdEquivProdArrow S X W)
          (Equiv.arrowProdEquivProdArrow S X W)) =
      (c.map KrausGate.ev ρ ⊗ₖ ω).submatrix (Equiv.arrowProdEquivProdArrow S Z W)
        (Equiv.arrowProdEquivProdArrow S Z W) := by
  simp only [map, krausFamily, KrausFamily.map_apply]
  refine (Fintype.sum_equiv (c.mapIndexEquiv (LayerMap.tensorRight W)) _ (fun p ↦
    (c.kraus KrausGate.ev p ⊗ₖ (1 : Matrix (Config W) (Config W) ℂ)).submatrix
      (Equiv.arrowProdEquivProdArrow S Z W) (Equiv.arrowProdEquivProdArrow S X W) *
      (ρ ⊗ₖ ω).submatrix (Equiv.arrowProdEquivProdArrow S X W)
        (Equiv.arrowProdEquivProdArrow S X W) *
      ((c.kraus KrausGate.ev p ⊗ₖ (1 : Matrix (Config W) (Config W) ℂ)).submatrix
        (Equiv.arrowProdEquivProdArrow S Z W) (Equiv.arrowProdEquivProdArrow S X W))ᴴ)
    fun p ↦ by rw [kraus_tensorRight W c p]).trans ?_
  have ht : ∀ K : Matrix (Config Z) (Config X) ℂ,
      (K ⊗ₖ (1 : Matrix (Config W) (Config W) ℂ)).submatrix
          (Equiv.arrowProdEquivProdArrow S Z W) (Equiv.arrowProdEquivProdArrow S X W) *
        (ρ ⊗ₖ ω).submatrix (Equiv.arrowProdEquivProdArrow S X W)
          (Equiv.arrowProdEquivProdArrow S X W) *
        ((K ⊗ₖ (1 : Matrix (Config W) (Config W) ℂ)).submatrix
          (Equiv.arrowProdEquivProdArrow S Z W) (Equiv.arrowProdEquivProdArrow S X W))ᴴ =
      ((K * ρ * Kᴴ) ⊗ₖ ω).submatrix (Equiv.arrowProdEquivProdArrow S Z W)
        (Equiv.arrowProdEquivProdArrow S Z W) := by
    intro K
    rw [conjTranspose_submatrix, submatrix_mul_equiv, submatrix_mul_equiv, conjTranspose_kronecker,
      conjTranspose_one, ← mul_kronecker_mul, ← mul_kronecker_mul, Matrix.mul_one, Matrix.one_mul]
  simp only [ht]
  ext a b
  simp [Matrix.sum_apply, kroneckerMap_apply, Finset.sum_mul]

omit [Fintype S] in
/-- The gates and onsite families of the tensored circuit are trace-preserving when those of the
circuit are. -/
theorem forall_isTP_tensorRight {c : Circuit Γ KrausGate X Z}
    (hc : c.Forall KrausGate.ev KrausFamily.IsTP) :
    (c.tensorRight W).Forall KrausGate.ev KrausFamily.IsTP :=
  forall_mapLayers _ (fun _ _ _ _ _ _ _ hL ↦ Layer.forall_tensorRight W
    (fun _ hK ↦ hK.tensorRight _) (fun _ e f hK ↦ hK.reindex e f) hL) hc

omit [Fintype S] in
/-- The gates and onsite families of the tensored circuit are unitary when those of the circuit
are. -/
theorem forall_isUnitary_tensorRight {c : Circuit Γ KrausGate X Z}
    (hc : c.Forall KrausGate.ev KrausFamily.IsUnitary) :
    (c.tensorRight W).Forall KrausGate.ev KrausFamily.IsUnitary :=
  forall_mapLayers _ (fun _ _ _ _ _ _ _ hL ↦ Layer.forall_tensorRight W
    (fun _ hK ↦ hK.tensorRight _) (fun _ e f hK ↦ hK.reindex e f) hL) hc

theorem depth_tensorRight_le (c : Circuit Γ KrausGate X Z) :
    (c.tensorRight W).depth ≤ c.depth :=
  total_mapLayers_le _ _ _ (fun _ _ _ _ _ _ _ ↦ le_rfl) c

theorem gateCount_tensorRight_le (c : Circuit Γ KrausGate X Z) :
    (c.tensorRight W).gateCount ≤ c.gateCount :=
  total_mapLayers_le _ _ _ (fun _ _ _ _ _ _ _ ↦ le_rfl) c

end Circuit

end QuantumCircuit
