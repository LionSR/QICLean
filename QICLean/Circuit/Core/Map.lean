/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Circuit.Core.LightCone
import QICLean.Circuit.Core.GateSum

/-!
# Moving circuits between sites, geometries and gate families

A circuit on the sites `S` moves to the sites `S'` along an equivalence `e : S' ≃ S ⊕ R`: the
sites of `S` become the sites `ι s = e.symm (inl s)` of `S'`, and the sites of `R` are idle,
with a fixed basis `W r` and the identity on it in every layer. A system `X` on `S` becomes the
system `lift e W X` on `S'`, the basis `X s` at `ι s` and `W r` at `e.symm (inr r)`. The cells
move along a morphism of geometries over `ι`, which preserves the sites of cells, and the gates
along a transport of gate families. The three uses are instances of the one notion:

* a register inside a larger system: `S' = S ⊕ R` and `e = Equiv.refl`;
* relabelling of sites along `σ : S ≃ S'`: `R = Empty`;
* coarsening of the geometry on the same sites, such as nearest-neighbour cells inside all
  pairs: `R = Empty` and `e = (Equiv.sumEmpty S Empty).symm`.

The Kraus operator of the moved circuit along a branch is the Kraus operator of the original
along the corresponding branch, tensored with the identity on the idle sites
(`Circuit.kraus_mapSites`). Local properties invariant under relabelling of bases, unbranched
circuits and light cones move along, and costs compare as the costs of the cells do.

A change of gate family on the same sites and geometry (`Circuit.mapGate`) is a map of gates
with an equivalence of outcomes compatible with the interpretations. It embeds a gate set into a
larger one, such as `G₁` into `GateSum G₁ G₂`.

## Main definitions

* `QuantumCircuit.lift` — a system on `S` as a system on `S'`.
* `QuantumCircuit.Geometry.Hom` — a morphism of geometries over a map of sites.
* `QuantumCircuit.GateTransport` — a transport of gates along `e`.
* `QuantumCircuit.Circuit.mapSites` — the moved circuit.
* `QuantumCircuit.GateMorphism`, `QuantumCircuit.Circuit.mapGate` — a change of gate family.

## Main results

* `QuantumCircuit.Circuit.kraus_mapSites` — the Kraus operators of the moved circuit.
* `QuantumCircuit.Circuit.forall_mapSites`, `QuantumCircuit.Circuit.isUnbranched_mapSites`,
  `QuantumCircuit.Circuit.lightCone_mapSites`, `QuantumCircuit.Circuit.gateCount_mapSites_le`,
  `QuantumCircuit.Circuit.depth_mapSites_le` — what moves along.
* `QuantumCircuit.Circuit.kraus_mapGate` and the analogues for `mapGate`.
-/

open Matrix ManyBody
open scoped Kronecker

namespace QuantumCircuit

variable {S S' R : Type} [Fintype S] [DecidableEq S] [Fintype S'] [DecidableEq S']
  [Fintype R] [DecidableEq R]

/-! ### Systems and configurations -/

/-- The site of `S'` of a site of `S`. -/
def siteEmb (e : S' ≃ S ⊕ R) : S ↪ S' :=
  ⟨fun s ↦ e.symm (.inl s), fun _ _ h ↦ Sum.inl_injective (e.symm.injective h)⟩

/-- A system on `S` as a system on `S'`: the basis `X s` at the site `ι s`, and `W r` at the
idle site `e.symm (inr r)`. -/
abbrev lift (e : S' ≃ S ⊕ R) (W : R → Type) (X : S → Type) : S' → Type :=
  fun s' ↦ Sum.elim X W (e s')

variable (e : S' ≃ S ⊕ R) (W : R → Type) [∀ r, Fintype (W r)] [∀ r, DecidableEq (W r)]

/-- The basis of `lift e W X` at the site `ι s` is the basis of `s`. -/
def liftSiteEquiv (X : S → Type) (s : S) : lift e W X (siteEmb e s) ≃ X s :=
  Equiv.cast (congrArg (Sum.elim X W) (e.apply_symm_apply _))

/-- The configurations of `lift e W X` are a configuration of `X` and one of the idle sites. -/
def liftConfigEquiv (X : S → Type) :
    Config (lift e W X) ≃ Config X × ((r : R) → W r) :=
  sorry

/-- The configurations of the image of a region. -/
def liftRegionEquiv (X : S → Type) (D : Finset S) :
    RegionConfig (lift e W X) (D.map (siteEmb e)) ≃ RegionConfig X D :=
  sorry

/-! ### Geometries and gates -/

/-- A morphism of geometries over the map of sites `ι`: an injective map of cells carrying the
sites of a cell to the sites of its image. Costs are compared separately. -/
structure Geometry.Hom {S S' : Type} (Γ : Geometry S) (Γ' : Geometry S') (ι : S ↪ S') where
  /-- The map of cells. -/
  cellMap : Γ.Cell ↪ Γ'.Cell
  /-- The sites of the image of a cell. -/
  cell_cellMap : ∀ b, Γ'.cell (cellMap b) = (Γ.cell b).map ι

/-- A transport of gates along `e`: a gate on `D` from `X` to `Y` gives a gate on the image of
`D` from `lift e W X` to `lift e W Y`, with an equivalence of outcomes. -/
structure GateTransport (G : Finset S → (S → Type) → (S → Type) → Type 1)
    (G' : Finset S' → (S' → Type) → (S' → Type) → Type 1) [GateFamily G] [GateFamily G'] where
  /-- The transported gate. -/
  map : ∀ ⦃D : Finset S⦄ ⦃X Y : S → Type⦄, G D X Y →
    G' (D.map (siteEmb e)) (lift e W X) (lift e W Y)
  /-- Its outcomes are those of the gate. -/
  outcome : ∀ ⦃D : Finset S⦄ ⦃X Y : S → Type⦄ (g : G D X Y),
    GateFamily.Outcome (map g) ≃ GateFamily.Outcome g

variable {G : Finset S → (S → Type) → (S → Type) → Type 1}
  {G' : Finset S' → (S' → Type) → (S' → Type) → Type 1} [GateFamily G] [GateFamily G']

/-- A transport is compatible with interpretations `ev` and `ev'` when the transported gate
has, outcome by outcome, the matrix of the gate in the transported configurations. -/
def GateTransport.IsCompatible (φ : GateTransport e W G G') (ev : Interpretation G)
    (ev' : Interpretation G') : Prop :=
  ∀ ⦃D : Finset S⦄ ⦃X Y : S → Type⦄ [∀ s, Fintype (X s)] [∀ s, DecidableEq (X s)]
    [∀ s, Fintype (Y s)] [∀ s, DecidableEq (Y s)] (g : G D X Y) (o : GateFamily.Outcome (φ.map g)),
    ev' (φ.map g) o =
      (ev g (φ.outcome g o)).submatrix (liftRegionEquiv e W Y D) (liftRegionEquiv e W X D)

/-- The transport of plain gates. -/
noncomputable def KrausGate.transport : GateTransport e W (KrausGate (S := S))
    (KrausGate (S := S')) where
  map _ X Y g := ⟨g.Index, fun i ↦ (g.op i).submatrix (liftRegionEquiv e W Y _)
    (liftRegionEquiv e W X _)⟩
  outcome _ _ _ _ := Equiv.refl _

theorem KrausGate.isCompatible_transport :
    (KrausGate.transport e W).IsCompatible e W KrausGate.ev KrausGate.ev :=
  fun _ _ _ _ _ _ _ _ _ ↦ rfl

/-! ### Moving layers and circuits -/

variable {Γ : Geometry S} {Γ' : Geometry S'}

namespace Layer

variable {X Y : S → Type} [∀ s, Fintype (X s)] [∀ s, DecidableEq (X s)]
  [∀ s, Fintype (Y s)] [∀ s, DecidableEq (Y s)]

/-- The layer moved along `e`, the morphism of geometries `h` and the transport `φ`: the
transported gates on the image cells, the onsite families at the sites of `S`, and the
identity at the idle sites. -/
noncomputable def mapSites (h : Γ.Hom Γ' (siteEmb e)) (φ : GateTransport e W G G')
    (L : Layer Γ G X Y) : Layer Γ' G' (lift e W X) (lift e W Y) :=
  sorry

/-- The Kraus indices of the moved layer are those of the layer. -/
noncomputable def mapSitesIndexEquiv (h : Γ.Hom Γ' (siteEmb e)) (φ : GateTransport e W G G')
    (L : Layer Γ G X Y) : (L.mapSites e W h φ).Index ≃ L.Index :=
  sorry

/-- The Kraus operators of the moved layer are those of the layer tensored with the identity on
the idle sites. -/
theorem kraus_mapSites (h : Γ.Hom Γ' (siteEmb e)) (φ : GateTransport e W G G')
    {ev : Interpretation G} {ev' : Interpretation G'} (hφ : φ.IsCompatible e W ev ev')
    (L : Layer Γ G X Y) (i : (L.mapSites e W h φ).Index) :
    (L.mapSites e W h φ).kraus ev' i =
      (L.kraus ev (L.mapSitesIndexEquiv e W h φ i) ⊗ₖ (1 : Matrix ((r : R) → W r) _ ℂ)).submatrix
        (liftConfigEquiv e W Y) (liftConfigEquiv e W X) :=
  sorry

end Layer

namespace Circuit

/-- The circuit moved along `e`, the morphism of geometries `h` and the transport `φ`. -/
noncomputable def mapSites (h : Γ.Hom Γ' (siteEmb e)) (φ : GateTransport e W G G') :
    {X Z : S → Type} → [∀ s, Fintype (X s)] → [∀ s, DecidableEq (X s)] →
      Circuit Γ G X Z → Circuit Γ' G' (lift e W X) (lift e W Z)
  | _, _, _, _, done _ => done _
  | _, _, _, _, step L next =>
      step (L.mapSites e W h φ) fun i ↦ (next (L.mapSitesIndexEquiv e W h φ i)).mapSites h φ

variable {X Z : S → Type} [∀ s, Fintype (X s)] [∀ s, DecidableEq (X s)]
  [∀ s, Fintype (Z s)] [∀ s, DecidableEq (Z s)]

/-- The branches of the moved circuit are those of the circuit. -/
noncomputable def mapSitesIndexEquiv (h : Γ.Hom Γ' (siteEmb e)) (φ : GateTransport e W G G')
    (c : Circuit Γ G X Z) : (c.mapSites e W h φ).Index ≃ c.Index :=
  sorry

/-- The Kraus operators of the moved circuit are those of the circuit tensored with the
identity on the idle sites. -/
theorem kraus_mapSites (h : Γ.Hom Γ' (siteEmb e)) (φ : GateTransport e W G G')
    {ev : Interpretation G} {ev' : Interpretation G'} (hφ : φ.IsCompatible e W ev ev')
    (c : Circuit Γ G X Z) (p : (c.mapSites e W h φ).Index) :
    (c.mapSites e W h φ).kraus ev' p =
      (c.kraus ev (c.mapSitesIndexEquiv e W h φ p) ⊗ₖ (1 : Matrix ((r : R) → W r) _ ℂ)).submatrix
        (liftConfigEquiv e W Z) (liftConfigEquiv e W X) :=
  sorry

theorem isUnbranched_mapSites (h : Γ.Hom Γ' (siteEmb e)) (φ : GateTransport e W G G')
    {c : Circuit Γ G X Z} (hc : c.IsUnbranched) : (c.mapSites e W h φ).IsUnbranched :=
  sorry

/-- A local property invariant under relabelling of bases, held by the identity, moves along
with every transported gate. -/
theorem forall_mapSites (h : Γ.Hom Γ' (siteEmb e)) (φ : GateTransport e W G G')
    {ev : Interpretation G} {ev' : Interpretation G'} (hφ : φ.IsCompatible e W ev ev')
    {P : ∀ {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β],
      KrausFamily α β → Prop}
    (hP : ∀ {α β α' β' : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
      [Fintype α'] [DecidableEq α'] [Fintype β'] [DecidableEq β'] (K : KrausFamily α β)
      (a : α' ≃ α) (b : β' ≃ β), P K → P ⟨K.Index, fun i ↦ (K.op i).submatrix b a⟩)
    (hone : ∀ {α : Type} [Fintype α] [DecidableEq α], P (KrausFamily.single (1 : Matrix α α ℂ)))
    {c : Circuit Γ G X Z} (hc : c.Forall ev P) : (c.mapSites e W h φ).Forall ev' P :=
  sorry

/-- The light cone of the image of a region is the image of its light cone. -/
theorem lightCone_mapSites (h : Γ.Hom Γ' (siteEmb e)) (φ : GateTransport e W G G')
    (c : Circuit Γ G X Z) (T : Finset S) :
    (c.mapSites e W h φ).lightCone (T.map (siteEmb e)) = (c.lightCone T).map (siteEmb e) :=
  sorry

/-- When no cell costs more after the move, neither does the circuit. -/
theorem gateCount_mapSites_le (h : Γ.Hom Γ' (siteEmb e)) (φ : GateTransport e W G G')
    (hcost : ∀ b, Γ'.cost (h.cellMap b) ≤ Γ.cost b) (c : Circuit Γ G X Z) :
    (c.mapSites e W h φ).gateCount ≤ c.gateCount :=
  sorry

/-- When a cell of positive cost after the move had positive cost before, the depth does not
grow. -/
theorem depth_mapSites_le (h : Γ.Hom Γ' (siteEmb e)) (φ : GateTransport e W G G')
    (hcost : ∀ b, 0 < Γ'.cost (h.cellMap b) → 0 < Γ.cost b) (c : Circuit Γ G X Z) :
    (c.mapSites e W h φ).depth ≤ c.depth :=
  sorry

end Circuit

/-! ### Change of gate family -/

section MapGate

variable {G₁ G₂ : Finset S → (S → Type) → (S → Type) → Type 1} [GateFamily G₁] [GateFamily G₂]

/-- A morphism of gate families on the same sites: a map of gates with an equivalence of
outcomes, compatible with the interpretations `ev₁` and `ev₂`. -/
structure GateMorphism (G₁ G₂ : Finset S → (S → Type) → (S → Type) → Type 1) [GateFamily G₁]
    [GateFamily G₂] (ev₁ : Interpretation G₁) (ev₂ : Interpretation G₂) where
  /-- The map of gates. -/
  map : ∀ ⦃D : Finset S⦄ ⦃X Y : S → Type⦄, G₁ D X Y → G₂ D X Y
  /-- The outcomes of the image are those of the gate. -/
  outcome : ∀ ⦃D : Finset S⦄ ⦃X Y : S → Type⦄ (g : G₁ D X Y),
    GateFamily.Outcome (map g) ≃ GateFamily.Outcome g
  /-- The image has the matrices of the gate. -/
  ev_map : ∀ ⦃D : Finset S⦄ ⦃X Y : S → Type⦄ [∀ s, Fintype (X s)] [∀ s, DecidableEq (X s)]
    [∀ s, Fintype (Y s)] [∀ s, DecidableEq (Y s)] (g : G₁ D X Y) (o : GateFamily.Outcome (map g)),
    ev₂ (map g) o = ev₁ g (outcome g o)

/-- The embedding of a gate family into its sum with another. -/
def GateMorphism.inl (ev₁ : Interpretation G₁) (ev₂ : Interpretation G₂) :
    GateMorphism G₁ (GateSum G₁ G₂) ev₁ (ev₁.sum ev₂) where
  map _ _ _ g := .inl g
  outcome _ _ _ _ := Equiv.refl _
  ev_map _ _ _ _ _ _ _ _ _ := rfl

variable {ev₁ : Interpretation G₁} {ev₂ : Interpretation G₂}

/-- A layer with its gates mapped. -/
def Layer.mapGate (φ : GateMorphism G₁ G₂ ev₁ ev₂) {X Y : S → Type} (L : Layer Γ G₁ X Y) :
    Layer Γ G₂ X Y where
  cells := L.cells
  pairwiseDisjoint := L.pairwiseDisjoint
  gate b := φ.map (L.gate b)
  onsite := L.onsite

/-- The Kraus indices of a layer with its gates mapped. -/
def Layer.mapGateIndexEquiv (φ : GateMorphism G₁ G₂ ev₁ ev₂) {X Y : S → Type}
    (L : Layer Γ G₁ X Y) : (L.mapGate φ).Index ≃ L.Index :=
  Equiv.prodCongr (Equiv.piCongrRight fun b ↦ φ.outcome (L.gate b)) (Equiv.refl _)

/-- A circuit with its gates mapped. -/
def Circuit.mapGate (φ : GateMorphism G₁ G₂ ev₁ ev₂) :
    {X Z : S → Type} → Circuit Γ G₁ X Z → Circuit Γ G₂ X Z
  | _, _, .done _ => .done _
  | _, _, @Circuit.step _ _ _ _ _ _ _ _ _ _ L next =>
      .step (L.mapGate φ) fun i ↦ (next (L.mapGateIndexEquiv φ i)).mapGate φ

/-- The branches of a circuit with its gates mapped. -/
def Circuit.mapGateIndexEquiv (φ : GateMorphism G₁ G₂ ev₁ ev₂) :
    {X Z : S → Type} → (c : Circuit Γ G₁ X Z) → (c.mapGate φ).Index ≃ c.Index
  | _, _, .done _ => Equiv.refl Unit
  | _, _, @Circuit.step _ _ _ _ _ _ _ _ _ _ L next =>
      Equiv.sigmaCongr (L.mapGateIndexEquiv φ) fun i ↦ (next _).mapGateIndexEquiv φ

variable {X Z : S → Type} [∀ s, Fintype (X s)] [∀ s, DecidableEq (X s)]

theorem Circuit.kraus_mapGate (φ : GateMorphism G₁ G₂ ev₁ ev₂) (c : Circuit Γ G₁ X Z)
    (p : (c.mapGate φ).Index) : (c.mapGate φ).kraus ev₂ p = c.kraus ev₁ (c.mapGateIndexEquiv φ p) :=
  sorry

omit [Fintype S'] [DecidableEq S'] [Fintype R] [DecidableEq R] [∀ s, Fintype (X s)]
  [∀ s, DecidableEq (X s)] in
theorem Circuit.isUnbranched_mapGate (φ : GateMorphism G₁ G₂ ev₁ ev₂) {c : Circuit Γ G₁ X Z}
    (hc : c.IsUnbranched) : (c.mapGate φ).IsUnbranched :=
  sorry

theorem Circuit.forall_mapGate (φ : GateMorphism G₁ G₂ ev₁ ev₂)
    {P : ∀ {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β],
      KrausFamily α β → Prop}
    (hP : ∀ {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
      (K : KrausFamily α β) {ι : Type} [Fintype ι] (u : ι ≃ K.Index),
        P K → P ⟨ι, fun i ↦ K.op (u i)⟩)
    {c : Circuit Γ G₁ X Z} (hc : c.Forall ev₁ P) : (c.mapGate φ).Forall ev₂ P :=
  sorry

omit [Fintype S'] [DecidableEq S'] [Fintype R] [DecidableEq R] [∀ s, Fintype (X s)]
  [∀ s, DecidableEq (X s)] in
/-- Mapping gates changes no cost that depends only on the cells of the layers. -/
theorem Circuit.total_mapGate (φ : GateMorphism G₁ G₂ ev₁ ev₂)
    (f₁ : ∀ ⦃X Y : S → Type⦄, Layer Γ G₁ X Y → ℕ) (f₂ : ∀ ⦃X Y : S → Type⦄, Layer Γ G₂ X Y → ℕ)
    (hf : ∀ ⦃X Y : S → Type⦄ (L : Layer Γ G₁ X Y), f₂ (L.mapGate φ) = f₁ L)
    (c : Circuit Γ G₁ X Z) : (c.mapGate φ).total f₂ = c.total f₁ :=
  sorry

omit [Fintype S'] [DecidableEq S'] [Fintype R] [DecidableEq R] [∀ s, Fintype (X s)]
  [∀ s, DecidableEq (X s)] in
theorem Circuit.lightCone_mapGate (φ : GateMorphism G₁ G₂ ev₁ ev₂) (c : Circuit Γ G₁ X Z)
    (T : Finset S) : (c.mapGate φ).lightCone T = c.lightCone T :=
  sorry

end MapGate

end QuantumCircuit
