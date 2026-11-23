/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Circuit.Core.Map
import QICLean.Circuit.Core.SingleBranch

/-!
# Moving the layers of a circuit that have a given shape

A map of layers (`QuantumCircuit.LayerMap`) moves every layer of a circuit to another geometry
and gate family. Some maps exist only for layers of a given shape. For example, a coarsening that
keeps the gates of a family, such as pair sources, is defined on layers of at most one cell with
the identity at the other sites of the blocks the cell meets, but not on a layer whose gate is
followed by a nontrivial onsite operation in the same block. A map of layers on a domain
(`QuantumCircuit.LayerMapOn`) moves the layers satisfying a condition `Domain`, and a circuit
all of whose layers satisfy it (`Circuit.ForallLayer`) is moved layer by layer
(`Circuit.mapLayersOn`).

The branches of the moved circuit are those of the circuit, and its Kraus operators are the
images of those of the circuit under a multiplicative unital map when this holds layer by layer.
Being unbranched passes to the moved circuit, and so do the conditions on layers that the map
carries over: one outcome per gate and one member per onsite family, a local property, a
condition on the gates, and a cost of layers. A map of all layers is the case of the domain of
all layers.

## Main definitions

* `QuantumCircuit.Circuit.ForallLayer` — every layer along every branch satisfies a condition.
* `QuantumCircuit.LayerMapOn` — a map of the layers satisfying a condition.
* `QuantumCircuit.Circuit.mapLayersOn`, `QuantumCircuit.Circuit.mapIndexEquivOn` — the moved
  circuit, and its branches.
* `QuantumCircuit.LayerMap.toLayerMapOn` — a map of all layers, on the domain of all layers.

## Main results

* `QuantumCircuit.Circuit.kraus_mapLayersOn` — the Kraus operators of the moved circuit.
* `QuantumCircuit.Circuit.mapLayersOn_comp` — moving commutes with composition.
* `QuantumCircuit.Circuit.isUnbranched_mapLayersOn`, `QuantumCircuit.Circuit.isSingle_mapLayersOn`,
  `QuantumCircuit.Circuit.forall_mapLayersOn`, `QuantumCircuit.Circuit.forallGate'_mapLayersOn`,
  `QuantumCircuit.Circuit.total_mapLayersOn` — properties of the moved circuit.
* `QuantumCircuit.Circuit.mapLayersOn_toLayerMapOn` — on the domain of all layers it is
  `Circuit.mapLayers`.
-/

open Matrix ManyBody

namespace QuantumCircuit

variable {S S' : Type} [Fintype S] [DecidableEq S] [Fintype S'] [DecidableEq S']
  {Γ : Geometry S} {G : Finset S → (S → Type) → (S → Type) → Type 1} [GateFamily G]
  {Γ' : Geometry S'} {G' : Finset S' → (S' → Type) → (S' → Type) → Type 1} [GateFamily G']

namespace Circuit

/-- Every layer of the circuit, on every branch, satisfies the condition `Q`. -/
def ForallLayer (Q : ∀ ⦃X Y : S → Type⦄ [∀ s, Fintype (X s)] [∀ s, DecidableEq (X s)]
      [∀ s, Fintype (Y s)] [∀ s, DecidableEq (Y s)], Layer Γ G X Y → Prop) :
    {X Z : S → Type} → [∀ s, Fintype (X s)] → [∀ s, DecidableEq (X s)] →
      Circuit Γ G X Z → Prop
  | _, _, _, _, done _ => True
  | _, _, _, _, step L next => Q L ∧ ∀ i, (next i).ForallLayer Q

omit [Fintype S] [Fintype S'] [DecidableEq S'] in
/-- A condition on layers passes to `c.append k` from `c` and every continuation. -/
theorem ForallLayer.append {Z : S → Type}
    {Q : ∀ ⦃X Y : S → Type⦄ [∀ s, Fintype (X s)] [∀ s, DecidableEq (X s)]
      [∀ s, Fintype (Y s)] [∀ s, DecidableEq (Y s)], Layer Γ G X Y → Prop} : {X Y : S → Type} →
    [∀ s, Fintype (X s)] → [∀ s, DecidableEq (X s)] → [∀ s, Fintype (Y s)] →
    [∀ s, DecidableEq (Y s)] → {c : Circuit Γ G X Y} → {k : c.Index → Circuit Γ G Y Z} →
      c.ForallLayer Q → (∀ p, (k p).ForallLayer Q) → (c.append k).ForallLayer Q
  | _, _, i₁, i₂, i₃, i₄, done _, _, _, hk => by
    obtain rfl : i₁ = i₃ := Subsingleton.elim _ _
    obtain rfl : i₂ = i₄ := Subsingleton.elim _ _
    exact hk ()
  | _, _, _, _, _, _, step _ next, _, hc, hk =>
    ⟨hc.1, fun i ↦ ForallLayer.append (c := next i) (hc.2 i) fun j ↦ hk ⟨i, j⟩⟩

omit [Fintype S] [Fintype S'] [DecidableEq S'] in
/-- A condition on layers passes to compositions. -/
theorem ForallLayer.comp {X Y Z : S → Type} [∀ s, Fintype (X s)] [∀ s, DecidableEq (X s)]
    [∀ s, Fintype (Y s)] [∀ s, DecidableEq (Y s)]
    {Q : ∀ ⦃X Y : S → Type⦄ [∀ s, Fintype (X s)] [∀ s, DecidableEq (X s)]
      [∀ s, Fintype (Y s)] [∀ s, DecidableEq (Y s)], Layer Γ G X Y → Prop}
    {c : Circuit Γ G X Y} {c' : Circuit Γ G Y Z} (hc : c.ForallLayer Q)
    (hc' : c'.ForallLayer Q) : (c.comp c').ForallLayer Q :=
  hc.append fun _ ↦ hc'

end Circuit

/-- A map of the layers satisfying the condition `Domain`, from the geometry `Γ` with gates `G`
to the geometry `Γ'` with gates `G'`: a map of systems and, for every layer in the domain, a
layer between the images of its systems, with an equivalence of Kraus indices. -/
structure LayerMapOn (Γ : Geometry S) (G : Finset S → (S → Type) → (S → Type) → Type 1)
    (Γ' : Geometry S') (G' : Finset S' → (S' → Type) → (S' → Type) → Type 1) [GateFamily G]
    [GateFamily G'] extends SystemMap S S' where
  /-- The layers that are moved. -/
  Domain : ∀ ⦃X Y : S → Type⦄ [∀ s, Fintype (X s)] [∀ s, DecidableEq (X s)]
    [∀ s, Fintype (Y s)] [∀ s, DecidableEq (Y s)], Layer Γ G X Y → Prop
  /-- The image of a layer in the domain. -/
  layer : ∀ ⦃X Y : S → Type⦄ [∀ s, Fintype (X s)] [∀ s, DecidableEq (X s)]
    [∀ s, Fintype (Y s)] [∀ s, DecidableEq (Y s)] (L : Layer Γ G X Y),
    Domain L → Layer Γ' G' (system X) (system Y)
  /-- The Kraus indices of the image of a layer are those of the layer. -/
  indexEquiv : ∀ ⦃X Y : S → Type⦄ [∀ s, Fintype (X s)] [∀ s, DecidableEq (X s)]
    [∀ s, Fintype (Y s)] [∀ s, DecidableEq (Y s)] (L : Layer Γ G X Y) (h : Domain L),
    (layer L h).Index ≃ L.Index

/-- A map of all layers, as a map on the domain of all layers. -/
def LayerMap.toLayerMapOn (F : LayerMap Γ G Γ' G') : LayerMapOn Γ G Γ' G' where
  toSystemMap := F.toSystemMap
  Domain _ _ _ _ _ _ _ := True
  layer _ _ _ _ _ _ L _ := F.layer L
  indexEquiv _ _ _ _ _ _ L _ := F.indexEquiv L

namespace Circuit

variable (F : LayerMapOn Γ G Γ' G')

/-- The circuit with every layer moved along `F`. -/
noncomputable def mapLayersOn : {X Z : S → Type} → [∀ s, Fintype (X s)] →
    [∀ s, DecidableEq (X s)] → (c : Circuit Γ G X Z) → c.ForallLayer F.Domain →
      Circuit Γ' G' (F.system X) (F.system Z)
  | _, _, _, _, done _, _ => done _
  | _, _, _, _, step L next, h =>
      step (F.layer L h.1) fun i ↦ (next (F.indexEquiv L h.1 i)).mapLayersOn (h.2 _)

/-- The branches of the moved circuit are those of the circuit. -/
noncomputable def mapIndexEquivOn : {X Z : S → Type} → [∀ s, Fintype (X s)] →
    [∀ s, DecidableEq (X s)] → (c : Circuit Γ G X Z) → (h : c.ForallLayer F.Domain) →
      (c.mapLayersOn F h).Index ≃ c.Index
  | _, _, _, _, done _, _ => Equiv.refl Unit
  | _, _, _, _, step L next, h =>
      Equiv.sigmaCongr (F.indexEquiv L h.1) fun i ↦
        (next (F.indexEquiv L h.1 i)).mapIndexEquivOn (h.2 _)

omit [Fintype S] [Fintype S'] in
/-- Equal circuits are moved to equal circuits. -/
theorem mapLayersOn_congr {X Z : S → Type} [∀ s, Fintype (X s)] [∀ s, DecidableEq (X s)]
    {c c' : Circuit Γ G X Z} (e : c = c') (h : c.ForallLayer F.Domain)
    (h' : c'.ForallLayer F.Domain) : c.mapLayersOn F h = c'.mapLayersOn F h' := by
  subst e
  rfl

/-- **Moving a circuit layer by layer.** The Kraus operators of the moved circuit are the images
of those of the circuit under a multiplicative and unital map `Φ`, when this holds for every
layer in the domain. -/
theorem kraus_mapLayersOn {ev : Interpretation G} {ev' : Interpretation G'}
    (Φ : ∀ ⦃X Z : S → Type⦄,
      Matrix (Config Z) (Config X) ℂ → Matrix (Config (F.system Z)) (Config (F.system X)) ℂ)
    (hone : ∀ ⦃X : S → Type⦄ [∀ s, DecidableEq (X s)],
      Φ (1 : Matrix (Config X) (Config X) ℂ) = 1)
    (hmul : ∀ ⦃X Y Z : S → Type⦄ [∀ s, Fintype (Y s)] (A : Matrix (Config Z) (Config Y) ℂ)
      (B : Matrix (Config Y) (Config X) ℂ), Φ (A * B) = Φ A * Φ B)
    (hL : ∀ ⦃X Y : S → Type⦄ [∀ s, Fintype (X s)] [∀ s, DecidableEq (X s)]
      [∀ s, Fintype (Y s)] [∀ s, DecidableEq (Y s)] (L : Layer Γ G X Y) (hD : F.Domain L)
      (i : (F.layer L hD).Index),
      (F.layer L hD).kraus ev' i = Φ (L.kraus ev (F.indexEquiv L hD i))) :
    {X Z : S → Type} → [∀ s, Fintype (X s)] → [∀ s, DecidableEq (X s)] →
      (c : Circuit Γ G X Z) → (h : c.ForallLayer F.Domain) → (p : (c.mapLayersOn F h).Index) →
        (c.mapLayersOn F h).kraus ev' p = Φ (c.kraus ev (c.mapIndexEquivOn F h p))
  | _, _, _, _, done _, _, _ => (hone (X := _)).symm
  | _, _, _, _, step L next, h, q => by
    obtain ⟨i, p⟩ := q
    change ((next (F.indexEquiv L h.1 i)).mapLayersOn F (h.2 _)).kraus ev' p *
        (F.layer L h.1).kraus ev' i =
      Φ ((next (F.indexEquiv L h.1 i)).kraus ev
          ((next (F.indexEquiv L h.1 i)).mapIndexEquivOn F (h.2 _) p) *
        L.kraus ev (F.indexEquiv L h.1 i))
    rw [kraus_mapLayersOn Φ hone hmul hL _ (h.2 _) p, hL L h.1 i, hmul]

omit [Fintype S] [Fintype S'] in
/-- Moving commutes with composition. -/
theorem mapLayersOn_comp {Z : S → Type} :
    {X Y : S → Type} → [∀ s, Fintype (X s)] → [∀ s, DecidableEq (X s)] →
    [∀ s, Fintype (Y s)] → [∀ s, DecidableEq (Y s)] →
    (c : Circuit Γ G X Y) → (c' : Circuit Γ G Y Z) → (h : c.ForallLayer F.Domain) →
    (h' : c'.ForallLayer F.Domain) →
      (c.comp c').mapLayersOn F (h.comp h') = (c.mapLayersOn F h).comp (c'.mapLayersOn F h')
  | _, _, i₁, i₂, i₃, i₄, done _, c', _, _ => by
    obtain rfl : i₁ = i₃ := Subsingleton.elim _ _
    obtain rfl : i₂ = i₄ := Subsingleton.elim _ _
    rfl
  | _, _, _, _, _, _, step L next, c', h, h' =>
    congrArg (step (F.layer L h.1)) (funext fun _ ↦ mapLayersOn_comp (next _) c' (h.2 _) h')

omit [Fintype S] [Fintype S'] in
/-- The moved circuit of an unbranched circuit is unbranched. -/
theorem isUnbranched_mapLayersOn : {X Z : S → Type} → [∀ s, Fintype (X s)] →
    [∀ s, DecidableEq (X s)] → (c : Circuit Γ G X Z) → (h : c.ForallLayer F.Domain) →
      c.IsUnbranched → (c.mapLayersOn F h).IsUnbranched
  | _, _, _, _, done _, _, _ => trivial
  | _, _, _, _, step _ next, h, hc =>
    ⟨fun _ _ ↦ mapLayersOn_congr F (hc.1 _ _) _ _,
      fun _ ↦ isUnbranched_mapLayersOn (next _) (h.2 _) (hc.2 _)⟩

omit [Fintype S] [Fintype S'] in
/-- The moved circuit has one outcome per gate and one member per onsite family when the circuit
does and every moved layer keeps this. -/
theorem isSingle_mapLayersOn
    (hS : ∀ ⦃X Y : S → Type⦄ [∀ s, Fintype (X s)] [∀ s, DecidableEq (X s)]
      [∀ s, Fintype (Y s)] [∀ s, DecidableEq (Y s)] (L : Layer Γ G X Y) (hD : F.Domain L),
      ((∀ b : L.cells, Nonempty (Unique (GateFamily.Outcome (L.gate b)))) ∧
        ∀ s, Nonempty (Unique (L.onsite s).Index)) →
      ((∀ b : (F.layer L hD).cells,
          Nonempty (Unique (GateFamily.Outcome ((F.layer L hD).gate b)))) ∧
        ∀ s, Nonempty (Unique ((F.layer L hD).onsite s).Index))) :
    {X Z : S → Type} → [∀ s, Fintype (X s)] → [∀ s, DecidableEq (X s)] →
      (c : Circuit Γ G X Z) → (h : c.ForallLayer F.Domain) → c.IsSingle →
        (c.mapLayersOn F h).IsSingle
  | _, _, _, _, done _, _, _ => trivial
  | _, _, _, _, step L next, h, hc =>
    ⟨hS L h.1 hc.1, fun _ ↦ isSingle_mapLayersOn hS (next _) (h.2 _) (hc.2 _)⟩

omit [Fintype S] [Fintype S'] in
/-- A local property passes to the moved circuit when it passes to every moved layer. -/
theorem forall_mapLayersOn {ev : Interpretation G} {ev' : Interpretation G'}
    {P : ∀ {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β],
      KrausFamily α β → Prop}
    (hL : ∀ ⦃X Y : S → Type⦄ [∀ s, Fintype (X s)] [∀ s, DecidableEq (X s)]
      [∀ s, Fintype (Y s)] [∀ s, DecidableEq (Y s)] (L : Layer Γ G X Y) (hD : F.Domain L),
      L.Forall ev P → (F.layer L hD).Forall ev' P) :
    {X Z : S → Type} → [∀ s, Fintype (X s)] → [∀ s, DecidableEq (X s)] →
      (c : Circuit Γ G X Z) → (h : c.ForallLayer F.Domain) → c.Forall ev P →
        (c.mapLayersOn F h).Forall ev' P
  | _, _, _, _, done _, _, _ => trivial
  | _, _, _, _, step L next, h, hc =>
    ⟨hL L h.1 hc.1, fun _ ↦ forall_mapLayersOn hL (next _) (h.2 _) (hc.2 _)⟩

omit [Fintype S] [Fintype S'] in
/-- A condition on the gates passes to the moved circuit when it passes to the gates of every
moved layer. -/
theorem forallGate'_mapLayersOn {A : ∀ ⦃D : Finset S⦄ ⦃X Y : S → Type⦄, G D X Y → Prop}
    {A' : ∀ ⦃D : Finset S'⦄ ⦃X Y : S' → Type⦄, G' D X Y → Prop}
    (hA : ∀ ⦃X Y : S → Type⦄ [∀ s, Fintype (X s)] [∀ s, DecidableEq (X s)]
      [∀ s, Fintype (Y s)] [∀ s, DecidableEq (Y s)] (L : Layer Γ G X Y) (hD : F.Domain L),
      (∀ b : L.cells, A (L.gate b)) → ∀ b : (F.layer L hD).cells, A' ((F.layer L hD).gate b)) :
    {X Z : S → Type} → [∀ s, Fintype (X s)] → [∀ s, DecidableEq (X s)] →
      (c : Circuit Γ G X Z) → (h : c.ForallLayer F.Domain) → c.ForallGate' A →
        (c.mapLayersOn F h).ForallGate' A'
  | _, _, _, _, done _, _, _ => trivial
  | _, _, _, _, step L next, h, hc =>
    ⟨hA L h.1 hc.1, fun _ ↦ forallGate'_mapLayersOn hA (next _) (h.2 _) (hc.2 _)⟩

/-- A cost of the moved layers equal to a cost of the layers gives the cost of the moved
circuit. -/
theorem total_mapLayersOn (f : ∀ ⦃X Y : S → Type⦄, Layer Γ G X Y → ℕ)
    (f' : ∀ ⦃X Y : S' → Type⦄, Layer Γ' G' X Y → ℕ)
    (hf : ∀ ⦃X Y : S → Type⦄ [∀ s, Fintype (X s)] [∀ s, DecidableEq (X s)]
      [∀ s, Fintype (Y s)] [∀ s, DecidableEq (Y s)] (L : Layer Γ G X Y) (hD : F.Domain L),
      f' (F.layer L hD) = f L) :
    {X Z : S → Type} → [∀ s, Fintype (X s)] → [∀ s, DecidableEq (X s)] →
      (c : Circuit Γ G X Z) → (h : c.ForallLayer F.Domain) →
        (c.mapLayersOn F h).total f' = c.total f
  | _, _, _, _, done _, _ => rfl
  | _, _, _, _, step L next, h => by
    change f' (F.layer L h.1) +
        Finset.univ.sup (fun i ↦ ((next (F.indexEquiv L h.1 i)).mapLayersOn F (h.2 _)).total f') =
      f L + Finset.univ.sup fun i ↦ (next i).total f
    rw [hf L h.1, ← Finset.map_univ_equiv (F.indexEquiv L h.1), Finset.sup_map]
    exact congrArg _ (Finset.sup_congr rfl fun i _ ↦ total_mapLayersOn f f' hf _ (h.2 _))

omit [Fintype S] [Fintype S'] [DecidableEq S'] [GateFamily G'] in
/-- Every circuit satisfies the condition of all layers. -/
theorem forallLayer_true : {X Z : S → Type} → [∀ s, Fintype (X s)] →
    [∀ s, DecidableEq (X s)] → (c : Circuit Γ G X Z) →
      c.ForallLayer fun _ _ _ _ _ _ _ ↦ True
  | _, _, _, _, done _ => trivial
  | _, _, _, _, step _ next => ⟨trivial, fun _ ↦ forallLayer_true (next _)⟩

omit [Fintype S] [Fintype S'] in
/-- On the domain of all layers, moving the layers is `Circuit.mapLayers`. -/
theorem mapLayersOn_toLayerMapOn (F : LayerMap Γ G Γ' G') : {X Z : S → Type} →
    [∀ s, Fintype (X s)] → [∀ s, DecidableEq (X s)] → (c : Circuit Γ G X Z) →
      (h : c.ForallLayer F.toLayerMapOn.Domain) → c.mapLayersOn F.toLayerMapOn h = c.mapLayers F
  | _, _, _, _, done _, _ => rfl
  | _, _, _, _, step L next, h =>
    congrArg (step (F.layer L)) (funext fun _ ↦ mapLayersOn_toLayerMapOn F (next _) (h.2 _))

end Circuit

end QuantumCircuit
