/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Circuit.Core.Parallel
import QICLean.ManyBody.Sites.SystemUpdate

/-!
# Layers that change the system on one region

A gate on a cell `b` may change the basis types of the sites of `b`, as a gate that prepares or
measures registers there does, while the other sites keep theirs. The layer `Layer.gateAt b hY g`
applies the gate `g` from the system `X` to a system `Y` that agrees with `X` outside the cell,
and the identity at every other site. Its Kraus operator at an outcome is the placement
`M ⊗ 1` of the matrix `M` of the gate between the two systems (`Layer.kraus_gateAt`). On one
system it is the layer `Layer.single`.

Likewise `Layer.onsiteOpAt s₀ hY A` applies the matrix `A` at the site `s₀`, from `X s₀` to
`Y s₀`, and the identity at every other site; it uses no cell, so it costs nothing.

A layer is *one step* (`Layer.IsStep`) when it has no cell, or one cell and the identity at
every other site, as the layers `gateAt`, `onsiteOpAt` and `ofOnsite` are; a circuit is
*sequential* when every layer along every branch is one step. The condition reads the identity with
classical decidability, so that it needs no instances on the basis types.

## Main definitions

* `QuantumCircuit.Layer.gateAt` — one gate, changing the system on its cell.
* `QuantumCircuit.Layer.onsiteOpAt` — one matrix at one site, changing the basis type there.
* `QuantumCircuit.Layer.IsIdentityAt`, `QuantumCircuit.Layer.IsStep`,
  `QuantumCircuit.Circuit.IsSequential` — one operation per step.

## Main results

* `QuantumCircuit.Layer.kraus_gateAt`, `QuantumCircuit.Layer.kraus_onsiteOpAt` — their Kraus
  operators are placements between the two systems.
* `QuantumCircuit.Layer.gateAt_eq_single` — on one system, `gateAt` is `single`.
* `QuantumCircuit.Layer.forall_gateAt`, `QuantumCircuit.Layer.forall_onsiteOpAt` — local
  properties that the identity has.
* `QuantumCircuit.Layer.gateCount_gateAt`, `QuantumCircuit.Layer.meets_gateAt`,
  `QuantumCircuit.Layer.gateCount_onsiteOpAt`, `QuantumCircuit.Layer.meets_onsiteOpAt` — their
  costs.
* `QuantumCircuit.Layer.isStep_gateAt`, `QuantumCircuit.Layer.isStep_onsiteOpAt`,
  `QuantumCircuit.Circuit.IsSequential.comp` — one operation per step.
-/

open Matrix ManyBody

namespace QuantumCircuit

namespace Layer

variable {S : Type} [Fintype S] [DecidableEq S] {Γ : Geometry S}
  {G : Finset S → (S → Type) → (S → Type) → Type 1} [GateFamily G] {X Y : S → Type}

/-- A local property of every identity holds for the identity between two equal basis types. -/
private theorem of_single_cast
    {P : ∀ {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β],
      KrausFamily α β → Prop}
    (hone : ∀ {α : Type} [Fintype α] [DecidableEq α], P (KrausFamily.single (1 : Matrix α α ℂ)))
    {α β : Type} [iα : Fintype α] [dα : DecidableEq α] [iβ : Fintype β] [dβ : DecidableEq β]
    (h : β = α) :
    P (KrausFamily.single ((Equiv.cast h).toPEquiv.toMatrix : Matrix β α ℂ)) := by
  subst h
  obtain rfl : iα = iβ := Subsingleton.elim _ _
  obtain rfl : dα = dβ := Subsingleton.elim _ _
  rw [Equiv.cast_refl, Equiv.toPEquiv_refl, PEquiv.toMatrix_refl]
  exact hone

/-! ### One gate changing the system on its cell -/

/-- The layer with the gate `g` on the cell `b`, from the system `X` to a system `Y` that agrees
with `X` outside the cell, and the identity at every other site. -/
def gateAt [∀ s, DecidableEq (X s)] (b : Γ.Cell) (hY : ∀ s ∉ Γ.cell b, Y s = X s)
    (g : G (Γ.cell b) X Y) : Layer Γ G X Y where
  cells := {b}
  pairwiseDisjoint := by simp
  gate x := (Finset.mem_singleton.mp x.2).symm ▸ g
  onsite s := KrausFamily.single (Equiv.cast (hY s.1 (by simpa using s.2))).toPEquiv.toMatrix

omit [Fintype S] [GateFamily G] in
theorem free_gateAt_iff [∀ s, DecidableEq (X s)] (b : Γ.Cell)
    (hY : ∀ s ∉ Γ.cell b, Y s = X s) (g : G (Γ.cell b) X Y) (s : S) :
    s ∉ (gateAt b hY g).cells.biUnion Γ.cell ↔ s ∉ Γ.cell b := by
  simp [gateAt]

omit [Fintype S] [GateFamily G] in
/-- On one system, the layer of one gate changing the system is the layer of one gate. -/
theorem gateAt_eq_single [∀ s, DecidableEq (X s)] (b : Γ.Cell) (g : G (Γ.cell b) X X) :
    gateAt b (fun _ _ ↦ rfl) g = single b g := by
  simp only [gateAt, single, Equiv.cast_refl, Equiv.toPEquiv_refl, PEquiv.toMatrix_refl]

/-- The Kraus operator of the layer of one gate `g` on the cell `b`, changing the system there,
is the placement `M ⊗ 1` between the two systems of the matrix `M` of `g` at the outcome of the
index. -/
theorem kraus_gateAt [∀ s, Fintype (X s)] [∀ s, DecidableEq (X s)] [∀ s, Fintype (Y s)]
    [∀ s, DecidableEq (Y s)] (ev : Interpretation G) (b : Γ.Cell)
    (hY : ∀ s ∉ Γ.cell b, Y s = X s) (g : G (Γ.cell b) X Y) (i : (gateAt b hY g).Index) :
    (gateAt b hY g).kraus ev i =
      placeBetween (Γ.cell b) hY (ev g (i.1 ⟨b, Finset.mem_singleton_self b⟩)) := by
  ext y x
  rw [placeBetween_apply, kraus]
  let : Unique (gateAt b hY g).cells := inferInstanceAs (Unique ({b} : Finset Γ.Cell))
  rw [Fintype.prod_unique]
  have hcell : ev ((gateAt b hY g).gate default) (i.1 default) (fun v ↦ y v) (fun v ↦ x v) =
      ev g (i.1 ⟨b, Finset.mem_singleton_self b⟩) (fun v ↦ y v) (fun v ↦ x v) := rfl
  have hone : ∀ s : (gateAt b hY g).Free, ((gateAt b hY g).onsite s).op (i.2 s) (y s) (x s) =
      if cast (hY s.1 ((free_gateAt_iff b hY g s.1).mp s.2)) (y s) = x s then 1 else 0 :=
    fun s ↦ by simp [gateAt, PEquiv.toMatrix_apply]
  rw [hcell, Finset.prod_congr rfl fun s _ ↦ hone s, Finset.prod_boole, mul_ite, mul_one,
    mul_zero]
  split_ifs with h₁ h₂ h₂
  · rfl
  · exact absurd (fun v hv ↦ h₁ ⟨v, (free_gateAt_iff b hY g v).mpr hv⟩ (Finset.mem_univ _)) h₂
  · exact absurd (fun (s : (gateAt b hY g).Free) _ ↦
      h₂ s.1 ((free_gateAt_iff b hY g s.1).mp s.2)) h₁
  · rfl

omit [Fintype S] in
/-- The layer of one gate changing the system satisfies a local property that its gate and every
identity have. -/
theorem forall_gateAt [∀ s, Fintype (X s)] [∀ s, DecidableEq (X s)] [∀ s, Fintype (Y s)]
    [∀ s, DecidableEq (Y s)] (ev : Interpretation G)
    {P : ∀ {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β],
      KrausFamily α β → Prop}
    (hone : ∀ {α : Type} [Fintype α] [DecidableEq α], P (KrausFamily.single (1 : Matrix α α ℂ)))
    (b : Γ.Cell) (hY : ∀ s ∉ Γ.cell b, Y s = X s) (g : G (Γ.cell b) X Y)
    (hg : P (⟨GateFamily.Outcome g, ev g⟩ :
      KrausFamily (RegionConfig X (Γ.cell b)) (RegionConfig Y (Γ.cell b)))) :
    (gateAt b hY g).Forall ev P := by
  refine ⟨fun c ↦ ?_, fun s ↦ of_single_cast hone _⟩
  obtain ⟨c, hc⟩ := c
  obtain rfl := Finset.mem_singleton.mp hc
  exact hg

omit [Fintype S] [GateFamily G] in
/-- The layer of one gate changing the system has the weight of its gate. -/
private theorem cellCost_gateAt [∀ s, DecidableEq (X s)]
    (w : ∀ ⦃X Y : S → Type⦄ (b : Γ.Cell), G (Γ.cell b) X Y → ℕ) (b : Γ.Cell)
    (hY : ∀ s ∉ Γ.cell b, Y s = X s) (g : G (Γ.cell b) X Y) :
    (gateAt b hY g).cellCost w = w b g := by
  let : Unique (gateAt b hY g).cells := inferInstanceAs (Unique ({b} : Finset Γ.Cell))
  rw [cellCost, Fintype.sum_unique]
  rfl

omit [Fintype S] [GateFamily G] in
/-- The layer of one gate has the gate count of its cell. -/
theorem gateCount_gateAt [∀ s, DecidableEq (X s)] (b : Γ.Cell)
    (hY : ∀ s ∉ Γ.cell b, Y s = X s) (g : G (Γ.cell b) X Y) :
    (gateAt b hY g).gateCount = Γ.cost b :=
  cellCost_gateAt _ b hY g

omit [Fintype S] [GateFamily G] in
/-- The layer of one gate meets the sites of its cell once when the cell has positive cost. -/
theorem meets_gateAt [∀ s, DecidableEq (X s)] (b : Γ.Cell)
    (hY : ∀ s ∉ Γ.cell b, Y s = X s) (g : G (Γ.cell b) X Y) (s : S) :
    (gateAt b hY g).meets s = if s ∈ Γ.cell b ∧ 0 < Γ.cost b then 1 else 0 :=
  cellCost_gateAt _ b hY g

/-! ### One matrix at one site -/

/-- The layer with no cell that applies the matrix `A` at the site `s₀`, from `X s₀` to `Y s₀`,
and the identity at every other site, where `Y` agrees with `X`. -/
def onsiteOpAt [∀ s, DecidableEq (X s)] (s₀ : S) (hY : ∀ s ≠ s₀, Y s = X s)
    (A : Matrix (Y s₀) (X s₀) ℂ) : Layer Γ G X Y :=
  ofOnsite fun s ↦ KrausFamily.single <|
    if h : s = s₀ then h ▸ A else (Equiv.cast (hY s h)).toPEquiv.toMatrix

/-- The Kraus operator of the layer of one matrix `A` at the site `s₀` is the placement of `A`
between the two systems, on the region `{s₀}`. -/
theorem kraus_onsiteOpAt [∀ s, Fintype (X s)] [∀ s, DecidableEq (X s)] [∀ s, Fintype (Y s)]
    [∀ s, DecidableEq (Y s)] (ev : Interpretation G) (s₀ : S) (hY : ∀ s ≠ s₀, Y s = X s)
    (A : Matrix (Y s₀) (X s₀) ℂ) (i : (onsiteOpAt (Γ := Γ) (G := G) s₀ hY A).Index) :
    (onsiteOpAt (Γ := Γ) (G := G) s₀ hY A).kraus ev i =
      placeBetween {s₀} (fun s hs ↦ hY s (Finset.notMem_singleton.mp hs))
        (A.submatrix (fun y ↦ y ⟨s₀, Finset.mem_singleton_self s₀⟩)
          (fun x ↦ x ⟨s₀, Finset.mem_singleton_self s₀⟩)) := by
  refine (kraus_ofOnsite ev _ i).trans ?_
  ext y x
  rw [piKronecker_apply]
  change ∏ s, (if h : s = s₀ then h ▸ A else (Equiv.cast (hY s h)).toPEquiv.toMatrix) (y s) (x s)
    = _
  rw [placeBetween_apply,
    ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ s₀), dite_eq_left rfl]
  have hone : ∀ s ∈ Finset.univ.erase s₀,
      (if h : s = s₀ then h ▸ A else (Equiv.cast (hY s h)).toPEquiv.toMatrix) (y s) (x s) =
        if ∀ h : s ≠ s₀, cast (hY s h) (y s) = x s then (1 : ℂ) else 0 :=
    fun s hs ↦ by
      rw [dite_eq_right (Finset.ne_of_mem_erase hs)]
      simp [PEquiv.toMatrix_apply, Finset.ne_of_mem_erase hs]
  rw [Finset.prod_congr rfl hone, Finset.prod_boole, mul_ite, mul_one, mul_zero]
  split_ifs with h₁ h₂ h₂
  · rfl
  · exact absurd (fun v hv ↦ h₁ v (Finset.mem_erase.mpr ⟨Finset.notMem_singleton.mp hv,
      Finset.mem_univ v⟩) (Finset.notMem_singleton.mp hv)) h₂
  · exact absurd (fun (s : S) (_ : s ∈ Finset.univ.erase s₀) (h : s ≠ s₀) ↦
      h₂ s (Finset.notMem_singleton.mpr h)) h₁
  · rfl

omit [Fintype S] in
/-- The layer of one matrix at one site satisfies a local property that the matrix and every
identity have. -/
theorem forall_onsiteOpAt [∀ s, Fintype (X s)] [∀ s, DecidableEq (X s)] [∀ s, Fintype (Y s)]
    [∀ s, DecidableEq (Y s)] (ev : Interpretation G)
    {P : ∀ {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β],
      KrausFamily α β → Prop}
    (hone : ∀ {α : Type} [Fintype α] [DecidableEq α], P (KrausFamily.single (1 : Matrix α α ℂ)))
    (s₀ : S) (hY : ∀ s ≠ s₀, Y s = X s) (A : Matrix (Y s₀) (X s₀) ℂ)
    (hA : P (KrausFamily.single A)) :
    (onsiteOpAt (Γ := Γ) (G := G) s₀ hY A).Forall ev P := by
  refine ⟨fun b ↦ absurd b.2 (Finset.notMem_empty _), fun ⟨s, _⟩ ↦ ?_⟩
  change P (KrausFamily.single
    (if h : s = s₀ then h ▸ A else (Equiv.cast (hY s h)).toPEquiv.toMatrix))
  by_cases h : s = s₀
  · subst h
    rw [dite_eq_left rfl]
    exact hA
  · rw [dite_eq_right h]
    exact of_single_cast hone _

omit [Fintype S] [GateFamily G] in
/-- The layer of one matrix at one site has no gate. -/
theorem gateCount_onsiteOpAt [∀ s, DecidableEq (X s)] (s₀ : S) (hY : ∀ s ≠ s₀, Y s = X s)
    (A : Matrix (Y s₀) (X s₀) ℂ) : (onsiteOpAt (Γ := Γ) (G := G) s₀ hY A).gateCount = 0 := by
  rw [gateCount, cellCost]
  exact Fintype.sum_eq_zero _ fun b ↦ absurd b.2 (Finset.notMem_empty _)

omit [Fintype S] [GateFamily G] in
/-- The layer of one matrix at one site meets no site. -/
theorem meets_onsiteOpAt [∀ s, DecidableEq (X s)] (s₀ : S) (hY : ∀ s ≠ s₀, Y s = X s)
    (A : Matrix (Y s₀) (X s₀) ℂ) (s : S) :
    (onsiteOpAt (Γ := Γ) (G := G) s₀ hY A).meets s = 0 := by
  rw [meets, cellCost]
  exact Fintype.sum_eq_zero _ fun b ↦ absurd b.2 (Finset.notMem_empty _)

/-! ### One operation per step -/

open Classical in
/-- The layer acts as the identity at the site `s`, which no cell meets: the basis type is
unchanged there and every member of the onsite family is the identity matrix. The identity is
read with classical decidability, so that the condition needs no instances. -/
def IsIdentityAt (L : Layer Γ G X Y) (s : L.Free) : Prop :=
  ∃ h : Y s.1 = X s.1, ∀ i y x, (L.onsite s).op i y x = if cast h y = x then 1 else 0

omit [Fintype S] [GateFamily G] in
/-- An onsite family of identity matrices between equal basis types acts as the identity. -/
theorem isIdentityAt_of_op_eq {L : Layer Γ G X Y} (s : L.Free) [DecidableEq (X s.1)]
    (h : Y s.1 = X s.1) (hop : ∀ i, (L.onsite s).op i = (Equiv.cast h).toPEquiv.toMatrix) :
    L.IsIdentityAt s :=
  ⟨h, fun i y x ↦ by
    rw [hop, PEquiv.toMatrix_apply]
    by_cases hx : cast h y = x <;> simp [Option.mem_def, hx]⟩

/-- One operation per step: the layer has no cell, or it has one cell and acts as the identity
at every other site. -/
def IsStep (L : Layer Γ G X Y) : Prop :=
  L.cells = ∅ ∨ ∃ b, L.cells = {b} ∧ ∀ s, L.IsIdentityAt s

omit [Fintype S] [GateFamily G] in
/-- The layer of one gate changing the system is one step. -/
theorem isStep_gateAt [∀ s, DecidableEq (X s)] (b : Γ.Cell) (hY : ∀ s ∉ Γ.cell b, Y s = X s)
    (g : G (Γ.cell b) X Y) : (gateAt b hY g).IsStep :=
  Or.inr ⟨b, rfl, fun s ↦ isIdentityAt_of_op_eq s _ fun _ ↦ rfl⟩

omit [Fintype S] [GateFamily G] in
/-- An onsite layer is one step. -/
theorem isStep_ofOnsite (o : (s : S) → KrausFamily (X s) (Y s)) :
    (ofOnsite (Γ := Γ) (G := G) o).IsStep :=
  Or.inl rfl

omit [Fintype S] [GateFamily G] in
/-- The layer of one matrix at one site is one step. -/
theorem isStep_onsiteOpAt [∀ s, DecidableEq (X s)] (s₀ : S) (hY : ∀ s ≠ s₀, Y s = X s)
    (A : Matrix (Y s₀) (X s₀) ℂ) : (onsiteOpAt (Γ := Γ) (G := G) s₀ hY A).IsStep :=
  Or.inl rfl

end Layer

namespace Circuit

variable {S : Type} [Fintype S] [DecidableEq S] {Γ : Geometry S}
  {G : Finset S → (S → Type) → (S → Type) → Type 1} [GateFamily G] {X Y Z : S → Type}

/-! ### Circuits of one operation per step -/

/-- Every layer along every branch is one step (`Layer.IsStep`): it has no cell, or one cell
and the identity at every other site. -/
def IsSequential : {X Z : S → Type} → Circuit Γ G X Z → Prop
  | _, _, done _ => True
  | _, _, step L next => L.IsStep ∧ ∀ i, (next i).IsSequential

omit [Fintype S] in
/-- Being sequential passes to `c.append k` from `c` and every continuation. -/
theorem IsSequential.append : {X Y : S → Type} → {c : Circuit Γ G X Y} →
    {k : c.Index → Circuit Γ G Y Z} → c.IsSequential → (∀ p, (k p).IsSequential) →
      (c.append k).IsSequential
  | _, _, done _, _, _, hk => hk ()
  | _, _, step _ next, _, hc, hk =>
    ⟨hc.1, fun i ↦ IsSequential.append (c := next i) (hc.2 i) fun j ↦ hk ⟨i, j⟩⟩

omit [Fintype S] in
/-- A composition of sequential circuits is sequential. -/
theorem IsSequential.comp {c : Circuit Γ G X Y} {c' : Circuit Γ G Y Z} (hc : c.IsSequential)
    (hc' : c'.IsSequential) : (c.comp c').IsSequential :=
  hc.append fun _ ↦ hc'

omit [Fintype S] in
/-- The circuit of one step is sequential. -/
theorem isSequential_ofLayer [∀ s, Fintype (Y s)] [∀ s, DecidableEq (Y s)] {L : Layer Γ G X Y}
    (hL : L.IsStep) : (ofLayer L).IsSequential :=
  ⟨hL, fun _ ↦ trivial⟩

end Circuit

end QuantumCircuit
