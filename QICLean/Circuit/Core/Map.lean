/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Circuit.Core.LightCone

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

omit [Fintype S] [DecidableEq S] [Fintype S'] [DecidableEq S'] [Fintype R] [DecidableEq R] in
@[simp] theorem siteEmb_apply (e : S' ≃ S ⊕ R) (s : S) : siteEmb e s = e.symm (.inl s) :=
  rfl

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
  (Equiv.piCongrLeft (fun t ↦ Sum.elim X W t) e).trans (Equiv.sumPiEquivProdPi _)

/-- The sites of a region are the sites of its image. -/
noncomputable def regionSiteEquiv (D : Finset S) :
    {v // v ∈ D} ≃ {v' // v' ∈ D.map (siteEmb e)} :=
  Equiv.ofBijective (fun v ↦ ⟨siteEmb e v.1, Finset.mem_map_of_mem _ v.2⟩) (by
    constructor
    · intro a b h
      exact Subtype.ext ((siteEmb e).injective (congrArg Subtype.val h))
    · rintro ⟨v', hv'⟩
      obtain ⟨s, hs, rfl⟩ := Finset.mem_map.mp hv'
      exact ⟨⟨s, hs⟩, rfl⟩)

omit [Fintype S] [DecidableEq S] [Fintype S'] [DecidableEq S'] [Fintype R] [DecidableEq R] [(r : R)
  → Fintype (W r)] [(r : R) → DecidableEq (W r)] in
theorem liftConfigEquiv_fst (X : S → Type) (z : Config (lift e W X)) (s : S) :
    (liftConfigEquiv e W X z).1 s =
      cast (congrArg (Sum.elim X W) (e.apply_symm_apply (.inl s))) (z (e.symm (.inl s))) := by
  change (Equiv.piCongrLeft (fun t ↦ Sum.elim X W t) e z) (.inl s) = _
  rw [Equiv.piCongrLeft_apply_eq_cast]

omit [Fintype S] [DecidableEq S] [Fintype S'] [DecidableEq S'] [Fintype R] [DecidableEq R] [(r : R)
  → Fintype (W r)] [(r : R) → DecidableEq (W r)] in
theorem liftConfigEquiv_snd (X : S → Type) (z : Config (lift e W X)) (r : R) :
    (liftConfigEquiv e W X z).2 r =
      cast (congrArg (Sum.elim X W) (e.apply_symm_apply (.inr r))) (z (e.symm (.inr r))) := by
  change (Equiv.piCongrLeft (fun t ↦ Sum.elim X W t) e z) (.inr r) = _
  rw [Equiv.piCongrLeft_apply_eq_cast]

/-- The configurations of the image of a region. -/
noncomputable def liftRegionEquiv (X : S → Type) (D : Finset S) :
    RegionConfig (lift e W X) (D.map (siteEmb e)) ≃ RegionConfig X D :=
  (Equiv.piCongrLeft (fun v' : {v' // v' ∈ D.map (siteEmb e)} ↦ lift e W X v'.1)
    (regionSiteEquiv e D)).symm.trans
    (Equiv.piCongrRight fun v ↦ liftSiteEquiv e W X v.1)

/-! ### Site maps from embeddings -/

section Split

variable {T : Type} [Fintype T] [DecidableEq T] {T' : Type} [Fintype T'] [DecidableEq T']

/-- The sites of `T'` outside the image of an embedding. -/
abbrev Idle (ι : T ↪ T') : Type := {s' // s' ∉ Finset.univ.map ι}

/-- The site map of an embedding `ι : T ↪ T'`: the sites of `T` at their images, and the sites
outside the image idle. -/
noncomputable def siteSplit (ι : T ↪ T') : T' ≃ T ⊕ Idle ι :=
  (Equiv.sumCompl (· ∈ Finset.univ.map ι)).symm.trans
    (Equiv.sumCongr (Equiv.ofBijective (fun s ↦ (⟨ι s, Finset.mem_map_of_mem _ (Finset.mem_univ s)⟩ :
        {s' // s' ∈ Finset.univ.map ι})) ⟨fun a b h ↦ ι.injective (congrArg Subtype.val h),
        fun ⟨s', hs'⟩ ↦ by
          obtain ⟨s, -, rfl⟩ := Finset.mem_map.mp hs'
          exact ⟨s, rfl⟩⟩).symm (Equiv.refl _))

omit [Fintype T'] in
@[simp] theorem siteEmb_siteSplit (ι : T ↪ T') : siteEmb (siteSplit ι) = ι := by
  ext s
  simp only [siteEmb_apply, siteSplit, Equiv.symm_trans_apply, Equiv.symm_symm,
    Equiv.sumCongr_symm, Equiv.sumCongr_apply, Sum.map_inl, Equiv.sumCompl_apply_inl]
  rfl

end Split

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

omit [Fintype S] [DecidableEq S] [Fintype S'] [DecidableEq S'] [Fintype R] [DecidableEq R] in
theorem KrausGate.isCompatible_transport :
    (KrausGate.transport e W).IsCompatible e W KrausGate.ev KrausGate.ev :=
  fun _ _ _ _ _ _ _ _ _ ↦ rfl

/-! ### Moving layers and circuits -/

variable {Γ : Geometry S} {Γ' : Geometry S'}

namespace Layer

variable {X Y : S → Type} [∀ s, Fintype (X s)] [∀ s, DecidableEq (X s)]
  [∀ s, Fintype (Y s)] [∀ s, DecidableEq (Y s)]

variable (h : Γ.Hom Γ' (siteEmb e)) (φ : GateTransport e W G G') (L : Layer Γ G X Y)

/-- The cells of a layer are the cells of its image. -/
noncomputable def cellsEquiv : L.cells ≃ {b' // b' ∈ L.cells.map h.cellMap} :=
  Equiv.ofBijective (fun b ↦ ⟨h.cellMap b.1, Finset.mem_map_of_mem _ b.2⟩) (by
    constructor
    · intro a b hab
      exact Subtype.ext (h.cellMap.injective (congrArg Subtype.val hab))
    · rintro ⟨b', hb'⟩
      obtain ⟨b, hb, rfl⟩ := Finset.mem_map.mp hb'
      exact ⟨⟨b, hb⟩, rfl⟩)

omit [Fintype S] [Fintype S'] [DecidableEq S'] [Fintype R] [DecidableEq R] [GateFamily G] [(s : S) →
  Fintype (X s)] [(s : S) → DecidableEq (X s)] [(s : S) → Fintype (Y s)] [(s : S) → DecidableEq (Y
  s)] in
theorem cell_cellsEquiv_symm (b' : {b' // b' ∈ L.cells.map h.cellMap}) :
    (Γ.cell ((L.cellsEquiv e h).symm b').1).map (siteEmb e) = Γ'.cell b'.1 := by
  rw [← h.cell_cellMap]
  exact congrArg (fun b ↦ Γ'.cell b.1) ((L.cellsEquiv e h).apply_symm_apply b')

/-- The onsite family of the moved layer at a site of `S ⊕ R`: that of the layer at a site of
`S`, the identity at an idle site. -/
noncomputable def liftOnsite : (t : S ⊕ R) → (∀ s, t = .inl s → s ∉ L.cells.biUnion Γ.cell) →
    KrausFamily (Sum.elim X W t) (Sum.elim Y W t)
  | .inl s, hs => L.onsite ⟨s, hs s rfl⟩
  | .inr r, _ => KrausFamily.single (1 : Matrix (W r) (W r) ℂ)

omit [Fintype S] [Fintype S'] [Fintype R] [DecidableEq R] [GateFamily G] [(s : S) → Fintype (X s)]
  [(s : S) → DecidableEq (X s)] [(s : S) → Fintype (Y s)] [(s : S) → DecidableEq (Y s)] in
theorem not_mem_of_mapSites {s' : S'}
    (hs' : s' ∉ (L.cells.map h.cellMap).biUnion Γ'.cell) :
    ∀ s, e s' = .inl s → s ∉ L.cells.biUnion Γ.cell := by
  intro s hs hmem
  obtain ⟨b, hb, hsb⟩ := Finset.mem_biUnion.mp hmem
  refine hs' (Finset.mem_biUnion.mpr ⟨h.cellMap b, Finset.mem_map_of_mem _ hb, ?_⟩)
  rw [h.cell_cellMap]
  have : s' = siteEmb e s := by
    change s' = e.symm (.inl s)
    rw [← hs, Equiv.symm_apply_apply]
  rw [this]
  exact Finset.mem_map_of_mem _ hsb

/-- The layer moved along `e`, the morphism of geometries `h` and the transport `φ`: the
transported gates on the image cells, the onsite families at the sites of `S`, and the
identity at the idle sites. -/
noncomputable def mapSites : Layer Γ' G' (lift e W X) (lift e W Y) where
  cells := L.cells.map h.cellMap
  pairwiseDisjoint := by
    intro b₁ hb₁ b₂ hb₂ hne
    obtain ⟨c₁, hc₁, rfl⟩ := Finset.mem_map.mp hb₁
    obtain ⟨c₂, hc₂, rfl⟩ := Finset.mem_map.mp hb₂
    simp only [Function.onFun, h.cell_cellMap, Finset.disjoint_map]
    exact L.pairwiseDisjoint hc₁ hc₂ fun hc ↦ hne (congrArg _ hc)
  gate b' := Eq.ndrec (motive := fun D ↦ G' D (lift e W X) (lift e W Y))
    (φ.map (L.gate ((L.cellsEquiv e h).symm b'))) (L.cell_cellsEquiv_symm e h b')
  onsite s' := L.liftOnsite W (e s') (L.not_mem_of_mapSites e h s'.2)

omit [∀ s, Fintype (X s)] [∀ s, DecidableEq (X s)] [∀ s, Fintype (Y s)]
  [∀ s, DecidableEq (Y s)] in
/-- The outcomes of a gate moved to an equal region. -/
def outcomeNdrec {D D' : Finset S'} (hD : D = D') (g : G' D (lift e W X) (lift e W Y)) :
    GateFamily.Outcome (Eq.ndrec (motive := fun D ↦ G' D (lift e W X) (lift e W Y)) g hD) ≃
      GateFamily.Outcome g := by
  subst hD; exact Equiv.refl _

/-- The cells of a layer are the cells of the moved layer. -/
noncomputable def mapSitesCellsEquiv : L.cells ≃ (L.mapSites e W h φ).cells :=
  L.cellsEquiv e h

/-- The idle and non-idle free sites of the moved layer. -/
noncomputable def freeEquiv : L.Free ⊕ R ≃ (L.mapSites e W h φ).Free :=
  Equiv.ofBijective
    (Sum.elim (fun s ↦ ⟨siteEmb e s.1, fun hmem ↦ by
        obtain ⟨b', hb', hsb⟩ := Finset.mem_biUnion.mp hmem
        obtain ⟨b, hb, rfl⟩ := Finset.mem_map.mp hb'
        rw [h.cell_cellMap] at hsb
        obtain ⟨t, ht, hts⟩ := Finset.mem_map.mp hsb
        obtain rfl := (siteEmb e).injective hts
        exact s.2 (Finset.mem_biUnion.mpr ⟨b, hb, ht⟩)⟩)
      (fun r ↦ ⟨e.symm (.inr r), fun hmem ↦ by
        obtain ⟨b', hb', hsb⟩ := Finset.mem_biUnion.mp hmem
        obtain ⟨b, hb, rfl⟩ := Finset.mem_map.mp hb'
        rw [h.cell_cellMap] at hsb
        obtain ⟨t, ht, hts⟩ := Finset.mem_map.mp hsb
        simp at hts⟩)) (by
    constructor
    · rintro (a | a) (b | b) hab
      · simp only [Sum.elim_inl, Subtype.mk.injEq, siteEmb_apply, EmbeddingLike.apply_eq_iff_eq,
          Sum.inl.injEq] at hab
        exact congrArg _ (Subtype.ext hab)
      · simp [siteEmb_apply] at hab
      · simp [siteEmb_apply] at hab
      · simp only [Sum.elim_inr, Subtype.mk.injEq, EmbeddingLike.apply_eq_iff_eq,
          Sum.inr.injEq] at hab
        exact congrArg _ hab
    · rintro ⟨s', hs'⟩
      rcases hes : e s' with s | r
      · refine ⟨.inl ⟨s, L.not_mem_of_mapSites e h hs' s hes⟩, Subtype.ext ?_⟩
        simp [← hes]
      · exact ⟨.inr r, Subtype.ext (by simp [← hes])⟩)

omit [∀ s, Fintype (X s)] [∀ s, DecidableEq (X s)] [∀ s, Fintype (Y s)]
  [∀ s, DecidableEq (Y s)] in
/-- The Kraus indices of the onsite family of the moved layer at a site of `S`. -/
def liftOnsiteIndexEquiv {t : S ⊕ R} (ht : ∀ s, t = .inl s → s ∉ L.cells.biUnion Γ.cell)
    {s : S} (hts : t = .inl s) :
    (L.liftOnsite W t ht).Index ≃ (L.onsite ⟨s, ht s hts⟩).Index := by
  subst hts; exact Equiv.refl _

omit [∀ s, Fintype (X s)] [∀ s, DecidableEq (X s)] [∀ s, Fintype (Y s)]
  [∀ s, DecidableEq (Y s)] in
/-- The Kraus index of the onsite family of the moved layer at an idle site is trivial. -/
def liftOnsiteIndexEquivInr {t : S ⊕ R} (ht : ∀ s, t = .inl s → s ∉ L.cells.biUnion Γ.cell)
    {r : R} (htr : t = .inr r) : (L.liftOnsite W t ht).Index ≃ Unit := by
  subst htr; exact Equiv.refl _

/-- The Kraus indices of the moved layer are those of the layer. -/
noncomputable def mapSitesIndexEquiv : (L.mapSites e W h φ).Index ≃ L.Index :=
  Equiv.prodCongr
    ((Equiv.piCongrLeft (fun b' ↦ GateFamily.Outcome ((L.mapSites e W h φ).gate b'))
      (L.cellsEquiv e h)).symm.trans (Equiv.piCongrRight fun b ↦
        (outcomeNdrec e W _ _).trans ((φ.outcome _).trans (Equiv.cast (congrArg
          (fun c ↦ GateFamily.Outcome (L.gate c)) ((L.cellsEquiv e h).symm_apply_apply b))))))
    (((Equiv.piCongrLeft (fun s' ↦ ((L.mapSites e W h φ).onsite s').Index)
      (L.freeEquiv e W h φ)).symm.trans (Equiv.sumPiEquivProdPi _)).trans
      ((Equiv.prodCongr (Equiv.piCongrRight fun s ↦ L.liftOnsiteIndexEquiv W _
          (s := s.1) (by simp [freeEquiv]))
        (Equiv.piCongrRight fun r ↦ L.liftOnsiteIndexEquivInr W _ (r := r)
          (by simp [freeEquiv]))).trans
        ((Equiv.prodCongr (Equiv.refl _) (Equiv.ofUnique (R → Unit) PUnit.{1})).trans
          (Equiv.prodPUnit _))))

omit [∀ s, Fintype (X s)] [∀ s, DecidableEq (X s)] [∀ s, Fintype (Y s)]
  [∀ s, DecidableEq (Y s)] in
omit [Fintype S] [DecidableEq S] [Fintype S'] [DecidableEq S'] [Fintype R] [DecidableEq R] [(r : R)
  → Fintype (W r)] [(r : R) → DecidableEq (W r)] in
theorem liftRegionEquiv_restrict {Z : S → Type} (D : Finset S) (z : Config (lift e W Z)) :
    liftRegionEquiv e W Z D (fun v : {v // v ∈ D.map (siteEmb e)} ↦ z v.1) =
      fun v : {v // v ∈ D} ↦ (liftConfigEquiv e W Z z).1 v.1 := by
  funext v
  change liftSiteEquiv e W Z v.1 (z (e.symm (.inl v.1))) =
    (Equiv.piCongrLeft (fun t ↦ Sum.elim Z W t) e z) (.inl v.1)
  rw [Equiv.piCongrLeft_apply_eq_cast]
  rfl

omit [Fintype S] [Fintype R] [DecidableEq R] [DecidableEq S] [Fintype S'] [DecidableEq S'] [(r : R)
  → Fintype (W r)] [(r : R) → DecidableEq (W r)] in
theorem ev_ndrec {ev' : Interpretation G'} {X' Y' : S → Type}
    [∀ s', Fintype (lift e W X' s')] [∀ s', DecidableEq (lift e W X' s')]
    [∀ s', Fintype (lift e W Y' s')] [∀ s', DecidableEq (lift e W Y' s')]
    {D D' : Finset S'} (hD : D = D') (g : G' D (lift e W X') (lift e W Y'))
    (o : GateFamily.Outcome (Eq.ndrec (motive := fun D ↦ G' D (lift e W X') (lift e W Y')) g hD))
    (y : Config (lift e W Y')) (x : Config (lift e W X')) :
    ev' (Eq.ndrec (motive := fun D ↦ G' D (lift e W X') (lift e W Y')) g hD) o
        (fun v ↦ y v) (fun v ↦ x v) =
      ev' g (outcomeNdrec e W hD g o) (fun v ↦ y v) (fun v ↦ x v) := by
  subst hD; rfl

omit [Fintype S] in
theorem ev_gate_congr (ev : Interpretation G) {c₁ c₂ : L.cells} (hc : c₁ = c₂)
    (o : GateFamily.Outcome (L.gate c₁)) (y : Config Y) (x : Config X) :
    ev (L.gate c₁) o (fun v ↦ y v) (fun v ↦ x v) =
      ev (L.gate c₂) (Equiv.cast (congrArg (fun c ↦ GateFamily.Outcome (L.gate c)) hc) o)
        (fun v ↦ y v) (fun v ↦ x v) := by
  subst hc; rfl

omit [Fintype S] [Fintype R] [DecidableEq R] [(r : R) → Fintype (W r)] [GateFamily G] [(s : S) →
  Fintype (X s)] [(s : S) → DecidableEq (X s)] [(s : S) → Fintype (Y s)] [(s : S) → DecidableEq (Y
  s)] in
theorem liftOnsite_op_inl {t : S ⊕ R} (ht : ∀ s, t = .inl s → s ∉ L.cells.biUnion Γ.cell)
    {s : S} (hts : t = .inl s) (o : (L.liftOnsite W t ht).Index) (a : Sum.elim Y W t)
    (b : Sum.elim X W t) :
    (L.liftOnsite W t ht).op o a b = (L.onsite ⟨s, ht s hts⟩).op
      (L.liftOnsiteIndexEquiv W ht hts o) (cast (congrArg (Sum.elim Y W) hts) a)
      (cast (congrArg (Sum.elim X W) hts) b) := by
  subst hts; rfl

omit [Fintype S] [Fintype R] [DecidableEq R] [(r : R) → Fintype (W r)] [GateFamily G] [(s : S) →
  Fintype (X s)] [(s : S) → DecidableEq (X s)] [(s : S) → Fintype (Y s)] [(s : S) → DecidableEq (Y
  s)] in
theorem liftOnsite_op_inr {t : S ⊕ R} (ht : ∀ s, t = .inl s → s ∉ L.cells.biUnion Γ.cell)
    {r : R} (htr : t = .inr r) (o : (L.liftOnsite W t ht).Index) (a : Sum.elim Y W t)
    (b : Sum.elim X W t) :
    (L.liftOnsite W t ht).op o a b = (1 : Matrix (W r) (W r) ℂ)
      (cast (congrArg (Sum.elim Y W) htr) a) (cast (congrArg (Sum.elim X W) htr) b) := by
  subst htr; rfl

omit [(r : R) → Fintype (W r)] [Fintype S] [Fintype S'] [Fintype R] [DecidableEq R] [(s : S) →
  Fintype (X s)] [(s : S) → DecidableEq (X s)] [(s : S) → Fintype (Y s)] [(s : S) → DecidableEq (Y
  s)] in
theorem mapSites_gate (b' : (L.mapSites e W h φ).cells) :
    (L.mapSites e W h φ).gate b' = Eq.ndrec (motive := fun D ↦ G' D (lift e W X) (lift e W Y))
      (φ.map (L.gate ((L.cellsEquiv e h).symm b'))) (L.cell_cellsEquiv_symm e h b') :=
  rfl

omit [Fintype S] [Fintype S'] [Fintype R] [DecidableEq R] in
theorem ev_mapSites_gate {ev' : Interpretation G'} (b' : (L.mapSites e W h φ).cells)
    (o : GateFamily.Outcome ((L.mapSites e W h φ).gate b')) (y : Config (lift e W Y))
    (x : Config (lift e W X)) :
    ev' ((L.mapSites e W h φ).gate b') o (fun v ↦ y v) (fun v ↦ x v) =
      ev' (φ.map (L.gate ((L.cellsEquiv e h).symm b'))) (outcomeNdrec e W _ _ o)
        (fun v ↦ y v) (fun v ↦ x v) :=
  ev_ndrec e W (X' := X) (Y' := Y) _ _ o y x

omit [Fintype S] [Fintype S'] [Fintype R] [DecidableEq R] [(r : R) → Fintype (W r)] [(s : S) →
  Fintype (X s)] [(s : S) → DecidableEq (X s)] [(s : S) → Fintype (Y s)] [(s : S) → DecidableEq (Y
  s)] in
theorem onsite_op_freeEquiv_inl (a : L.Free)
    (o : ((L.mapSites e W h φ).onsite (L.freeEquiv e W h φ (.inl a))).Index)
    (yv : lift e W Y (L.freeEquiv e W h φ (.inl a)).1)
    (xv : lift e W X (L.freeEquiv e W h φ (.inl a)).1) :
    ((L.mapSites e W h φ).onsite (L.freeEquiv e W h φ (.inl a))).op o yv xv =
      (L.onsite a).op (L.liftOnsiteIndexEquiv W _ (e.apply_symm_apply (.inl a.1)) o)
        (cast (congrArg (Sum.elim Y W) (e.apply_symm_apply (.inl a.1))) yv)
        (cast (congrArg (Sum.elim X W) (e.apply_symm_apply (.inl a.1))) xv) :=
  L.liftOnsite_op_inl W _ (e.apply_symm_apply (.inl a.1)) o yv xv

omit [Fintype S] [Fintype S'] [Fintype R] [DecidableEq R] [(r : R) → Fintype (W r)] [(s : S) →
  Fintype (X s)] [(s : S) → DecidableEq (X s)] [(s : S) → Fintype (Y s)] [(s : S) → DecidableEq (Y
  s)] in
theorem onsite_op_freeEquiv_inr (r : R)
    (o : ((L.mapSites e W h φ).onsite (L.freeEquiv e W h φ (.inr r))).Index)
    (yv : lift e W Y (L.freeEquiv e W h φ (.inr r)).1)
    (xv : lift e W X (L.freeEquiv e W h φ (.inr r)).1) :
    ((L.mapSites e W h φ).onsite (L.freeEquiv e W h φ (.inr r))).op o yv xv =
      (1 : Matrix (W r) (W r) ℂ) (cast (congrArg (Sum.elim Y W) (e.apply_symm_apply (.inr r))) yv)
        (cast (congrArg (Sum.elim X W) (e.apply_symm_apply (.inr r))) xv) :=
  L.liftOnsite_op_inr W _ (e.apply_symm_apply (.inr r)) o yv xv

omit [DecidableEq R] in
/-- The Kraus operators of the moved layer are those of the layer tensored with the identity on
the idle sites. -/
theorem kraus_mapSites (h : Γ.Hom Γ' (siteEmb e)) (φ : GateTransport e W G G')
    {ev : Interpretation G} {ev' : Interpretation G'} (hφ : φ.IsCompatible e W ev ev')
    (L : Layer Γ G X Y) (i : (L.mapSites e W h φ).Index) :
    (L.mapSites e W h φ).kraus ev' i =
      (L.kraus ev (L.mapSitesIndexEquiv e W h φ i) ⊗ₖ (1 : Matrix ((r : R) → W r) _ ℂ)).submatrix
        (liftConfigEquiv e W Y) (liftConfigEquiv e W X) := by
  ext y x
  rw [submatrix_apply, kronecker_apply]
  simp only [kraus]
  rw [← Fintype.prod_equiv (L.mapSitesCellsEquiv e W h φ) _ _ fun _ ↦ rfl,
    ← Fintype.prod_equiv (L.freeEquiv e W h φ) _ _ fun _ ↦ rfl, Fintype.prod_sum_type,
    mul_assoc]
  congr 1
  · refine Finset.prod_congr rfl fun b _ ↦ ?_
    rw [L.ev_mapSites_gate e W h φ (ev' := ev')]
    refine (congrFun (congrFun (hφ _ _) _) _).trans ?_
    rw [submatrix_apply, liftRegionEquiv_restrict, liftRegionEquiv_restrict]
    exact ev_gate_congr L ev ((L.cellsEquiv e h).symm_apply_apply b) _ _ _
  · congr 1
    · refine Finset.prod_congr rfl fun a _ ↦ ?_
      rw [L.onsite_op_freeEquiv_inl e W h φ, liftConfigEquiv_fst, liftConfigEquiv_fst]
      rfl
    · rw [Finset.prod_congr rfl fun r _ ↦ L.onsite_op_freeEquiv_inr e W h φ r _ _ _]
      simp only [one_apply, Finset.prod_boole, Finset.mem_univ, true_implies]
      refine if_congr ?_ rfl rfl
      rw [funext_iff]
      simp only [liftConfigEquiv_snd]
      exact Iff.rfl

omit [(r : R) → Fintype (W r)] [Fintype S] [Fintype S'] [Fintype R] [DecidableEq R] [(s : S) →
  Fintype (X s)] [(s : S) → DecidableEq (X s)] [(s : S) → Fintype (Y s)] [(s : S) → DecidableEq (Y
  s)] in
theorem lightCone_mapSites (T : Finset S) :
    (L.mapSites e W h φ).lightCone (T.map (siteEmb e)) = (L.lightCone T).map (siteEmb e) := by
  simp only [lightCone, mapSites, Finset.filter_map, Finset.map_union, Function.comp_def,
    h.cell_cellMap, ← Finset.map_inter, Finset.map_nonempty]
  congr 1
  ext v
  simp only [Finset.mem_biUnion, Finset.mem_map]
  constructor
  · rintro ⟨_, ⟨b, hb, rfl⟩, hv⟩
    rw [h.cell_cellMap] at hv
    obtain ⟨t, ht, rfl⟩ := Finset.mem_map.mp hv
    exact ⟨t, ⟨b, hb, ht⟩, rfl⟩
  · rintro ⟨t, ⟨b, hb, ht⟩, rfl⟩
    exact ⟨h.cellMap b, ⟨b, hb, rfl⟩, by rw [h.cell_cellMap]; exact Finset.mem_map_of_mem _ ht⟩

omit [(r : R) → Fintype (W r)] [Fintype S] [Fintype S'] [Fintype R] [DecidableEq R] [(s : S) →
  Fintype (X s)] [(s : S) → DecidableEq (X s)] [(s : S) → Fintype (Y s)] [(s : S) → DecidableEq (Y
  s)] in
theorem gateCount_mapSites :
    (L.mapSites e W h φ).gateCount = ∑ b ∈ L.cells, Γ'.cost (h.cellMap b) := by
  rw [gateCount_eq_sum]
  exact Finset.sum_map _ _ _

omit [(r : R) → Fintype (W r)] [Fintype S] [Fintype S'] [Fintype R] [DecidableEq R] [(s : S) →
  Fintype (X s)] [(s : S) → DecidableEq (X s)] [(s : S) → Fintype (Y s)] [(s : S) → DecidableEq (Y
  s)] in
theorem depth_mapSites_le (hcost : ∀ b, 0 < Γ'.cost (h.cellMap b) → 0 < Γ.cost b) :
    (L.mapSites e W h φ).depth ≤ L.depth := by
  unfold depth
  split_ifs with h₁ h₂ <;> try omega
  obtain ⟨b', hb'⟩ := h₁
  rw [Finset.mem_filter] at hb'
  obtain ⟨b, hb, rfl⟩ := Finset.mem_map.mp hb'.1
  exact absurd ⟨b, Finset.mem_filter.mpr ⟨hb, hcost b hb'.2⟩⟩ h₂

end Layer

namespace Circuit

/-- The circuit moved along `e`, the morphism of geometries `h` and the transport `φ`. -/
noncomputable def mapSites (h : Γ.Hom Γ' (siteEmb e)) (φ : GateTransport e W G G') :
    {X Z : S → Type} → [∀ s, Fintype (X s)] → [∀ s, DecidableEq (X s)] →
      Circuit Γ G X Z → Circuit Γ' G' (lift e W X) (lift e W Z)
  | _, _, _, _, done _ => done _
  | _, _, _, _, step L next =>
      step (L.mapSites e W h φ) fun i ↦ (next (L.mapSitesIndexEquiv e W h φ i)).mapSites h φ

/-- The branches of the moved circuit are those of the circuit. -/
noncomputable def mapSitesIndexEquiv (h : Γ.Hom Γ' (siteEmb e)) (φ : GateTransport e W G G') :
    {X Z : S → Type} → [∀ s, Fintype (X s)] → [∀ s, DecidableEq (X s)] →
      (c : Circuit Γ G X Z) → (c.mapSites e W h φ).Index ≃ c.Index
  | _, _, _, _, done _ => Equiv.refl Unit
  | _, _, _, _, step L next =>
      Equiv.sigmaCongr (L.mapSitesIndexEquiv e W h φ) fun i ↦
        (next (L.mapSitesIndexEquiv e W h φ i)).mapSitesIndexEquiv h φ

omit [DecidableEq R] in
/-- The Kraus operators of the moved circuit are those of the circuit tensored with the
identity on the idle sites. -/
theorem kraus_mapSites (h : Γ.Hom Γ' (siteEmb e)) (φ : GateTransport e W G G')
    {ev : Interpretation G} {ev' : Interpretation G'} (hφ : φ.IsCompatible e W ev ev') :
    {X Z : S → Type} → [∀ s, Fintype (X s)] → [∀ s, DecidableEq (X s)] →
      (c : Circuit Γ G X Z) →
      (p : (c.mapSites e W h φ).Index) →
      (c.mapSites e W h φ).kraus ev' p =
        (c.kraus ev (c.mapSitesIndexEquiv e W h φ p) ⊗ₖ
          (1 : Matrix ((r : R) → W r) _ ℂ)).submatrix (liftConfigEquiv e W Z)
          (liftConfigEquiv e W X)
  | _, _, _, _, done _, p => by
      change (1 : Matrix _ _ ℂ) = ((1 : Matrix _ _ ℂ) ⊗ₖ (1 : Matrix _ _ ℂ)).submatrix _ _
      rw [one_kronecker_one, submatrix_one_equiv]
  | _, _, _, _, step L next, q => by
      classical
      obtain ⟨i, p⟩ := q
      change ((next (L.mapSitesIndexEquiv e W h φ i)).mapSites e W h φ).kraus ev' p *
        (L.mapSites e W h φ).kraus ev' i = _
      rw [kraus_mapSites h φ hφ _ p, Layer.kraus_mapSites e W h φ hφ L i]
      change _ = ((kraus ev (next _) _ * L.kraus ev _) ⊗ₖ _).submatrix _ _
      rw [submatrix_mul_equiv, ← mul_kronecker_mul, Matrix.mul_one]
      rfl

variable {X Z : S → Type} [∀ s, Fintype (X s)] [∀ s, DecidableEq (X s)]
  [∀ s, Fintype (Z s)] [∀ s, DecidableEq (Z s)]

omit [Fintype S] [Fintype S'] [Fintype R] [DecidableEq R] in
theorem isUnbranched_mapSites (h : Γ.Hom Γ' (siteEmb e)) (φ : GateTransport e W G G') :
    {X Z : S → Type} → [∀ s, Fintype (X s)] → [∀ s, DecidableEq (X s)] →
      {c : Circuit Γ G X Z} → c.IsUnbranched → (c.mapSites e W h φ).IsUnbranched
  | _, _, _, _, done _, _ => trivial
  | _, _, _, _, step L next, hc =>
    ⟨fun i j ↦ by
      change (next _).mapSites e W h φ = (next _).mapSites e W h φ
      rw [hc.1 _ _],
      fun i ↦ isUnbranched_mapSites h φ (hc.2 _)⟩

omit [Fintype R] [DecidableEq R] in
/-- A cost of the moved layers bounded by a cost of the layers bounds the cost of the moved
circuit. -/
theorem total_mapSites_le (h : Γ.Hom Γ' (siteEmb e)) (φ : GateTransport e W G G')
    (f : ∀ ⦃X Y : S → Type⦄, Layer Γ G X Y → ℕ) (f' : ∀ ⦃X Y : S' → Type⦄, Layer Γ' G' X Y → ℕ)
    (hf : ∀ ⦃X Y : S → Type⦄ [∀ s, Fintype (X s)] [∀ s, DecidableEq (X s)]
      [∀ s, Fintype (Y s)] [∀ s, DecidableEq (Y s)] (L : Layer Γ G X Y),
      f' (L.mapSites e W h φ) ≤ f L) :
    {X Z : S → Type} → [∀ s, Fintype (X s)] → [∀ s, DecidableEq (X s)] →
      (c : Circuit Γ G X Z) → (c.mapSites e W h φ).total f' ≤ c.total f
  | _, _, _, _, done _ => le_rfl
  | _, _, _, _, step L next => by
    change f' (L.mapSites e W h φ) + Finset.univ.sup (fun i ↦
      ((next (L.mapSitesIndexEquiv e W h φ i)).mapSites e W h φ).total f') ≤
      f L + Finset.univ.sup fun i ↦ (next i).total f
    exact add_le_add (hf L) (Finset.sup_le fun i _ ↦
      (total_mapSites_le h φ f f' hf _).trans (Finset.le_sup (f := fun i ↦ (next i).total f)
        (Finset.mem_univ _)))

omit [Fintype S] [Fintype S'] [Fintype R] [DecidableEq R] in
/-- A local property invariant under relabelling of bases and of Kraus indices, held by the
identity, moves along with every transported gate. -/
theorem forall_mapSites (h : Γ.Hom Γ' (siteEmb e)) (φ : GateTransport e W G G')
    {ev : Interpretation G} {ev' : Interpretation G'} (hφ : φ.IsCompatible e W ev ev')
    {P : ∀ {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β],
      KrausFamily α β → Prop}
    (hP : ∀ {α β α' β' ι : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
      [Fintype α'] [DecidableEq α'] [Fintype β'] [DecidableEq β'] [Fintype ι]
      (K : KrausFamily α β) (u : ι ≃ K.Index) (a : α' ≃ α) (b : β' ≃ β),
      P K → P ⟨ι, fun i ↦ (K.op (u i)).submatrix b a⟩)
    (hone : ∀ {α : Type} [Fintype α] [DecidableEq α], P (KrausFamily.single (1 : Matrix α α ℂ))) :
    {X Z : S → Type} → [∀ s, Fintype (X s)] → [∀ s, DecidableEq (X s)] →
      {c : Circuit Γ G X Z} → c.Forall ev P → (c.mapSites e W h φ).Forall ev' P
  | _, _, _, _, done _, _ => trivial
  | _, _, _, _, @step _ _ _ _ _ X₀ Y₀ _ _ _ L next, hc => by
    refine ⟨⟨fun b' ↦ ?_, fun s' ↦ ?_⟩, fun i ↦ forall_mapSites h φ hφ hP hone (hc.2 _)⟩
    · have hgen : ∀ {D D' : Finset S'} (hD : D = D') (g : G' D (lift e W X₀) (lift e W Y₀)),
          P (⟨GateFamily.Outcome g, ev' g⟩ : KrausFamily (RegionConfig (lift e W X₀) D)
            (RegionConfig (lift e W Y₀) D)) →
          P (⟨GateFamily.Outcome (Eq.ndrec (motive := fun D ↦ G' D (lift e W X₀) (lift e W Y₀))
              g hD), ev' (Eq.ndrec (motive := fun D ↦ G' D (lift e W X₀) (lift e W Y₀)) g hD)⟩ :
              KrausFamily (RegionConfig (lift e W X₀) D') (RegionConfig (lift e W Y₀) D')) := by
        intro D D' hD g hg; subst hD; exact hg
      refine hgen _ _ ?_
      have hK := hP _ (φ.outcome _) (liftRegionEquiv e W _ _) (liftRegionEquiv e W _ _)
        (hc.1.1 ((L.cellsEquiv e h).symm b'))
      rw [show ev' (φ.map (L.gate ((L.cellsEquiv e h).symm b'))) = fun o ↦
        (ev (L.gate ((L.cellsEquiv e h).symm b')) (φ.outcome _ o)).submatrix
          (liftRegionEquiv e W _ _) (liftRegionEquiv e W _ _) from funext (hφ _)]
      exact hK
    · have hgen : ∀ (t : S ⊕ R) (ht : ∀ s, t = .inl s → s ∉ L.cells.biUnion Γ.cell),
          P (L.liftOnsite W t ht) := by
        rintro (s | r) ht
        · exact hc.1.2 _
        · exact hone
      exact hgen _ _

omit [Fintype R] [DecidableEq R] in
/-- The light cone of the image of a region is the image of its light cone. -/
theorem lightCone_mapSites (h : Γ.Hom Γ' (siteEmb e)) (φ : GateTransport e W G G')
    (T : Finset S) : {X Z : S → Type} → [∀ s, Fintype (X s)] → [∀ s, DecidableEq (X s)] →
      (c : Circuit Γ G X Z) →
      (c.mapSites e W h φ).lightCone (T.map (siteEmb e)) = (c.lightCone T).map (siteEmb e)
  | _, _, _, _, done _ => rfl
  | _, _, _, _, step L next => by
    change (L.mapSites e W h φ).lightCone (Finset.univ.sup fun i ↦
      ((next (L.mapSitesIndexEquiv e W h φ i)).mapSites e W h φ).lightCone
        (T.map (siteEmb e))) = (L.lightCone (Finset.univ.sup fun i ↦ (next i).lightCone T)).map
        (siteEmb e)
    simp only [lightCone_mapSites h φ T]
    rw [← Layer.lightCone_mapSites e W h φ]
    congr 1
    ext v
    simp only [Finset.mem_sup, Finset.mem_univ, true_and, Finset.mem_map]
    constructor
    · rintro ⟨i, t, ht, rfl⟩
      exact ⟨t, ⟨_, ht⟩, rfl⟩
    · rintro ⟨t, ⟨i, ht⟩, rfl⟩
      exact ⟨(L.mapSitesIndexEquiv e W h φ).symm i, t, by simpa using ht, rfl⟩

omit [(s : S) → Fintype (Z s)] [(s : S) → DecidableEq (Z s)] [Fintype R] [DecidableEq R] in
/-- When no cell costs more after the move, neither does the circuit. -/
theorem gateCount_mapSites_le (h : Γ.Hom Γ' (siteEmb e)) (φ : GateTransport e W G G')
    (hcost : ∀ b, Γ'.cost (h.cellMap b) ≤ Γ.cost b) (c : Circuit Γ G X Z) :
    (c.mapSites e W h φ).gateCount ≤ c.gateCount :=
  total_mapSites_le e W h φ _ _ (fun _ _ _ _ _ _ L ↦ by
    rw [L.gateCount_mapSites e W h φ, Layer.gateCount_eq_sum]
    exact Finset.sum_le_sum fun b _ ↦ hcost b) c

omit [(s : S) → Fintype (Z s)] [(s : S) → DecidableEq (Z s)] [Fintype R] [DecidableEq R] in
/-- When a cell of positive cost after the move had positive cost before, the depth does not
grow. -/
theorem depth_mapSites_le (h : Γ.Hom Γ' (siteEmb e)) (φ : GateTransport e W G G')
    (hcost : ∀ b, 0 < Γ'.cost (h.cellMap b) → 0 < Γ.cost b) (c : Circuit Γ G X Z) :
    (c.mapSites e W h φ).depth ≤ c.depth :=
  total_mapSites_le e W h φ _ _ (fun _ _ _ _ _ _ L ↦ L.depth_mapSites_le e W h φ hcost) c

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

variable {ev₁ : Interpretation G₁} {ev₂ : Interpretation G₂} {Δ : Geometry S}

theorem Geometry.Hom.cell_eq (h : Γ.Hom Δ (Function.Embedding.refl S)) (b : Γ.Cell) :
    Δ.cell (h.cellMap b) = Γ.cell b := by
  rw [h.cell_cellMap, Finset.map_refl]

/-- The cells of a finite set are the cells of its image. -/
noncomputable def Geometry.Hom.cellsEquiv {S S' : Type} {Γ : Geometry S} {Γ' : Geometry S'}
    {ι : S ↪ S'} (h : Γ.Hom Γ' ι) (s : Finset Γ.Cell) : s ≃ {b' // b' ∈ s.map h.cellMap} :=
  Equiv.ofBijective (fun b ↦ ⟨h.cellMap b.1, Finset.mem_map_of_mem _ b.2⟩) (by
    constructor
    · intro a b hab
      exact Subtype.ext (h.cellMap.injective (congrArg Subtype.val hab))
    · rintro ⟨b', hb'⟩
      obtain ⟨b, hb, rfl⟩ := Finset.mem_map.mp hb'
      exact ⟨⟨b, hb⟩, rfl⟩)

namespace Layer

variable {X Y : S → Type}

omit [Fintype S'] [DecidableEq S'] [Fintype R] [DecidableEq R] [GateFamily G₁]
  [GateFamily G₂] in
theorem cell_cellsEquiv_symm_eq (h : Γ.Hom Δ (Function.Embedding.refl S)) (L : Layer Γ G₁ X Y)
    (b' : {b' // b' ∈ L.cells.map h.cellMap}) :
    Γ.cell ((h.cellsEquiv L.cells).symm b').1 = Δ.cell b'.1 := by
  rw [← h.cell_eq]
  exact congrArg (fun b ↦ Δ.cell b.1) ((h.cellsEquiv L.cells).apply_symm_apply b')

omit [Fintype S'] [DecidableEq S'] [Fintype R] [DecidableEq R] [GateFamily G₁]
  [GateFamily G₂] in
theorem mem_biUnion_map_iff (h : Γ.Hom Δ (Function.Embedding.refl S)) (L : Layer Γ G₁ X Y)
    (s : S) : s ∈ (L.cells.map h.cellMap).biUnion Δ.cell ↔ s ∈ L.cells.biUnion Γ.cell := by
  simp only [Finset.mem_biUnion, Finset.mem_map, h.cell_eq]
  constructor
  · rintro ⟨_, ⟨b, hb, rfl⟩, hs⟩
    exact ⟨b, hb, by rwa [h.cell_eq] at hs⟩
  · rintro ⟨b, hb, hs⟩
    exact ⟨h.cellMap b, ⟨b, hb, rfl⟩, by rwa [h.cell_eq]⟩

/-- The layer with its cells moved along `h` and its gates along `φ`, on the same sites and
systems. -/
noncomputable def mapGate (h : Γ.Hom Δ (Function.Embedding.refl S))
    (φ : GateMorphism G₁ G₂ ev₁ ev₂) (L : Layer Γ G₁ X Y) : Layer Δ G₂ X Y where
  cells := L.cells.map h.cellMap
  pairwiseDisjoint := by
    intro b₁ hb₁ b₂ hb₂ hne
    obtain ⟨c₁, hc₁, rfl⟩ := Finset.mem_map.mp hb₁
    obtain ⟨c₂, hc₂, rfl⟩ := Finset.mem_map.mp hb₂
    simp only [Function.onFun, h.cell_eq]
    exact L.pairwiseDisjoint hc₁ hc₂ fun hc ↦ hne (congrArg _ hc)
  gate b' := Eq.ndrec (motive := fun D ↦ G₂ D X Y)
    (φ.map (L.gate ((h.cellsEquiv L.cells).symm b'))) (L.cell_cellsEquiv_symm_eq h b')
  onsite s := L.onsite ⟨s.1, fun hs ↦ s.2 ((L.mem_biUnion_map_iff h s.1).mpr hs)⟩

/-- The cells of a layer are the cells of the layer with its cells moved. -/
noncomputable def mapGateCellsEquiv (h : Γ.Hom Δ (Function.Embedding.refl S))
    (φ : GateMorphism G₁ G₂ ev₁ ev₂) (L : Layer Γ G₁ X Y) : L.cells ≃ (L.mapGate h φ).cells :=
  h.cellsEquiv L.cells

omit [Fintype S'] [DecidableEq S'] [Fintype R] [DecidableEq R] [GateFamily G₁] in
/-- The outcomes of a gate moved to an equal region. -/
def outcomeNdrec' {D D' : Finset S} (hD : D = D') (g : G₂ D X Y) :
    GateFamily.Outcome (Eq.ndrec (motive := fun D ↦ G₂ D X Y) g hD) ≃ GateFamily.Outcome g := by
  subst hD; exact Equiv.refl _

omit [Fintype S'] [DecidableEq S'] [Fintype R] [DecidableEq R] [GateFamily G₁] [GateFamily G₂] in
/-- The free sites of a layer with its cells moved. -/
def mapGateFreeEquiv (h : Γ.Hom Δ (Function.Embedding.refl S)) (φ : GateMorphism G₁ G₂ ev₁ ev₂)
    (L : Layer Γ G₁ X Y) : (L.mapGate h φ).Free ≃ L.Free :=
  Equiv.subtypeEquivRight fun s ↦ not_congr (L.mem_biUnion_map_iff h s)

omit [Fintype S'] [DecidableEq S'] [Fintype R] [DecidableEq R] in
/-- The Kraus indices of a layer with its cells and gates moved. -/
noncomputable def mapGateIndexEquiv (h : Γ.Hom Δ (Function.Embedding.refl S))
    (φ : GateMorphism G₁ G₂ ev₁ ev₂) (L : Layer Γ G₁ X Y) : (L.mapGate h φ).Index ≃ L.Index :=
  Equiv.prodCongr
    ((Equiv.piCongrLeft (fun b' ↦ GateFamily.Outcome ((L.mapGate h φ).gate b'))
      (h.cellsEquiv L.cells)).symm.trans (Equiv.piCongrRight fun b ↦
        (outcomeNdrec' _ _).trans ((φ.outcome _).trans (Equiv.cast (congrArg
          (fun c ↦ GateFamily.Outcome (L.gate c)) ((h.cellsEquiv L.cells).symm_apply_apply b))))))
    (Equiv.piCongrLeft (fun s ↦ (L.onsite s).Index) (L.mapGateFreeEquiv h φ))

omit [Fintype S'] [DecidableEq S'] [Fintype R] [DecidableEq R] [GateFamily G₁] in
theorem ev_ndrec' {D D' : Finset S} [∀ s, Fintype (X s)] [∀ s, DecidableEq (X s)]
    [∀ s, Fintype (Y s)] [∀ s, DecidableEq (Y s)] (hD : D = D') (g : G₂ D X Y)
    (o : GateFamily.Outcome (Eq.ndrec (motive := fun D ↦ G₂ D X Y) g hD))
    (y : Config Y) (x : Config X) :
    ev₂ (Eq.ndrec (motive := fun D ↦ G₂ D X Y) g hD) o (fun v ↦ y v) (fun v ↦ x v) =
      ev₂ g (outcomeNdrec' hD g o) (fun v ↦ y v) (fun v ↦ x v) := by
  subst hD; rfl

omit [Fintype S'] [DecidableEq S'] [Fintype R] [DecidableEq R] in
theorem kraus_mapGate [∀ s, Fintype (X s)] [∀ s, DecidableEq (X s)] [∀ s, Fintype (Y s)]
    [∀ s, DecidableEq (Y s)] (h : Γ.Hom Δ (Function.Embedding.refl S))
    (φ : GateMorphism G₁ G₂ ev₁ ev₂) (L : Layer Γ G₁ X Y) (i : (L.mapGate h φ).Index) :
    (L.mapGate h φ).kraus ev₂ i = L.kraus ev₁ (L.mapGateIndexEquiv h φ i) := by
  ext y x
  simp only [kraus]
  rw [← Fintype.prod_equiv (L.mapGateCellsEquiv h φ) _ _ fun _ ↦ rfl,
    ← Fintype.prod_equiv (L.mapGateFreeEquiv h φ).symm _ _ fun _ ↦ rfl]
  congr 1
  refine Finset.prod_congr rfl fun b _ ↦ ?_
  refine (ev_ndrec' _ _ _ y x).trans ?_
  refine (congrFun (congrFun (φ.ev_map _ _) _) _).trans ?_
  exact ev_gate_congr L ev₁ ((h.cellsEquiv L.cells).symm_apply_apply b) _ _ _

omit [Fintype S'] [DecidableEq S'] [Fintype R] [DecidableEq R] in
theorem lightCone_mapGate (h : Γ.Hom Δ (Function.Embedding.refl S))
    (φ : GateMorphism G₁ G₂ ev₁ ev₂) (L : Layer Γ G₁ X Y) (T : Finset S) :
    (L.mapGate h φ).lightCone T = L.lightCone T := by
  simp only [lightCone, mapGate, Finset.filter_map, Function.comp_def, h.cell_eq]
  congr 1
  ext v
  simp only [Finset.mem_biUnion, Finset.mem_map, h.cell_eq]
  constructor
  · rintro ⟨_, ⟨b, hb, rfl⟩, hv⟩
    exact ⟨b, hb, by rwa [h.cell_eq] at hv⟩
  · rintro ⟨b, hb, hv⟩
    exact ⟨h.cellMap b, ⟨b, hb, rfl⟩, by rwa [h.cell_eq]⟩

omit [Fintype S'] [DecidableEq S'] [Fintype R] [DecidableEq R] in
theorem gateCount_mapGate (h : Γ.Hom Δ (Function.Embedding.refl S))
    (φ : GateMorphism G₁ G₂ ev₁ ev₂) (L : Layer Γ G₁ X Y) :
    (L.mapGate h φ).gateCount = ∑ b ∈ L.cells, Δ.cost (h.cellMap b) := by
  rw [gateCount_eq_sum]
  exact Finset.sum_map _ _ _

omit [Fintype S'] [DecidableEq S'] [Fintype R] [DecidableEq R] in
theorem depth_mapGate_le (h : Γ.Hom Δ (Function.Embedding.refl S))
    (φ : GateMorphism G₁ G₂ ev₁ ev₂) (hcost : ∀ b, 0 < Δ.cost (h.cellMap b) → 0 < Γ.cost b)
    (L : Layer Γ G₁ X Y) : (L.mapGate h φ).depth ≤ L.depth := by
  unfold depth
  split_ifs with h₁ h₂ <;> try omega
  obtain ⟨b', hb'⟩ := h₁
  rw [Finset.mem_filter] at hb'
  obtain ⟨b, hb, rfl⟩ := Finset.mem_map.mp hb'.1
  exact absurd ⟨b, Finset.mem_filter.mpr ⟨hb, hcost b hb'.2⟩⟩ h₂

end Layer

/-- A circuit with its cells moved along `h` and its gates along `φ`, on the same sites. -/
noncomputable def Circuit.mapGate (h : Γ.Hom Δ (Function.Embedding.refl S))
    (φ : GateMorphism G₁ G₂ ev₁ ev₂) :
    {X Z : S → Type} → Circuit Γ G₁ X Z → Circuit Δ G₂ X Z
  | _, _, .done _ => .done _
  | _, _, @Circuit.step _ _ _ _ _ _ _ _ _ _ L next =>
      .step (L.mapGate h φ) fun i ↦ (next (L.mapGateIndexEquiv h φ i)).mapGate h φ

/-- The branches of a circuit with its cells and gates moved. -/
noncomputable def Circuit.mapGateIndexEquiv (h : Γ.Hom Δ (Function.Embedding.refl S))
    (φ : GateMorphism G₁ G₂ ev₁ ev₂) :
    {X Z : S → Type} → (c : Circuit Γ G₁ X Z) → (c.mapGate h φ).Index ≃ c.Index
  | _, _, .done _ => Equiv.refl Unit
  | _, _, @Circuit.step _ _ _ _ _ _ _ _ _ _ L next =>
      Equiv.sigmaCongr (L.mapGateIndexEquiv h φ) fun _ ↦ (next _).mapGateIndexEquiv h φ

/-- Reindexing a supremum over all indices along an equivalence. -/
theorem _root_.Finset.univ_sup_equiv {α β γ : Type} [Fintype α] [Fintype β] [SemilatticeSup γ]
    [OrderBot γ] (u : α ≃ β) (F : β → γ) :
    (Finset.univ.sup fun a ↦ F (u a)) = Finset.univ.sup F :=
  le_antisymm (Finset.sup_le fun a _ ↦ Finset.le_sup (f := F) (Finset.mem_univ _))
    (Finset.sup_le fun b _ ↦ by
      simpa using Finset.le_sup (f := fun a ↦ F (u a)) (Finset.mem_univ (u.symm b)))

theorem Circuit.kraus_mapGate (h : Γ.Hom Δ (Function.Embedding.refl S))
    (φ : GateMorphism G₁ G₂ ev₁ ev₂) :
    {X Z : S → Type} → [∀ s, Fintype (X s)] → [∀ s, DecidableEq (X s)] →
      (c : Circuit Γ G₁ X Z) → (p : (c.mapGate h φ).Index) →
      (c.mapGate h φ).kraus ev₂ p = c.kraus ev₁ (c.mapGateIndexEquiv h φ p)
  | _, _, _, _, .done _, _ => rfl
  | _, _, _, _, @Circuit.step _ _ _ _ _ _ _ _ _ _ L next, q => by
    obtain ⟨i, p⟩ := q
    change ((next (L.mapGateIndexEquiv h φ i)).mapGate h φ).kraus ev₂ p *
      (L.mapGate h φ).kraus ev₂ i = _
    rw [Circuit.kraus_mapGate h φ _ p, Layer.kraus_mapGate h φ L i]
    rfl

theorem Circuit.isUnbranched_mapGate (h : Γ.Hom Δ (Function.Embedding.refl S))
    (φ : GateMorphism G₁ G₂ ev₁ ev₂) :
    {X Z : S → Type} → {c : Circuit Γ G₁ X Z} → c.IsUnbranched → (c.mapGate h φ).IsUnbranched
  | _, _, .done _, _ => trivial
  | _, _, @Circuit.step _ _ _ _ _ _ _ _ _ _ L next, hc =>
    ⟨fun i j ↦ by
      change (next _).mapGate h φ = (next _).mapGate h φ
      rw [hc.1 _ _],
      fun i ↦ Circuit.isUnbranched_mapGate h φ (hc.2 _)⟩

theorem Circuit.forall_mapGate (h : Γ.Hom Δ (Function.Embedding.refl S))
    (φ : GateMorphism G₁ G₂ ev₁ ev₂)
    {P : ∀ {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β],
      KrausFamily α β → Prop}
    (hP : ∀ {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
      (K : KrausFamily α β) {ι : Type} [Fintype ι] (u : ι ≃ K.Index),
        P K → P ⟨ι, fun i ↦ K.op (u i)⟩) :
    {X Z : S → Type} → [∀ s, Fintype (X s)] → [∀ s, DecidableEq (X s)] →
      {c : Circuit Γ G₁ X Z} → c.Forall ev₁ P → (c.mapGate h φ).Forall ev₂ P
  | _, _, _, _, .done _, _ => trivial
  | _, _, _, _, @Circuit.step _ _ _ _ _ X₀ Y₀ _ _ _ L next, hc => by
    refine ⟨⟨fun b' ↦ ?_, fun s ↦ hc.1.2 _⟩, fun i ↦ Circuit.forall_mapGate h φ hP (hc.2 _)⟩
    have hgen : ∀ {D D' : Finset S} (hD : D = D') (g : G₂ D X₀ Y₀),
        P (⟨GateFamily.Outcome g, ev₂ g⟩ : KrausFamily (RegionConfig X₀ D) (RegionConfig Y₀ D)) →
        P (⟨GateFamily.Outcome (Eq.ndrec (motive := fun D ↦ G₂ D X₀ Y₀) g hD),
          ev₂ (Eq.ndrec (motive := fun D ↦ G₂ D X₀ Y₀) g hD)⟩ :
            KrausFamily (RegionConfig X₀ D') (RegionConfig Y₀ D')) := by
      intro D D' hD g hg; subst hD; exact hg
    refine hgen _ _ ?_
    have := hP _ (φ.outcome _) (hc.1.1 ((h.cellsEquiv L.cells).symm b'))
    rw [show ev₂ (φ.map (L.gate ((h.cellsEquiv L.cells).symm b'))) = fun o ↦
      ev₁ (L.gate ((h.cellsEquiv L.cells).symm b')) (φ.outcome _ o) from funext (φ.ev_map _)]
    exact this

/-- A cost of the moved layers bounded by a cost of the layers bounds the cost of the moved
circuit. -/
theorem Circuit.total_mapGate_le (h : Γ.Hom Δ (Function.Embedding.refl S))
    (φ : GateMorphism G₁ G₂ ev₁ ev₂)
    (f₁ : ∀ ⦃X Y : S → Type⦄, Layer Γ G₁ X Y → ℕ) (f₂ : ∀ ⦃X Y : S → Type⦄, Layer Δ G₂ X Y → ℕ)
    (hf : ∀ ⦃X Y : S → Type⦄ (L : Layer Γ G₁ X Y), f₂ (L.mapGate h φ) ≤ f₁ L) :
    {X Z : S → Type} → (c : Circuit Γ G₁ X Z) → (c.mapGate h φ).total f₂ ≤ c.total f₁
  | _, _, .done _ => le_rfl
  | _, _, @Circuit.step _ _ _ _ _ _ _ _ _ _ L next => by
    change f₂ (L.mapGate h φ) + Finset.univ.sup (fun i ↦
      ((next (L.mapGateIndexEquiv h φ i)).mapGate h φ).total f₂) ≤ _
    refine add_le_add (hf L) (Finset.sup_le fun i _ ↦ ?_)
    exact (Circuit.total_mapGate_le h φ f₁ f₂ hf _).trans
      (Finset.le_sup (f := fun i ↦ (next i).total f₁) (Finset.mem_univ _))

theorem Circuit.gateCount_mapGate_le (h : Γ.Hom Δ (Function.Embedding.refl S))
    (φ : GateMorphism G₁ G₂ ev₁ ev₂) (hcost : ∀ b, Δ.cost (h.cellMap b) ≤ Γ.cost b)
    {X Z : S → Type} (c : Circuit Γ G₁ X Z) : (c.mapGate h φ).gateCount ≤ c.gateCount :=
  Circuit.total_mapGate_le h φ _ _ (fun _ _ L ↦ by
    rw [L.gateCount_mapGate h φ, Layer.gateCount_eq_sum]
    exact Finset.sum_le_sum fun b _ ↦ hcost b) c

theorem Circuit.depth_mapGate_le (h : Γ.Hom Δ (Function.Embedding.refl S))
    (φ : GateMorphism G₁ G₂ ev₁ ev₂) (hcost : ∀ b, 0 < Δ.cost (h.cellMap b) → 0 < Γ.cost b)
    {X Z : S → Type} (c : Circuit Γ G₁ X Z) : (c.mapGate h φ).depth ≤ c.depth :=
  Circuit.total_mapGate_le h φ _ _ (fun _ _ L ↦ L.depth_mapGate_le h φ hcost) c

theorem Circuit.lightCone_mapGate (h : Γ.Hom Δ (Function.Embedding.refl S))
    (φ : GateMorphism G₁ G₂ ev₁ ev₂) (T : Finset S) :
    {X Z : S → Type} → (c : Circuit Γ G₁ X Z) → (c.mapGate h φ).lightCone T = c.lightCone T
  | _, _, .done _ => rfl
  | _, _, @Circuit.step _ _ _ _ _ _ _ _ _ _ L next => by
    change (L.mapGate h φ).lightCone (Finset.univ.sup fun i ↦
      ((next (L.mapGateIndexEquiv h φ i)).mapGate h φ).lightCone T) = _
    simp only [Circuit.lightCone_mapGate h φ T]
    rw [Finset.univ_sup_equiv (L.mapGateIndexEquiv h φ) fun i ↦ (next i).lightCone T,
      Layer.lightCone_mapGate]
    rfl

end MapGate

end QuantumCircuit
