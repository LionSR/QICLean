/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Circuit.Party.Syntax.AddPair
import QICLean.Circuit.Party.Syntax.PartyCircuit
import QICLean.Circuit.Core.GateSum

/-!
# Pair sources and pair effects

* `SourceGate` — a pair source: a vector `η ∈ ℂ^{α × β}` prepared on a fresh factor `α` of the
  party `p` and a fresh factor `β` of a party `q ≠ p`.
* `PairEffectGate` — a pair effect: the bra `⟨η|` on a factor `α` of `p` and a factor `β` of
  `q ≠ p`, which it removes.
* `ChainGate` — both; the gates of monomials, which are party circuits with these gates
  (`Monomial`).

A source on `{p, q}` changes the basis types at `p` and `q` only. The fresh factors are located
by two equivalences `Y p ≃ α × X p` and `Y q ≃ β × X q`, so the indices of a gate are variables.
The canonical output is `addPair X hpq α β`, with the fresh factors in front
(`SourceGate.ofAddPair`). The matrix of a source depends on the equivalences only through a
relabelling of the output (`SourceGate.ev_reindexOutput`), and any two sources with the same
data differ by such a relabelling (`SourceGate.eq_reindexOutput`); the output of a source read in
canonical form is `SourceGate.toAddPair`. The operator of one source is the preparation of its
vector, the output read through `SourceGate.configEquiv` (`SourceGate.op_gate`), and that of one
pair effect is its adjoint (`PairEffectGate.op_gate`).

## Main definitions

* `QuantumCircuit.Party.PairSource`, `QuantumCircuit.Party.SourceInventory`.
* `QuantumCircuit.Party.SourceGate`, `QuantumCircuit.Party.PairEffectGate`, their matrices on
  the cell `regionMatrix`, interpretations `ev`, canonical gates `ofAddPair`, canonical readings
  `toAddPair` and `configEquiv`.
* `QuantumCircuit.Party.ChainGate`, `QuantumCircuit.Party.chainEv`,
  `QuantumCircuit.Party.Monomial`.

## Main results

* `QuantumCircuit.Party.SourceGate.ev_ofAddPair_apply`,
  `QuantumCircuit.Party.PairEffectGate.ev_ofAddPair_apply` — the canonical gates.
* `QuantumCircuit.Party.SourceGate.ev_reindexOutput`,
  `QuantumCircuit.Party.PairEffectGate.ev_reindexInput`,
  `QuantumCircuit.Party.SourceGate.eq_reindexOutput` — the equivalences enter only by
  relabelling.
* `QuantumCircuit.Party.SourceGate.op_gate`, `QuantumCircuit.Party.PairEffectGate.op_gate` —
  the operators of one source and of one effect.
* `QuantumCircuit.Party.SourceGate.norm_ev_le`, `QuantumCircuit.Party.PairEffectGate.norm_ev_le`
  — a normalized source or effect is a contraction.

## References

* Polynomial-PEPS manuscript (September 24, 2026), `04-compression.tex`, lines 21–36 (gates),
  32–35 (pair sources and effects), 53–70 (Lemma 5.1).
-/

open Matrix ManyBody
open scoped Matrix.Norms.L2Operator

namespace QuantumCircuit.Party

variable {P : Type} [DecidableEq P]

/-! ### Pair-source data -/

/-- A pair-source occurrence: two distinct endpoint parties, the basis types of the two fresh
factors, and the prepared vector. Source: `04-compression.tex`, lines 32–35 and 68–70. -/
structure PairSource (P : Type) : Type 1 where
  /-- The first endpoint. -/
  left : P
  /-- The second endpoint. -/
  right : P
  /-- The endpoints are distinct. -/
  distinct : left ≠ right
  /-- The basis of the fresh factor at `left`. -/
  leftBasis : Type
  /-- The basis of the fresh factor at `right`. -/
  rightBasis : Type
  [leftFintype : Fintype leftBasis]
  [leftDecEq : DecidableEq leftBasis]
  [rightFintype : Fintype rightBasis]
  [rightDecEq : DecidableEq rightBasis]
  /-- The prepared vector. -/
  vector : EuclideanSpace ℂ (leftBasis × rightBasis)

attribute [instance] PairSource.leftFintype PairSource.leftDecEq PairSource.rightFintype
  PairSource.rightDecEq

/-- A finite list of pair-source occurrences; repeated pairs stay distinct occurrences. -/
abbrev SourceInventory (P : Type) := List (PairSource P)

/-- Every source vector of the inventory is normalized. Source: `04-compression.tex`,
lines 68–70. -/
def SourceInventory.IsNormalized (S : SourceInventory P) : Prop := ∀ s ∈ S, ‖s.vector‖ = 1

/-- The unordered pair of endpoints. -/
def PairSource.partyPair (s : PairSource P) : Sym2 P := s(s.left, s.right)

/-! ### Pair sources -/

/-- A pair source on the cell `D = {left, right}`: the vector `vector` prepared on fresh factors
of the two endpoints, located in the output bases by `leftEquiv` and `rightEquiv`; the bases
outside `D` are unchanged. Source: `04-compression.tex`, lines 32–35. -/
structure SourceGate (D : Finset P) (X Y : P → Type) : Type 1 extends PairSource P where
  /-- The cell is the pair of endpoints. -/
  cell_eq : D = {left, right}
  /-- The output basis of `left` is the fresh factor times the input basis. -/
  leftEquiv : Y left ≃ leftBasis × X left
  /-- The output basis of `right` is the fresh factor times the input basis. -/
  rightEquiv : Y right ≃ rightBasis × X right
  /-- Outside the cell the bases are unchanged. -/
  outside : ∀ s ∉ D, Y s = X s

namespace SourceGate

variable {D : Finset P} {X Y Y' : P → Type}

/-- The first endpoint lies in the cell. -/
theorem left_mem (g : SourceGate D X Y) : g.left ∈ D :=
  (Finset.ext_iff.mp g.cell_eq _).mpr (Finset.mem_insert_self _ _)

/-- The second endpoint lies in the cell. -/
theorem right_mem (g : SourceGate D X Y) : g.right ∈ D :=
  (Finset.ext_iff.mp g.cell_eq _).mpr (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))

/-- The canonical source: the fresh factors in front of the bases of the endpoints. -/
def ofAddPair {p q : P} (hpq : p ≠ q) (α β : Type) [Fintype α] [DecidableEq α] [Fintype β]
    [DecidableEq β] (η : EuclideanSpace ℂ (α × β)) (X : P → Type) :
    SourceGate {p, q} X (addPair X hpq α β) where
  left := p
  right := q
  distinct := hpq
  leftBasis := α
  rightBasis := β
  vector := η
  cell_eq := rfl
  leftEquiv := addPairLeft hpq α β
  rightEquiv := addPairRight hpq α β
  outside := addPair_eq_of_notMem hpq α β

/-- The matrix of a source on its cell: `|η⟩` on the fresh factors and the identity on the old
ones. -/
def regionMatrix [∀ s, DecidableEq (X s)] (g : SourceGate D X Y) :
    Matrix (RegionConfig Y D) (RegionConfig X D) ℂ :=
  fun y x ↦
    let yl := g.leftEquiv (y ⟨g.left, g.left_mem⟩)
    let yr := g.rightEquiv (y ⟨g.right, g.right_mem⟩)
    if yl.2 = x ⟨g.left, g.left_mem⟩ ∧ yr.2 = x ⟨g.right, g.right_mem⟩ then
      g.vector (yl.1, yr.1) else 0

/-- A configuration of the cell in the output system is a configuration of the fresh factors and
a configuration of the cell in the input system. -/
def outputEquiv (g : SourceGate D X Y) :
    RegionConfig Y D ≃ (g.leftBasis × g.rightBasis) × RegionConfig X D :=
  (pairConfigEquiv Y g.distinct g.cell_eq).trans <|
    (Equiv.prodCongr g.leftEquiv g.rightEquiv).trans <|
      (Equiv.prodProdProdComm _ _ _ _).trans <|
        Equiv.prodCongr (Equiv.refl _) (pairConfigEquiv X g.distinct g.cell_eq).symm

/-- The matrix of a source is the preparation of its vector on the fresh factors. -/
theorem regionMatrix_eq_prepMatrix [∀ s, DecidableEq (X s)] (g : SourceGate D X Y) :
    g.regionMatrix = prepMatrix g.outputEquiv g.vector := by
  ext y x
  simp only [regionMatrix, prepMatrix_apply, outputEquiv, Equiv.trans_apply,
    pairConfigEquiv_apply, Equiv.prodCongr_apply, Prod.map, Equiv.prodProdProdComm_apply,
    Equiv.refl_apply, Equiv.symm_apply_eq, Prod.mk.injEq]

end SourceGate

/-- A pair source has one outcome. -/
instance : GateFamily (S := P) SourceGate where
  Outcome _ := Unit
  fintype _ := inferInstance

/-- Pair sources have one outcome each. -/
instance : GateFamily.UniqueOutcome (S := P) SourceGate where
  nonempty_unique _ _ _ _ := ⟨inferInstanceAs (Unique Unit)⟩

/-- The interpretation of pair sources: the matrix of the source. -/
def SourceGate.ev : Interpretation (S := P) SourceGate :=
  fun g _ ↦ g.regionMatrix

/-- A pair source is allowed when its vector is normalized. Source: `04-compression.tex`,
lines 32–34. -/
def SourceGate.IsAllowed {D : Finset P} {X Y : P → Type} (g : SourceGate D X Y) : Prop :=
  ‖g.vector‖ = 1

namespace SourceGate

variable {D : Finset P} {X Y Y' : P → Type}

/-- The canonical source reads as the preparation of `η` in front of the bases of `p`
and `q`. -/
@[simp] theorem ev_ofAddPair_apply {p q : P} (hpq : p ≠ q) (α β : Type) [Fintype α]
    [DecidableEq α] [Fintype β] [DecidableEq β] (η : EuclideanSpace ℂ (α × β)) (X : P → Type)
    [∀ s, Fintype (X s)] [∀ s, DecidableEq (X s)] (o : Unit)
    (y : RegionConfig (addPair X hpq α β) {p, q}) (x : RegionConfig X {p, q}) :
    SourceGate.ev (ofAddPair hpq α β η X) o y x =
      if (addPairLeft hpq α β (y ⟨p, by simp⟩)).2 = x ⟨p, by simp⟩ ∧
          (addPairRight hpq α β (y ⟨q, by simp⟩)).2 = x ⟨q, by simp⟩ then
        η ((addPairLeft hpq α β (y ⟨p, by simp⟩)).1, (addPairRight hpq α β (y ⟨q, by simp⟩)).1)
      else 0 :=
  rfl

/-- The same source with the output bases relabelled along `e`, the bases outside `D` being
equal. -/
def reindexOutput (g : SourceGate D X Y) (e : ∀ s, Y' s ≃ Y s) (he : ∀ s ∉ D, Y' s = Y s) :
    SourceGate D X Y' where
  toPairSource := g.toPairSource
  cell_eq := g.cell_eq
  leftEquiv := (e g.left).trans g.leftEquiv
  rightEquiv := (e g.right).trans g.rightEquiv
  outside s hs := (he s hs).trans (g.outside s hs)

/-- **The matrix depends on the equivalences only by relabelling.** Relabelling the output bases
reindexes the rows of the matrix. -/
theorem ev_reindexOutput [∀ s, Fintype (X s)] [∀ s, DecidableEq (X s)] [∀ s, Fintype (Y s)]
    [∀ s, DecidableEq (Y s)] [∀ s, Fintype (Y' s)] [∀ s, DecidableEq (Y' s)]
    (g : SourceGate D X Y) (e : ∀ s, Y' s ≃ Y s) (he : ∀ s ∉ D, Y' s = Y s) (o : Unit) :
    SourceGate.ev (g.reindexOutput e he) o =
      (SourceGate.ev g o).submatrix (fun y v ↦ e v (y v)) id :=
  rfl

/-- Two sources with the same pair data differ by the relabelling of the output bases that
matches their equivalences. -/
theorem eq_reindexOutput (g : SourceGate D X Y) (g' : SourceGate D X Y')
    (h : g'.toPairSource = g.toPairSource) :
    ∃ (e : ∀ s, Y' s ≃ Y s) (he : ∀ s ∉ D, Y' s = Y s), g' = g.reindexOutput e he := by
  obtain ⟨⟨l, r, d, α, β, η⟩, hc, le, re, out⟩ := g
  obtain ⟨s', hc', le', re', out'⟩ := g'
  obtain rfl : s' = ⟨l, r, d, α, β, η⟩ := h
  have hout : ∀ s ∉ D, Y' s = Y s := fun s hs ↦ (out' s hs).trans (out s hs).symm
  let e : ∀ s, Y' s ≃ Y s := fun s ↦
    if hl : s = l then hl ▸ le'.trans le.symm
    else if hr : s = r then hr ▸ re'.trans re.symm
    else Equiv.cast (hout s (by simp [hc, hl, hr]))
  have hel : e l = le'.trans le.symm := by simp [e]
  have her : e r = re'.trans re.symm := by simp [e, d.symm]
  refine ⟨e, hout, ?_⟩
  simp only [reindexOutput, mk.injEq, true_and]
  refine ⟨?_, ?_⟩
  · rw [hel, Equiv.trans_assoc, Equiv.symm_trans_self, Equiv.trans_refl]
  · rw [her, Equiv.trans_assoc, Equiv.symm_trans_self, Equiv.trans_refl]

/-- A source is the canonical source of its data up to a relabelling of the output. -/
theorem eq_reindexOutput_ofAddPair (g : SourceGate D X Y) :
    ∃ (hD : D = {g.left, g.right}) (e : ∀ s, Y s ≃ addPair X g.distinct g.leftBasis
        g.rightBasis s) (he : ∀ s ∉ D, Y s = addPair X g.distinct g.leftBasis g.rightBasis s),
      HEq g ((ofAddPair g.distinct g.leftBasis g.rightBasis g.vector X).reindexOutput e
        (hD ▸ he)) := by
  obtain ⟨ps, hc, le, re, out⟩ := g
  subst hc
  obtain ⟨e, he, h⟩ := eq_reindexOutput (ofAddPair ps.distinct ps.leftBasis ps.rightBasis
    ps.vector X) ⟨ps, rfl, le, re, out⟩ rfl
  exact ⟨rfl, e, he, heq_of_eq h⟩

/-- The matrix of a source has operator norm at most `‖η‖`; a normalized source is a
contraction. -/
theorem norm_ev_le [∀ s, Fintype (X s)] [∀ s, DecidableEq (X s)] [∀ s, Fintype (Y s)]
    [∀ s, DecidableEq (Y s)] (g : SourceGate D X Y) (o : Unit) :
    ‖SourceGate.ev g o‖ ≤ ‖g.vector‖ := by
  change ‖g.regionMatrix‖ ≤ _
  rw [regionMatrix_eq_prepMatrix]
  exact norm_prepMatrix_le _ _

/-- The matrix of a source on a cell with configurations has operator norm `‖η‖`; a normalized
source is an isometry. -/
theorem norm_ev [∀ s, Fintype (X s)] [∀ s, DecidableEq (X s)] [∀ s, Fintype (Y s)]
    [∀ s, DecidableEq (Y s)] [Nonempty (RegionConfig X D)] (g : SourceGate D X Y) (o : Unit) :
    ‖SourceGate.ev g o‖ = ‖g.vector‖ := by
  change ‖g.regionMatrix‖ = _
  rw [regionMatrix_eq_prepMatrix]
  exact norm_prepMatrix _ _

/-- A party outside the cell is not the first endpoint. -/
theorem ne_left_of_notMem (g : SourceGate D X Y) {s : P} (hs : s ∉ D) : s ≠ g.left :=
  fun h ↦ hs (h ▸ g.left_mem)

/-- A party outside the cell is not the second endpoint. -/
theorem ne_right_of_notMem (g : SourceGate D X Y) {s : P} (hs : s ∉ D) : s ≠ g.right :=
  fun h ↦ hs (h ▸ g.right_mem)

/-- The output basis of a source, read in the canonical form `addPair` of its input. -/
def toAddPair (g : SourceGate D X Y) (s : P) :
    Y s ≃ addPair X g.distinct g.leftBasis g.rightBasis s :=
  if hl : s = g.left then
    (Equiv.cast (congrArg Y hl)).trans (g.leftEquiv.trans
      ((addPairLeft g.distinct g.leftBasis g.rightBasis).symm.trans (Equiv.cast (by rw [hl]))))
  else if hr : s = g.right then
    (Equiv.cast (congrArg Y hr)).trans (g.rightEquiv.trans
      ((addPairRight g.distinct g.leftBasis g.rightBasis).symm.trans (Equiv.cast (by rw [hr]))))
  else
    (Equiv.cast (g.outside s (by rw [g.cell_eq]; simp [hl, hr]))).trans
      (Equiv.cast (addPair_of_ne g.distinct g.leftBasis g.rightBasis hl hr).symm)

/-- At the first endpoint, the canonical reading of the output basis is `leftEquiv`. -/
@[simp] theorem addPairLeft_toAddPair (g : SourceGate D X Y) (y : Y g.left) :
    addPairLeft g.distinct g.leftBasis g.rightBasis (g.toAddPair g.left y) = g.leftEquiv y := by
  simp [toAddPair]

/-- At the second endpoint, the canonical reading of the output basis is `rightEquiv`. -/
@[simp] theorem addPairRight_toAddPair (g : SourceGate D X Y) (y : Y g.right) :
    addPairRight g.distinct g.leftBasis g.rightBasis (g.toAddPair g.right y) =
      g.rightEquiv y := by
  simp [toAddPair, g.distinct.symm]

/-- Outside the cell, the canonical reading of the output basis is the identification of the
equal bases. -/
theorem toAddPair_of_notMem (g : SourceGate D X Y) {s : P} (hs : s ∉ D) (y : Y s) :
    g.toAddPair s y = cast (addPair_of_ne g.distinct g.leftBasis g.rightBasis
      (g.ne_left_of_notMem hs) (g.ne_right_of_notMem hs)).symm (cast (g.outside s hs) y) := by
  simp [toAddPair, g.ne_left_of_notMem hs, g.ne_right_of_notMem hs]

/-- A configuration of the output of a source is a configuration of the fresh factors and a
configuration of the input. -/
def configEquiv (g : SourceGate D X Y) :
    Config Y ≃ (g.leftBasis × g.rightBasis) × Config X :=
  (Equiv.piCongrRight g.toAddPair).trans
    (addPairConfigEquiv (X := X) g.distinct g.leftBasis g.rightBasis)

/-- The fresh part of a configuration of the output of a source. -/
@[simp] theorem configEquiv_apply_fst (g : SourceGate D X Y) (y : Config Y) :
    (g.configEquiv y).1 = ((g.leftEquiv (y g.left)).1, (g.rightEquiv (y g.right)).1) := by
  simp [configEquiv]

/-- The old part of a configuration of the output of a source, at the first endpoint. -/
@[simp] theorem configEquiv_apply_snd_left (g : SourceGate D X Y) (y : Config Y) :
    (g.configEquiv y).2 g.left = (g.leftEquiv (y g.left)).2 := by
  simp [configEquiv]

/-- The old part of a configuration of the output of a source, at the second endpoint. -/
@[simp] theorem configEquiv_apply_snd_right (g : SourceGate D X Y) (y : Config Y) :
    (g.configEquiv y).2 g.right = (g.rightEquiv (y g.right)).2 := by
  simp [configEquiv]

/-- The old part of a configuration of the output of a source, outside the cell. -/
theorem configEquiv_apply_snd_of_notMem (g : SourceGate D X Y) (y : Config Y) {s : P}
    (hs : s ∉ D) : (g.configEquiv y).2 s = cast (g.outside s hs) (y s) := by
  simp [configEquiv, addPairConfigEquiv_apply_snd_of_ne _ _ _ _ (g.ne_left_of_notMem hs)
    (g.ne_right_of_notMem hs), toAddPair_of_notMem g hs]

/-- The configurations of the output of the canonical source are read by
`addPairConfigEquiv`. -/
theorem configEquiv_ofAddPair {p q : P} (hpq : p ≠ q) (α β : Type) [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β] (η : EuclideanSpace ℂ (α × β)) (X : P → Type) :
    (ofAddPair hpq α β η X).configEquiv = addPairConfigEquiv hpq α β := by
  ext σ : 1
  refine Prod.ext ?_ (funext fun s ↦ ?_)
  · exact (configEquiv_apply_fst _ σ).trans (addPairConfigEquiv_apply_fst hpq α β σ).symm
  by_cases hp : s = p
  · subst hp
    exact (configEquiv_apply_snd_left (ofAddPair hpq α β η X) σ).trans
      (addPairConfigEquiv_apply_snd_left hpq α β σ).symm
  by_cases hq : s = q
  · subst hq
    exact (configEquiv_apply_snd_right (ofAddPair hpq α β η X) σ).trans
      (addPairConfigEquiv_apply_snd_right hpq α β σ).symm
  exact (configEquiv_apply_snd_of_notMem (ofAddPair hpq α β η X) σ (by simp [hp, hq])).trans
    (addPairConfigEquiv_apply_snd_of_ne hpq α β σ hp hq).symm

/-- **The operator of one source** is the preparation of its vector, the output read through
`configEquiv`: it maps `|x⟩` to `η ⊗ |x⟩`. -/
theorem op_gate [Fintype P] [∀ s, Fintype (X s)] [∀ s, DecidableEq (X s)] [∀ s, Fintype (Y s)]
    [∀ s, DecidableEq (Y s)] (g : SourceGate D X Y) :
    (PartyCircuit.gate D g.outside g).op SourceGate.ev = prepMatrix g.configEquiv g.vector := by
  ext y x
  rw [PartyCircuit.op_gate, placeBetween_apply, prepMatrix_apply]
  change (if _ then g.regionMatrix _ _ else 0) = _
  dsimp only [regionMatrix]
  rw [← ite_and]
  refine if_congr ⟨fun ⟨h, hl, hr⟩ ↦ funext fun s ↦ ?_, fun h ↦ ⟨fun v hv ↦ ?_, ?_, ?_⟩⟩
    (congrArg g.vector (configEquiv_apply_fst g y).symm) rfl
  · by_cases hsl : s = g.left
    · subst hsl
      exact (configEquiv_apply_snd_left g y).trans hl
    by_cases hsr : s = g.right
    · subst hsr
      exact (configEquiv_apply_snd_right g y).trans hr
    have hs : s ∉ D := by rw [g.cell_eq]; simp [hsl, hsr]
    exact (configEquiv_apply_snd_of_notMem g y hs).trans (h s hs)
  · rw [← h, configEquiv_apply_snd_of_notMem g y hv]
  · exact (configEquiv_apply_snd_left g y).symm.trans (congrFun h _)
  · exact (configEquiv_apply_snd_right g y).symm.trans (congrFun h _)

end SourceGate

/-! ### Pair effects -/

/-- A pair effect on the cell `D = {left, right}`: the bra `⟨vector|` on factors of the two
endpoints, located in the input bases by `leftEquiv` and `rightEquiv`, which it removes; the
bases outside `D` are unchanged. Source: `04-compression.tex`, lines 32–35 and 53–70. -/
structure PairEffectGate (D : Finset P) (X Y : P → Type) : Type 1 extends PairSource P where
  /-- The cell is the pair of endpoints. -/
  cell_eq : D = {left, right}
  /-- The input basis of `left` is the removed factor times the output basis. -/
  leftEquiv : X left ≃ leftBasis × Y left
  /-- The input basis of `right` is the removed factor times the output basis. -/
  rightEquiv : X right ≃ rightBasis × Y right
  /-- Outside the cell the bases are unchanged. -/
  outside : ∀ s ∉ D, Y s = X s

namespace PairEffectGate

variable {D : Finset P} {X Y X' : P → Type}

/-- The first endpoint lies in the cell. -/
theorem left_mem (g : PairEffectGate D X Y) : g.left ∈ D :=
  (Finset.ext_iff.mp g.cell_eq _).mpr (Finset.mem_insert_self _ _)

/-- The second endpoint lies in the cell. -/
theorem right_mem (g : PairEffectGate D X Y) : g.right ∈ D :=
  (Finset.ext_iff.mp g.cell_eq _).mpr (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))

/-- The canonical effect: it removes the factors in front of the bases of the endpoints. -/
def ofAddPair {p q : P} (hpq : p ≠ q) (α β : Type) [Fintype α] [DecidableEq α] [Fintype β]
    [DecidableEq β] (η : EuclideanSpace ℂ (α × β)) (Y : P → Type) :
    PairEffectGate {p, q} (addPair Y hpq α β) Y where
  left := p
  right := q
  distinct := hpq
  leftBasis := α
  rightBasis := β
  vector := η
  cell_eq := rfl
  leftEquiv := addPairLeft hpq α β
  rightEquiv := addPairRight hpq α β
  outside s hs := (addPair_eq_of_notMem hpq α β s hs).symm

/-- The source with the same data in the opposite direction: it prepares the vector that the
effect removes. -/
def toSourceGate (g : PairEffectGate D X Y) : SourceGate D Y X where
  toPairSource := g.toPairSource
  cell_eq := g.cell_eq
  leftEquiv := g.leftEquiv
  rightEquiv := g.rightEquiv
  outside s hs := (g.outside s hs).symm

/-- The matrix of a pair effect on its cell: `⟨η|` on the removed factors and the identity on
the remaining ones. -/
def regionMatrix [∀ s, DecidableEq (Y s)] (g : PairEffectGate D X Y) :
    Matrix (RegionConfig Y D) (RegionConfig X D) ℂ :=
  fun y x ↦
    let xl := g.leftEquiv (x ⟨g.left, g.left_mem⟩)
    let xr := g.rightEquiv (x ⟨g.right, g.right_mem⟩)
    if y ⟨g.left, g.left_mem⟩ = xl.2 ∧ y ⟨g.right, g.right_mem⟩ = xr.2 then
      star (g.vector (xl.1, xr.1)) else 0

/-- The matrix of a pair effect is the adjoint of the matrix of the source with the same
data. -/
theorem regionMatrix_eq_conjTranspose [∀ s, DecidableEq (Y s)] (g : PairEffectGate D X Y) :
    g.regionMatrix = g.toSourceGate.regionMatrixᴴ := by
  ext y x
  simp only [regionMatrix, conjTranspose_apply, SourceGate.regionMatrix, toSourceGate,
    apply_ite star, star_zero]
  exact if_congr ⟨fun h ↦ ⟨h.1.symm, h.2.symm⟩, fun h ↦ ⟨h.1.symm, h.2.symm⟩⟩ rfl rfl

/-- The same effect with the input bases relabelled along `e`, the bases outside `D` being
equal. -/
def reindexInput (g : PairEffectGate D X Y) (e : ∀ s, X' s ≃ X s) (he : ∀ s ∉ D, X' s = X s) :
    PairEffectGate D X' Y where
  toPairSource := g.toPairSource
  cell_eq := g.cell_eq
  leftEquiv := (e g.left).trans g.leftEquiv
  rightEquiv := (e g.right).trans g.rightEquiv
  outside s hs := (g.outside s hs).trans (he s hs).symm

end PairEffectGate

/-- A pair effect has one outcome. -/
instance : GateFamily (S := P) PairEffectGate where
  Outcome _ := Unit
  fintype _ := inferInstance

/-- Pair effects have one outcome each. -/
instance : GateFamily.UniqueOutcome (S := P) PairEffectGate where
  nonempty_unique _ _ _ _ := ⟨inferInstanceAs (Unique Unit)⟩

/-- The interpretation of pair effects: the matrix of the effect. -/
def PairEffectGate.ev : Interpretation (S := P) PairEffectGate :=
  fun g _ ↦ g.regionMatrix

/-- A pair effect is allowed when its vector is normalized. Source: `04-compression.tex`,
lines 34–35. -/
def PairEffectGate.IsAllowed {D : Finset P} {X Y : P → Type} (g : PairEffectGate D X Y) :
    Prop :=
  ‖g.vector‖ = 1

namespace PairEffectGate

variable {D : Finset P} {X Y X' : P → Type}

/-- The canonical effect reads as `⟨η|` on the factors in front of the bases of `p` and `q`. -/
@[simp] theorem ev_ofAddPair_apply {p q : P} (hpq : p ≠ q) (α β : Type) [Fintype α]
    [DecidableEq α] [Fintype β] [DecidableEq β] (η : EuclideanSpace ℂ (α × β)) (Y : P → Type)
    [∀ s, Fintype (Y s)] [∀ s, DecidableEq (Y s)] (o : Unit)
    (y : RegionConfig Y {p, q}) (x : RegionConfig (addPair Y hpq α β) {p, q}) :
    PairEffectGate.ev (ofAddPair hpq α β η Y) o y x =
      if y ⟨p, by simp⟩ = (addPairLeft hpq α β (x ⟨p, by simp⟩)).2 ∧
          y ⟨q, by simp⟩ = (addPairRight hpq α β (x ⟨q, by simp⟩)).2 then
        star (η ((addPairLeft hpq α β (x ⟨p, by simp⟩)).1,
          (addPairRight hpq α β (x ⟨q, by simp⟩)).1))
      else 0 :=
  rfl

/-- The matrix depends on the equivalences only by relabelling, as for sources. -/
theorem ev_reindexInput [∀ s, Fintype (X s)] [∀ s, DecidableEq (X s)] [∀ s, Fintype (Y s)]
    [∀ s, DecidableEq (Y s)] [∀ s, Fintype (X' s)] [∀ s, DecidableEq (X' s)]
    (g : PairEffectGate D X Y) (e : ∀ s, X' s ≃ X s) (he : ∀ s ∉ D, X' s = X s) (o : Unit) :
    PairEffectGate.ev (g.reindexInput e he) o =
      (PairEffectGate.ev g o).submatrix id (fun x v ↦ e v (x v)) :=
  rfl

/-- The matrix of an effect has operator norm at most `‖η‖`; a normalized effect is a
contraction. -/
theorem norm_ev_le [∀ s, Fintype (X s)] [∀ s, DecidableEq (X s)] [∀ s, Fintype (Y s)]
    [∀ s, DecidableEq (Y s)] (g : PairEffectGate D X Y) (o : Unit) :
    ‖PairEffectGate.ev g o‖ ≤ ‖g.vector‖ := by
  change ‖g.regionMatrix‖ ≤ _
  rw [regionMatrix_eq_conjTranspose, l2_opNorm_conjTranspose]
  exact g.toSourceGate.norm_ev_le ()

/-- The matrix of an effect on a cell with configurations has operator norm `‖η‖`. -/
theorem norm_ev [∀ s, Fintype (X s)] [∀ s, DecidableEq (X s)] [∀ s, Fintype (Y s)]
    [∀ s, DecidableEq (Y s)] [Nonempty (RegionConfig Y D)] (g : PairEffectGate D X Y)
    (o : Unit) : ‖PairEffectGate.ev g o‖ = ‖g.vector‖ := by
  change ‖g.regionMatrix‖ = _
  rw [regionMatrix_eq_conjTranspose, l2_opNorm_conjTranspose]
  exact g.toSourceGate.norm_ev ()

/-- The input basis of a pair effect, read in the canonical form `addPair` of its output. -/
def toAddPair (g : PairEffectGate D X Y) (s : P) :
    X s ≃ addPair Y g.distinct g.leftBasis g.rightBasis s :=
  g.toSourceGate.toAddPair s

/-- A configuration of the input of a pair effect is a configuration of the removed factors and a
configuration of the output. -/
def configEquiv (g : PairEffectGate D X Y) :
    Config X ≃ (g.leftBasis × g.rightBasis) × Config Y :=
  g.toSourceGate.configEquiv

/-- **The operator of one pair effect** is the adjoint of the preparation of its vector, the input
read through `configEquiv`: it maps `η' ⊗ |y⟩` to `⟨η, η'⟩ |y⟩`. -/
theorem op_gate [Fintype P] [∀ s, Fintype (X s)] [∀ s, DecidableEq (X s)] [∀ s, Fintype (Y s)]
    [∀ s, DecidableEq (Y s)] (g : PairEffectGate D X Y) :
    (PartyCircuit.gate D g.outside g).op PairEffectGate.ev =
      (prepMatrix g.configEquiv g.vector)ᴴ := by
  have h := SourceGate.op_gate g.toSourceGate
  change _ = (prepMatrix g.toSourceGate.configEquiv g.toSourceGate.vector)ᴴ
  rw [← h, PartyCircuit.op_gate, PartyCircuit.op_gate, placeBetween_conjTranspose]
  change placeBetween D _ g.regionMatrix = placeBetween D _ g.toSourceGate.regionMatrixᴴ
  rw [regionMatrix_eq_conjTranspose]

end PairEffectGate

/-! ### Gates of monomials -/

/-- The gates of monomials: pair sources and pair effects. -/
abbrev ChainGate := GateSum (SourceGate (P := P)) PairEffectGate

/-- The gates of monomials have one outcome each. -/
instance : GateFamily.UniqueOutcome (ChainGate (P := P)) where
  nonempty_unique
    | _, _, _, .inl _ => ⟨inferInstanceAs (Unique Unit)⟩
    | _, _, _, .inr _ => ⟨inferInstanceAs (Unique Unit)⟩

/-- The interpretation of the gates of monomials. -/
def chainEv : Interpretation (ChainGate (P := P)) :=
  Interpretation.sum SourceGate.ev PairEffectGate.ev

/-- Pair sources and pair effects are allowed when their vectors are normalized. -/
def ChainGate.IsAllowed : ∀ ⦃D : Finset P⦄ ⦃X Y : P → Type⦄ [∀ s, Fintype (X s)]
    [∀ s, DecidableEq (X s)] [∀ s, Fintype (Y s)] [∀ s, DecidableEq (Y s)],
    ChainGate D X Y → Prop
  | _, _, _, _, _, _, _, .inl g => g.IsAllowed
  | _, _, _, _, _, _, _, .inr g => g.IsAllowed

/-! ### Monomials -/

/-- A monomial on the parties `D`: a party circuit on the sites of `D` whose gates are pair
sources and pair effects. Source: `04-compression.tex`, lines 32–35 (allowed monomials). -/
abbrev Monomial (D : Finset P) (X Y : D → Type) := PartyCircuit (ChainGate (P := ↥D)) X Y

end QuantumCircuit.Party
