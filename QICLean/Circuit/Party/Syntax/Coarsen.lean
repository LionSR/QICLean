/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Circuit.Party.Syntax.OwnerMap
import QICLean.Circuit.Party.Syntax.Local

/-!
# Words read on blocks of parties

Along a map of parties `f : P → Q`, a word on `P` is read as a word on `Q` whose basis at `q` is
the configurations of the block `f⁻¹{q}` (`ManyBody.blockSystem f`): `Word.coarsen f`, defined
by recursion on the syntax. A pair source whose endpoints lie in distinct blocks stays a pair
source, on the image cell (`SourceGate.coarse`); a pair source inside one block becomes one local
operation of that block, its matrix extended to the block by the identity; a local operation of
a party becomes a local operation of its block, and local operations at every party become their
products over the blocks.

The operator of the coarse word is the operator of the word, read along the identification
`ManyBody.blockConfigEquiv` of the configurations of the blocked system with those of the
system (`Word.op_coarsen`); its sources are those mapped by `SourceInventory.mapOwner`
(`Word.sources_coarsen`), and it is allowed when the word is (`Word.isAllowed_coarsen`).

## Main definitions

* `QuantumCircuit.Party.freshBlockEquiv`, `QuantumCircuit.Party.SourceGate.coarse`.
* `QuantumCircuit.Party.Word.coarsen`.

## Main results

* `QuantumCircuit.Party.SourceGate.configEquiv_coarse` — the coarse source on configurations.
* `QuantumCircuit.Party.Word.op_coarsen`, `QuantumCircuit.Party.Word.sum_op_coarsen`.
* `QuantumCircuit.Party.Word.sources_coarsen`, `QuantumCircuit.Party.Word.isAllowed_coarsen`,
  `QuantumCircuit.Party.Word.coarsen_comp`, `QuantumCircuit.Party.Word.coarsen_localOp`.

## References

* Polynomial-PEPS manuscript (September 24, 2026), Theorem 5.2, `04-compression.tex`,
  lines 383–448 (the affected and exterior systems), lines 409–417 (internal source
  preparations).
-/

open Matrix ManyBody
open scoped Matrix.Norms.L2Operator

namespace QuantumCircuit.Party

variable {P Q : Type} [Fintype P] [DecidableEq P] [DecidableEq Q]

/-! ### A fresh factor at one site of a block -/

/-- The configurations of a region in which one site `l` receives a fresh factor in front of its
basis, the other sites keeping theirs: a configuration of the fresh factor and one of the old
region. -/
def freshBlockEquiv {X Y : P → Type} {B : Finset P} {l : P} {α : Type} (hl : l ∈ B)
    (hY : ∀ v ∈ B, v ≠ l → Y v = X v) (e : Y l ≃ α × X l) :
    RegionConfig Y B ≃ α × RegionConfig X B where
  toFun z := ((e (z ⟨l, hl⟩)).1, fun v ↦
    if h : v.1 = l then cast (congrArg X h.symm) (e (z ⟨l, hl⟩)).2
    else cast (hY v.1 v.2 h) (z v))
  invFun a v :=
    if h : v.1 = l then cast (congrArg Y h.symm) (e.symm (a.1, a.2 ⟨l, hl⟩))
    else cast (hY v.1 v.2 h).symm (a.2 v)
  left_inv z := by
    funext ⟨v, hv⟩
    by_cases h : v = l
    · subst h
      simp
    · simp [h]
  right_inv a := by
    obtain ⟨a, x⟩ := a
    refine Prod.ext (by simp) (funext fun ⟨v, hv⟩ ↦ ?_)
    by_cases h : v = l
    · subst h
      simp
    · simp [h]

omit [Fintype P] in
/-- The fresh part of a configuration. -/
@[simp] theorem freshBlockEquiv_apply_fst {X Y : P → Type} {B : Finset P} {l : P} {α : Type}
    (hl : l ∈ B) (hY : ∀ v ∈ B, v ≠ l → Y v = X v) (e : Y l ≃ α × X l) (z : RegionConfig Y B) :
    (freshBlockEquiv hl hY e z).1 = (e (z ⟨l, hl⟩)).1 :=
  rfl

omit [Fintype P] in
/-- The old part of a configuration, at the site `l`. -/
theorem freshBlockEquiv_apply_snd_self {X Y : P → Type} {B : Finset P} {l : P} {α : Type}
    (hl : l ∈ B) (hY : ∀ v ∈ B, v ≠ l → Y v = X v) (e : Y l ≃ α × X l) (z : RegionConfig Y B) :
    (freshBlockEquiv hl hY e z).2 ⟨l, hl⟩ = (e (z ⟨l, hl⟩)).2 := by
  simp [freshBlockEquiv]

omit [Fintype P] in
/-- The old part of a configuration, away from the site `l`. -/
theorem freshBlockEquiv_apply_snd_of_ne {X Y : P → Type} {B : Finset P} {l : P} {α : Type}
    (hl : l ∈ B) (hY : ∀ v ∈ B, v ≠ l → Y v = X v) (e : Y l ≃ α × X l) (z : RegionConfig Y B)
    (v : {v // v ∈ B}) (hv : v.1 ≠ l) :
    (freshBlockEquiv hl hY e z).2 v = cast (hY v.1 v.2 hv) (z v) := by
  simp [freshBlockEquiv, hv]

/-! ### Pair sources read on blocks -/

namespace SourceGate

variable {D : Finset P} {X Y : P → Type}

omit [Fintype P] in
/-- The cell of a source, read on blocks, is the pair of the blocks of its endpoints. -/
theorem image_eq (f : P → Q) (g : SourceGate D X Y) : D.image f = {f g.left, f g.right} :=
  (congrArg (Finset.image f) g.cell_eq).trans (by rw [Finset.image_insert, Finset.image_singleton])

/-- A site in the block of one endpoint, other than that endpoint, lies outside the cell when the
endpoints lie in distinct blocks. -/
private theorem notMem_of_mem_block (f : P → Q) (g : SourceGate D X Y)
    (h : f g.left ≠ f g.right) {e e' : P} (he : e = g.left ∧ e' = g.right ∨
      e = g.right ∧ e' = g.left) {v : P} (hv : v ∈ blockPreimage f {f e}) (hve : v ≠ e) :
    v ∉ D := by
  rw [g.cell_eq, Finset.mem_insert, Finset.mem_singleton]
  have hfv : f v = f e := by simpa using hv
  rintro (rfl | rfl) <;> rcases he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  exacts [hve rfl, h hfv, h hfv.symm, hve rfl]

omit [DecidableEq P] in
/-- The sites outside the preimage of the image cell lie outside the cell. -/
private theorem notMem_of_notMem_blockPreimage (f : P → Q) {v : P}
    (hv : v ∉ blockPreimage f (D.image f)) : v ∉ D :=
  fun hvD ↦ hv (by simpa using ⟨v, hvD, rfl⟩)

/-- A source joining two blocks, read on the blocks: the same pair data on the pair of blocks,
the fresh factors in front of the configurations of the blocks. -/
def coarse (f : P → Q) (g : SourceGate D X Y) (h : f g.left ≠ f g.right) :
    SourceGate (D.image f) (blockSystem f X) (blockSystem f Y) where
  left := f g.left
  right := f g.right
  distinct := h
  leftBasis := g.leftBasis
  rightBasis := g.rightBasis
  vector := g.vector
  cell_eq := g.image_eq f
  leftEquiv := freshBlockEquiv (by simp)
    (fun _ hv hve ↦ g.outside _ (notMem_of_mem_block f g h (.inl ⟨rfl, rfl⟩) hv hve))
    g.leftEquiv
  rightEquiv := freshBlockEquiv (by simp)
    (fun _ hv hve ↦ g.outside _ (notMem_of_mem_block f g h (.inr ⟨rfl, rfl⟩) hv hve))
    g.rightEquiv
  outside := blockSystem_eq_of_notMem f fun _ hv ↦
    g.outside _ (notMem_of_notMem_blockPreimage f hv)

/-- Reading a source on blocks keeps its vector and moves its endpoints to their blocks. -/
@[simp] theorem toPairSource_coarse (f : P → Q) (g : SourceGate D X Y)
    (h : f g.left ≠ f g.right) :
    (g.coarse f h).toPairSource =
      ⟨f g.left, f g.right, h, g.leftBasis, g.rightBasis, g.vector⟩ :=
  rfl

omit [DecidableEq P] in
/-- The value at a site of a configuration of the blocked system depends only on the site. -/
private theorem block_apply_congr {f : P → Q} {T : P → Type} (z : Config (blockSystem f T))
    {b b' : Q}
    {v : P} (hb : b' = b) {h : v ∈ blockPreimage f {b}} {h' : v ∈ blockPreimage f {b'}} :
    z b' ⟨v, h'⟩ = z b ⟨v, h⟩ := by
  subst hb
  rfl

/-- **The coarse source on configurations**: its fresh part and its old part are those of the
source, read along `blockConfigEquiv`. -/
theorem configEquiv_coarse (f : P → Q) (g : SourceGate D X Y) (h : f g.left ≠ f g.right)
    (z : Config (blockSystem f Y)) :
    (g.coarse f h).configEquiv z =
      ((g.configEquiv (blockConfigEquiv f Y z)).1,
        (blockConfigEquiv f X).symm (g.configEquiv (blockConfigEquiv f Y z)).2) := by
  refine Prod.ext ((configEquiv_apply_fst _ z).trans ?_) (funext fun b ↦ funext fun v ↦ ?_)
  · rw [configEquiv_apply_fst]
    rfl
  have hfv : f v.1 = b := Finset.mem_singleton.mp (Finset.mem_filter.mp v.2).2
  change _ = (g.configEquiv (blockConfigEquiv f Y z)).2 v.1
  by_cases hl : b = f g.left
  · subst hl
    have h1 := congrFun (configEquiv_apply_snd_left (g.coarse f h) z) v
    refine h1.trans ?_
    by_cases hvl : v.1 = g.left
    · obtain ⟨v, hv⟩ := v
      dsimp only at hvl
      subst hvl
      rw [configEquiv_apply_snd_left g (blockConfigEquiv f Y z)]
      exact freshBlockEquiv_apply_snd_self _
        (fun _ hv' hve ↦ g.outside _ (notMem_of_mem_block f g h (.inl ⟨rfl, rfl⟩) hv' hve)) _ _
    · have hvD : v.1 ∉ D := notMem_of_mem_block f g h (.inl ⟨rfl, rfl⟩) v.2 hvl
      refine (freshBlockEquiv_apply_snd_of_ne _ (fun _ hv' hve ↦
        g.outside _ (notMem_of_mem_block f g h (.inl ⟨rfl, rfl⟩) hv' hve)) _ _ v hvl).trans ?_
      rw [configEquiv_apply_snd_of_notMem g _ hvD, blockConfigEquiv_apply]
      rw [block_apply_congr z hfv]
      rfl
  by_cases hr : b = f g.right
  · subst hr
    have h1 := congrFun (configEquiv_apply_snd_right (g.coarse f h) z) v
    refine h1.trans ?_
    by_cases hvr : v.1 = g.right
    · obtain ⟨v, hv⟩ := v
      dsimp only at hvr
      subst hvr
      rw [configEquiv_apply_snd_right g (blockConfigEquiv f Y z)]
      exact freshBlockEquiv_apply_snd_self _
        (fun _ hv' hve ↦ g.outside _ (notMem_of_mem_block f g h (.inr ⟨rfl, rfl⟩) hv' hve)) _ _
    · have hvD : v.1 ∉ D := notMem_of_mem_block f g h (.inr ⟨rfl, rfl⟩) v.2 hvr
      refine (freshBlockEquiv_apply_snd_of_ne _ (fun _ hv' hve ↦
        g.outside _ (notMem_of_mem_block f g h (.inr ⟨rfl, rfl⟩) hv' hve)) _ _ v hvr).trans ?_
      rw [configEquiv_apply_snd_of_notMem g _ hvD, blockConfigEquiv_apply]
      rw [block_apply_congr z hfv]
      rfl
  · have hb : b ∉ D.image f := by rw [g.image_eq f]; simp [hl, hr]
    have hvD : v.1 ∉ D := fun hvD ↦ hb (hfv ▸ Finset.mem_image_of_mem f hvD)
    rw [configEquiv_apply_snd_of_notMem (g.coarse f h) z hb,
      configEquiv_apply_snd_of_notMem g _ hvD,
      blockConfigEquiv_apply]
    have hAB : (fun w : {w // w ∈ blockPreimage f {b}} ↦ Y w) =
        fun w : {w // w ∈ blockPreimage f {b}} ↦ X w :=
      funext fun w ↦ g.outside w.1 fun hwD ↦ hb (by
        rw [← Finset.mem_singleton.mp (Finset.mem_filter.mp w.2).2]
        exact Finset.mem_image_of_mem f hwD)
    refine (cast_pi_apply hAB _ _ v).trans ?_
    obtain ⟨v, hv⟩ := v
    dsimp only at hfv ⊢
    subst hfv
    rfl

end SourceGate

/-! ### Words read on blocks -/

namespace Word

variable (f : P → Q)

omit [DecidableEq P] in
/-- A cell inside one block lies in the preimage of that block. -/
private theorem subset_blockPreimage {D : Finset P} {b : Q} (hD : ∀ s ∈ D, f s = b) :
    D ⊆ blockPreimage f {b} :=
  fun s hs ↦ by simpa using hD s hs

omit [Fintype P] [DecidableEq Q] in
/-- The cell of a pair source with both endpoints in the block `b` lies in that block. -/
private theorem forall_mem_cell {D : Finset P} {X Y : P → Type} (g : SourceGate D X Y)
    (h : f g.left = f g.right) : ∀ s ∈ D, f s = f g.left := by
  intro s hs
  rw [g.cell_eq, Finset.mem_insert, Finset.mem_singleton] at hs
  rcases hs with rfl | rfl
  exacts [rfl, h.symm]

omit [DecidableEq P] in
/-- Two systems agreeing outside a cell inside the block `b` agree outside that block. -/
private theorem eq_of_notMem_blockPreimage {D : Finset P} {X Y : P → Type} {b : Q}
    (hD : ∀ s ∈ D, f s = b) (hY : ∀ s ∉ D, Y s = X s) :
    ∀ v ∉ blockPreimage f {b}, Y v = X v :=
  fun v hv ↦ hY v fun hvD ↦ hv (subset_blockPreimage f hD hvD)

/-- The word read on the blocks of `f`: a pair source joining two blocks stays a pair source on
the image cell, a pair source inside one block becomes one local operation of that block, a
local operation of a party one local operation of its block, and local operations at every party
their products over the blocks. Source: `04-compression.tex`, lines 409–417. -/
noncomputable def coarsen : {X Y : P → Type} → [∀ p, Fintype (X p)] → [∀ p, DecidableEq (X p)] →
    Word X Y → Word (blockSystem f X) (blockSystem f Y)
  | _, _, _, _, .done _ => .done _
  | _, _, _, _, @PartyCircuit.gate _ _ _ _ _ _ D hY g =>
    if h : f g.left = f g.right then
      .localOp (f g.left)
        (fun b hb ↦ blockSystem_eq_of_notMem f (D' := {f g.left})
          (eq_of_notMem_blockPreimage f (forall_mem_cell f g h) hY) b
          (Finset.notMem_singleton.mpr hb))
        (subregionPlaceBetween (subset_blockPreimage f (forall_mem_cell f g h)) hY
          g.regionMatrix)
    else .gate (D.image f) (g.coarse f h).outside (g.coarse f h)
  | _, _, _, _, @PartyCircuit.localOp _ _ _ _ _ _ p hY A =>
    .localOp (f p)
      (fun b hb ↦ blockSystem_eq_of_notMem f (D' := {f p})
        (eq_of_notMem_blockPreimage f (D := {p}) (fun s hs ↦ by rw [Finset.mem_singleton.mp hs])
          fun s hs ↦ hY s (Finset.notMem_singleton.mp hs)) b (Finset.notMem_singleton.mpr hb))
      (subregionPlaceBetween (subset_blockPreimage f (D := {p})
          fun s hs ↦ by rw [Finset.mem_singleton.mp hs])
        (fun s hs ↦ hY s (Finset.notMem_singleton.mp hs))
        (A.submatrix (fun y ↦ y ⟨p, Finset.mem_singleton_self p⟩)
          (fun x ↦ x ⟨p, Finset.mem_singleton_self p⟩)))
  | _, _, _, _, @PartyCircuit.localOps _ _ _ _ _ _ A =>
    .localOps fun b ↦ piKronecker fun v : {v // v ∈ blockPreimage f {b}} ↦ A v
  | _, _, _, _, @PartyCircuit.comp _ _ _ _ _ _ _ w w' => .comp (coarsen w) (coarsen w')

/-- Reading on blocks commutes with composition. -/
@[simp] theorem coarsen_comp {X Y Z : P → Type} [∀ p, Fintype (X p)] [∀ p, DecidableEq (X p)]
    [∀ p, Fintype (Y p)] [∀ p, DecidableEq (Y p)] (w : Word X Y) (w' : Word Y Z) :
    coarsen f (PartyCircuit.comp w w') = PartyCircuit.comp (coarsen f w) (coarsen f w') :=
  rfl

/-- A reading along equivalences, inverted. -/
private theorem eq_reindex_symm {m n m' n' : Type} {e₁ : m ≃ m'} {e₂ : n ≃ n'}
    {M : Matrix m n ℂ} {N : Matrix m' n' ℂ} (h : reindex e₁ e₂ M = N) :
    M = reindex e₁.symm e₂.symm N := by
  subst h
  ext
  simp

/-- Reading on blocks a local operation of a party. -/
theorem coarsen_localOp {X Y : P → Type} [∀ p, Fintype (X p)] [∀ p, DecidableEq (X p)]
    [∀ p, Fintype (Y p)] [∀ p, DecidableEq (Y p)] (p : P) (hY : ∀ s ≠ p, Y s = X s)
    (A : Matrix (Y p) (X p) ℂ) :
    coarsen f (PartyCircuit.localOp (G := SourceGate) p hY A) =
      PartyCircuit.localOp (f p)
        (fun b hb ↦ blockSystem_eq_of_notMem f (D' := {f p})
          (eq_of_notMem_blockPreimage f (D := {p}) (fun s hs ↦ by rw [Finset.mem_singleton.mp hs])
            fun s hs ↦ hY s (Finset.notMem_singleton.mp hs)) b (Finset.notMem_singleton.mpr hb))
        (subregionPlaceBetween (subset_blockPreimage f (D := {p})
            fun s hs ↦ by rw [Finset.mem_singleton.mp hs])
          (fun s hs ↦ hY s (Finset.notMem_singleton.mp hs))
          (A.submatrix (fun y ↦ y ⟨p, Finset.mem_singleton_self p⟩)
            (fun x ↦ x ⟨p, Finset.mem_singleton_self p⟩))) :=
  rfl

/-- **The operator of the word read on blocks is the operator of the word, read along
`blockConfigEquiv`.** Source: `04-compression.tex`, lines 409–417. -/
theorem op_coarsen [Fintype Q] : {X Y : P → Type} → [∀ p, Fintype (X p)] →
    [∀ p, DecidableEq (X p)] → (w : Word X Y) →
      (coarsen f w).op = reindex (blockConfigEquiv f Y).symm (blockConfigEquiv f X).symm w.op
  | _, _, _, _, .done _ => by
    unfold Word.op
    rw [coarsen, PartyCircuit.op_done, PartyCircuit.op_done]
    ext
    simp [one_apply]
  | _, _, _, _, @PartyCircuit.gate _ _ _ _ _ _ D hY g => by
    by_cases h : f g.left = f g.right
    · apply eq_reindex_symm
      unfold Word.op
      rw [coarsen, dite_eq_left h, PartyCircuit.op_localOp,
        reindex_blockConfigEquiv_placeBetween_singleton f _
          (eq_of_notMem_blockPreimage f (forall_mem_cell f g h) hY),
        placeBetween_subregionPlaceBetween, PartyCircuit.op_gate]
      rfl
    · rw [coarsen, dite_eq_right h]
      change Word.op (source (g.coarse f h)) = reindex _ _ (Word.op (source g))
      rw [op_source, op_source]
      ext σ τ
      simp only [reindex_apply, submatrix_apply, Equiv.symm_symm, prepMatrix_apply,
        SourceGate.configEquiv_coarse, Equiv.symm_apply_eq]
      rfl
  | _, _, _, _, @PartyCircuit.localOp _ _ _ _ _ _ p hY A => by
    apply eq_reindex_symm
    unfold Word.op
    rw [coarsen_localOp, PartyCircuit.op_localOp,
      reindex_blockConfigEquiv_placeBetween_singleton f _
        (eq_of_notMem_blockPreimage f (D := {p}) (fun s hs ↦ by rw [Finset.mem_singleton.mp hs])
          fun s hs ↦ hY s (Finset.notMem_singleton.mp hs)),
      placeBetween_subregionPlaceBetween, PartyCircuit.op_localOp]
  | _, _, _, _, @PartyCircuit.localOps _ _ _ _ _ _ A => by
    unfold Word.op
    rw [coarsen, PartyCircuit.op_localOps, PartyCircuit.op_localOps,
      reindex_blockConfigEquiv_symm_piKronecker]
  | _, _, _, _, @PartyCircuit.comp _ _ _ _ _ _ _ w w' => by
    rw [coarsen_comp, op_comp, op_comp, op_coarsen w, op_coarsen w', reindex_apply,
      reindex_apply, reindex_apply, submatrix_mul_equiv]

/-- A weighted sum of words read on blocks is the weighted sum read along `blockConfigEquiv`. -/
theorem sum_op_coarsen [Fintype Q] {X Y : P → Type} [∀ p, Fintype (X p)]
    [∀ p, DecidableEq (X p)] {ι : Type} [Fintype ι] (c : ι → ℂ) (w : ι → Word X Y) :
    ∑ ξ, c ξ • (coarsen f (w ξ)).op =
      reindex (blockConfigEquiv f Y).symm (blockConfigEquiv f X).symm (∑ ξ, c ξ • (w ξ).op) := by
  simp only [op_coarsen]
  ext σ τ
  simp [Matrix.sum_apply]

/-- **The sources of the word read on blocks** are those of the word whose endpoints lie in
distinct blocks, moved to the blocks. -/
theorem sources_coarsen : {X Y : P → Type} → [∀ p, Fintype (X p)] → [∀ p, DecidableEq (X p)] →
    (w : Word X Y) → (coarsen f w).sources = w.sources.mapOwner f
  | _, _, _, _, .done _ => rfl
  | _, _, _, _, @PartyCircuit.gate _ _ _ _ _ _ D hY g => by
    by_cases h : f g.left = f g.right
    · rw [coarsen, dite_eq_left h]
      simp [sources, SourceInventory.mapOwner, PairSource.mapOwner, h]
    · rw [coarsen, dite_eq_right h]
      simp [sources, SourceInventory.mapOwner, PairSource.mapOwner, h]
  | _, _, _, _, @PartyCircuit.localOp _ _ _ _ _ _ _ _ _ => rfl
  | _, _, _, _, @PartyCircuit.localOps _ _ _ _ _ _ _ => rfl
  | _, _, _, _, @PartyCircuit.comp _ _ _ _ _ _ _ w w' => by
    rw [coarsen_comp, sources_comp, sources_comp, sources_coarsen w, sources_coarsen w',
      SourceInventory.mapOwner_append]

/-- **Reading on blocks keeps allowed words allowed.** -/
theorem isAllowed_coarsen : {X Y : P → Type} → [∀ p, Fintype (X p)] →
    [∀ p, DecidableEq (X p)] → {w : Word X Y} → w.IsAllowed → (coarsen f w).IsAllowed
  | _, _, _, _, .done _, _ => trivial
  | _, _, _, _, @PartyCircuit.gate _ _ _ _ _ _ D hY g, hw => by
    by_cases h : f g.left = f g.right
    · rw [coarsen, dite_eq_left h]
      exact (norm_subregionPlaceBetween_le _ _ _).trans hw.1
    · rw [coarsen, dite_eq_right h]
      exact ⟨((g.coarse f h).norm_ev_le ()).trans hw.2.le, hw.2⟩
  | _, _, _, _, @PartyCircuit.localOp _ _ _ _ _ _ p _ A, hw =>
    (norm_subregionPlaceBetween_le _ _ _).trans ((norm_submatrix_singleton_le p A).trans hw)
  | _, _, _, _, @PartyCircuit.localOps _ _ _ _ _ _ _, hw => fun _ ↦
    l2_opNorm_piKronecker_le_one fun v ↦ hw v
  | _, _, _, _, @PartyCircuit.comp _ _ _ _ _ _ _ _ _, hw =>
    ⟨isAllowed_coarsen hw.1, isAllowed_coarsen hw.2⟩

end Word

end QuantumCircuit.Party
