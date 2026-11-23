/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Circuit.Party.Syntax.Restrict
import QICLean.Circuit.Party.Syntax.OnCell

/-!
# Party operations of coarsened, framed and restricted circuits

The party operations `PartyCircuit.partyOp c p` of a party circuit without gates are the factors
of its operator (`PartyCircuit.op_eq_piKronecker_partyOp`). This module computes them for the
circuits built from a local circuit by the operations of the syntax.

* Framing: the party operation of `c.frame W` at `p` is `1 ⊗ partyOp c p`, and its region
  operation is `1 ⊗ regionOp c R` read along the pairing of configurations
  (`PartyCircuit.partyOp_frame`, `PartyCircuit.regionOp_frame`).
* Coarsening: the party operation at the block `b` of a local word read on the blocks of
  `f : P → Q` is the region operation of the word on the block, `f⁻¹{b}`
  (`Word.partyOp_coarsen`); at a block that is a single party `p` it is the party operation of
  `p` (`Word.partyOp_coarsen_of_fiber`), at an empty block the scalar `1`
  (`Word.partyOp_coarsen_apply_of_forall_ne`), and on a region of blocks it is the region
  operation of the preimage (`Word.regionOp_coarsen`).
* Restriction and cells: the party operations of a restricted word are those of the word
  (`Word.partyOp_restrict`); a local word on the parties of a cell, run inside all parties, has
  the party operations of the word on the cell and the identity elsewhere (`Word.partyOp_onCell`).
* A local circuit acts at a party that none of its operations names as the identification of
  the two equal bases (`PartyCircuit.partyOp_of_notMem_parties`); the parties of a coarsened word
  lie in the image of the parties of the word (`Word.parties_coarsen_subset`). Equality fails:
  local operations at every party can multiply to the identity on a block although no factor is
  the identity.
* A word on a type of no parties has all entries of its operator equal to `1`
  (`Word.op_apply_of_isEmpty`).

Coarsening does not commute with framing as an identity of words: a block of the framed system
is a configuration of pairs, a framed block is a pair of configurations. The operators agree
along the identification of the two (`Word.op_coarsen_frame`).

## Main results

* `QuantumCircuit.Party.PartyCircuit.partyOp_comp` and the other rules, `regionOp_localOps`.
* `QuantumCircuit.Party.PartyCircuit.partyOp_frame`, `regionOp_frame`, `isLocal_frame`.
* `QuantumCircuit.Party.PartyCircuit.partyOp_of_notMem_parties`.
* `QuantumCircuit.Party.Word.partyOp_coarsen`, `partyOp_coarsen_of_fiber`,
  `partyOp_coarsen_apply_of_forall_ne`, `regionOp_coarsen`, `isLocal_coarsen`,
  `parties_coarsen_subset`, `op_coarsen_frame`, `partyOp_onCell`.
* `QuantumCircuit.Party.Word.partyOp_restrict`, `isLocal_restrict`, `op_apply_of_isEmpty`.

## References

* Polynomial-PEPS manuscript (September 24, 2026), Theorem 5.2, `04-compression.tex`,
  lines 233–251 (the local maps of a source-free word collected by party), lines 383–434 (the
  affected and exterior blocks).
-/

open Matrix ManyBody
open scoped Kronecker

namespace QuantumCircuit.Party

variable {P : Type} [DecidableEq P]

/-- The Kronecker product of identifications of equal bases is the identification of the equal
configurations. -/
private theorem piKronecker_cast {ι : Type} [Fintype ι] {A B : ι → Type}
    [∀ i, DecidableEq (B i)] (hAB : ∀ i, A i = B i) (h : (∀ i, A i) = ∀ i, B i) :
    piKronecker (fun i ↦ (Equiv.cast (hAB i)).toPEquiv.toMatrix) =
      (Equiv.cast h).toPEquiv.toMatrix := by
  obtain rfl : A = B := funext hAB
  simp

namespace PartyCircuit

variable {G : Finset P → (P → Type) → (P → Type) → Type 1} [GateFamily G] {X Y Z : P → Type}

/-! ### The rules of the party operations -/

section Rules

variable [∀ p, DecidableEq (X p)]

omit [GateFamily G] in
/-- The empty circuit has the identity at every party. -/
@[simp] theorem partyOp_done (p : P) : (done X : PartyCircuit G X X).partyOp p = 1 :=
  rfl

variable [∀ p, Fintype (Y p)] [∀ p, DecidableEq (Y p)]

omit [GateFamily G] in
/-- A gate has the operation `0` at every party. -/
@[simp] theorem partyOp_gate (D : Finset P) (hY : ∀ s ∉ D, Y s = X s) (g : G D X Y) (p : P) :
    (gate D hY g).partyOp p = 0 :=
  rfl

omit [GateFamily G] in
/-- The party operations of one local operation are its party family. -/
@[simp] theorem partyOp_localOp (q : P) (hY : ∀ s ≠ q, Y s = X s) (A : Matrix (Y q) (X q) ℂ) :
    (localOp (G := G) q hY A).partyOp = localOpFamily q hY A :=
  rfl

omit [GateFamily G] in
/-- The party operations of local operations at every party are those operations. -/
@[simp] theorem partyOp_localOps (A : ∀ p, Matrix (Y p) (X p) ℂ) :
    (localOps (G := G) A).partyOp = A :=
  rfl

omit [GateFamily G] in
/-- The region operation of local operations at every party is their Kronecker product over
the region. -/
@[simp] theorem regionOp_localOps (A : ∀ p, Matrix (Y p) (X p) ℂ) (R : Finset P) :
    (localOps (G := G) A).regionOp R = piKronecker fun p : {p // p ∈ R} ↦ A p :=
  rfl

omit [GateFamily G] in
/-- The party operation of a composition is the product of the party operations, the first on
the right. -/
@[simp] theorem partyOp_comp (c : PartyCircuit G X Y) (c' : PartyCircuit G Y Z) (p : P) :
    (comp c c').partyOp p = c'.partyOp p * c.partyOp p :=
  rfl

end Rules

/-! ### Parties not named by a local circuit -/

omit [GateFamily G] in
/-- **A local circuit is the identity at a party it does not name**: the bases agree there, and
the party operation is the identification of the equal bases. -/
theorem partyOp_of_notMem_parties [Fintype P] : {X Y : P → Type} → [∀ p, DecidableEq (X p)] →
    (c : PartyCircuit G X Y) → c.IsLocal → (p : P) → p ∉ c.parties →
      ∃ h : Y p = X p, c.partyOp p = (Equiv.cast h).toPEquiv.toMatrix
  | _, _, _, done _, _, _, _ => ⟨rfl, by simp⟩
  | _, _, _, gate _ _ _, hc, _, _ => hc.elim
  | _, _, _, @localOp _ _ _ _ _ _ q hY A, _, p, hp => by
    have hpq : p ≠ q := by simpa [parties] using hp
    exact ⟨hY p hpq, localOpFamily_of_ne q hY A hpq⟩
  | _, _, _, @localOps _ _ _ _ _ _ A, _, p, hp => by
    simp only [parties, Finset.mem_filter, Finset.mem_univ, true_and, not_not] at hp
    obtain ⟨h, hA⟩ := hp
    refine ⟨h, ?_⟩
    ext y x
    simp [hA, PEquiv.toMatrix_apply, eq_comm]
  | _, _, _, @comp _ _ _ _ _ _ _ c c', hc, p, hp => by
    rw [parties, Finset.mem_union, not_or] at hp
    obtain ⟨h₁, e₁⟩ := partyOp_of_notMem_parties c hc.1 p hp.1
    obtain ⟨h₂, e₂⟩ := partyOp_of_notMem_parties c' hc.2 p hp.2
    refine ⟨h₂.trans h₁, ?_⟩
    rw [partyOp_comp, e₁, e₂, ← PEquiv.toMatrix_trans, ← Equiv.toPEquiv_trans]
    congr 2
    ext x
    simp

/-! ### Framed circuits -/

section Frame

variable [GateFrame G] (W : P → Type) [∀ p, Fintype (W p)] [∀ p, DecidableEq (W p)]

omit [DecidableEq P] [GateFamily G] [GateFrame G] [∀ p, Fintype (W p)]
  [∀ p, DecidableEq (W p)] in
/-- The identification of `W × Y` with `W × X` along an identification of `Y` with `X`. -/
private theorem cast_prod_mk {p : P} {T T' : Type} (h : T' = T) (h' : (W p × T') = (W p × T))
    (a : W p) (y : T') : cast h' (a, y) = (a, cast h y) := by
  subst h
  rfl

/-- **The party operation of a framed circuit is `1 ⊗` the party operation.** -/
theorem partyOp_frame : {X Y : P → Type} → [∀ p, Fintype (X p)] → [∀ p, DecidableEq (X p)] →
    (c : PartyCircuit G X Y) → (p : P) →
      (c.frame W).partyOp p = (1 : Matrix (W p) (W p) ℂ) ⊗ₖ c.partyOp p
  | _, _, _, _, done _, _ => one_kronecker_one.symm
  | _, _, _, _, @gate _ _ _ _ _ _ _ _ _, _ => (kronecker_zero _).symm
  | _, _, _, _, @localOp _ _ _ _ _ _ q hY A, p => by
    rw [frame, partyOp_localOp, partyOp_localOp]
    by_cases hp : p = q
    · subst hp
      rw [localOpFamily_self, localOpFamily_self]
    · rw [localOpFamily_of_ne _ _ _ hp, localOpFamily_of_ne _ _ _ hp]
      ext ⟨a, y⟩ ⟨b, x⟩
      rw [kroneckerMap_apply, PEquiv.toMatrix_apply, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply,
        Equiv.toPEquiv_apply, Equiv.cast_apply, Equiv.cast_apply, cast_prod_mk W (hY p hp),
        one_apply]
      by_cases hab : a = b <;> simp [hab, Prod.ext_iff]
  | _, _, _, _, @localOps _ _ _ _ _ _ _, _ => rfl
  | _, _, _, _, @comp _ _ _ _ _ _ _ c c', p => by
    rw [frame, partyOp_comp, partyOp_comp, partyOp_frame c, partyOp_frame c', ← mul_kronecker_mul,
      Matrix.one_mul]

/-- **The region operation of a framed circuit is `1 ⊗` the region operation**, read along the
pairing of configurations. -/
theorem regionOp_frame [∀ p, Fintype (X p)] [∀ p, DecidableEq (X p)] (c : PartyCircuit G X Y)
    (R : Finset P) :
    (c.frame W).regionOp R =
      reindex (Equiv.arrowProdEquivProdArrow {v // v ∈ R} (fun v ↦ W v) (fun v ↦ Y v)).symm
        (Equiv.arrowProdEquivProdArrow {v // v ∈ R} (fun v ↦ W v) (fun v ↦ X v)).symm
        ((1 : Matrix (RegionConfig W R) (RegionConfig W R) ℂ) ⊗ₖ c.regionOp R) := by
  simp only [regionOp, partyOp_frame]
  rw [piKronecker_kronecker, piKronecker_one]

omit [DecidableEq P] in
/-- A framed circuit is local exactly when the circuit is. -/
@[simp] theorem isLocal_frame : {X Y : P → Type} → [∀ p, Fintype (X p)] →
    [∀ p, DecidableEq (X p)] → (c : PartyCircuit G X Y) → (c.frame W).IsLocal ↔ c.IsLocal
  | _, _, _, _, done _ => Iff.rfl
  | _, _, _, _, @gate _ _ _ _ _ _ _ _ _ => Iff.rfl
  | _, _, _, _, @localOp _ _ _ _ _ _ _ _ _ => Iff.rfl
  | _, _, _, _, @localOps _ _ _ _ _ _ _ => Iff.rfl
  | _, _, _, _, @comp _ _ _ _ _ _ _ c c' => and_congr (isLocal_frame c) (isLocal_frame c')

end Frame

end PartyCircuit

/-! ### Coarsened words -/

namespace Word

variable [Fintype P] {Q : Type} [DecidableEq Q] (f : P → Q)

omit [DecidableEq P] in
/-- A site of the block `b` has its block equal to `b`. -/
private theorem eq_of_mem_block {v : P} {b : Q} (h : v ∈ blockPreimage f {b}) : f v = b :=
  Finset.mem_singleton.mp (Finset.mem_filter.mp h).2

/-- **A coarsened local word is local.** -/
theorem isLocal_coarsen : {X Y : P → Type} → [∀ p, Fintype (X p)] → [∀ p, DecidableEq (X p)] →
    {w : Word X Y} → PartyCircuit.IsLocal w → PartyCircuit.IsLocal (coarsen f w)
  | _, _, _, _, .done _, _ => trivial
  | _, _, _, _, @PartyCircuit.gate _ _ _ _ _ _ _ _ _, hw => hw.elim
  | _, _, _, _, @PartyCircuit.localOp _ _ _ _ _ _ _ _ _, _ => trivial
  | _, _, _, _, @PartyCircuit.localOps _ _ _ _ _ _ _, _ => trivial
  | _, _, _, _, @PartyCircuit.comp _ _ _ _ _ _ _ _ _, hw =>
    ⟨isLocal_coarsen hw.1, isLocal_coarsen hw.2⟩

/-- **The party operation at a block of a coarsened local word is the region operation of the
word on the block.** The basis of the block `b` is the configurations of `f⁻¹{b}`. Source:
`04-compression.tex`, lines 233–251 and 409–417. -/
theorem partyOp_coarsen : {X Y : P → Type} → [∀ p, Fintype (X p)] → [∀ p, DecidableEq (X p)] →
    (w : Word X Y) → PartyCircuit.IsLocal w → (b : Q) →
      (coarsen f w).partyOp b = w.regionOp (blockPreimage f {b})
  | _, _, _, _, .done _, _, _ => piKronecker_one.symm
  | _, _, _, _, @PartyCircuit.gate _ _ _ _ _ _ _ _ _, hw, _ => hw.elim
  | _, _, _, _, @PartyCircuit.localOp _ _ _ _ _ _ p hY A, _, b => by
    rw [coarsen_localOp, PartyCircuit.partyOp_localOp, PartyCircuit.regionOp,
      PartyCircuit.partyOp_localOp]
    by_cases hb : b = f p
    · subst hb
      rw [PartyCircuit.localOpFamily_self]
      have hp : p ∈ blockPreimage f {f p} := by simp
      ext y x
      rw [subregionPlaceBetween_apply, piKronecker_apply, submatrix_apply,
        ← Finset.mul_prod_erase _ _ (Finset.mem_univ ⟨p, hp⟩)]
      have hf : ∀ v (hv : v ≠ (⟨p, hp⟩ : {v // v ∈ blockPreimage f {f p}})),
          PartyCircuit.localOpFamily p hY A v.1 (y v) (x v) =
            if cast (hY v.1 fun e ↦ hv (Subtype.ext e)) (y v) = x v then 1 else 0 := by
        intro v hv
        rw [PartyCircuit.localOpFamily_of_ne p hY A fun e ↦ hv (Subtype.ext e)]
        simp [PEquiv.toMatrix_apply, eq_comm]
      have hrest : ∏ v ∈ Finset.univ.erase (⟨p, hp⟩ : {v // v ∈ blockPreimage f {f p}}),
          PartyCircuit.localOpFamily p hY A v.1 (y v) (x v) =
            if ∀ (v : {v // v ∈ blockPreimage f {f p}}) (hv : v.1 ∉ ({p} : Finset P)),
              cast (hY v.1 (Finset.notMem_singleton.mp hv)) (y v) = x v then 1 else 0 := by
        split_ifs with h
        · refine Finset.prod_eq_one fun v hv ↦ ?_
          have hv' := Finset.ne_of_mem_erase hv
          rw [hf v hv']
          simp [h v (Finset.notMem_singleton.mpr fun e ↦ hv' (Subtype.ext e))]
        · push Not at h
          obtain ⟨v, hv, hne⟩ := h
          have hv' : v ≠ ⟨p, hp⟩ := fun e ↦ hv (Finset.mem_singleton.mpr (congrArg Subtype.val e))
          refine Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hv', Finset.mem_univ v⟩) ?_
          rw [hf v hv']
          simp [hne]
      have h0 : PartyCircuit.localOpFamily p hY A
          (⟨p, hp⟩ : {v // v ∈ blockPreimage f {f p}}).1 = A :=
        PartyCircuit.localOpFamily_self p hY A
      rw [hrest, mul_ite, mul_one, mul_zero, h0]
    · have hne : ∀ v : {v // v ∈ blockPreimage f {b}}, v.1 ≠ p := fun v e ↦
        hb (e ▸ eq_of_mem_block f v.2).symm
      rw [PartyCircuit.localOpFamily_of_ne _ _ _ hb]
      simp only [PartyCircuit.localOpFamily_of_ne p hY A (hne _)]
      exact (piKronecker_cast _ _).symm
  | _, _, _, _, @PartyCircuit.localOps _ _ _ _ _ _ _, _, _ => rfl
  | _, _, _, _, @PartyCircuit.comp _ _ _ _ _ _ _ w w', hw, b => by
    rw [coarsen_comp, PartyCircuit.partyOp_comp, partyOp_coarsen w hw.1,
      partyOp_coarsen w' hw.2, PartyCircuit.regionOp, PartyCircuit.regionOp, piKronecker_mul]
    rfl

/-- **At a block that is a single party `p`**, the party operation of a coarsened local word is
the party operation of `p`, read through the value of a block configuration at `p`. -/
theorem partyOp_coarsen_of_fiber {X Y : P → Type} [∀ p, Fintype (X p)] [∀ p, DecidableEq (X p)]
    (w : Word X Y) (hw : PartyCircuit.IsLocal w) {b : Q} {p : P} (hf : ∀ r, f r = b ↔ r = p) :
    (coarsen f w).partyOp b =
      (w.partyOp p).submatrix (fun y ↦ y ⟨p, by simpa using (hf p).mpr rfl⟩)
        (fun x ↦ x ⟨p, by simpa using (hf p).mpr rfl⟩) := by
  rw [partyOp_coarsen f w hw]
  ext y x
  rw [PartyCircuit.regionOp, piKronecker_apply, submatrix_apply]
  have hp : p ∈ blockPreimage f {b} := by simpa using (hf p).mpr rfl
  rw [Fintype.prod_eq_single (⟨p, hp⟩ : {v // v ∈ blockPreimage f {b}}) fun v hv ↦
    absurd (Subtype.ext ((hf v.1).mp (eq_of_mem_block f v.2))) hv]

/-- **At a block containing no party**, every entry of the party operation of a coarsened local
word is `1`: the block has one configuration. -/
theorem partyOp_coarsen_apply_of_forall_ne {X Y : P → Type} [∀ p, Fintype (X p)]
    [∀ p, DecidableEq (X p)] (w : Word X Y) (hw : PartyCircuit.IsLocal w) {b : Q}
    (hb : ∀ p, f p ≠ b) (y : blockSystem f Y b) (x : blockSystem f X b) :
    (coarsen f w).partyOp b y x = 1 := by
  rw [partyOp_coarsen f w hw, PartyCircuit.regionOp, piKronecker_apply]
  exact Finset.prod_eq_one fun v _ ↦ (hb v.1 (eq_of_mem_block f v.2)).elim

/-- **The region operation of a coarsened local word on a region of blocks is the region
operation of the word on its preimage**, read along `blockRegionConfigEquiv`. -/
theorem regionOp_coarsen {X Y : P → Type} [∀ p, Fintype (X p)] [∀ p, DecidableEq (X p)]
    (w : Word X Y) (hw : PartyCircuit.IsLocal w) (R : Finset Q) :
    (coarsen f w).regionOp R =
      reindex (blockRegionConfigEquiv f Y R).symm (blockRegionConfigEquiv f X R).symm
        (w.regionOp (blockPreimage f R)) := by
  let e : {v // v ∈ blockPreimage f R} ≃ Σ b : {b // b ∈ R}, {v // v ∈ blockPreimage f {b.1}} :=
    { toFun := fun v ↦ ⟨⟨f v.1, (Finset.mem_filter.mp v.2).2⟩, v.1,
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, Finset.mem_singleton_self _⟩⟩
      invFun := fun s ↦ ⟨s.2.1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by
        simp [eq_of_mem_block f s.2.2]⟩⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun ⟨⟨b, hb⟩, v, hv⟩ ↦ by
        obtain rfl : f v = b := eq_of_mem_block f hv
        rfl }
  ext z z'
  simp only [reindex_apply, submatrix_apply, Equiv.symm_symm, PartyCircuit.regionOp,
    piKronecker_apply]
  rw [Finset.prod_congr rfl fun b _ ↦
    congrFun (congrFun (partyOp_coarsen f w hw b.1) (z b)) (z' b)]
  simp only [PartyCircuit.regionOp, piKronecker_apply]
  rw [← Fintype.prod_sigma (fun s : (Σ b : {b // b ∈ R}, {v // v ∈ blockPreimage f {b.1}}) ↦
    w.partyOp s.2.1 (z s.1 s.2) (z' s.1 s.2))]
  exact (Fintype.prod_equiv e _ _ fun _ ↦ rfl).symm

/-- **The parties of a coarsened word lie in the image of the parties of the word.** -/
theorem parties_coarsen_subset [Fintype Q] : {X Y : P → Type} → [∀ p, Fintype (X p)] →
    [∀ p, DecidableEq (X p)] → (w : Word X Y) →
      PartyCircuit.parties (coarsen f w) ⊆ (PartyCircuit.parties w).image f
  | _, _, _, _, .done _ => fun _ h ↦ absurd h (Finset.notMem_empty _)
  | _, _, _, _, @PartyCircuit.gate _ _ _ _ _ _ D hY g => by
    by_cases h : f g.left = f g.right
    · rw [coarsen, dite_eq_left h]
      simpa [PartyCircuit.parties] using ⟨g.left, g.left_mem, rfl⟩
    · rw [coarsen, dite_eq_right h]
      simp [PartyCircuit.parties]
  | _, _, _, _, @PartyCircuit.localOp _ _ _ _ _ _ p hY A => by
    simp [coarsen_localOp, PartyCircuit.parties]
  | X, Y, _, _, @PartyCircuit.localOps _ _ _ _ _ _ A => by
    intro b hb
    simp only [coarsen, PartyCircuit.parties, Finset.mem_filter, Finset.mem_univ,
      true_and] at hb
    refine Finset.mem_image.mpr (by_contra fun hbi ↦ hb ?_)
    have hv (v : {v // v ∈ blockPreimage f {b}}) := fun hmem ↦
      hbi ⟨v.1, hmem, eq_of_mem_block f v.2⟩
    simp only [PartyCircuit.parties, Finset.mem_filter, Finset.mem_univ, true_and, imp_false,
      not_not] at hv
    choose h hA using hv
    have H : blockSystem f Y b = blockSystem f X b :=
      congrArg (fun T : {v // v ∈ blockPreimage f {b}} → Type ↦ ∀ v, T v) (funext h)
    refine ⟨H, fun y x ↦ ?_⟩
    simp only [piKronecker_apply, hA]
    by_cases hc : cast H y = x
    · rw [ite_eq_left hc]
      exact Finset.prod_eq_one fun v _ ↦ ite_eq_left ((cast_pi_eq_iff h H y x).mp hc v)
    · rw [ite_eq_right hc]
      obtain ⟨v, hv⟩ := not_forall.mp (mt (cast_pi_eq_iff h H y x).mpr hc)
      exact Finset.prod_eq_zero (Finset.mem_univ v) (ite_eq_right hv)
  | _, _, _, _, @PartyCircuit.comp _ _ _ _ _ _ _ w w' => by
    rw [coarsen_comp, PartyCircuit.parties, PartyCircuit.parties, Finset.image_union]
    exact Finset.union_subset_union (parties_coarsen_subset w) (parties_coarsen_subset w')

/-- **Coarsening a framed word.** The blocks of the framed system are configurations of pairs,
the blocks of the framed coarse word pairs of configurations; read along the identification of
the two, the operators agree. -/
theorem op_coarsen_frame [Fintype Q] (W : P → Type) [∀ p, Fintype (W p)] [∀ p, DecidableEq (W p)]
    {X Y : P → Type} [∀ p, Fintype (X p)] [∀ p, DecidableEq (X p)] (w : Word X Y) :
    (coarsen f (w.frame W)).op =
      reindex
        ((blockConfigProdEquiv f W Y).trans
          (Equiv.arrowProdEquivProdArrow Q (blockSystem f W) (blockSystem f Y)).symm).symm
        ((blockConfigProdEquiv f W X).trans
          (Equiv.arrowProdEquivProdArrow Q (blockSystem f W) (blockSystem f X)).symm).symm
        (Word.op ((coarsen f w).frame (blockSystem f W))) := by
  rw [op_coarsen, Word.op_frame, reindex_blockConfigEquiv_one_kronecker, Word.op_frame,
    op_coarsen]
  ext y x
  simp only [reindex_apply, submatrix_apply, Equiv.symm_symm, Equiv.trans_apply,
    Equiv.apply_symm_apply]

omit [Fintype P] in
/-- **The party operations of a local word run on its cell**: those of the word at the parties of
the cell, and the identification of the equal bases at the other parties. -/
theorem partyOp_onCell (D : Finset P) {X Y : P → Type} [∀ p, Fintype (X p)]
    [∀ p, DecidableEq (X p)] [∀ p, Fintype (Y p)] [∀ p, DecidableEq (Y p)]
    (hY : ∀ s ∉ D, Y s = X s) (w : Word (fun s : ↥D ↦ X s) (fun s : ↥D ↦ Y s))
    (hw : PartyCircuit.IsLocal w) (p : P) :
    (onCell D hY w).partyOp p =
      if h : p ∈ D then w.partyOp ⟨p, h⟩ else (Equiv.cast (hY p h)).toPEquiv.toMatrix := by
  rw [onCell, PartyCircuit.partyOp_comp, PartyCircuit.partyOp_comp, PartyCircuit.partyOp_frame,
    partyOp_coarsen Subtype.val w hw]
  change (cellEquiv D X Y hY p).toPEquiv.toMatrix * (((1 : Matrix (p ∉ D → X p) _ ℂ) ⊗ₖ _) *
    (cellEquiv D X X (fun _ _ ↦ rfl) p).symm.toPEquiv.toMatrix) = _
  rw [PEquiv.toMatrix_toPEquiv_mul, PEquiv.mul_toMatrix_toPEquiv]
  ext y x
  simp only [submatrix_apply, id, Equiv.symm_symm, kroneckerMap_apply, one_apply,
    PartyCircuit.regionOp, piKronecker_apply]
  by_cases hp : p ∈ D
  · have hk : (⟨p, hp⟩ : ↥D) ∈ blockPreimage (Subtype.val : ↥D → P) {p} := by simp
    rw [dite_eq_left hp, ite_eq_left (funext fun h ↦ (h hp).elim), one_mul,
      Fintype.prod_eq_single (⟨⟨p, hp⟩, hk⟩ : {k // k ∈ blockPreimage (Subtype.val : ↥D → P) {p}})
        fun k hk' ↦ absurd (Subtype.ext (Subtype.ext (eq_of_mem_block Subtype.val k.2))) hk']
    rfl
  · rw [dite_eq_right hp, Finset.prod_eq_one
      fun (k : {k // k ∈ blockPreimage (Subtype.val : ↥D → P) {p}}) _ ↦
        (hp (eq_of_mem_block Subtype.val k.2 ▸ k.1.2)).elim, mul_one]
    simp [cellEquiv, PEquiv.toMatrix_apply, funext_iff, hp, eq_comm]
end Word

/-! ### Restricted words and words on no parties -/

namespace Word

variable (S : Finset P)

/-- **The party operations of a restricted word are those of the word.** -/
theorem partyOp_restrict : {X Y : P → Type} → [∀ p, DecidableEq (X p)] → (w : Word X Y) →
    (h : w.UsesOnly ↑S) → (v : ↥S) → (restrict S w h).partyOp v = w.partyOp v.1
  | _, _, _, .done _, _, _ => rfl
  | _, _, _, @PartyCircuit.gate _ _ _ _ _ _ _ _ _, _, _ => rfl
  | X, Y, _, @PartyCircuit.localOp _ _ _ _ _ _ p hY A, h, ⟨v, hv⟩ => by
    rw [restrict, PartyCircuit.partyOp_localOp, PartyCircuit.partyOp_localOp]
    by_cases hvp : v = p
    · subst hvp
      change PartyCircuit.localOpFamily (P := ↥S) (X := fun s : ↥S ↦ X s)
          (Y := fun s : ↥S ↦ Y s) ⟨v, h⟩ _ A ⟨v, h⟩ =
        PartyCircuit.localOpFamily v hY A v
      rw [PartyCircuit.localOpFamily_self, PartyCircuit.localOpFamily_self]
    · rw [PartyCircuit.localOpFamily_of_ne _ _ _ fun e ↦ hvp (congrArg Subtype.val e),
        PartyCircuit.localOpFamily_of_ne _ _ _ hvp]
  | _, _, _, @PartyCircuit.localOps _ _ _ _ _ _ _, _, _ => rfl
  | _, _, _, @PartyCircuit.comp _ _ _ _ _ _ _ w w', h, v => by
    rw [restrict, PartyCircuit.partyOp_comp, PartyCircuit.partyOp_comp,
      partyOp_restrict w h.1 v, partyOp_restrict w' h.2 v]

/-- A restricted word is local exactly when the word is. -/
@[simp] theorem isLocal_restrict : {X Y : P → Type} → (w : Word X Y) → (h : w.UsesOnly ↑S) →
    PartyCircuit.IsLocal (restrict S w h) ↔ PartyCircuit.IsLocal w
  | _, _, .done _, _ => Iff.rfl
  | _, _, @PartyCircuit.gate _ _ _ _ _ _ _ _ _, _ => Iff.rfl
  | _, _, @PartyCircuit.localOp _ _ _ _ _ _ _ _ _, _ => Iff.rfl
  | _, _, @PartyCircuit.localOps _ _ _ _ _ _ _, _ => Iff.rfl
  | _, _, @PartyCircuit.comp _ _ _ _ _ _ _ w w', h =>
    and_congr (isLocal_restrict w h.1) (isLocal_restrict w' h.2)

/-- **A word on a type of no parties has every entry of its operator equal to `1`**: each
system has one configuration, and the word has no pair source. -/
theorem op_apply_of_isEmpty [Fintype P] [IsEmpty P] : {X Y : P → Type} →
    [∀ p, Fintype (X p)] → [∀ p, DecidableEq (X p)] → (w : Word X Y) →
      (y : Config Y) → (x : Config X) → w.op y x = 1
  | _, _, _, _, .done _, y, x => by
    rw [Word.op, PartyCircuit.op_done, one_apply, ite_eq_left (Subsingleton.elim y x)]
  | _, _, _, _, @PartyCircuit.gate _ _ _ _ _ _ _ _ g, _, _ => (IsEmpty.false g.left).elim
  | _, _, _, _, @PartyCircuit.localOp _ _ _ _ _ _ p _ _, _, _ => (IsEmpty.false p).elim
  | _, _, _, _, @PartyCircuit.localOps _ _ _ _ _ _ _, y, x => by
    rw [Word.op, PartyCircuit.op_localOps, piKronecker_apply, Finset.univ_eq_empty,
      Finset.prod_empty]
  | _, _, _, _, @PartyCircuit.comp _ _ _ _ _ _ _ w w', y, x => by
    rw [Word.op_comp, mul_apply]
    simp only [op_apply_of_isEmpty w, op_apply_of_isEmpty w', mul_one, Finset.sum_const,
      Finset.card_univ, Fintype.card_unique, one_smul]

end Word

end QuantumCircuit.Party
