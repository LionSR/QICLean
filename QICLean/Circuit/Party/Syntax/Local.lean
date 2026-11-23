/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Circuit.Party.Syntax.Word
import QICLean.Analysis.Norm.PiKroneckerNorm

/-!
# Party circuits without gates act party by party

One local operation `A` of the party `p` is the Kronecker product of the family that is `A` at
`p` and the identification of the equal bases at the other parties (`localOpFamily`,
`PartyCircuit.op_localOp_eq_piKronecker`). A party circuit without gates (`IsLocal`, a
structural predicate; for a word, no pair source) therefore acts party by party: its operator is
the Kronecker product of its *party operations* `partyOp c p`, the products along the circuit
of its local operations at `p` (`PartyCircuit.op_eq_piKronecker_partyOp`); read across a region
and its complement it is the product of the *region operation* and the operation of the
complement (`PartyCircuit.op_eq_reindex_kronecker_regionOp`). The party operations of an allowed
circuit are contractions, so an allowed word without pair sources is one contraction at each
party (`Word.exists_piKronecker_of_sources_eq_nil`).

The *parties* of a party circuit are those named by its operations: the cells of its gates, the
party of each of its local operations, whatever its matrix (a scalar local operation names its
party), and the parties where a family of local operations at every party is not the
identification of equal bases.

## Main definitions

* `QuantumCircuit.Party.PartyCircuit.localOpFamily`.
* `QuantumCircuit.Party.PartyCircuit.IsLocal`, `partyOp`, `regionOp`, `parties`.

## Main results

* `QuantumCircuit.Party.PartyCircuit.op_localOp_eq_piKronecker`.
* `QuantumCircuit.Party.PartyCircuit.op_eq_piKronecker_partyOp`,
  `QuantumCircuit.Party.PartyCircuit.op_eq_reindex_kronecker_regionOp`.
* `QuantumCircuit.Party.PartyCircuit.norm_partyOp_le_one`,
  `QuantumCircuit.Party.PartyCircuit.exists_eq_piKronecker`,
  `QuantumCircuit.Party.Word.exists_piKronecker_of_sources_eq_nil`.
* `QuantumCircuit.Party.Word.isLocal_iff_sources_eq_nil`,
  `QuantumCircuit.Party.Word.usesOnly_iff_parties_subset`.

## References

* Polynomial-PEPS manuscript (September 24, 2026), Theorem 5.2, `04-compression.tex`,
  lines 233–251 (collecting the local maps of a source-free word by party).
-/

open Matrix ManyBody
open scoped Kronecker Matrix.Norms.L2Operator

namespace QuantumCircuit.Party

variable {P : Type} [DecidableEq P]

namespace PartyCircuit

variable {G : Finset P → (P → Type) → (P → Type) → Type 1} [GateFamily G] {X Y Z : P → Type}

/-! ### One local operation as a family of party matrices -/

/-- The family of party matrices of one local operation: `A` at `p`, the identification of the
equal bases elsewhere. -/
def localOpFamily [∀ p, DecidableEq (X p)] (p : P) (hY : ∀ s ≠ p, Y s = X s)
    (A : Matrix (Y p) (X p) ℂ) (s : P) : Matrix (Y s) (X s) ℂ :=
  if h : s = p then by subst h; exact A else (Equiv.cast (hY s h)).toPEquiv.toMatrix

/-- The family at the acting party. -/
@[simp] theorem localOpFamily_self [∀ p, DecidableEq (X p)] (p : P) (hY : ∀ s ≠ p, Y s = X s)
    (A : Matrix (Y p) (X p) ℂ) : localOpFamily p hY A p = A := by
  simp [localOpFamily]

/-- The family away from the acting party. -/
theorem localOpFamily_of_ne [∀ p, DecidableEq (X p)] (p : P) (hY : ∀ s ≠ p, Y s = X s)
    (A : Matrix (Y p) (X p) ℂ) {s : P} (hs : s ≠ p) :
    localOpFamily p hY A s = (Equiv.cast (hY s hs)).toPEquiv.toMatrix := by
  simp [localOpFamily, hs]

/-- The family of a contraction consists of contractions. -/
theorem norm_localOpFamily_le_one [∀ p, Fintype (X p)] [∀ p, DecidableEq (X p)]
    [∀ p, Fintype (Y p)] (p : P) (hY : ∀ s ≠ p, Y s = X s) {A : Matrix (Y p) (X p) ℂ}
    (hA : ‖A‖ ≤ 1) (s : P) : ‖localOpFamily p hY A s‖ ≤ 1 := by
  by_cases hs : s = p
  · subst hs
    rwa [localOpFamily_self]
  · rw [localOpFamily_of_ne p hY A hs]
    exact l2_opNorm_toMatrix_toPEquiv_le _

/-- **One local operation is the Kronecker product of its party family.** -/
theorem op_localOp_eq_piKronecker [Fintype P] [GateFamily.UniqueOutcome G]
    (ev : Interpretation G) [∀ p, Fintype (X p)] [∀ p, DecidableEq (X p)] [∀ p, Fintype (Y p)]
    [∀ p, DecidableEq (Y p)] (p : P) (hY : ∀ s ≠ p, Y s = X s) (A : Matrix (Y p) (X p) ℂ) :
    (localOp (G := G) p hY A).op ev = piKronecker (localOpFamily p hY A) := by
  ext y x
  rw [op_localOp, placeBetween_apply, piKronecker_apply,
    ← Finset.mul_prod_erase _ _ (Finset.mem_univ p), localOpFamily_self]
  have hf : ∀ s (hs : s ≠ p), localOpFamily p hY A s (y s) (x s) =
      if cast (hY s hs) (y s) = x s then 1 else 0 := fun s hs ↦ by
    rw [localOpFamily_of_ne p hY A hs]
    simp [PEquiv.toMatrix_apply, eq_comm]
  have hrest : ∏ s ∈ Finset.univ.erase p, localOpFamily p hY A s (y s) (x s) =
      if ∀ v (hv : v ∉ ({p} : Finset P)), cast (hY v (Finset.notMem_singleton.mp hv)) (y v) = x v
        then 1 else 0 := by
    split_ifs with h
    · refine Finset.prod_eq_one fun s hs ↦ ?_
      have hs' := Finset.ne_of_mem_erase hs
      rw [hf s hs']
      simp [h s (Finset.notMem_singleton.mpr hs')]
    · push Not at h
      obtain ⟨v, hv, hne⟩ := h
      have hv' : v ≠ p := Finset.notMem_singleton.mp hv
      refine Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hv', Finset.mem_univ v⟩) ?_
      rw [hf v hv']
      simp [hne]
  rw [hrest, mul_ite, mul_one, mul_zero]
  rfl

/-! ### Circuits without gates -/

/-- A party circuit is local when it has no gate. -/
def IsLocal : {X Y : P → Type} → PartyCircuit G X Y → Prop
  | _, _, done _ => True
  | _, _, gate _ _ _ => False
  | _, _, localOp _ _ _ => True
  | _, _, localOps _ => True
  | _, _, comp c c' => IsLocal c ∧ IsLocal c'

/-- Being local is decidable. -/
instance instDecidableIsLocal : {X Y : P → Type} → (c : PartyCircuit G X Y) →
    Decidable c.IsLocal
  | _, _, done _ => inferInstanceAs (Decidable True)
  | _, _, gate _ _ _ => inferInstanceAs (Decidable False)
  | _, _, localOp _ _ _ => inferInstanceAs (Decidable True)
  | _, _, localOps _ => inferInstanceAs (Decidable True)
  | _, _, comp c c' =>
    letI := instDecidableIsLocal c
    letI := instDecidableIsLocal c'
    inferInstanceAs (Decidable (c.IsLocal ∧ c'.IsLocal))

omit [DecidableEq P] [GateFamily G] in
/-- A party circuit is local exactly when it has no gate. -/
theorem isLocal_iff_gates_eq_nil : {X Y : P → Type} → (c : PartyCircuit G X Y) →
    c.IsLocal ↔ c.gates = []
  | _, _, done _ => iff_of_true trivial rfl
  | _, _, gate _ _ _ => iff_of_false id (List.cons_ne_nil _ _)
  | _, _, localOp _ _ _ => iff_of_true trivial rfl
  | _, _, localOps _ => iff_of_true trivial rfl
  | _, _, comp c c' => (and_congr (isLocal_iff_gates_eq_nil c)
      (isLocal_iff_gates_eq_nil c')).trans List.append_eq_nil_iff.symm

/-- The party operation at `p` of a party circuit: the product along the circuit of its local
operations at `p`, the first on the right. It is meaningful for local circuits; a gate
contributes `0`. -/
noncomputable def partyOp : {X Y : P → Type} → [∀ p, DecidableEq (X p)] →
    PartyCircuit G X Y → ∀ p, Matrix (Y p) (X p) ℂ
  | _, _, _, done _ => fun _ ↦ 1
  | _, _, _, gate _ _ _ => fun _ ↦ 0
  | _, _, _, localOp p hY A => localOpFamily p hY A
  | _, _, _, localOps A => A
  | _, _, _, comp c c' => fun p ↦ partyOp c' p * partyOp c p

/-- The region operation of a party circuit on `R`: the Kronecker product of its party
operations at the parties of `R`. -/
noncomputable def regionOp [∀ p, DecidableEq (X p)] (c : PartyCircuit G X Y) (R : Finset P) :
    Matrix (RegionConfig Y R) (RegionConfig X R) ℂ :=
  piKronecker fun p : R ↦ c.partyOp p

section Ops

variable [Fintype P] [GateFamily.UniqueOutcome G] (ev : Interpretation G)

/-- **A local party circuit is the Kronecker product of its party operations.** Source:
`04-compression.tex`, lines 233–251. -/
theorem op_eq_piKronecker_partyOp : {X Y : P → Type} → [∀ p, Fintype (X p)] →
    [∀ p, DecidableEq (X p)] → (c : PartyCircuit G X Y) → c.IsLocal →
      c.op ev = piKronecker c.partyOp
  | _, _, _, _, done _, _ => piKronecker_one.symm
  | _, _, _, _, gate _ _ _, h => h.elim
  | _, _, _, _, localOp p hY A, _ => op_localOp_eq_piKronecker ev p hY A
  | _, _, _, _, localOps A, _ => op_localOps ev A
  | _, _, _, _, comp c c', h => by
    rw [op_comp, op_eq_piKronecker_partyOp c h.1, op_eq_piKronecker_partyOp c' h.2,
      piKronecker_mul]
    rfl

/-- A local party circuit read across a region `R` and its complement: the region operation
tensored with the product of the party operations outside `R`. -/
theorem op_eq_reindex_kronecker_regionOp [∀ p, Fintype (X p)] [∀ p, DecidableEq (X p)]
    (c : PartyCircuit G X Y) (hc : c.IsLocal) (R : Finset P) :
    c.op ev = reindex (cutEquiv Y R).symm (cutEquiv X R).symm
      (c.regionOp R ⊗ₖ piKronecker fun p : {p // p ∉ R} ↦ c.partyOp p) := by
  rw [op_eq_piKronecker_partyOp ev c hc, regionOp, ← reindex_cutEquiv_piKronecker,
    reindex_apply, reindex_apply, submatrix_submatrix]
  simp

omit [Fintype P] in
/-- **The party operations of an allowed circuit are contractions.** -/
theorem norm_partyOp_le_one
    {A : ∀ ⦃D : Finset P⦄ ⦃X Y : P → Type⦄ [∀ s, Fintype (X s)] [∀ s, DecidableEq (X s)]
      [∀ s, Fintype (Y s)] [∀ s, DecidableEq (Y s)], G D X Y → Prop} :
    {X Y : P → Type} → [∀ p, Fintype (X p)] → [∀ p, DecidableEq (X p)] →
      [∀ p, Fintype (Y p)] → {c : PartyCircuit G X Y} → c.IsAllowed ev A →
        ∀ p, ‖c.partyOp p‖ ≤ 1
  | X, _, iF, _, iF', done _, _ => fun p ↦ by
    obtain rfl : iF = iF' := Subsingleton.elim _ _
    change ‖(1 : Matrix (X p) (X p) ℂ)‖ ≤ 1
    simpa using l2_opNorm_toMatrix_toPEquiv_le (Equiv.refl (X p))
  | _, _, _, _, iF, @gate _ _ _ _ iF' _ _ _ _, _ => fun _ ↦ by
    obtain rfl : iF = iF' := Subsingleton.elim _ _
    change ‖(0 : Matrix _ _ ℂ)‖ ≤ 1
    simp
  | _, _, _, _, iF, @localOp _ _ _ _ iF' _ p hY _, h => by
    obtain rfl : iF = iF' := Subsingleton.elim _ _
    exact norm_localOpFamily_le_one p hY h
  | _, _, _, _, iF, @localOps _ _ _ _ iF' _ _, h => by
    obtain rfl : iF = iF' := Subsingleton.elim _ _
    exact h
  | _, _, _, _, _, comp c c', h => fun p ↦
    (l2_opNorm_mul _ _).trans ((mul_le_mul (norm_partyOp_le_one h.2 p)
      (norm_partyOp_le_one h.1 p) (norm_nonneg _) zero_le_one).trans_eq (one_mul 1))

omit [Fintype P] in
/-- The region operations of an allowed circuit are contractions. -/
theorem norm_regionOp_le_one
    {A : ∀ ⦃D : Finset P⦄ ⦃X Y : P → Type⦄ [∀ s, Fintype (X s)] [∀ s, DecidableEq (X s)]
      [∀ s, Fintype (Y s)] [∀ s, DecidableEq (Y s)], G D X Y → Prop}
    [∀ p, Fintype (X p)] [∀ p, DecidableEq (X p)] [∀ p, Fintype (Y p)]
    {c : PartyCircuit G X Y} (hc : c.IsAllowed ev A) (R : Finset P) :
    ‖c.regionOp R‖ ≤ 1 :=
  l2_opNorm_piKronecker_le_one fun p ↦ norm_partyOp_le_one ev hc p

/-- **An allowed local circuit is a tensor product of contractions at the parties.** -/
theorem exists_eq_piKronecker
    {A : ∀ ⦃D : Finset P⦄ ⦃X Y : P → Type⦄ [∀ s, Fintype (X s)] [∀ s, DecidableEq (X s)]
      [∀ s, Fintype (Y s)] [∀ s, DecidableEq (Y s)], G D X Y → Prop}
    [∀ p, Fintype (X p)] [∀ p, DecidableEq (X p)] [∀ p, Fintype (Y p)]
    {c : PartyCircuit G X Y} (hc : c.IsAllowed ev A) (hl : c.IsLocal) :
    ∃ B : ∀ p, Matrix (Y p) (X p) ℂ, (∀ p, ‖B p‖ ≤ 1) ∧ c.op ev = piKronecker B :=
  ⟨c.partyOp, norm_partyOp_le_one ev hc, op_eq_piKronecker_partyOp ev c hl⟩

end Ops

/-! ### The parties of a circuit -/

open Classical in
/-- The parties named by the operations of a party circuit: the cells of its gates, the party of
each local operation (whatever its matrix), and the parties at which a family of local
operations at every party is not the identification of equal bases. -/
noncomputable def parties [Fintype P] : {X Y : P → Type} → PartyCircuit G X Y → Finset P
  | _, _, done _ => ∅
  | _, _, gate D _ _ => D
  | _, _, localOp p _ _ => {p}
  | X, Y, localOps A => Finset.univ.filter fun p ↦
    ¬ ∃ h : Y p = X p, ∀ y x, A p y x = if cast h y = x then 1 else 0
  | _, _, comp c c' => parties c ∪ parties c'

end PartyCircuit

/-! ### Words without pair sources -/

namespace Word

variable {X Y : P → Type}

/-- A word is local exactly when it has no pair source. -/
theorem isLocal_iff_sources_eq_nil : {X Y : P → Type} → (w : Word X Y) →
    PartyCircuit.IsLocal w ↔ w.sources = []
  | _, _, PartyCircuit.done _ => iff_of_true trivial rfl
  | _, _, PartyCircuit.gate _ _ _ => iff_of_false id (List.cons_ne_nil _ _)
  | _, _, PartyCircuit.localOp _ _ _ => iff_of_true trivial rfl
  | _, _, PartyCircuit.localOps _ => iff_of_true trivial rfl
  | _, _, PartyCircuit.comp w w' => (and_comm.trans (and_congr (isLocal_iff_sources_eq_nil w')
      (isLocal_iff_sources_eq_nil w))).trans List.append_eq_nil_iff.symm

/-- **An allowed word without pair sources is one contraction at each party.** Source:
`04-compression.tex`, lines 233–251. -/
theorem exists_piKronecker_of_sources_eq_nil [Fintype P] [∀ p, Fintype (X p)]
    [∀ p, DecidableEq (X p)] [∀ p, Fintype (Y p)] {w : Word X Y} (hw : w.IsAllowed)
    (hs : w.sources = []) :
    ∃ A : ∀ p, Matrix (Y p) (X p) ℂ, (∀ p, ‖A p‖ ≤ 1) ∧ w.op = piKronecker A :=
  PartyCircuit.exists_eq_piKronecker _ hw ((isLocal_iff_sources_eq_nil w).mpr hs)

open Classical in
/-- **A word uses only the parties of `R` exactly when its parties lie in `R`.** -/
theorem usesOnly_iff_parties_subset [Fintype P] {R : Set P} : {X Y : P → Type} →
    (w : Word X Y) → w.UsesOnly R ↔ (↑(PartyCircuit.parties w) : Set P) ⊆ R
  | _, _, PartyCircuit.done _ => iff_of_true trivial (by simp [PartyCircuit.parties])
  | _, _, PartyCircuit.gate _ _ _ => Iff.rfl
  | _, _, PartyCircuit.localOp _ _ _ => by simp [UsesOnly, PartyCircuit.parties]
  | _, _, PartyCircuit.localOps _ => by
    simp only [UsesOnly, PartyCircuit.parties, Finset.coe_filter, Finset.mem_univ, true_and]
    exact ⟨fun h p hp ↦ by_contra fun hR ↦ hp (h p hR), fun h p hR ↦ by_contra fun hp ↦ hR (h hp)⟩
  | _, _, PartyCircuit.comp w w' => by
    rw [UsesOnly, usesOnly_iff_parties_subset w, usesOnly_iff_parties_subset w',
      PartyCircuit.parties, Finset.coe_union, Set.union_subset_iff]

/-- A word uses only its own parties. -/
theorem usesOnly_parties [Fintype P] (w : Word X Y) :
    w.UsesOnly ↑(PartyCircuit.parties w) :=
  (usesOnly_iff_parties_subset w).mpr subset_rfl

end Word

end QuantumCircuit.Party
