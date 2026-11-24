/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Circuit.Party.Original.Frame
import QICLean.Circuit.Party.Syntax.Local
import QICLean.Spectral.Eigenvalue.MatrixReindexEuclidean

/-!
# Finite sequences of original circuits

* **Relabellings.** `OriginalCircuit.relabel e` (no gate) and `OriginalCircuit.castSystems`,
  which reads a circuit between two systems equal to its own along the identifications of the
  bases: two relabellings and no gate.
* **Sequences.** `OriginalCircuit.sequence a step t` composes the stages
  `step s : OriginalCircuit (a s) (a (s + 1))`, `s < t`, for a family of systems
  `a : ℕ → P → Type`; operator, nonprivate count, participation and expansion bounds add up
  stage by stage.
* **Three stages.** `chainSystem`, `chainStep`: a first circuit into `B 0`, circuits from `B t`
  to `B (t + 1)` for `t < n`, a last circuit from `B n` to `Z`, then empty circuits, as one
  sequence; the stage boundaries are read by `castSystems`. A
  boundary adds two relabellings and nothing else: no gate, no cost, no participation, no gate
  occurrence (`numGates_castSystems`, `nonprivateCount_castSystems`,
  `participation_castSystems`, `participationCount_castSystems`, `gates_castSystems`,
  `castSystemsLocationsEquiv`), and the operator of a stage is the operator of its circuit read
  along the identification of the configurations (`op_castSystems`, `op_chainStep_succ_of_lt`).

Original circuits beside spectator factors are in `Original/Frame`.

## Main definitions

* `QuantumCircuit.Party.OriginalCircuit.relabel`,
  `QuantumCircuit.Party.OriginalCircuit.castSystems`.
* `QuantumCircuit.Party.OriginalCircuit.sequence`.
* `QuantumCircuit.Party.OriginalCircuit.chainSystem`, `chainStep`, `chainVec`.

## Main results

* `QuantumCircuit.Party.OriginalCircuit.op_sequence_succ`, `nonprivateCount_sequence`,
  `participation_sequence`, `isExpansionBounded_sequence`, `isMonomialBounded_sequence`.
* `QuantumCircuit.Party.OriginalCircuit.toEuclideanLin_op_relabel`,
  `toEuclideanLin_op_relabel_prodComm_prodVec` — relabellings on vectors.
* `QuantumCircuit.Party.OriginalCircuit.op_castSystems`, `numGates_castSystems`,
  `gateCount_castSystems`, `nonprivateCount_castSystems`, `participation_castSystems`,
  `participationCount_castSystems`, `gates_castSystems`, `participants_castSystemsLocationsEquiv`
  — the stage boundaries.
* `QuantumCircuit.Party.OriginalCircuit.chainStep_induction`, `op_chainStep_succ_of_lt`,
  `toEuclideanLin_op_chainStep_succ_of_gt`,
  `QuantumCircuit.Party.OriginalCircuit.norm_chainStep_op_sub_le`.

## References

* Polynomial-PEPS manuscript (September 24, 2026), `04-compression.tex`, lines 21–43 and 140–149
  and 199–229; Proposition 7.1, `06-geometry.tex`, lines 25–41 and 658–681; `07-assembly.tex`,
  lines 29–36.
-/

open Matrix ManyBody
open scoped Kronecker Matrix.Norms.L2Operator

namespace QuantumCircuit.Party

variable {P : Type} [DecidableEq P]

namespace OriginalCircuit


/-! ### Relabellings and identifications of systems

The stage boundaries of a sequence identify systems that are equal but not definitionally equal
(`chainSystem A B n Z (t + 1)` is `B t` only up to `if`); `castSystems` reads a circuit between
the equal systems by two relabellings along `Equiv.cast`, no gate. The two conditions under which
such boundaries are acceptable are the following lemmas.

1. **Nothing is counted at a boundary**: `numGates_castSystems`, `gateCount_castSystems` and
   `nonprivateCount_castSystems` (the gate count), `participation_castSystems`,
   `participationCount_castSystems`, `gates_castSystems` (the gates with their cells, systems
   and gate expansions, hence their sources and pair effects), `gateCells_castSystems`,
   `castSystemsLocationsEquiv` with `participants_castSystemsLocationsEquiv` (the gate
   occurrences), `gates_toEffectCircuit_castSystems` and the expansion, monomial and
   pair-source bounds `isExpansionBounded_castSystems`, `isMonomialBounded_castSystems`,
   `isSourceBounded_castSystems`.
2. **The operator is that of the circuit read along the configuration equivalence**:
   `op_castSystems` (reindexing along `Equiv.piCongrRight` of the casts), and on vectors
   `toEuclideanLin_op_castSystems`.

A property of circuits that is not preserved by the two relabellings does not pass to a stage
automatically: `chainStep_induction` assumes that it passes to identified systems. -/

section Relabel

variable {X Y Z X' Y' : P → Type} [∀ p, Fintype (X p)] [∀ p, DecidableEq (X p)]
  [∀ p, Fintype (Y p)] [∀ p, DecidableEq (Y p)]

/-- The relabelling of the bases along `e` as an original circuit: one local operation at every
party, no gate. -/
def relabel (e : ∀ s, Y s ≃ X s) : OriginalCircuit X Y :=
  localOps (fun s ↦ (e s).toPEquiv.toMatrix) fun s ↦ l2_opNorm_toMatrix_toPEquiv_le (e s)

/-- The relabelling is the relabelling of the party circuit. -/
@[simp] theorem toPartyCircuit_relabel (e : ∀ s, Y s ≃ X s) :
    (relabel e).toPartyCircuit = PartyCircuit.relabel e :=
  rfl

/-- The operator of a relabelling. -/
theorem op_relabel [Fintype P] (e : ∀ s, Y s ≃ X s) :
    (relabel e).op = (Equiv.piCongrRight e).toPEquiv.toMatrix :=
  PartyCircuit.op_relabel _ e

/-- A relabelling maps a vector `v` to `v` read along the relabelling of the configurations. -/
theorem toEuclideanLin_op_relabel [Fintype P] (e : ∀ s, Y s ≃ X s)
    (v : EuclideanSpace ℂ (Config X)) :
    toEuclideanLin (relabel e).op v =
      LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ (Equiv.piCongrRight e).symm v := by
  ext y
  simp [op_relabel, LinearIsometryEquiv.piLpCongrLeft_apply, Equiv.piCongrLeft'_apply,
    Matrix.toLpLin_apply, PEquiv.toMatrix_toPEquiv_mulVec]

/-- A relabelling exchanging the two factors of a product system maps `x ⊗ y` to `y ⊗ x`. -/
theorem toEuclideanLin_op_relabel_prodComm_prodVec [Fintype P] (x : EuclideanSpace ℂ (Config X))
    (y : EuclideanSpace ℂ (Config Y)) :
    toEuclideanLin (relabel fun p ↦ Equiv.prodComm (Y p) (X p)).op (prodVec x y) =
      prodVec y x := by
  ext z
  rw [toEuclideanLin_op_relabel]
  simp [LinearIsometryEquiv.piLpCongrLeft_apply, Equiv.piCongrLeft'_apply, mul_comm]

/-- A relabelling has no nonprivate gate. -/
@[simp] theorem nonprivateCount_relabel (e : ∀ s, Y s ≃ X s) : (relabel e).nonprivateCount = 0 :=
  rfl

/-- No party participates in a relabelling. -/
@[simp] theorem participation_relabel (e : ∀ s, Y s ≃ X s) (p : P) :
    (relabel e).participation p = 0 :=
  rfl

variable [∀ p, Fintype (X' p)] [∀ p, DecidableEq (X' p)] [∀ p, Fintype (Y' p)]
  [∀ p, DecidableEq (Y' p)]

/-- An original circuit read between systems equal to its own, along the identifications
`Equiv.cast` of the bases: a relabelling, the circuit, a relabelling. -/
def castSystems (w : OriginalCircuit X Y) (hX : X = X') (hY : Y = Y') : OriginalCircuit X' Y' :=
  ((relabel fun s ↦ Equiv.cast (congrFun hX s)).comp w).comp
    (relabel fun s ↦ Equiv.cast (congrFun hY s).symm)

/-- **The operator of a circuit between identified systems is its operator read along the
identifications of the configurations**. -/
theorem op_castSystems [Fintype P] (w : OriginalCircuit X Y) (hX : X = X') (hY : Y = Y') :
    (w.castSystems hX hY).op =
      reindex (Equiv.piCongrRight fun s ↦ Equiv.cast (congrFun hY s))
        (Equiv.piCongrRight fun s ↦ Equiv.cast (congrFun hX s)) w.op := by
  rw [castSystems, op_comp, op_comp, op_relabel, op_relabel, PEquiv.toMatrix_toPEquiv_mul,
    PEquiv.mul_toMatrix_toPEquiv]
  rfl

/-- The identifications add no gate. -/
@[simp] theorem numGates_castSystems (w : OriginalCircuit X Y) (hX : X = X') (hY : Y = Y') :
    (w.castSystems hX hY).toPartyCircuit.numGates = w.toPartyCircuit.numGates :=
  Nat.zero_add _

/-- The identifications add nothing to the gate count. -/
@[simp] theorem nonprivateCount_castSystems (w : OriginalCircuit X Y) (hX : X = X')
    (hY : Y = Y') : (w.castSystems hX hY).nonprivateCount = w.nonprivateCount :=
  Nat.zero_add _

/-- The identifications add nothing to the gate count. -/
@[simp] theorem gateCount_castSystems (w : OriginalCircuit X Y) (hX : X = X') (hY : Y = Y') :
    (w.castSystems hX hY).toPartyCircuit.gateCount = w.toPartyCircuit.gateCount :=
  Nat.zero_add _

/-- The identifications add nothing to the participation of a party. -/
@[simp] theorem participation_castSystems (w : OriginalCircuit X Y) (hX : X = X')
    (hY : Y = Y') (p : P) : (w.castSystems hX hY).participation p = w.participation p :=
  Nat.zero_add _

/-- The identifications add nothing to the number of gates containing a party. -/
@[simp] theorem participationCount_castSystems (w : OriginalCircuit X Y) (hX : X = X')
    (hY : Y = Y') (p : P) :
    (w.castSystems hX hY).toPartyCircuit.participationCount p =
      w.toPartyCircuit.participationCount p :=
  Nat.zero_add _

/-- **The identifications keep the gates**: the list of gates, with their cells, systems and gate
expansions (so their pair sources and pair effects), is that of the circuit. -/
@[simp] theorem gates_castSystems (w : OriginalCircuit X Y) (hX : X = X') (hY : Y = Y') :
    (w.castSystems hX hY).toPartyCircuit.gates = w.toPartyCircuit.gates :=
  (List.append_nil _).trans (List.nil_append _)

/-- The identifications keep the cells of the gates. -/
@[simp] theorem gateCells_castSystems (w : OriginalCircuit X Y) (hX : X = X') (hY : Y = Y') :
    (w.castSystems hX hY).toPartyCircuit.gateCells = w.toPartyCircuit.gateCells :=
  (List.append_nil _).trans (List.nil_append _)

/-- The effect circuit between identified systems has the gates of the effect circuit. -/
@[simp] theorem gates_toEffectCircuit_castSystems (w : OriginalCircuit X Y) (hX : X = X')
    (hY : Y = Y') : (w.castSystems hX hY).toEffectCircuit.gates = w.toEffectCircuit.gates :=
  (List.append_nil _).trans (List.nil_append _)

/-- The identifications keep the gate occurrences. -/
def castSystemsLocationsEquiv (w : OriginalCircuit X Y) (hX : X = X') (hY : Y = Y') :
    w.nonprivateLocations ≃ (w.castSystems hX hY).nonprivateLocations :=
  (Equiv.emptySum Empty _).symm.trans (Equiv.sumEmpty _ Empty).symm

/-- The identifications keep the cell of every gate occurrence. -/
@[simp] theorem participants_castSystemsLocationsEquiv (w : OriginalCircuit X Y) (hX : X = X')
    (hY : Y = Y') (g : w.nonprivateLocations) :
    (w.castSystems hX hY).participants (w.castSystemsLocationsEquiv hX hY g) = w.participants g :=
  rfl

/-- A circuit between identified systems has no gate exactly when the circuit has none. -/
@[simp] theorem isLocal_castSystems_iff (w : OriginalCircuit X Y) (hX : X = X') (hY : Y = Y') :
    (w.castSystems hX hY).toPartyCircuit.IsLocal ↔ w.toPartyCircuit.IsLocal :=
  ⟨fun h ↦ h.1.2, fun h ↦ ⟨⟨trivial, h⟩, trivial⟩⟩

/-- Identifying the systems keeps the expansion bounds. -/
theorem isExpansionBounded_castSystems (w : OriginalCircuit X Y) (hX : X = X') (hY : Y = Y')
    {r : ℕ} {S : ℝ} : (w.castSystems hX hY).IsExpansionBounded r S ↔ w.IsExpansionBounded r S := by
  simp only [castSystems, isExpansionBounded_comp]
  exact ⟨fun h ↦ h.1.2, fun h ↦ ⟨⟨trivial, h⟩, trivial⟩⟩

/-- Identifying the systems keeps the monomial bounds. -/
theorem isMonomialBounded_castSystems (w : OriginalCircuit X Y) (hX : X = X') (hY : Y = Y')
    {K : ℕ} : (w.castSystems hX hY).IsMonomialBounded K ↔ w.IsMonomialBounded K := by
  simp only [castSystems, isMonomialBounded_comp]
  exact ⟨fun h ↦ h.1.2, fun h ↦ ⟨⟨trivial, h⟩, trivial⟩⟩

/-- Identifying the systems keeps the pair-source bounds. -/
theorem isSourceBounded_castSystems (w : OriginalCircuit X Y) (hX : X = X') (hY : Y = Y')
    {r : ℕ} : (w.castSystems hX hY).IsSourceBounded r ↔ w.IsSourceBounded r := by
  simp only [castSystems, isSourceBounded_comp]
  exact ⟨fun h ↦ h.1.2, fun h ↦ ⟨⟨trivial, h⟩, trivial⟩⟩

/-- Identifying the systems keeps the cells of the occurrences. -/
theorem forall_participants_castSystems {Q : Finset P → Prop} (w : OriginalCircuit X Y)
    (hX : X = X') (hY : Y = Y') (h : ∀ g, Q (w.participants g)) :
    ∀ g, Q ((w.castSystems hX hY).participants g) := by
  rintro ((g | g) | g)
  · exact g.elim
  · exact h g
  · exact g.elim

end Relabel

/-! ### Finite sequences -/

section Sequence

variable (a : ℕ → P → Type) [∀ t p, Fintype (a t p)] [∀ t p, DecidableEq (a t p)]
  (step : ∀ t, OriginalCircuit (a t) (a (t + 1)))

/-- The chronological composite of the stages before `t`. Source: `06-geometry.tex`, lines 25–32,
and `07-assembly.tex`, lines 29–36. -/
def sequence : (t : ℕ) → OriginalCircuit (a 0) (a t)
  | 0 => done (a 0)
  | t + 1 => (sequence t).comp (step t)

/-- The composite of no stage is the empty circuit. -/
@[simp] theorem sequence_zero : sequence a step 0 = done (a 0) :=
  rfl

/-- The composite of the first `t + 1` stages is that of the first `t` followed by stage `t`. -/
theorem sequence_succ (t : ℕ) : sequence a step (t + 1) = (sequence a step t).comp (step t) :=
  rfl

/-- The composite of no stage is the identity. -/
theorem op_sequence_zero [Fintype P] : (sequence a step 0).op = 1 :=
  rfl

/-- The next stage acts after the composite. Source: `07-assembly.tex`, lines 29–36. -/
theorem op_sequence_succ [Fintype P] (t : ℕ) :
    (sequence a step (t + 1)).op = (step t).op * (sequence a step t).op :=
  op_comp _ _

/-- A uniform bound on the expansions of the stages bounds the composite. Source: Proposition 7.1,
item 2, `06-geometry.tex`, lines 25–32. -/
theorem isExpansionBounded_sequence (r : ℕ) (S : ℝ) (t : ℕ)
    (h : ∀ s < t, (step s).IsExpansionBounded r S) :
    (sequence a step t).IsExpansionBounded r S := by
  induction t with
  | zero => trivial
  | succ t ih => exact ⟨ih fun s hs ↦ h s (by omega), h t (by omega)⟩

/-- A uniform monomial bound of the stages bounds the composite. -/
theorem isMonomialBounded_sequence (K t : ℕ) (h : ∀ s < t, (step s).IsMonomialBounded K) :
    (sequence a step t).IsMonomialBounded K := by
  induction t with
  | zero => trivial
  | succ t ih => exact ⟨ih fun s hs ↦ h s (by omega), h t (by omega)⟩

/-- A uniform pair-source bound of the stages bounds the composite. -/
theorem isSourceBounded_sequence (r t : ℕ) (h : ∀ s < t, (step s).IsSourceBounded r) :
    (sequence a step t).IsSourceBounded r := by
  induction t with
  | zero => trivial
  | succ t ih => exact ⟨ih fun s hs ↦ h s (by omega), h t (by omega)⟩

/-- The composite keeps every nonprivate occurrence, repeated uses included. Source: Proposition
7.1, item 2, `06-geometry.tex`, lines 25–32, and `04-compression.tex`, lines 140–142. -/
theorem nonprivateCount_sequence (t : ℕ) :
    (sequence a step t).nonprivateCount = ∑ s ∈ Finset.range t, (step s).nonprivateCount := by
  induction t with
  | zero => rfl
  | succ t ih => rw [Finset.sum_range_succ, ← ih]; rfl

/-- A condition on the participants of every occurrence of every stage holds for the composite.
Source: Proposition 7.1, items 2 and 3, `06-geometry.tex`, lines 25–37. -/
theorem forall_participants_sequence (Q : Finset P → Prop) (t : ℕ)
    (h : ∀ s < t, ∀ g, Q ((step s).participants g)) :
    ∀ g, Q ((sequence a step t).participants g) := by
  induction t with
  | zero => exact fun g ↦ Empty.elim g
  | succ t ih =>
      rintro (g | g)
      · exact ih (fun s hs ↦ h s (by omega)) g
      · exact h t (by omega) g

/-- A party's participation is the sum over the stages. Source: Proposition 7.1, item 2,
`06-geometry.tex`, lines 31–32, and `04-compression.tex`, lines 140–142. -/
theorem participation_sequence (t : ℕ) (p : P) :
    (sequence a step t).participation p = ∑ s ∈ Finset.range t, (step s).participation p := by
  induction t with
  | zero => rfl
  | succ t ih => rw [Finset.sum_range_succ, ← ih]; rfl

end Sequence

/-! ### Three stages in a row -/

section Chain

variable (A : P → Type) (B : ℕ → P → Type) (n : ℕ) (Z : P → Type)

/-- The systems of a sequence made of a first circuit into `B 0`, the circuits from `B t` to `B (t +
1)` for `t < n`, and a last circuit from `B n` to `Z`, after which the system stays `Z`. -/
def chainSystem : ℕ → P → Type
  | 0 => A
  | t + 1 => fun p ↦ if t ≤ n then B t p else Z p

omit [DecidableEq P] in
variable {A B n Z} in
/-- Up to the last circuit, the system after stage `t` is `B t`. -/
theorem chainSystem_succ_of_le {t : ℕ} (h : t ≤ n) : chainSystem A B n Z (t + 1) = B t :=
  funext fun _ ↦ ite_eq_left h

omit [DecidableEq P] in
variable {A B n Z} in
/-- After the last circuit, the system is `Z`. -/
theorem chainSystem_succ_of_lt {t : ℕ} (h : n < t) : chainSystem A B n Z (t + 1) = Z :=
  funext fun _ ↦ ite_eq_right (by omega)

/-- The systems of the stages are finite. -/
instance instFintypeChainSystem [∀ p, Fintype (A p)] [∀ t p, Fintype (B t p)]
    [∀ p, Fintype (Z p)] : ∀ t p, Fintype (chainSystem A B n Z t p)
  | 0, p => inferInstanceAs (Fintype (A p))
  | t + 1, p => by
    change Fintype (if t ≤ n then B t p else Z p)
    split <;> infer_instance

/-- The systems of the stages have decidable equality. -/
instance instDecidableEqChainSystem [∀ p, DecidableEq (A p)] [∀ t p, DecidableEq (B t p)]
    [∀ p, DecidableEq (Z p)] : ∀ t p, DecidableEq (chainSystem A B n Z t p)
  | 0, p => inferInstanceAs (DecidableEq (A p))
  | t + 1, p => by
    change DecidableEq (if t ≤ n then B t p else Z p)
    split <;> infer_instance

variable [∀ p, Fintype (A p)] [∀ p, DecidableEq (A p)] [∀ t p, Fintype (B t p)]
  [∀ t p, DecidableEq (B t p)] [∀ p, Fintype (Z p)] [∀ p, DecidableEq (Z p)]

variable {A B n Z}

/-- The circuits of the sequence: the first circuit, the middle circuits, the last circuit, then
empty circuits, each read between the systems of its stages. -/
def chainStep (c₀ : OriginalCircuit A (B 0)) (c : ∀ t, OriginalCircuit (B t) (B (t + 1)))
    (e : OriginalCircuit (B n) Z) :
    ∀ t, OriginalCircuit (chainSystem A B n Z t) (chainSystem A B n Z (t + 1))
  | 0 => c₀.castSystems rfl (chainSystem_succ_of_le (Nat.zero_le n)).symm
  | t + 1 =>
    if h : t < n then
      (c t).castSystems (chainSystem_succ_of_le h.le).symm (chainSystem_succ_of_le h).symm
    else if h' : t = n then
      e.castSystems (by rw [chainSystem_succ_of_le h'.le, h'])
        (chainSystem_succ_of_lt (by omega)).symm
    else
      (done Z).castSystems (chainSystem_succ_of_lt (by omega)).symm
        (chainSystem_succ_of_lt (by omega)).symm

section Equations

variable (c₀ : OriginalCircuit A (B 0)) (c : ∀ t, OriginalCircuit (B t) (B (t + 1)))
  (e : OriginalCircuit (B n) Z)

/-- The first stage is the first circuit, its output system identified. -/
theorem chainStep_zero :
    chainStep c₀ c e 0 = c₀.castSystems rfl (chainSystem_succ_of_le (Nat.zero_le n)).symm :=
  rfl

/-- A middle stage is the middle circuit, its systems identified. -/
theorem chainStep_succ_of_lt {t : ℕ} (h : t < n) :
    chainStep c₀ c e (t + 1) =
      (c t).castSystems (chainSystem_succ_of_le h.le).symm (chainSystem_succ_of_le h).symm := by
  rw [chainStep, dite_eq_left h]

/-- The stage after the middle circuits is the last circuit, its systems identified. -/
theorem chainStep_succ_self :
    chainStep c₀ c e (n + 1) =
      e.castSystems (chainSystem_succ_of_le le_rfl).symm
        (chainSystem_succ_of_lt (Nat.lt_succ_self n)).symm := by
  rw [chainStep, dite_eq_right (lt_irrefl n), dite_eq_left rfl]

/-- The stages after the last circuit are empty circuits, their systems identified. -/
theorem chainStep_succ_of_gt {t : ℕ} (h : n < t) :
    chainStep c₀ c e (t + 1) =
      (done Z).castSystems (chainSystem_succ_of_lt h).symm
        (chainSystem_succ_of_lt (h.trans (Nat.lt_succ_self t))).symm := by
  rw [chainStep, dite_eq_right (by omega), dite_eq_right (by omega)]

/-- The first stage is the first circuit, its operator read along the identification of its output
system. -/
theorem op_chainStep_zero [Fintype P] :
    (chainStep c₀ c e 0).op =
      reindex (Equiv.piCongrRight fun s ↦ Equiv.cast
          (congrFun (chainSystem_succ_of_le (A := A) (Z := Z) (Nat.zero_le n)).symm s))
        (Equiv.refl _) c₀.op :=
  op_castSystems c₀ rfl (chainSystem_succ_of_le (Nat.zero_le n)).symm

/-- A middle stage is the middle circuit, its operator read along the identifications of its
systems. -/
theorem op_chainStep_succ_of_lt [Fintype P] {t : ℕ} (h : t < n) :
    (chainStep c₀ c e (t + 1)).op =
      reindex (Equiv.piCongrRight fun s ↦ Equiv.cast
          (congrFun (chainSystem_succ_of_le (A := A) (Z := Z) h).symm s))
        (Equiv.piCongrRight fun s ↦ Equiv.cast
          (congrFun (chainSystem_succ_of_le (A := A) (Z := Z) h.le).symm s)) (c t).op := by
  rw [chainStep_succ_of_lt c₀ c e h, op_castSystems]

/-- The stage after the middle circuits is the last circuit, its operator read along the
identifications of its systems. -/
theorem op_chainStep_succ_self [Fintype P] :
    (chainStep c₀ c e (n + 1)).op =
      reindex (Equiv.piCongrRight fun s ↦ Equiv.cast
          (congrFun (chainSystem_succ_of_lt (A := A) (B := B) (Nat.lt_succ_self n)).symm s))
        (Equiv.piCongrRight fun s ↦ Equiv.cast
          (congrFun (chainSystem_succ_of_le (A := A) (Z := Z) (le_refl n)).symm s)) e.op := by
  rw [chainStep_succ_self, op_castSystems]

/-- The stages after the last circuit have no gate. -/
theorem isLocal_chainStep_succ_of_gt {t : ℕ} (h : n < t) :
    (chainStep c₀ c e (t + 1)).toPartyCircuit.IsLocal := by
  rw [chainStep_succ_of_gt c₀ c e h]
  exact (isLocal_castSystems_iff _ _ _).mpr trivial

end Equations

/-- **Properties of the sequence.** A property, possibly depending on the position, that holds for
the first circuit, the middle circuits, the last circuit and the empty circuit, and passes to
identified systems, holds for every circuit of the sequence. -/
theorem chainStep_induction
    (Q : ℕ → ∀ (X Y : P → Type) [∀ p, Fintype (X p)] [∀ p, DecidableEq (X p)]
      [∀ p, Fintype (Y p)] [∀ p, DecidableEq (Y p)], OriginalCircuit X Y → Prop)
    (hcast : ∀ t (X Y X' Y' : P → Type) [∀ p, Fintype (X p)] [∀ p, DecidableEq (X p)]
      [∀ p, Fintype (Y p)] [∀ p, DecidableEq (Y p)] [∀ p, Fintype (X' p)]
      [∀ p, DecidableEq (X' p)] [∀ p, Fintype (Y' p)] [∀ p, DecidableEq (Y' p)]
      (w : OriginalCircuit X Y) (hX : X = X') (hY : Y = Y'), Q t X Y w →
        Q t X' Y' (w.castSystems hX hY))
    {c₀ : OriginalCircuit A (B 0)} {c : ∀ t, OriginalCircuit (B t) (B (t + 1))}
    {e : OriginalCircuit (B n) Z} (h₀ : Q 0 _ _ c₀) (hc : ∀ t < n, Q (t + 1) _ _ (c t))
    (he : Q (n + 1) _ _ e) (hid : ∀ t, n < t → Q (t + 1) _ _ (done Z)) :
    ∀ t, Q t _ _ (chainStep c₀ c e t)
  | 0 => by rw [chainStep_zero]; exact hcast 0 _ _ _ _ _ _ _ h₀
  | t + 1 => by
    rcases lt_trichotomy t n with h | rfl | h
    · rw [chainStep_succ_of_lt c₀ c e h]
      exact hcast (t + 1) _ _ _ _ _ _ _ (hc t h)
    · rw [chainStep_succ_self]
      exact hcast (t + 1) _ _ _ _ _ _ _ he
    · rw [chainStep_succ_of_gt c₀ c e h]
      exact hcast (t + 1) _ _ _ _ _ _ _ (hid t h)

/-- A vector read on a system equal to its own, along the identifications of the bases. -/
noncomputable def castVector [Fintype P] {X X' : P → Type} [∀ p, Fintype (X p)]
    [∀ p, Fintype (X' p)] (h : X = X') :
    EuclideanSpace ℂ (Config X) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Config X') :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ (Equiv.piCongrRight fun s ↦ Equiv.cast (congrFun h s))

omit [∀ p, Fintype (A p)] [∀ p, DecidableEq (A p)] [∀ t p, Fintype (B t p)]
  [∀ t p, DecidableEq (B t p)] [∀ p, Fintype (Z p)] [∀ p, DecidableEq (Z p)] in
/-- Reading a vector along the identification of a system with itself does nothing. -/
@[simp] theorem castVector_rfl [Fintype P] {X : P → Type} [∀ p, Fintype (X p)]
    (x : EuclideanSpace ℂ (Config X)) : castVector rfl x = x :=
  rfl

/-- The vectors of the stages: `x₀` of `A`, `y t` of `B t` for `t ≤ n`, and `z` of `Z` from the
stage `n + 2` on. -/
noncomputable def chainVec [Fintype P] (x₀ : EuclideanSpace ℂ (Config A))
    (y : ∀ t, EuclideanSpace ℂ (Config (B t))) (z : EuclideanSpace ℂ (Config Z)) :
    ∀ t, EuclideanSpace ℂ (Config (chainSystem A B n Z t))
  | 0 => x₀
  | t + 1 =>
    if h : t ≤ n then castVector (chainSystem_succ_of_le (A := A) (Z := Z) h).symm (y t)
    else castVector (chainSystem_succ_of_lt (A := A) (B := B) (by omega)).symm z

section Vectors

variable [Fintype P] (x₀ : EuclideanSpace ℂ (Config A)) (y : ∀ t, EuclideanSpace ℂ (Config (B t)))
  (z : EuclideanSpace ℂ (Config Z))

omit [∀ p, DecidableEq (A p)] [∀ t p, DecidableEq (B t p)] [∀ p, DecidableEq (Z p)] in
/-- The vector of the first stage is `x₀`. -/
theorem chainVec_zero : chainVec (n := n) x₀ y z 0 = x₀ :=
  rfl

omit [∀ p, DecidableEq (A p)] [∀ t p, DecidableEq (B t p)] [∀ p, DecidableEq (Z p)] in
/-- Up to the last circuit, the vector after stage `t` is `y t`. -/
theorem chainVec_succ_of_le {t : ℕ} (h : t ≤ n) :
    chainVec x₀ y z (t + 1) = castVector (chainSystem_succ_of_le h).symm (y t) := by
  rw [chainVec, dite_eq_left h]

omit [∀ p, DecidableEq (A p)] [∀ t p, DecidableEq (B t p)] [∀ p, DecidableEq (Z p)] in
/-- After the last circuit, the vector is `z`. -/
theorem chainVec_succ_of_lt {t : ℕ} (h : n < t) :
    chainVec x₀ y z (t + 1) = castVector (chainSystem_succ_of_lt h).symm z :=
  dite_eq_right (by omega)

end Vectors

omit [∀ p, Fintype (A p)] [∀ p, DecidableEq (A p)] [∀ t p, Fintype (B t p)]
  [∀ t p, DecidableEq (B t p)] [∀ p, Fintype (Z p)] [∀ p, DecidableEq (Z p)] in
/-- **The operator between identified systems on vectors**: identifying the systems commutes with
applying the operator. -/
theorem toEuclideanLin_op_castSystems [Fintype P] {X Y X' Y' : P → Type}
    [∀ p, Fintype (X p)] [∀ p, DecidableEq (X p)] [∀ p, Fintype (Y p)] [∀ p, DecidableEq (Y p)]
    [∀ p, Fintype (X' p)] [∀ p, DecidableEq (X' p)] [∀ p, Fintype (Y' p)]
    [∀ p, DecidableEq (Y' p)] (w : OriginalCircuit X Y) (hX : X = X') (hY : Y = Y')
    (x : EuclideanSpace ℂ (Config X)) :
    Matrix.toEuclideanLin (w.castSystems hX hY).op (castVector hX x) =
      castVector hY (Matrix.toEuclideanLin w.op x) := by
  rw [op_castSystems]
  exact Matrix.toEuclideanLin_reindex_piLpCongrLeft₂ _ _ _ x

omit [∀ p, Fintype (A p)] [∀ p, DecidableEq (A p)] [∀ t p, Fintype (B t p)]
  [∀ t p, DecidableEq (B t p)] [∀ p, Fintype (Z p)] [∀ p, DecidableEq (Z p)] in
/-- The error of a circuit between identified systems is the error of the circuit. -/
theorem norm_toEuclideanLin_op_castSystems_sub [Fintype P] {X Y X' Y' : P → Type}
    [∀ p, Fintype (X p)] [∀ p, DecidableEq (X p)] [∀ p, Fintype (Y p)] [∀ p, DecidableEq (Y p)]
    [∀ p, Fintype (X' p)] [∀ p, DecidableEq (X' p)] [∀ p, Fintype (Y' p)]
    [∀ p, DecidableEq (Y' p)] (w : OriginalCircuit X Y) (hX : X = X') (hY : Y = Y')
    (x : EuclideanSpace ℂ (Config X)) (y : EuclideanSpace ℂ (Config Y)) :
    ‖Matrix.toEuclideanLin (w.castSystems hX hY).op (castVector hX x) - castVector hY y‖ =
      ‖Matrix.toEuclideanLin w.op x - y‖ := by
  rw [toEuclideanLin_op_castSystems, ← map_sub, LinearIsometryEquiv.norm_map]

/-- **The stages after the last circuit act as the identity**, read along the identifications of
their systems with `Z`. -/
theorem toEuclideanLin_op_chainStep_succ_of_gt [Fintype P] {c₀ : OriginalCircuit A (B 0)}
    {c : ∀ t, OriginalCircuit (B t) (B (t + 1))} {e : OriginalCircuit (B n) Z} {t : ℕ}
    (h : n < t) (z : EuclideanSpace ℂ (Config Z)) :
    Matrix.toEuclideanLin (chainStep c₀ c e (t + 1)).op
        (castVector (chainSystem_succ_of_lt h).symm z) =
      castVector (chainSystem_succ_of_lt (h.trans (Nat.lt_succ_self t))).symm z := by
  rw [chainStep_succ_of_gt c₀ c e h, toEuclideanLin_op_castSystems, op_done]
  simp only [Matrix.toEuclideanLin, Matrix.toLpLin_one, LinearMap.id_apply]

/-- **Errors along the sequence.** If the first circuit takes `x₀` within `ε 0` of `y 0`, each
middle circuit takes `y t` within `ε (t + 1)` of `y (t + 1)`, and the last circuit takes `y n`
within `ε (n + 1)` of `z`, then every circuit of the sequence takes the vector of its stage within
the corresponding error of the next one. -/
theorem norm_chainStep_op_sub_le [Fintype P] {c₀ : OriginalCircuit A (B 0)}
    {c : ∀ t, OriginalCircuit (B t) (B (t + 1))} {e : OriginalCircuit (B n) Z}
    {x₀ : EuclideanSpace ℂ (Config A)} {y : ∀ t, EuclideanSpace ℂ (Config (B t))}
    {z : EuclideanSpace ℂ (Config Z)} (ε : ℕ → ℝ)
    (h₀ : ‖Matrix.toEuclideanLin c₀.op x₀ - y 0‖ ≤ ε 0)
    (hc : ∀ t < n, ‖Matrix.toEuclideanLin (c t).op (y t) - y (t + 1)‖ ≤ ε (t + 1))
    (he : ‖Matrix.toEuclideanLin e.op (y n) - z‖ ≤ ε (n + 1))
    (hid : ∀ t, n < t → 0 ≤ ε (t + 1)) :
    ∀ t, ‖Matrix.toEuclideanLin (chainStep c₀ c e t).op (chainVec x₀ y z t) -
      chainVec x₀ y z (t + 1)‖ ≤ ε t
  | 0 => by
    rw [chainStep_zero, chainVec_succ_of_le x₀ y z (Nat.zero_le n)]
    exact (norm_toEuclideanLin_op_castSystems_sub c₀ rfl _ x₀ (y 0)).le.trans h₀
  | t + 1 => by
    rcases lt_trichotomy t n with h | rfl | h
    · rw [chainStep_succ_of_lt c₀ c e h, chainVec_succ_of_le x₀ y z h.le,
        chainVec_succ_of_le x₀ y z h, norm_toEuclideanLin_op_castSystems_sub]
      exact hc t h
    · rw [chainStep_succ_self, chainVec_succ_of_le x₀ y z le_rfl,
        chainVec_succ_of_lt x₀ y z (Nat.lt_succ_self t), norm_toEuclideanLin_op_castSystems_sub]
      exact he
    · rw [chainVec_succ_of_lt x₀ y z h, chainVec_succ_of_lt x₀ y z (h.trans (Nat.lt_succ_self t)),
        toEuclideanLin_op_chainStep_succ_of_gt h, sub_self, norm_zero]
      exact hid t h

end Chain

end OriginalCircuit

end QuantumCircuit.Party
