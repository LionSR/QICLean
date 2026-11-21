/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Channel.KrausMap.KrausCPTP
import QICLean.Channel.Schwarz.Basic

/-!
# Finite Kraus families

A finite Kraus family from `ℂ^α` to `ℂ^β` is a finite family of matrices `K_i : ℂ^α → ℂ^β`
indexed by a type of its own. No normalization is imposed. The family determines the map
`ρ ↦ ∑ᵢ Kᵢ ρ Kᵢᴴ`, which is `rectangularKrausMap`, and its effect `E = ∑ᵢ Kᵢᴴ Kᵢ`. The family is
trace-preserving when `E = 1` and trace-nonincreasing when `E ≤ 1`; a single operator is a
contraction exactly when it is trace-nonincreasing, and it is unitary when `VᴴV = 1` and
`VVᴴ = 1`.

The index type is part of the data so that families with different numbers of operators can
be collected in one structure, as in a layer of a circuit, where each cell carries its own
family.

## Main definitions

* `KrausFamily` — a finite family of matrices with its index type.
* `KrausFamily.map`, `KrausFamily.effect` — the map `ρ ↦ ∑ Kᵢ ρ Kᵢᴴ` and `∑ Kᵢᴴ Kᵢ`.
* `KrausFamily.IsTP`, `KrausFamily.IsTraceNonincreasing`, `KrausFamily.IsUnitary` — the
  normalizations.
* `KrausFamily.single` — the family of one operator.
* `KrausFamily.adjoint` — the family of the adjoint operators.
* `KrausFamily.reindex` — a family carried along equivalences of its bases.
* `KrausFamily.prepare`, `KrausFamily.discard` — the preparation of a basis vector from the
  one-point basis, and the discard of a basis onto it.
* `KrausFamily.measure` — the measurement of a basis.

## Main results

* `KrausFamily.isKrausCPTP_map` — a trace-preserving family gives a quantum channel in the
  sense of `IsKrausCPTP` (Wolf, Thm. 2.1 and §2.1).
* `KrausFamily.trace_map` — a trace-preserving family preserves the trace.
* `KrausFamily.trace_map_le` — a trace-nonincreasing family decreases the trace of
  positive semidefinite inputs.
* `KrausFamily.trace_map_mul` — the map of a family and the map of its adjoint family are dual
  for the trace pairing.
* `KrausFamily.map_prepare`, `KrausFamily.map_discard` — preparation and discard as maps.
* `KrausFamily.IsTP.nonempty_index`, `KrausFamily.IsTP.nonempty_target` — a trace-preserving
  family on a nonempty basis has an operator, and its target basis is nonempty.
-/

open Matrix
open scoped ComplexOrder MatrixOrder

/-- A finite Kraus family from `ℂ^α` to `ℂ^β`: matrices `op i : ℂ^α → ℂ^β` indexed by a finite
type `Index`, with no normalization. Wolf, *Quantum Channels & Operations*, Thm. 2.1. -/
structure KrausFamily (α β : Type) : Type 1 where
  /-- The index type of the Kraus operators. -/
  Index : Type
  [fintype : Fintype Index]
  /-- The Kraus operators. -/
  op : Index → Matrix β α ℂ

attribute [instance] KrausFamily.fintype

namespace KrausFamily

variable {α β : Type}

/-- The family of one operator. -/
def single (V : Matrix β α ℂ) : KrausFamily α β :=
  ⟨Unit, fun _ ↦ V⟩

@[simp] theorem single_op (V : Matrix β α ℂ) (i : (single V).Index) : (single V).op i = V :=
  rfl

/-- The adjoint of a Kraus family: the adjoints of its operators, with the same index type. -/
def adjoint (K : KrausFamily α β) : KrausFamily β α :=
  ⟨K.Index, fun i ↦ (K.op i)ᴴ⟩

variable [Fintype α] [Fintype β]

/-- The map `ρ ↦ ∑ᵢ Kᵢ ρ Kᵢᴴ` of a Kraus family. -/
noncomputable def map (K : KrausFamily α β) : Matrix α α ℂ →ₗ[ℂ] Matrix β β ℂ :=
  rectangularKrausMap K.op

omit [Fintype β] in
theorem map_apply (K : KrausFamily α β) (ρ : Matrix α α ℂ) :
    K.map ρ = ∑ i, K.op i * ρ * (K.op i)ᴴ :=
  rfl

/-- The effect `∑ᵢ Kᵢᴴ Kᵢ` of a Kraus family. -/
noncomputable def effect (K : KrausFamily α β) : Matrix α α ℂ :=
  ∑ i, (K.op i)ᴴ * K.op i

omit [Fintype β] in
/-- The map of the family of one operator `V` is the conjugation by `V`. -/
theorem map_single (V : Matrix β α ℂ) (ρ : Matrix α α ℂ) : (single V).map ρ = V * ρ * Vᴴ :=
  (map_apply _ _).trans (Fintype.sum_unique (ι := Unit) _)

omit [Fintype β] in
/-- The entries of the map of a Kraus family on the matrix unit `|a⟩⟨a'|`. -/
theorem map_matrixUnit_apply [DecidableEq α] (K : KrausFamily α β) (a a' : α) (c c' : β) :
    K.map (Matrix.single a a' 1) c c' = ∑ i, K.op i c a * star (K.op i c' a') := by
  rw [map_apply, Matrix.sum_apply]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  simp [mul_apply, Matrix.single_apply, ite_and]

omit [Fintype α] in
theorem effect_single (V : Matrix β α ℂ) : (single V).effect = Vᴴ * V :=
  Fintype.sum_unique (ι := Unit) _

variable [DecidableEq α]

/-- A Kraus family is trace-preserving when its operators are, `Kraus.IsTP`: its effect
`∑ᵢ Kᵢᴴ Kᵢ` is the identity. -/
def IsTP (K : KrausFamily α β) : Prop :=
  Kraus.IsTP K.op

omit [Fintype α] in
theorem isTP_iff_effect_eq_one {K : KrausFamily α β} : K.IsTP ↔ K.effect = 1 :=
  Iff.rfl

/-- A Kraus family is trace-nonincreasing when its effect is at most the identity. For a
single operator this says that the operator is a contraction. -/
def IsTraceNonincreasing (K : KrausFamily α β) : Prop :=
  K.effect ≤ 1

/-- A Kraus family is unitary when it consists of one operator `V` with `VᴴV = 1` and
`VVᴴ = 1`. The bases `α` and `β` then have the same size but need not be equal. -/
def IsUnitary [DecidableEq β] (K : KrausFamily α β) : Prop :=
  Nonempty (Unique K.Index) ∧ ∀ i, (K.op i)ᴴ * K.op i = 1 ∧ K.op i * (K.op i)ᴴ = 1

omit [Fintype α] in
theorem IsTP.isTraceNonincreasing {K : KrausFamily α β} (h : K.IsTP) :
    K.IsTraceNonincreasing := by
  rw [IsTraceNonincreasing, isTP_iff_effect_eq_one.mp h]

theorem IsUnitary.isTP [DecidableEq β] {K : KrausFamily α β} (h : K.IsUnitary) : K.IsTP := by
  obtain ⟨⟨u⟩, hK⟩ := h
  rw [isTP_iff_effect_eq_one, effect, Fintype.sum_unique]
  exact (hK default).1

/-- The adjoint of a unitary family is unitary. -/
theorem IsUnitary.adjoint [DecidableEq β] {K : KrausFamily α β} (h : K.IsUnitary) :
    K.adjoint.IsUnitary :=
  ⟨h.1, fun i ↦ by simp [KrausFamily.adjoint, (h.2 i).1, (h.2 i).2]⟩

/-- The operators of a unitary Kraus family at any two indices agree, and so do those of a family
equal to it. The equation lets the statement apply to a family given by a term, such as a
conditional, whose index type is not syntactically that of `K'`. -/
theorem IsUnitary.op_eq_of_eq [DecidableEq β] {K K' : KrausFamily α β} (hK' : K'.IsUnitary)
    (h : K = K') (i : K.Index) (j : K'.Index) : K.op i = K'.op j := by
  subst h
  have := hK'.1.some
  exact congrArg K.op (Subsingleton.elim i j)

/-- The family of one unitary operator is unitary. -/
theorem isUnitary_single {V : Matrix α α ℂ} (hV : V ∈ Matrix.unitaryGroup α ℂ) :
    (single V).IsUnitary :=
  ⟨⟨inferInstanceAs (Unique Unit)⟩, fun _ ↦
    ⟨Matrix.mem_unitaryGroup_iff'.mp hV, Matrix.mem_unitaryGroup_iff.mp hV⟩⟩

/-- A trace-preserving Kraus family is a quantum channel. -/
theorem isKrausCPTP_map [DecidableEq β] {K : KrausFamily α β} (h : K.IsTP) :
    IsKrausCPTP K.map :=
  Matrix.rectangularKrausMap_isKrausCPTP K.op h

omit [DecidableEq α] in
/-- The map of a family and the map of its adjoint family are dual for the trace pairing:
`tr(∑ Kᵢ ρ Kᵢᴴ · A) = tr(ρ · ∑ Kᵢᴴ A Kᵢ)`. -/
theorem trace_map_mul (K : KrausFamily α β) (ρ : Matrix α α ℂ) (A : Matrix β β ℂ) :
    (K.map ρ * A).trace = (ρ * K.adjoint.map A).trace := by
  simp only [map_apply, adjoint, conjTranspose_conjTranspose, Finset.sum_mul, Matrix.mul_sum,
    trace_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [Matrix.mul_assoc, Matrix.mul_assoc, trace_mul_comm, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
    ← Matrix.mul_assoc]

omit [DecidableEq α] in
/-- The trace of a Kraus map is the trace pairing of its effect with the input. -/
theorem trace_map_eq_trace_effect_mul (K : KrausFamily α β) (ρ : Matrix α α ℂ) :
    (K.map ρ).trace = (K.effect * ρ).trace := by
  classical
  have he : K.adjoint.map 1 = K.effect := by
    simp only [map_apply, adjoint, Matrix.mul_one, conjTranspose_conjTranspose, effect]
  simpa only [Matrix.mul_one, he, trace_mul_comm ρ K.effect] using K.trace_map_mul ρ 1

/-- A trace-preserving Kraus family preserves the trace. -/
theorem trace_map {K : KrausFamily α β} (h : K.IsTP) (ρ : Matrix α α ℂ) :
    (K.map ρ).trace = ρ.trace := by
  rw [trace_map_eq_trace_effect_mul, isTP_iff_effect_eq_one.mp h, Matrix.one_mul]

/-- A trace-nonincreasing Kraus family decreases the trace of every positive semidefinite
input. The inequality is in the real order on complex traces. -/
theorem trace_map_le {K : KrausFamily α β} (h : K.IsTraceNonincreasing)
    {ρ : Matrix α α ℂ} (hρ : ρ.PosSemidef) : (K.map ρ).trace ≤ ρ.trace := by
  have hn := (Matrix.le_iff.mp h).trace_mul_nonneg hρ
  rw [Matrix.sub_mul, Matrix.one_mul, Matrix.trace_sub, sub_nonneg] at hn
  rw [trace_map_eq_trace_effect_mul]
  exact hn

/-! ### Preparation and discard -/

/-- The preparation of the basis vector `b` from the one-point basis: the operator `|b⟩`. -/
def prepare {β : Type} [DecidableEq β] (b : β) : KrausFamily PUnit β :=
  single (Matrix.single b () 1)

/-- The discard of a basis: the operators `⟨a|`, one for each basis vector `a`. -/
def discard (α : Type) [Fintype α] [DecidableEq α] : KrausFamily α PUnit :=
  ⟨α, fun a ↦ Matrix.single () a 1⟩

/-- The measurement of the basis `α`: the projections `|a⟩⟨a|`, indexed by `a : α`. -/
def measure (α : Type) [Fintype α] [DecidableEq α] : KrausFamily α α :=
  ⟨α, fun a ↦ Matrix.single a a 1⟩

theorem isTP_prepare {β : Type} [Fintype β] [DecidableEq β] (b : β) : (prepare b).IsTP := by
  rw [isTP_iff_effect_eq_one]
  ext x y
  simp [prepare, effect_single, mul_apply, Matrix.single_apply]

theorem isTP_discard (α : Type) [Fintype α] [DecidableEq α] : (discard α).IsTP := by
  rw [isTP_iff_effect_eq_one, effect]
  simp only [discard, conjTranspose_single, star_one, single_mul_single_same, mul_one]
  exact sum_single_one

theorem map_prepare {β : Type} [DecidableEq β] (b : β)
    (ρ : Matrix PUnit PUnit ℂ) : (prepare b).map ρ = ρ () () • Matrix.single b b 1 := by
  ext x y
  simp [map_apply, prepare, single, Matrix.single_apply]

theorem map_discard (α : Type) [Fintype α] [DecidableEq α] (ρ : Matrix α α ℂ) :
    (discard α).map ρ = of fun _ _ ↦ ρ.trace := by
  ext x y
  simp [map_apply, discard, trace, Matrix.sum_apply]

/-- A trace-preserving family has a nonzero effect on a nonempty basis. -/
private theorem IsTP.effect_ne_zero {α β : Type} [DecidableEq α] [Fintype β] [Nonempty α]
    {K : KrausFamily α β} (h : K.IsTP) : K.effect ≠ 0 := fun h0 ↦ by
  obtain ⟨a⟩ := ‹Nonempty α›
  simpa using congrFun (congrFun (h.symm.trans h0) a) a

/-- A trace-preserving Kraus family on a nonempty basis has an operator. -/
theorem IsTP.nonempty_index {α β : Type} [DecidableEq α] [Fintype β] [Nonempty α]
    {K : KrausFamily α β} (h : K.IsTP) : Nonempty K.Index := by
  by_contra hi
  rw [not_nonempty_iff] at hi
  exact h.effect_ne_zero (Finset.sum_of_isEmpty _)

/-- A trace-preserving family between one-element bases is the identity: every entry of its map
is the entry of the input. -/
theorem IsTP.map_apply_of_subsingleton {α β : Type} [Fintype α] [DecidableEq α] [Fintype β]
    [Subsingleton α] [Subsingleton β] {K : KrausFamily α β} (h : K.IsTP) (ρ : Matrix α α ℂ)
    (a a' : α) (b b' : β) : K.map ρ b b' = ρ a a' := by
  rw [Subsingleton.elim a' a, Subsingleton.elim b' b]
  let := uniqueOfSubsingleton a
  let := uniqueOfSubsingleton b
  have hK := congrFun (congrFun (isTP_iff_effect_eq_one.mp h) a) a
  rw [effect, Matrix.sum_apply, one_apply_eq] at hK
  rw [map_apply, Matrix.sum_apply, ← mul_one (ρ a a), ← hK, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  simp only [mul_apply, Fintype.sum_unique, conjTranspose_apply, Subsingleton.elim default a,
    Subsingleton.elim default b]
  ring

/-- The target basis of a trace-preserving Kraus family on a nonempty basis is nonempty. -/
theorem IsTP.nonempty_target {α β : Type} [DecidableEq α] [Fintype β] [Nonempty α]
    {K : KrausFamily α β} (h : K.IsTP) : Nonempty β := by
  by_contra hb
  rw [not_nonempty_iff] at hb
  exact h.effect_ne_zero (Finset.sum_eq_zero fun i _ ↦ by
    rw [Subsingleton.elim (K.op i) 0, Matrix.mul_zero])

/-! ### Reindexing -/

section Reindex

variable {α β α' β' : Type}

/-- The family carried along equivalences `e` of the input and `f` of the output bases. -/
def reindex (K : KrausFamily α β) (e : α' ≃ α) (f : β' ≃ β) : KrausFamily α' β' :=
  ⟨K.Index, fun i ↦ (K.op i).submatrix f e⟩

@[simp] theorem reindex_op (K : KrausFamily α β) (e : α' ≃ α) (f : β' ≃ β)
    (i : (K.reindex e f).Index) : (K.reindex e f).op i = (K.op i).submatrix f e :=
  rfl

theorem effect_reindex [Fintype β] [Fintype β'] (K : KrausFamily α β) (e : α' ≃ α)
    (f : β' ≃ β) : (K.reindex e f).effect = K.effect.submatrix e e := by
  ext a b
  simp only [effect, reindex_op, conjTranspose_submatrix, submatrix_mul_equiv, Matrix.sum_apply,
    submatrix_apply]
  rfl

theorem IsTP.reindex [Fintype β] [Fintype β'] [DecidableEq α] [DecidableEq α']
    {K : KrausFamily α β} (hK : K.IsTP) (e : α' ≃ α) (f : β' ≃ β) : (K.reindex e f).IsTP := by
  rw [isTP_iff_effect_eq_one, effect_reindex, isTP_iff_effect_eq_one.mp hK, submatrix_one_equiv]

theorem IsUnitary.reindex [Fintype α] [Fintype β] [Fintype α'] [Fintype β'] [DecidableEq α]
    [DecidableEq β] [DecidableEq α'] [DecidableEq β'] {K : KrausFamily α β} (hK : K.IsUnitary)
    (e : α' ≃ α) (f : β' ≃ β) : (K.reindex e f).IsUnitary := by
  obtain ⟨u, hK⟩ := hK
  refine ⟨u, fun i ↦ ⟨?_, ?_⟩⟩ <;>
    simp only [reindex_op, conjTranspose_submatrix, submatrix_mul_equiv, (hK i).1, (hK i).2,
      submatrix_one_equiv]

end Reindex

end KrausFamily
