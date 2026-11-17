/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Channel.KrausCPTP

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

## Main results

* `KrausFamily.isKrausCPTP_map` — a trace-preserving family gives a quantum channel in the
  sense of `IsKrausCPTP` (Wolf, Thm. 2.1 and §2.1).
* `KrausFamily.trace_map` — a trace-preserving family preserves the trace.
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

omit [Fintype α] in
theorem effect_single (V : Matrix β α ℂ) : (single V).effect = Vᴴ * V :=
  Fintype.sum_unique (ι := Unit) _

variable [DecidableEq α]

/-- A Kraus family is trace-preserving when its effect is the identity. -/
def IsTP (K : KrausFamily α β) : Prop :=
  K.effect = 1

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
  rw [IsTraceNonincreasing, h]

theorem IsUnitary.isTP [DecidableEq β] {K : KrausFamily α β} (h : K.IsUnitary) : K.IsTP := by
  obtain ⟨⟨u⟩, hK⟩ := h
  rw [IsTP, effect, Fintype.sum_unique]
  exact (hK default).1

/-- A trace-preserving Kraus family is a quantum channel. -/
theorem isKrausCPTP_map [DecidableEq β] {K : KrausFamily α β} (h : K.IsTP) :
    IsKrausCPTP K.map := by
  let e := Fintype.equivFin K.Index
  refine ⟨Fintype.card K.Index, fun j ↦ K.op (e.symm j), fun ρ ↦ ?_, ?_⟩
  · rw [map_apply]
    exact (e.symm.sum_comp fun i ↦ K.op i * ρ * (K.op i)ᴴ).symm
  · rw [← h, effect]
    exact e.symm.sum_comp fun i ↦ (K.op i)ᴴ * K.op i

/-- A trace-preserving Kraus family preserves the trace. -/
theorem trace_map {K : KrausFamily α β} (h : K.IsTP) (ρ : Matrix α α ℂ) :
    (K.map ρ).trace = ρ.trace := by
  rw [map_apply, trace_sum]
  simp_rw [trace_mul_cycle (K.op _), ← trace_sum, ← Finset.sum_mul]
  rw [show ∑ i, (K.op i)ᴴ * K.op i = K.effect from rfl, h, Matrix.one_mul]

end KrausFamily
