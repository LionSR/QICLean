/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.ManyBody.Sites.Support
import Mathlib.Algebra.Star.BigOperators
import Mathlib.LinearAlgebra.Matrix.Hermitian

/-!
# Interactions on a system of sites

An interaction on a system of sites `X` assigns to every index `i` of a type `ι` an operator
supported on the region `S i`. The index type and the supports are parameters: a chain, a
domain of a lattice, a square with its site and edge terms are interactions for particular
choices of the sites, the basis types and the supports, and several terms may share a
support. Hermiticity, norm bounds, the range and the degree of an interaction are not part of
the structure; the statements that use them take them as hypotheses. In particular a family
whose sum is Hermitian, but whose terms are not, is an interaction.

When the index type is finite, the Hamiltonian of an interaction is the sum of its terms.
Statements about the evolution that an interaction generates are stated with
`ManyBody.Interaction.hamiltonian`; that is the one spelling of the sum of the terms.

This is the object of the dynamics layer in TNLean's `docs/many_body_circuit_architecture.md`
("a family of Hermitian terms with supports, and the evolution it generates"); it replaces the
separate arguments `(h : κ → Matrix _ _ ℂ) (T : κ → Set ι)
(hSupport : ∀ j, h j ∈ _)` of TNLean's Lieb–Robinson modules.

## Main definitions

* `ManyBody.Interaction` — terms indexed by a type, each supported on a given region.
* `ManyBody.Interaction.hamiltonian` — the sum of the terms.

## Main results

* `ManyBody.Interaction.isHermitian_hamiltonian` — Hermitian terms have a Hermitian sum.
* `ManyBody.Interaction.hamiltonian_neg` — the Hamiltonian of the negated interaction.
-/

open Matrix

namespace ManyBody

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- An interaction on the system `X` with supports `S`: a term for every index `i`, supported
on the region `S i`. Hermiticity and norm bounds are hypotheses of the statements that need
them. -/
@[ext]
structure Interaction (X : V → Type*) [∀ v, Fintype (X v)] [∀ v, DecidableEq (X v)]
    {ι : Type*} (S : ι → Finset V) where
  /-- The term with index `i`. -/
  term : ι → Matrix (Config X) (Config X) ℂ
  /-- The term with index `i` is supported on the region `S i`. -/
  mem : ∀ i, term i ∈ supportedOperators X (S i)

namespace Interaction

variable {X : V → Type*} [∀ v, Fintype (X v)] [∀ v, DecidableEq (X v)] {ι : Type*}
  {S : ι → Finset V}

/-- The Hamiltonian `H = ∑ᵢ hᵢ` of an interaction with finitely many terms. -/
noncomputable def hamiltonian [Fintype ι] (Φ : Interaction X S) :
    Matrix (Config X) (Config X) ℂ :=
  ∑ i, Φ.term i

/-- The negated interaction, with the same supports. -/
instance : Neg (Interaction X S) :=
  ⟨fun Φ ↦ ⟨fun i ↦ -Φ.term i, fun i ↦ neg_mem (Φ.mem i)⟩⟩

@[simp]
theorem neg_term (Φ : Interaction X S) (i : ι) : (-Φ).term i = -Φ.term i :=
  rfl

theorem hamiltonian_neg [Fintype ι] (Φ : Interaction X S) :
    (-Φ).hamiltonian = -Φ.hamiltonian := by
  simp [hamiltonian]

/-- An interaction of Hermitian terms has a Hermitian Hamiltonian. -/
theorem isHermitian_hamiltonian [Fintype ι] {Φ : Interaction X S}
    (hΦ : ∀ i, (Φ.term i).IsHermitian) : Φ.hamiltonian.IsHermitian :=
  (isSelfAdjoint_sum Finset.univ fun i _ ↦ (hΦ i).isSelfAdjoint).isHermitian

end Interaction

end ManyBody
