/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.ManyBody.Dynamics.Interaction
import QICLean.Algebra.HermitianPartSum
import Mathlib.Analysis.CStarAlgebra.Matrix

/-!
# Hermitian parts of the terms of an interaction

A model may assume only that the sum of its terms is Hermitian, not that every term is. Replacing
every term `hᵢ` by its Hermitian part `ℜ hᵢ = (hᵢ + hᵢ⋆)/2` gives an interaction with the same
supports, Hermitian terms of no larger norm, and, when the sum was Hermitian, the same
Hamiltonian.

Moved from TNLean, `TNLean/PEPS/Approximation/SquareHamiltonianHermitianTerms.lean` and
`TNLean/PEPS/AreaLaw/RectangularHamiltonian.lean` (`hermitianTerm` and its lemmas) at commit
`71c1185e9352a3b5237b37a6840640751da6ca2d`. Changes: one definition for every interaction in
place of one for each of the square and rectangular models.

## Main definitions

* `ManyBody.Interaction.hermitianPart` — the interaction of the Hermitian parts of the terms.

## Main results

* `ManyBody.Interaction.isHermitian_hermitianPart_term`,
  `ManyBody.Interaction.norm_hermitianPart_term_le` — the new terms are Hermitian and no larger.
* `ManyBody.Interaction.hamiltonian_hermitianPart` — a Hermitian Hamiltonian is unchanged.

## References

* OpenAI, *Polynomial PEPS approximation of gapped square-grid ground states*,
  September 24, 2026, `00-introduction.tex`, lines 39–44 (`eq:model`), and `03-patches.tex`,
  lines 214–333.
-/

open Matrix ComplexStarModule
open scoped Matrix.Norms.L2Operator

namespace ManyBody

namespace Interaction

variable {V : Type*} [Fintype V] [DecidableEq V] {X : V → Type*} [∀ v, Fintype (X v)]
  [∀ v, DecidableEq (X v)] {ι : Type*} {S : ι → Finset V}

/-- The interaction whose terms are the Hermitian parts `ℜ hᵢ` of the terms of `Φ`, with the
same supports. Polynomial-PEPS, `00-introduction.tex`, lines 39–44; `03-patches.tex`,
lines 214–333. -/
noncomputable def hermitianPart (Φ : Interaction X S) : Interaction X S where
  term i := (ℜ (Φ.term i) : Matrix (Config X) (Config X) ℂ)
  mem i := coe_realPart_mem_of_star_mem
    (S := (supportedOperators X (S i)).toSubmodule.restrictScalars ℝ)
    (Φ.mem i) (show star (Φ.term i) ∈ supportedOperators X (S i) from star_mem (Φ.mem i))

theorem hermitianPart_term (Φ : Interaction X S) (i : ι) :
    Φ.hermitianPart.term i = (ℜ (Φ.term i) : Matrix (Config X) (Config X) ℂ) :=
  rfl

/-- The terms of the Hermitian part are Hermitian. -/
theorem isHermitian_hermitianPart_term (Φ : Interaction X S) (i : ι) :
    (Φ.hermitianPart.term i).IsHermitian :=
  (ℜ (Φ.term i)).property.isHermitian

/-- Taking the Hermitian part does not increase the norm of a term. -/
theorem norm_hermitianPart_term_le (Φ : Interaction X S) (i : ι) :
    ‖Φ.hermitianPart.term i‖ ≤ ‖Φ.term i‖ :=
  realPart.norm_le (Φ.term i)

/-- If the Hamiltonian of `Φ` is Hermitian, the Hermitian parts of its terms have the same
sum. Polynomial-PEPS, `03-patches.tex`, lines 214–333. -/
theorem hamiltonian_hermitianPart [Fintype ι] (Φ : Interaction X S)
    (hΦ : Φ.hamiltonian.IsHermitian) : Φ.hermitianPart.hamiltonian = Φ.hamiltonian :=
  sum_coe_realPart_of_isSelfAdjoint Finset.univ Φ.term hΦ.isSelfAdjoint

end Interaction

end ManyBody
