/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Representation.SubsystemTransport

/-!
# Symmetric projections under equivariant coordinates

An equivariant identification transports the finite-group averaging
projection by the same coordinate equivalence.

Source: *A two-dimensional area law from a global spectral gap*, September 24,
2026, `05-replicas.tex`, lines 14--27 and 73--80; `07-comparators.tex`,
lines 421--456, revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

open Matrix
open scoped BigOperators

namespace PermutationRepresentation

/-- Transport the actual finite-group averaging projection along an
equivariant coordinate equivalence. -/
theorem symProj_of_intertwine
    {G X Y : Type*} [Group G] [Fintype G]
    [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
    (e : X ≃ Y) {φ : G →* Equiv.Perm X} {ψ : G →* Equiv.Perm Y}
    (h : ∀ g x, ψ g (e x) = e (φ g x)) :
    symProj ψ = reindex e e (symProj φ) := by
  ext x y
  simp only [symProj, reindex_apply, submatrix_apply, Matrix.smul_apply, Matrix.sum_apply]
  congr 1
  apply Finset.sum_congr rfl
  intro g hg
  exact congrArg (fun M => M x y) (permOp_of_intertwine e h g)

end PermutationRepresentation
