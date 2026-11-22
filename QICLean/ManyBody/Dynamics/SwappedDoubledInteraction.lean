/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.ManyBody.Dynamics.InteractionOperations

/-!
# The doubled interaction conjugated by the exchange of two copies

For an interaction `Φ` on the sites `V`, conjugate the doubled interaction `(hᵢ ⊗ 1 + 1 ⊗ hᵢ)ᵢ`
by the exchange `F_D = ManyBody.pairSwapOp D` of the two copies on a region `D`, and relabel the
result along a bijection `e` of the sites and bijections `f v` of the paired basis labels, for
instance `finProdFinEquiv : Fin q × Fin q ≃ Fin (q * q)`. Its Hamiltonian is `F_D K F_D*` in the
relabelled basis, for the doubled Hamiltonian `K = H ⊗ 1 + 1 ⊗ H` of `Φ`.

This is TNLean's `TNLean.Lattice.hamiltonian_relabel_conj_pairSwapOp_doubled`
(`Lattice/RegionalSwapSupport`, at commit `707a50e56c`), stated for any relabelling; there the
sites are relabelled by the identity and the paired labels along `finProdFinEquiv`.

## Main results

* `ManyBody.Interaction.hamiltonian_relabel_conj_pairSwapOp_doubled`.

## References

* OpenAI, *Polynomial PEPS approximation of gapped square-grid ground states*, September 24,
  2026, `02-information.tex`, lines 416–424.
-/

open Matrix

namespace ManyBody

namespace Interaction

variable {V : Type*} [Fintype V] [DecidableEq V] {X : V → Type*} [∀ v, Fintype (X v)]
  [∀ v, DecidableEq (X v)] {ι : Type*} [Fintype ι] {S : ι → Finset V}
  {V' : Type*} [Fintype V'] [DecidableEq V'] {X' : V' → Type*} [∀ v, Fintype (X' v)]
  [∀ v, DecidableEq (X' v)]

/-- **The swapped doubled Hamiltonian.** Conjugate the doubled interaction of `Φ` by the
exchange `F_D` of the two copies on `D` and relabel it along `e` and `f`. Its Hamiltonian is
`F_D K F_D*`, for the doubled Hamiltonian `K` of `Φ`, in the relabelled basis. Polynomial PEPS
approximation, `02-information.tex`, lines 416–424. -/
theorem hamiltonian_relabel_conj_pairSwapOp_doubled (Φ : Interaction X S) (D : Finset V)
    (hP : ∀ i, pairSwapOp D * Φ.doubled.term i * (pairSwapOp D)ᴴ ∈
      supportedOperators (fun v ↦ X v × X v) (S i))
    (e : V ≃ V') (f : ∀ v, X v × X v ≃ X' (e v)) (T : ι → Finset V')
    (hT : ∀ i v, v ∈ S i ↔ e v ∈ T i) :
    ((Φ.doubled.conj (pairSwapOp D) hP).relabel e f T hT).hamiltonian =
      reindex (siteConfigurationEquiv e f) (siteConfigurationEquiv e f) (pairSwapOp D) *
        reindex ((Equiv.arrowProdEquivProdArrow V X X).symm.trans (siteConfigurationEquiv e f))
          ((Equiv.arrowProdEquivProdArrow V X X).symm.trans (siteConfigurationEquiv e f))
          (doubledHamiltonian Φ.hamiltonian) *
        (reindex (siteConfigurationEquiv e f) (siteConfigurationEquiv e f) (pairSwapOp D))ᴴ := by
  have hK : reindex ((Equiv.arrowProdEquivProdArrow V X X).symm.trans (siteConfigurationEquiv e f))
      ((Equiv.arrowProdEquivProdArrow V X X).symm.trans (siteConfigurationEquiv e f))
      (doubledHamiltonian Φ.hamiltonian) =
      reindex (siteConfigurationEquiv e f) (siteConfigurationEquiv e f)
        (reindex (Equiv.arrowProdEquivProdArrow V X X).symm
          (Equiv.arrowProdEquivProdArrow V X X).symm (doubledHamiltonian Φ.hamiltonian)) :=
    rfl
  rw [hamiltonian_relabel, hamiltonian_conj, hamiltonian_doubled, hK]
  simp only [reindex_apply, conjTranspose_submatrix, submatrix_mul_equiv]

end Interaction

end ManyBody
