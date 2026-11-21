/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.ManyBody.Dynamics.Interaction
import QICLean.Spectral.Filter.PositiveReplacement

/-!
# The positive terms of a gapped interaction

Let `Φ = (hᵢ)ᵢ` be an interaction with finitely many Hermitian terms of norm at most `J`, and
`Ω` a unit vector. The positive term with index `i` is the positive constraint
`kᵢ = |Mᵢ| / c_*` of the centered filtered term `Mᵢ` of `hᵢ`, filtered with the Hamiltonian of
`Φ` at width `Δ / 2`, where `c_* = max {1, J (‖f‖₁ + 1)}` and `‖f‖₁` is the `L¹` norm of the
filter kernel. Every `kᵢ` is positive, and for `Δ > 0` it is a contraction.
If `Ω` is a ground vector of `H` with gap `Δ > 0`, then `kᵢ Ω = 0` and `∑ᵢ kᵢ` dominates
`c_*⁻¹ (H - E₀)`; these are the spectral part of the positive replacement,
`SpectralFilter.positive_replacement`, applied to the terms of `Φ`.

Generalizes TNLean's `ManyBody.PlaneInteraction.positiveTerm`
(`TNLean/PEPS/AreaLaw/Scan/ActualEnergyTerms.lean` at commit `414a18fb88`), stated there for
interactions on a finite domain of the plane: the definition uses only the terms and their
Hamiltonian.

## Main definitions

* `ManyBody.Interaction.positiveTerm` — the positive constraint of a term.

## Main results

* `ManyBody.Interaction.positiveTerm_nonneg`, `ManyBody.Interaction.positiveTerm_le_one`.
* `ManyBody.Interaction.positiveTerm_mulVec_eq_zero`,
  `ManyBody.Interaction.smul_sub_le_sum_positiveTerm` — at a gapped ground vector.

## References

* OpenAI, *A two-dimensional area law from a global spectral gap*, September 24, 2026,
  Proposition 4.3 (`prop:positive`), `03-quasilocal.tex`, lines 220–284.
-/

open Matrix SpectralFilter
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder

namespace ManyBody

namespace Interaction

variable {V : Type*} [Fintype V] [DecidableEq V] {X : V → Type*} [∀ v, Fintype (X v)]
  [∀ v, DecidableEq (X v)] {ι : Type*} [Fintype ι] {S : ι → Finset V}

/-- **The positive term** `kᵢ = |Mᵢ| / c_*` of the term with index `i`: the positive constraint,
normalized by `c_* = max {1, J (‖f‖₁ + 1)}`, of the centered filtered term `Mᵢ` of `hᵢ` for
the Hamiltonian of `Φ`, the unit vector `Ω` and the filter width `Δ / 2`. Area law,
`03-quasilocal.tex`, lines 250–266. -/
noncomputable def positiveTerm (Φ : Interaction X S) (J Δ : ℝ) (Ω : EuclideanSpace ℂ (Config X))
    (i : ι) : Matrix (Config X) (Config X) ℂ :=
  positiveConstraint (positiveNormalization 1 (Δ / 2) J)
    (centeredFilter 1 (Δ / 2) Φ.hamiltonian Ω (Φ.term i))

variable {Φ : Interaction X S} {J Δ : ℝ} {Ω : EuclideanSpace ℂ (Config X)}

variable (Φ J Δ Ω) in
/-- The positive terms are positive. -/
theorem positiveTerm_nonneg (i : ι) : 0 ≤ Φ.positiveTerm J Δ Ω i :=
  positiveConstraint_nonneg (positiveNormalization_pos 1 (Δ / 2) J).le _

/-- For Hermitian terms of norm at most `J`, a unit vector `Ω` and `Δ > 0`, the positive terms
are bounded by the identity. Area law, `03-quasilocal.tex`, lines 263–266. -/
theorem positiveTerm_le_one (hΦ : ∀ i, (Φ.term i).IsHermitian) (hJ : ∀ i, ‖Φ.term i‖ ≤ J)
    (hΔ : 0 < Δ) (hΩ : ‖Ω‖ = 1) (i : ι) : Φ.positiveTerm J Δ Ω i ≤ 1 := by
  refine positiveConstraint_le_one (positiveNormalization_pos 1 (Δ / 2) J) ?_
  refine (norm_centeredFilter_le le_rfl (half_pos hΔ) (isHermitian_hamiltonian hΦ) hΩ
    (Φ.term i)).trans ?_
  exact (mul_le_mul_of_nonneg_right (hJ i)
    (add_nonneg (filterL1_nonneg _ _) zero_le_one)).trans (le_max_right _ _)

section Gapped

variable {E₀ : ℝ} (hΦ : ∀ i, (Φ.term i).IsHermitian) (hJ : ∀ i, ‖Φ.term i‖ ≤ J) (hΔ : 0 < Δ)
  (hΩ : ‖Ω‖ = 1) (hHΩ : Φ.hamiltonian *ᵥ WithLp.ofLp Ω = (E₀ : ℂ) • WithLp.ofLp Ω)
  (hgap : (Φ.hamiltonian - (E₀ : ℂ) • 1 -
    (Δ : ℂ) • (1 - vecMulVec (WithLp.ofLp Ω) (star (WithLp.ofLp Ω)))).PosSemidef)
include hΦ hJ hΔ hΩ hHΩ hgap

omit hJ in
/-- At a ground vector `Ω` of energy `E₀` with gap `Δ > 0`, every positive term annihilates
`Ω`; no bound on the norms of the terms is needed. Area law, `03-quasilocal.tex`,
lines 252–257 and 264–265. -/
theorem positiveTerm_mulVec_eq_zero (i : ι) : Φ.positiveTerm J Δ Ω i *ᵥ WithLp.ofLp Ω = 0 :=
  positiveConstraint_mulVec_eq_zero _
    (isHermitian_centeredFilter 1 _ (isHermitian_hamiltonian hΦ) Ω (hΦ i))
    (centeredFilter_mulVec_eq_zero le_rfl (half_pos hΔ) (half_le_self hΔ.le)
      (isHermitian_hamiltonian hΦ) hΩ hHΩ hgap (Φ.term i))

/-- At a ground vector `Ω` of energy `E₀` with gap `Δ > 0`, the sum of the positive terms
dominates `c_*⁻¹ (H - E₀)`. Area law, Proposition 4.3, `eq:quasilocal-positive`,
`03-quasilocal.tex`, lines 220–284. -/
theorem smul_sub_le_sum_positiveTerm :
    (positiveNormalization 1 (Δ / 2) J)⁻¹ • (Φ.hamiltonian - (E₀ : ℂ) • 1) ≤
      ∑ i, Φ.positiveTerm J Δ Ω i :=
  (positive_replacement le_rfl hΔ hΩ hHΩ hgap Φ.term hΦ hJ rfl).2.1

end Gapped

end Interaction

end ManyBody
