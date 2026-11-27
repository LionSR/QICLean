/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Representation.Character.Delta
import QICLean.Analysis.Real.ComplexSqrt
import Mathlib.LinearAlgebra.Eigenspace.Basic
import QICLean.Representation.Character.DeltaPositive

/-!
# Fourth-root weights of a representation

The isotypic weight operator `Θ` acts by the positive real fourth root of `dᵢ/mᵢ` on each
irreducible summand of dimension `dᵢ` and multiplicity `mᵢ`. It commutes with the representation
and satisfies `Θ⁴ = |G| Δ` for the operator `Δ` of `QICLean.Representation.Character.Delta`.
Its square acts by the square root of `dᵢ/mᵢ`, which on a summand of multiplicity one is the
square root of the dimension. When every multiplicity is one, these are the fourth-root
dimension weights of Schuch, Cirac, and Pérez-García, arXiv:1001.3807, Section 7, lines
2958–3007. The algebraic construction applies to every finite-dimensional complex
representation; it assumes neither unitarity nor semi-regularity.

**Local fix (fourth-root normalization):** The source states `Θ⁴ = Δ`, although its Lemma 4.4
defines `Δ` with the factor `|G|⁻¹`. With that definition, the exact identity is `Θ⁴ = |G| Δ`.
This normalization correction is recorded in the TNLean note
<https://sirui-lu.com/TNLean/paper-gaps/rmp_peps_quantum_double_g_isometry.pdf>.

Moved from TNLean, `TNLean/Algebra/RepresentationTheta.lean` and
`TNLean/Algebra/RepresentationThetaSquared.lean` at commit `49b78ed821` (Apache-2.0).
Changes: the two modules are merged.

## Main results

* `Representation.thetaOperator_apply_of_mem`: the action of `Θ` on an irreducible summand.
* `Representation.thetaOperator_pow_four`: `Θ⁴ = |G| Δ`.
* `Representation.thetaOperator_commute`: `Θ` commutes with the representation.
* `Representation.thetaOperator_sq_apply_of_mem`: the action of `Θ²` on an irreducible summand.

Moved from TNLean, `TNLean/Algebra/RepresentationThetaPositive.lean` at commit `021ba0bd19`
(Apache-2.0).
-/

noncomputable section
open Module LinearMap
open scoped BigOperators
namespace Representation

variable {G V : Type*} [Group G] [Fintype G]
variable [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]

/-- The fourth-root isotypic weights. Source: SCP10, Section 7, lines 2962–2977. -/
noncomputable def thetaOperator (ρ : Representation ℂ G V) : Module.End ℂ V :=
  ∑ χ ∈ irreducibleCharacterFinset ρ,
    (Real.sqrt (Real.sqrt ((χ 1).re / (characterMultiplicity ρ χ).re)) : ℂ) •
      charProjector ρ χ

/-- On an irreducible summand, Θ acts by the fourth root of its dimension
divided by its multiplicity. Source: SCP10, Section 7, lines 2962–2977,
extended to arbitrary occurring multiplicities. -/
theorem thetaOperator_apply_of_mem (ρ : Representation ℂ G V)
    (S : Subrepresentation ρ) [S.toRepresentation.IsIrreducible] {v : V} (hv : v ∈ S) :
    thetaOperator ρ v =
      (Real.sqrt (Real.sqrt ((S.toRepresentation.character 1).re /
        (characterMultiplicity ρ S.toRepresentation.character).re)) : ℂ) • v :=
  sum_smul_charProjector_apply_of_mem ρ _ S hv

/-- For multiplicity one, the weight is the fourth root of the irreducible dimension.
Source: SCP10, the displayed definition of Θ, lines 2962–2972. -/
theorem thetaOperator_apply_of_multiplicity_one (ρ : Representation ℂ G V)
    (S : Subrepresentation ρ) [S.toRepresentation.IsIrreducible]
    (hm : characterMultiplicity ρ S.toRepresentation.character = 1)
    {v : V} (hv : v ∈ S) :
    thetaOperator ρ v =
      (Real.sqrt (Real.sqrt (finrank ℂ S.toSubmodule : ℝ)) : ℂ) • v := by
  rw [thetaOperator_apply_of_mem ρ S hv, hm, char_one]
  simp only [Complex.natCast_re, Complex.one_re, div_one]

private theorem thetaCoefficient_pow_four (ρ : Representation ℂ G V)
    (S : Subrepresentation ρ) :
    (Real.sqrt (Real.sqrt ((S.toRepresentation.character 1).re /
      (characterMultiplicity ρ S.toRepresentation.character).re)) : ℂ) ^ 4 =
        S.toRepresentation.character 1 / characterMultiplicity ρ S.toRepresentation.character := by
  rw [char_one, characterMultiplicity_eq_finrank]
  simp only [Complex.natCast_re, ← Complex.ofReal_pow]
  have hn : 0 ≤ (finrank ℂ S.toSubmodule : ℝ) /
      (finrank ℂ (IntertwiningMap S.toRepresentation ρ) : ℝ) :=
    div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have hroot (r : ℝ) (hr : 0 ≤ r) : Real.sqrt (Real.sqrt r) ^ 4 = r := by
    calc
      _ = (Real.sqrt (Real.sqrt r) ^ 2) ^ 2 := by ring
      _ = Real.sqrt r ^ 2 := by rw [Real.sq_sqrt (Real.sqrt_nonneg r)]
      _ = r := Real.sq_sqrt hr
  rw [hroot _ hn]
  simp only [Complex.ofReal_div, Complex.ofReal_natCast]

/-- The exact fourth-power identity with the normalized trace-dual operator.
Source: SCP10, Section 7, lines 2971–2972, with the normalization of Lemma 4.4. -/
theorem thetaOperator_pow_four (ρ : Representation ℂ G V) :
    thetaOperator ρ ^ 4 = (Nat.card G : ℂ) • deltaOperator ρ := by
  classical
  apply linearMap_ext_on_irreducible ρ
  intro S hS v hv
  let := hS
  by_cases hv0 : v = 0
  · subst v
    simp
  have heig : (thetaOperator ρ).HasEigenvector
      (Real.sqrt (Real.sqrt ((S.toRepresentation.character 1).re /
        (characterMultiplicity ρ S.toRepresentation.character).re)) : ℂ) v :=
    ⟨Module.End.mem_eigenspace_iff.mpr (thetaOperator_apply_of_mem ρ S hv), hv0⟩
  rw [heig.pow_apply, LinearMap.smul_apply, deltaOperator_apply_of_mem ρ S hv,
    smul_smul, thetaCoefficient_pow_four]
  congr 1
  have hG := natCard_ne_zero_complex (G := G)
  field_simp

/-- The fourth-root weights commute with every group action.
Source: SCP10, the simultaneous block form of Θ and V, lines 2958–2972. -/
theorem thetaOperator_commute (ρ : Representation ℂ G V) (g : G) :
    Commute (thetaOperator ρ) (ρ g) :=
  sum_smul_charProjector_commute ρ _ g
end Representation

namespace Representation

variable {G V : Type*} [Group G] [Fintype G]
variable [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]

/-- The square of the fourth-root weight operator acts on an irreducible summand by the square
root of its dimension divided by its multiplicity. Source: SCP10, Section 7, lines 2977–3007,
extended to arbitrary occurring multiplicities. -/
theorem thetaOperator_sq_apply_of_mem (ρ : Representation ℂ G V)
    (S : Subrepresentation ρ) [S.toRepresentation.IsIrreducible]
    {v : V} (hv : v ∈ S) :
    (thetaOperator ρ ^ 2) v =
      (Real.sqrt ((S.toRepresentation.character 1).re /
        (characterMultiplicity ρ S.toRepresentation.character).re) : ℂ) • v := by
  rw [pow_two, Module.End.mul_apply, thetaOperator_apply_of_mem ρ S hv,
    map_smul, thetaOperator_apply_of_mem ρ S hv, smul_smul, ← pow_two,
    Complex.ofReal_sqrt_sq _ (Real.sqrt_nonneg _)]

/-- On an irreducible summand of multiplicity one, the square of the fourth-root weight operator
acts by the square root of its dimension. Source: SCP10, Section 7, lines 2992–3007. -/
theorem thetaOperator_sq_apply_of_multiplicity_one (ρ : Representation ℂ G V)
    (S : Subrepresentation ρ) [S.toRepresentation.IsIrreducible]
    (hm : characterMultiplicity ρ S.toRepresentation.character = 1)
    {v : V} (hv : v ∈ S) :
    (thetaOperator ρ ^ 2) v =
      (Real.sqrt (Module.finrank ℂ S.toSubmodule : ℝ) : ℂ) • v := by
  rw [thetaOperator_sq_apply_of_mem ρ S hv, hm, char_one]
  simp only [Complex.natCast_re, Complex.one_re, div_one]

end Representation

section

open Module LinearMap

open scoped ComplexOrder

namespace Representation

variable {G V : Type*} [Group G] [Fintype G]

variable [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]

/-- The fourth-root weight is invertible, with no unitarity assumption.
Source: SCP10, §7, lines 3000–3006, and Lemma 4.4, lines 970–976. -/
theorem isUnit_thetaOperator (ρ : Representation ℂ G V) : IsUnit (thetaOperator ρ) := by
  apply (isUnit_pow_iff (by norm_num : (4 : ℕ) ≠ 0)).mp
  rw [thetaOperator_pow_four, Algebra.smul_def]
  exact ((isUnit_iff_ne_zero.mpr (natCard_ne_zero_complex (G := G))).map
    (algebraMap ℂ (Module.End ℂ V))).mul (isUnit_deltaOperator ρ)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E]

/-- The fourth-root weight of a unitary representation is positive.
Source: the positive coefficients in SCP10, §7, lines 3000–3006. -/
theorem isPositive_thetaOperator_of_unitary (ρ : Representation ℂ G E)
    (hρ : ∀ g, LinearMap.adjoint (ρ g) = ρ g⁻¹) :
    (thetaOperator ρ).IsPositive := by
  classical
  rw [thetaOperator]
  apply isPositive_sum_smul_charProjector_of_nonneg ρ _ hρ
  intro χ hχ
  positivity

/-- In every orthonormal basis, the fourth-root weight is positive definite.
Source: the positive occurring block weights in SCP10, §7, lines 3000–3006. -/
theorem posDef_toMatrix_thetaOperator_of_unitary (ρ : Representation ℂ G E)
    (hρ : ∀ g, LinearMap.adjoint (ρ g) = ρ g⁻¹)
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : OrthonormalBasis ι ℂ E) :
    (LinearMap.toMatrix b.toBasis b.toBasis (thetaOperator ρ)).PosDef := by
  have hp := (LinearMap.posSemidef_toMatrix_iff b).mpr
    (isPositive_thetaOperator_of_unitary ρ hρ)
  apply hp.posDef_iff_isUnit.mpr
  exact (isUnit_thetaOperator ρ).map (LinearMap.toMatrixAlgEquiv b.toBasis).toMonoidHom

end Representation

end
