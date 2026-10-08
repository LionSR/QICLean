/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.ReplicaRegionalDensity
import QICLean.Analysis.TraceDistance
import QICLean.Analysis.KroneckerExponential
import QICLean.Representation.LabelProjectors
import QICLean.Representation.TensorPowerAction

/-!
# Physical label moments of an excitation component

The actual excitation component has the unit ground vector on every good copy.
For any physical region, its exponential label moment therefore equals the iid
regional moment multiplied by the squared norm of the same component. The left
side retains every complementary physical and exterior coordinate in its literal
rank-one trace pairing; no marginal or independence premise is supplied.

This is the exact iid evaluation used in OpenAI, *A two-dimensional area law from
a global spectral gap*, September 24, 2026, `07-comparators.tex`, lines 556–560,
following the regional product argument at lines 520–549. The exponent is any real
number, so both physical signs are included. Zero copies and zero components are
included. This identity does not prove the signed centred label-moment rate at
lines 227–237, equation `comparator:signed-label-moments`, or the sharp comparison.
-/

open scoped BigOperators Matrix Kronecker
namespace Matrix

variable {Q T K : Type*} [Fintype Q] [DecidableEq Q]
  [Fintype T] [DecidableEq T] [Fintype K] [DecidableEq K]

/-
Provenance-ID: 8750-qic-physical-label-moment-01
Original formalization, no upstream Lean proof text reused.
Declaration: Matrix.trace_exp_labelEntropy_replicaExcitationComponent_eq
Manuscript: September 24, 2026, comparator:component-inverse, lines 520–549 and 556–560.
-/

/-- The exponential label trace pairing of the actual excitation component is
its squared norm times the iid one-region label moment, for every real exponent.
The chosen good-copy enumeration is the same on the retained region and its
complement, and every exterior coordinate remains in the original rank-one
pairing. OpenAI, *A two-dimensional area law from a global spectral gap*,
September 24, 2026, `07-comparators.tex`, lines 520–549 and 556–560, equation
`comparator:component-inverse`. Only the one-copy ground vector is unit; no
symmetry, marginal identity, component normalization or nonzero premise is used. -/
theorem trace_exp_labelEntropy_replicaExcitationComponent_eq
    (Ω : Q × T → ℂ) (hΩ : ‖WithLp.toLp 2 Ω‖ = 1)
    {k : ℕ} (B : Finset (Fin k)) (u : (Fin k → Q × T) × K → ℂ) (a : ℝ) :
    let m := Bᶜ.card
    let w := (replicaExcitationProjection Ω k B ⊗ₖ (1 : Matrix K K ℂ)) *ᵥ u
    let f := fun x : ((Fin m → Q) × K) × ((Fin m → T) × (↥B → Q × T)) =>
      w ((FiniteProduct.splitEquiv (fun _ : Fin k => Q × T) B).symm
        (x.2.2, fun i => (x.1.1 ((Finset.equivFin Bᶜ) i),
          x.2.1 ((Finset.equivFin Bᶜ) i))), x.1.2)
    let F := PermutationRepresentation.labelEntropy (TensorPower.copyPerm Q m)
    let ρ := finKronecker (fun _ : Fin m => partialTraceRight (vecMulVec Ω (star Ω)))
    (vecMulVec f (star f) * NormedSpace.exp ((a : ℂ) •
      ((F ⊗ₖ (1 : Matrix K K ℂ)) ⊗ₖ
        (1 : Matrix ((Fin m → T) × (↥B → Q × T))
          ((Fin m → T) × (↥B → Q × T)) ℂ)))).trace =
      (‖WithLp.toLp 2 w‖ ^ 2 : ℂ) * (ρ * NormedSpace.exp ((a : ℂ) • F)).trace := by
  intro m w f F ρ
  rw [← Matrix.smul_kronecker, Matrix.exp_kronecker_one,
    ← trace_partialTraceRight_mul]
  rw [partialTraceRight_replicaExcitationComponent_goodRegional_density Ω hΩ B u]
  rw [← Matrix.smul_kronecker, Matrix.exp_kronecker_one,
    ← Matrix.mul_kronecker_mul, Matrix.mul_one, Matrix.trace_kronecker,
    trace_partialTraceLeft]
  rw [trace_vecMulVec, ← EuclideanSpace.inner_eq_star_dotProduct
    (WithLp.toLp 2 w) (WithLp.toLp 2 w), inner_self_eq_norm_sq_to_K]
  exact mul_comm _ _
end Matrix
