/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.ReplicaGoodConfigurationSingletonMoment

/-!
# The original three physical marginal densities

Each singleton density is the partial trace of the same original physical
pure matrix. It is positive semidefinite for every physical vector and has
trace one when that vector is a unit vector. Empty coordinate spaces and
singular density matrices require no separate convention.

Source: *A two-dimensional area law from a global spectral gap*, September 24,
2026, `07-comparators.tex`, lines 550--560, revision
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

noncomputable section

open TensorPower
open scoped Matrix

namespace Matrix

variable (ι : Fin 5 → Type*) [∀ f, Fintype (ι f)] [∀ f, DecidableEq (ι f)]
variable (Ω : ι 0 × (ι 1 × ι 2) → ℂ)

/-- The original one-copy marginal on one of the three physical factors.
Source: `07-comparators.tex`, lines 550–560. -/
def physicalSingletonDensity (j : Fin 3) :
    Matrix (ι (j.castAdd 2)) (ι (j.castAdd 2)) ℂ :=
  partialTraceRight ((vecMulVec Ω (star Ω)).submatrix
    (physicalSingletonEquiv ι j).symm (physicalSingletonEquiv ι j).symm)

/-- The original singleton marginal is positive semidefinite.
Source: `07-comparators.tex`, lines 550–560. -/
theorem posSemidef_physicalSingletonDensity (j : Fin 3) :
    (physicalSingletonDensity ι Ω j).PosSemidef :=
  ((posSemidef_vecMulVec_self_star (R := ℂ) Ω).submatrix
    (physicalSingletonEquiv ι j).symm).partialTraceRight

/-- A unit original physical vector has trace-one singleton marginals.
Source: `07-comparators.tex`, lines 550–560. -/
theorem trace_physicalSingletonDensity (hΩ : ‖WithLp.toLp 2 Ω‖ = 1) (j : Fin 3) :
    (physicalSingletonDensity ι Ω j).trace = 1 := by
  rw [physicalSingletonDensity, trace_partialTraceRight, trace_submatrix_equiv,
    trace_vecMulVec, ← EuclideanSpace.inner_eq_star_dotProduct
      (WithLp.toLp 2 Ω) (WithLp.toLp 2 Ω), inner_self_eq_norm_sq_to_K, hΩ]
  norm_num


end Matrix
