/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.ReplicaGoodConfigurationDensity
import QICLean.Analysis.ReplicaGoodPairMarginal
import QICLean.Analysis.TraceDistance

/-!
# Tracing the good middle physical coordinates

The actual good-copy density retains five factors in the order `Q,Y,V,C,R`.
Regrouping these factors as `((Q,C),(V,R)),Y` and tracing the middle
physical copies yields the existing common good-pair density. Thus its
moment estimates apply to this same five-factor density. Positivity and
total mass are also derived from the actual excitation component.

No symmetry or normalization is required for these coordinate identities.
The good middle physical coordinates are retained until the indicated
partial trace.

## References

* OpenAI, *A two-dimensional area law from a global spectral gap*,
  September 24, 2026, `07-comparators.tex`, lines 513–549,
  `comparator:merge-decomposition` and `comparator:merge-moments`, revision
  `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

noncomputable section

open scoped BigOperators Matrix Kronecker
open TensorPower

namespace TensorPower

/-- Regroup the five good-copy factors as the two exterior physical/auxiliary
pairs, followed by all good middle physical copies. The same copy ordering
is used in every register. Source: `07-comparators.tex`, lines 513–549. -/
def fiveFactorPairMiddleEquiv (ι : Fin 5 → Type*) (m : ℕ) :
    Config m ι ≃ (((Fin m → ι 0) × (Fin m → ι 3)) ×
      ((Fin m → ι 2) × (Fin m → ι 4))) × (Fin m → ι 1) where
  toFun x := (((fun j ↦ x j 0, fun j ↦ x j 3),
    (fun j ↦ x j 2, fun j ↦ x j 4)), fun j ↦ x j 1)
  invFun x j := Fin.cons (x.1.1.1 j) (Fin.cons (x.2 j)
    (Fin.cons (x.1.2.1 j) (Fin.cons (x.1.1.2 j)
      (Fin.cons (x.1.2.2 j) (fun i ↦ Fin.elim0 i)))))
  left_inv x := by
    funext j f
    fin_cases f <;> rfl
  right_inv x := rfl

end TensorPower

namespace Matrix

variable (ι : Fin 5 → Type*) [∀ f, Fintype (ι f)] [∀ f, DecidableEq (ι f)]
variable (Ω : ι 0 × (ι 1 × ι 2) → ℂ) (k : ℕ) (B : Finset (Fin k))
variable (u : (Fin k → ι 0 × (ι 1 × ι 2)) ×
  ((Fin k → ι 3) × (Fin k → ι 4)) → ℂ)

/-- The actual five-factor good-copy density is positive semidefinite.
Source: `07-comparators.tex`, lines 520–549. -/
theorem posSemidef_replicaGoodConfigurationMarginal :
    (replicaGoodConfigurationMarginal ι Ω k B u).PosSemidef := by
  dsimp only [replicaGoodConfigurationMarginal]
  exact (posSemidef_vecMulVec_self_star (R := ℂ) _).partialTraceRight

/-- Tracing exactly the good middle physical coordinates gives the actual
common good-pair marginal. All bad physical and auxiliary coordinates were
already traced in the five-factor density.
Source: `07-comparators.tex`, lines 513–549. -/
theorem partialTraceRight_replicaGoodConfigurationMarginal_pairMiddle :
    partialTraceRight
      ((replicaGoodConfigurationMarginal ι Ω k B u).submatrix
        (fiveFactorPairMiddleEquiv ι Bᶜ.card).symm
        (fiveFactorPairMiddleEquiv ι Bᶜ.card).symm) =
      replicaGoodPairMarginal Ω k B u := by
  classical
  ext x y
  simp only [partialTraceRight_apply, submatrix_apply,
    replicaGoodConfigurationMarginal, replicaGoodPairMarginal,
    partialTraceRight_apply, vecMulVec_apply, Pi.star_apply,
    Fintype.sum_prod_type] <;> rfl

/-- The total mass of the five-factor density is the squared norm of the
same actual excitation component. Zero components and zero copies are
included. Source: `07-comparators.tex`, lines 520–549. -/
theorem trace_replicaGoodConfigurationMarginal :
    (replicaGoodConfigurationMarginal ι Ω k B u).trace =
      ((‖WithLp.toLp 2 ((replicaExcitationProjection Ω k B ⊗ₖ
        (1 : Matrix ((Fin k → ι 3) × (Fin k → ι 4))
          ((Fin k → ι 3) × (Fin k → ι 4)) ℂ)) *ᵥ u)‖ ^ 2 : ℝ) : ℂ) := by
  have h := congrArg Matrix.trace
    (partialTraceRight_replicaGoodConfigurationMarginal_pairMiddle ι Ω k B u)
  rw [trace_partialTraceRight, trace_submatrix_equiv] at h
  exact h.trans (trace_replicaGoodPairMarginal Ω k B u)

/-- Any observable on the two good pairs has exactly the same expectation
after tracing the good middle physical coordinates. This identity applies
in particular to the paired merge exponential.
Source: `07-comparators.tex`, lines 520–549. -/
theorem trace_replicaGoodConfigurationMarginal_pairMiddle_mul
    (H : Matrix (((Fin Bᶜ.card → ι 0) × (Fin Bᶜ.card → ι 3)) ×
        ((Fin Bᶜ.card → ι 2) × (Fin Bᶜ.card → ι 4)))
      (((Fin Bᶜ.card → ι 0) × (Fin Bᶜ.card → ι 3)) ×
        ((Fin Bᶜ.card → ι 2) × (Fin Bᶜ.card → ι 4))) ℂ) :
    (((replicaGoodConfigurationMarginal ι Ω k B u).submatrix
        (fiveFactorPairMiddleEquiv ι Bᶜ.card).symm
        (fiveFactorPairMiddleEquiv ι Bᶜ.card).symm) *
      (H ⊗ₖ (1 : Matrix (Fin Bᶜ.card → ι 1) (Fin Bᶜ.card → ι 1) ℂ))).trace =
      (replicaGoodPairMarginal Ω k B u * H).trace := by
  rw [← trace_partialTraceRight_mul,
    partialTraceRight_replicaGoodConfigurationMarginal_pairMiddle]

end Matrix
