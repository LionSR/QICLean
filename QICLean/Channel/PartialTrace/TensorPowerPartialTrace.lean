/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Algebra.PartialTrace
import QICLean.Algebra.Kronecker.KroneckerFactorPositivity
import QICLean.Algebra.Matrix.MatrixAux

/-!
# Partial traces of regrouped tensor powers

The partial trace of a tensor product is the tensor product of its partial
traces. The coordinate equivalence below applies one fixed bipartite
decomposition to each copy and then collects all copies of each factor.
No positivity or normalization is needed. The same holds for a Kronecker product of a family
of matrices on `X p × E p` whose factor types depend on the index `p`
(`Matrix.partialTraceRight_piKronecker_submatrix`).

Source: *A two-dimensional area law from a global spectral gap*, September 24,
2026, `07-comparators.tex`, lines 550–560, revision
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`; *Polynomial PEPS approximation of gapped
square-grid ground states*, September 24, 2026, proof of Theorem 5.2, `04-compression.tex`,
lines 574–579.

## Main results

* `Matrix.partialTraceLeft_vecMulVec_prod`, `Matrix.norm_sq_one_kronecker_mulVec_prod`: reduced
  densities of actual tensor powers of bipartite vectors.
-/

section TensorPowerPartialTrace

noncomputable section
open scoped BigOperators Matrix Kronecker

namespace TensorPower

/-- Apply a bipartite coordinate decomposition to each copy, then collect
the two families of factors. Source: `07-comparators.tex`, lines 550–560. -/
def copiesProductEquiv {A Q T : Type*} (e : A ≃ Q × T) (m : ℕ) :
    (Fin m → A) ≃ (Fin m → Q) × (Fin m → T) :=
  (Equiv.arrowCongr (Equiv.refl (Fin m)) e).trans
    (Equiv.arrowProdEquivProdArrow (Fin m) (fun _ => Q) (fun _ => T))

end TensorPower

namespace Matrix

/-- Tracing out the second factors `E p` of a Kronecker product of matrices on `X p × E p`,
after grouping the configurations into the pair `((p ↦ x p), (p ↦ e p))`, gives the Kronecker
product of the partial traces. The factor types may vary with `p`.

OpenAI, *Polynomial PEPS approximation of gapped square-grid ground states* (September 24,
2026), proof of Theorem 5.2, `04-compression.tex`, lines 574–579. -/
theorem partialTraceRight_piKronecker_submatrix {P : Type*} [Fintype P] [DecidableEq P]
    {X E : P → Type*} [∀ p, Fintype (E p)] (M : (p : P) → Matrix (X p × E p) (X p × E p) ℂ) :
    partialTraceRight ((piKronecker M).submatrix (Equiv.arrowProdEquivProdArrow P X E).symm
      (Equiv.arrowProdEquivProdArrow P X E).symm) =
      piKronecker fun p ↦ partialTraceRight (M p) := by
  ext x y
  simp only [partialTraceRight_apply, submatrix_apply, piKronecker_apply]
  exact (Fintype.prod_sum fun p (e : E p) ↦ M p (x p, e) (y p, e)).symm

/-- The partial trace of the actual regrouped tensor product is the tensor
product of the actual one-copy partial traces. The factors need not agree.
Source: `07-comparators.tex`, lines 550–560. -/
theorem partialTraceRight_piKronecker_reindex
    {A Q T : Type*} [Fintype T]
    (e : A ≃ Q × T) (m : ℕ) (M : Fin m → Matrix A A ℂ) :
    partialTraceRight ((piKronecker M).submatrix
      (TensorPower.copiesProductEquiv e m).symm
      (TensorPower.copiesProductEquiv e m).symm) =
        piKronecker (fun j => partialTraceRight ((M j).submatrix e.symm e.symm)) := by
  exact partialTraceRight_piKronecker_submatrix fun j => (M j).submatrix e.symm e.symm

end Matrix

end

end TensorPowerPartialTrace

section PureTensorPower

/-!
## Reduced densities of actual tensor powers of bipartite vectors

Regrouping the literal tensor power of a bipartite vector into its two systems
gives the tensor power of its actual reduced density. The squared norm after
an orthogonal projection on the second system is the corresponding trace mass.
In particular, this applies to each actual Schur label projector.

These are the pure-state identities used in the OpenAI area-law manuscript,
`07-comparators.tex`, lines 255–281, `comparator:high-label`.
They hold for arbitrary one-copy vectors and zero copies, including empty
one-copy factors. No invertibility of the reduced density is required.
Concentration, the entropy window and selection of a common label sequence
remain separate statements.
-/

/-
Original actual-product marginal and projection-mass identities supporting
OpenAI, A two-dimensional area law from a global spectral gap,
September 24, 2026, 07-comparators.tex lines 255–281, comparator:high-label.
Independently formalized; no upstream Lean proof text reused.
-/

open scoped BigOperators Matrix Kronecker

namespace Matrix

variable {S Ω : Type*} [Fintype S] [Fintype Ω]

omit [Fintype Ω] in
/-- The reduced density of the literal, regrouped tensor power of a bipartite
vector is the tensor power of its actual one-copy reduced density.
OpenAI area-law manuscript, `07-comparators.tex`, lines 255–281,
`comparator:high-label`. -/
theorem partialTraceLeft_vecMulVec_prod (ψ : S × Ω → ℂ) (k : ℕ) :
    partialTraceLeft (vecMulVec
      (fun x : (Fin k → S) × (Fin k → Ω) => ∏ i, ψ (x.1 i, x.2 i))
      (star (fun x : (Fin k → S) × (Fin k → Ω) => ∏ i, ψ (x.1 i, x.2 i)))) =
    piKronecker (fun _ : Fin k => partialTraceLeft (vecMulVec ψ (star ψ))) := by
  ext x y
  simp only [partialTraceLeft_apply, vecMulVec_apply, Pi.star_apply, star_prod,
    piKronecker_apply]
  simpa only [Finset.prod_mul_distrib] using
    (Fintype.prod_sum (fun (i : Fin k) (s : S) =>
      ψ (s, x i) * star (ψ (s, y i)))).symm

private theorem norm_sq_mulVec_eq_re_trace {n : Type*} [Fintype n]
    (P : Matrix n n ℂ) (hP : IsStarProjection P) (v : n → ℂ) :
    ‖WithLp.toLp 2 (P *ᵥ v)‖ ^ 2 = (vecMulVec v (star v) * P).trace.re := by
  rw [trace_mul_comm, mul_vecMulVec, trace_vecMulVec, dotProduct_comm]
  have hpair := star_dotProduct_mulVec P v (P *ᵥ v)
  rw [mulVec_mulVec, hP.isIdempotentElem.eq, ← star_eq_conjTranspose,
    hP.isSelfAdjoint.star_eq] at hpair
  simpa only [hpair, EuclideanSpace.equiv, PiLp.coe_symm_continuousLinearEquiv,
    RCLike.re_to_complex] using
    (re_star_dotProduct_self_eq_norm_sq (P *ᵥ v)).symm

/-- The squared norm after an actual orthogonal projection on the second
system of a repeated bipartite vector equals its actual tensor-power density
mass. Choosing a Schur label projector gives its sector mass directly.
OpenAI area-law manuscript, `07-comparators.tex`, lines 255–281,
`comparator:high-label`. -/
theorem norm_sq_one_kronecker_mulVec_prod [DecidableEq S]
    (ψ : S × Ω → ℂ) (k : ℕ) (P : Matrix (Fin k → Ω) (Fin k → Ω) ℂ)
    (hP : IsStarProjection P) :
    ‖WithLp.toLp 2 (((1 : Matrix (Fin k → S) (Fin k → S) ℂ) ⊗ₖ P) *ᵥ
      (fun x : (Fin k → S) × (Fin k → Ω) => ∏ i, ψ (x.1 i, x.2 i)))‖ ^ 2 =
    (piKronecker (fun _ : Fin k => partialTraceLeft (vecMulVec ψ (star ψ))) *
      P).trace.re := by
  rw [← partialTraceLeft_vecMulVec_prod ψ k, trace_partialTraceLeft_mul]
  refine norm_sq_mulVec_eq_re_trace _ ?_ _
  rw [isStarProjection_iff', ← mul_kronecker_mul, one_mul,
    hP.isIdempotentElem.eq, star_eq_conjTranspose,
    conjTranspose_kronecker, conjTranspose_one, ← star_eq_conjTranspose,
    hP.isSelfAdjoint.star_eq]
  exact ⟨rfl, rfl⟩

end Matrix

end PureTensorPower
