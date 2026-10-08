/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Algebra.KroneckerFactorPositivity
import QICLean.Algebra.MatrixAux
import QICLean.Channel.PartialTrace

/-!
# Reduced densities of actual tensor powers of bipartite vectors

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

/-- The reduced density of the literal, regrouped tensor power of a bipartite
vector is the tensor power of its actual one-copy reduced density.
OpenAI area-law manuscript, `07-comparators.tex`, lines 255–281,
`comparator:high-label`. -/
theorem partialTraceLeft_vecMulVec_prod (ψ : S × Ω → ℂ) (k : ℕ) :
    partialTraceLeft (vecMulVec
      (fun x : (Fin k → S) × (Fin k → Ω) => ∏ i, ψ (x.1 i, x.2 i))
      (star (fun x : (Fin k → S) × (Fin k → Ω) => ∏ i, ψ (x.1 i, x.2 i)))) =
    finKronecker (fun _ : Fin k => partialTraceLeft (vecMulVec ψ (star ψ))) := by
  ext x y
  simp only [partialTraceLeft_apply, vecMulVec_apply, Pi.star_apply, star_prod,
    finKronecker_apply]
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
    (finKronecker (fun _ : Fin k => partialTraceLeft (vecMulVec ψ (star ψ))) *
      P).trace.re := by
  rw [← partialTraceLeft_vecMulVec_prod ψ k, trace_partialTraceLeft_mul]
  refine norm_sq_mulVec_eq_re_trace _ ?_ _
  rw [isStarProjection_iff', ← mul_kronecker_mul, one_mul,
    hP.isIdempotentElem.eq, star_eq_conjTranspose,
    conjTranspose_kronecker, conjTranspose_one, ← star_eq_conjTranspose,
    hP.isSelfAdjoint.star_eq]
  exact ⟨rfl, rfl⟩

end Matrix
