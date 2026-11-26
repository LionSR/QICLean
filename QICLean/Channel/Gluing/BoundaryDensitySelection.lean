/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Spectral.Eigenvalue.DensityMaxEigenvector
import QICLean.Analysis.TraceNorm.RectangularTraceNorm
import QICLean.Channel.Gluing.BoundaryGluing
import QICLean.Analysis.FunctionalCalculus.ShiftedDensityPowers
import Mathlib.Topology.Order.Compact

/-!
# A leading eigenvector of a minimizing feasible density matrix

A nonempty density set with support and boundary constraints admits a global minimum
of the left energy. A unit eigenvector for the largest eigenvalue of a minimizing
density matrix is fixed by the same support matrix: its eigenvalue is positive, so
the support identity for the density matrix can be cancelled on this eigenvector.

This is an auxiliary existence statement for the size-trimming optimization problem
of Landau, Vazirani and Vidick, arXiv:1307.5143v1, `algo53.tex`, equation `eq:conv`,
lines 472–476, and the leading eigenvector in Lemma 2.5 (`l:leading`), lines 493–505.

It also contains the following results.

* `Matrix.exists_boundary_density_minimizer_of_nonempty`,
  `Matrix.exists_boundary_density_minimizer`: a minimum under boundary and support constraints.
-/

open scoped Matrix Kronecker ComplexOrder

namespace Matrix

section BoundaryDensityMinimizer

/-!
## A minimum under boundary and support constraints

Fix a matrix `P` on the left sites, a boundary matrix `X` and a radius `η`. Density matrices
`σ` fixed by left multiplication by `P ⊗ 1`, whose boundary marginal is within trace-norm
distance `η` of `X`, form a compact set. If the pure state of a unit left vector `x` satisfies
these constraints, the set is nonempty. More generally, whenever the feasible density set is
nonempty, its left energy attains a global minimum. In the pure-state case, this minimum is
at most the left energy of `x`, and its boundary marginal is within `2η` of that of `x`.

This is the existence and optimality part of the size-trimming optimization problem of
Landau, Vazirani and Vidick, arXiv:1307.5143v1, `algo53.tex`, equation `eq:conv`, lines
472–476, and its use in Lemma `l:leading`, lines 493–505. Nonemptiness is supplied for a
boundary matrix close to the pure left state; it is not asserted for arbitrary net points.
-/

variable {a s b : Type*} [Fintype a] [Fintype s] [Fintype b]
  [DecidableEq a] [DecidableEq s] [DecidableEq b]

omit [DecidableEq a] in
/-- A nonempty feasible density set for the size-trimming optimization problem of LVV13
(`algo53.tex`, equation `eq:conv`, lines 472–476) has a global minimum of the left energy.
Nonemptiness is an explicit hypothesis; feasibility is not asserted for arbitrary boundary
matrices. No projection or self-adjointness condition on `P`, `HL` or `X` is needed. -/
theorem exists_boundary_density_minimizer_of_nonempty
    (P HL : Matrix (a × s) (a × s) ℂ) (X : Matrix (s × b) (s × b) ℂ) (η : ℝ)
    (hne : Set.Nonempty {ρ : Matrix ((a × s) × b) ((a × s) × b) ℂ |
      ρ.PosSemidef ∧ ρ.trace = 1 ∧ (P ⊗ₖ (1 : Matrix b b ℂ)) * ρ = ρ ∧
      rectangularTraceNorm (partialTraceFirst ρ - X) ≤ η}) :
    ∃ σ : Matrix ((a × s) × b) ((a × s) × b) ℂ,
      σ.PosSemidef ∧ σ.trace = 1 ∧ (P ⊗ₖ (1 : Matrix b b ℂ)) * σ = σ ∧
      rectangularTraceNorm (partialTraceFirst σ - X) ≤ η ∧
      (∀ ρ : Matrix ((a × s) × b) ((a × s) × b) ℂ,
        ρ.PosSemidef → ρ.trace = 1 → (P ⊗ₖ (1 : Matrix b b ℂ)) * ρ = ρ →
        rectangularTraceNorm (partialTraceFirst ρ - X) ≤ η →
        (σ * (HL ⊗ₖ (1 : Matrix b b ℂ))).trace.re ≤
          (ρ * (HL ⊗ₖ (1 : Matrix b b ℂ))).trace.re) := by
  let Q := P ⊗ₖ (1 : Matrix b b ℂ)
  let F := {ρ : Matrix ((a × s) × b) ((a × s) × b) ℂ |
    ρ.PosSemidef ∧ ρ.trace = 1 ∧ Q * ρ = ρ ∧
      rectangularTraceNorm (partialTraceFirst ρ - X) ≤ η}
  have hsupport : IsClosed {ρ : Matrix ((a × s) × b) ((a × s) × b) ℂ | Q * ρ = ρ} :=
    isClosed_eq (continuous_const.mul continuous_id) continuous_id
  have hboundary : IsClosed {ρ : Matrix ((a × s) × b) ((a × s) × b) ℂ |
      rectangularTraceNorm (partialTraceFirst ρ - X) ≤ η} := by
    let e := (Equiv.prodAssoc a s b).trans (Equiv.prodComm a (s × b))
    let T := (partialTraceRightLM (α := s × b) (β := a)).comp
      (reindexLinearEquiv ℂ ℂ e e).toLinearMap
    exact (isClosed_setOf_rectangularTraceNorm_le η).preimage
      (T.continuous_of_finiteDimensional.sub continuous_const)
  have hcompact : IsCompact F := by
    simpa only [F, Set.ofPred_and, Set.inter_assoc] using
      isCompact_setOf_posSemidef_trace_eq_one.inter_right (hsupport.inter hboundary)
  have henergy : Continuous fun ρ : Matrix ((a × s) × b) ((a × s) × b) ℂ ↦
      (ρ * (HL ⊗ₖ (1 : Matrix b b ℂ))).trace.re :=
    Complex.continuous_re.comp ((continuous_id.mul continuous_const).matrix_trace)
  obtain ⟨σ, hσ, hmin⟩ := hcompact.exists_isMinOn hne henergy.continuousOn
  refine ⟨σ, hσ.1, hσ.2.1, hσ.2.2.1, hσ.2.2.2, ?_⟩
  intro ρ hρp hρt hρP hρX
  exact hmin ⟨hρp, hρt, hρP, hρX⟩

omit [DecidableEq a] in
/-- A minimizing density matrix for the size-trimming optimization problem of LVV13
(`algo53.tex`, equation `eq:conv`, lines 472–476), given a feasible pure left state. The
energy comparison and boundary distance used in Lemma `l:leading` (lines 493–505) follow
from minimization and the triangle inequality. -/
theorem exists_boundary_density_minimizer
    (P HL : Matrix (a × s) (a × s) ℂ) (X : Matrix (s × b) (s × b) ℂ) (η : ℝ)
    (x : EuclideanSpace ℂ ((a × s) × b)) (hx : ‖x‖ = 1)
    (hPx : (P ⊗ₖ (1 : Matrix b b ℂ)) *ᵥ WithLp.ofLp x = WithLp.ofLp x)
    (hX : rectangularTraceNorm
      (partialTraceFirst (vecMulVec (WithLp.ofLp x) (star (WithLp.ofLp x))) - X) ≤ η) :
    ∃ σ : Matrix ((a × s) × b) ((a × s) × b) ℂ,
      σ.PosSemidef ∧ σ.trace = 1 ∧ (P ⊗ₖ (1 : Matrix b b ℂ)) * σ = σ ∧
      rectangularTraceNorm (partialTraceFirst σ - X) ≤ η ∧
      (∀ ρ : Matrix ((a × s) × b) ((a × s) × b) ℂ,
        ρ.PosSemidef → ρ.trace = 1 → (P ⊗ₖ (1 : Matrix b b ℂ)) * ρ = ρ →
        rectangularTraceNorm (partialTraceFirst ρ - X) ≤ η →
        (σ * (HL ⊗ₖ (1 : Matrix b b ℂ))).trace.re ≤
          (ρ * (HL ⊗ₖ (1 : Matrix b b ℂ))).trace.re) ∧
      (σ * (HL ⊗ₖ (1 : Matrix b b ℂ))).trace.re ≤
        (vecMulVec (WithLp.ofLp x) (star (WithLp.ofLp x)) *
          (HL ⊗ₖ (1 : Matrix b b ℂ))).trace.re ∧
      rectangularTraceNorm (partialTraceFirst σ -
        partialTraceFirst (vecMulVec (WithLp.ofLp x) (star (WithLp.ofLp x)))) ≤ 2 * η := by
  let Q := P ⊗ₖ (1 : Matrix b b ℂ)
  let ρx := vecMulVec (WithLp.ofLp x) (star (WithLp.ofLp x))
  have hρxp : ρx.PosSemidef := posSemidef_vecMulVec_self_star _
  have hρxt : ρx.trace = 1 := by
    change (vecMulVec (WithLp.ofLp x) (star (WithLp.ofLp x))).trace = 1
    rw [trace_vecMulVec, ← EuclideanSpace.inner_eq_star_dotProduct,
      inner_self_eq_norm_sq_to_K, hx]
    norm_num
  have hρxP : Q * ρx = ρx := by
    change Q * vecMulVec (WithLp.ofLp x) (star (WithLp.ofLp x)) = ρx
    rw [mul_vecMulVec, hPx]
  obtain ⟨σ, hσ, htr, hσP, hσX, hmin⟩ :=
    exists_boundary_density_minimizer_of_nonempty P HL X η ⟨ρx, hρxp, hρxt, hρxP, hX⟩
  refine ⟨σ, hσ, htr, hσP, hσX, hmin, hmin ρx hρxp hρxt hρxP hX, ?_⟩
  · have hneg : rectangularTraceNorm (X - partialTraceFirst ρx) =
        rectangularTraceNorm (partialTraceFirst ρx - X) := by
      rw [show X - partialTraceFirst ρx = (-1 : ℂ) • (partialTraceFirst ρx - X) by
        simp, rectangularTraceNorm_smul]
      norm_num
    calc
      rectangularTraceNorm (partialTraceFirst σ - partialTraceFirst ρx) =
          rectangularTraceNorm ((partialTraceFirst σ - X) + (X - partialTraceFirst ρx)) := by
            rw [sub_add_sub_cancel]
      _ ≤ rectangularTraceNorm (partialTraceFirst σ - X) +
          rectangularTraceNorm (X - partialTraceFirst ρx) := rectangularTraceNorm_add_le _ _
      _ ≤ 2 * η := by rw [hneg]; linarith [hσX]

end BoundaryDensityMinimizer

section BoundaryDensitySelection

variable {a s b : Type*} [Fintype a] [Fintype s] [Fintype b]
  [DecidableEq s] [DecidableEq b]

/-- A global minimum over the feasible densities has a positive maximal-eigenvalue
unit vector fixed by the support matrix. Auxiliary existence for LVV13, `algo53.tex`,
equation `eq:conv`, lines 472–476, and Lemma 2.5, lines 493–505. -/
theorem exists_boundary_density_minimizer_max_eigenvector
    (P HL : Matrix (a × s) (a × s) ℂ) (X : Matrix (s × b) (s × b) ℂ) (η : ℝ)
    (hne : Set.Nonempty {ρ : Matrix ((a × s) × b) ((a × s) × b) ℂ |
      ρ.PosSemidef ∧ ρ.trace = 1 ∧ (P ⊗ₖ (1 : Matrix b b ℂ)) * ρ = ρ ∧
      rectangularTraceNorm (partialTraceFirst ρ - X) ≤ η}) :
    ∃ (σ : Matrix ((a × s) × b) ((a × s) × b) ℂ)
      (u : EuclideanSpace ℂ ((a × s) × b)) (μ : ℝ),
      σ.PosSemidef ∧ σ.trace = 1 ∧ (P ⊗ₖ (1 : Matrix b b ℂ)) * σ = σ ∧
      rectangularTraceNorm (partialTraceFirst σ - X) ≤ η ∧
      (∀ ρ : Matrix ((a × s) × b) ((a × s) × b) ℂ,
        ρ.PosSemidef → ρ.trace = 1 → (P ⊗ₖ (1 : Matrix b b ℂ)) * ρ = ρ →
        rectangularTraceNorm (partialTraceFirst ρ - X) ≤ η →
        (σ * (HL ⊗ₖ (1 : Matrix b b ℂ))).trace.re ≤
          (ρ * (HL ⊗ₖ (1 : Matrix b b ℂ))).trace.re) ∧
      ‖u‖ = 1 ∧ 0 < μ ∧ σ *ᵥ WithLp.ofLp u = (μ : ℂ) • WithLp.ofLp u ∧
      (P ⊗ₖ (1 : Matrix b b ℂ)) *ᵥ WithLp.ofLp u = WithLp.ofLp u ∧
      ∀ (ν : ℝ) (w : EuclideanSpace ℂ ((a × s) × b)), w ≠ 0 →
        σ *ᵥ WithLp.ofLp w = (ν : ℂ) • WithLp.ofLp w → ν ≤ μ := by
  obtain ⟨σ, hσ, htr, hP, hX, hmin⟩ :=
    exists_boundary_density_minimizer_of_nonempty P HL X η hne
  obtain ⟨u, μ, hu, heig, hμ, hmax⟩ := hσ.exists_unit_eigenvector_max_eigenvalue htr
  refine ⟨σ, u, μ, hσ, htr, hP, hX, hmin, hu, hμ, heig, ?_, hmax⟩
  apply smul_right_injective _ (show (μ : ℂ) ≠ 0 by exact_mod_cast ne_of_gt hμ)
  simpa only [← mulVec_mulVec, heig, mulVec_smul] using
    congrArg (fun A ↦ A *ᵥ WithLp.ofLp u) hP

end BoundaryDensitySelection

end Matrix
