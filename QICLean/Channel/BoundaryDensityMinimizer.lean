/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.RectangularTraceNormTopology
import QICLean.Channel.BoundaryGluing
import QICLean.Analysis.ShiftedDensityPowers
import Mathlib.Topology.Order.Compact

/-!
# A minimum under boundary and support constraints

Fix a matrix `P` on the left sites, a boundary matrix `X` and a radius `η`. Density matrices
`σ` fixed by left multiplication by `P ⊗ 1`, whose boundary marginal is within trace-norm
distance `η` of `X`, form a compact set. If the pure state of a unit left vector `x` satisfies
these constraints, the set is nonempty and its left energy attains a minimum. The minimum is
at most the left energy of `x`, and its boundary marginal is within `2η` of that of `x`.

This is the existence and optimality part of the size-trimming optimization problem of
Landau, Vazirani and Vidick, arXiv:1307.5143v1, `algo53.tex`, equation `eq:conv`, lines
472–476, and its use in Lemma `l:leading`, lines 493–505. Nonemptiness is supplied for a
boundary matrix close to the pure left state; it is not asserted for arbitrary net points.
-/

open scoped Matrix Kronecker ComplexOrder

namespace Matrix

variable {a s b : Type*} [Fintype a] [Fintype s] [Fintype b]
  [DecidableEq a] [DecidableEq s] [DecidableEq b]

omit [Fintype s] [Fintype b] [DecidableEq a] [DecidableEq s] [DecidableEq b] in
private theorem continuous_partialTraceFirst :
    Continuous (partialTraceFirst : Matrix ((a × s) × b) ((a × s) × b) ℂ →
      Matrix (s × b) (s × b) ℂ) := by
  change Continuous (fun X : Matrix ((a × s) × b) ((a × s) × b) ℂ ↦
    fun i j : s × b ↦ ∑ k : a, X ((k, i.1), i.2) ((k, j.1), j.2))
  exact continuous_pi fun i ↦ continuous_pi fun j ↦ continuous_finsetSum _ fun k _ ↦
    (continuous_apply ((k, j.1), j.2)).comp (continuous_apply ((k, i.1), i.2))

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
  let F := {ρ : Matrix ((a × s) × b) ((a × s) × b) ℂ |
    ρ.PosSemidef ∧ ρ.trace = 1 ∧ Q * ρ = ρ ∧
      rectangularTraceNorm (partialTraceFirst ρ - X) ≤ η}
  have hsupport : IsClosed {ρ : Matrix ((a × s) × b) ((a × s) × b) ℂ | Q * ρ = ρ} :=
    isClosed_eq (continuous_const.mul continuous_id) continuous_id
  have hboundary : IsClosed {ρ : Matrix ((a × s) × b) ((a × s) × b) ℂ |
      rectangularTraceNorm (partialTraceFirst ρ - X) ≤ η} :=
    (isClosed_setOf_rectangularTraceNorm_le η).preimage
      (continuous_partialTraceFirst.sub continuous_const)
  have hcompact : IsCompact F := by
    simpa only [F, Set.ofPred_and, Set.inter_assoc] using
      isCompact_setOf_posSemidef_trace_eq_one.inter_right (hsupport.inter hboundary)
  have hρxp : ρx.PosSemidef := posSemidef_vecMulVec_self_star _
  have hρxt : ρx.trace = 1 := by
    change (vecMulVec (WithLp.ofLp x) (star (WithLp.ofLp x))).trace = 1
    rw [trace_vecMulVec, ← EuclideanSpace.inner_eq_star_dotProduct,
      inner_self_eq_norm_sq_to_K, hx]
    norm_num
  have hρxP : Q * ρx = ρx := by
    change Q * vecMulVec (WithLp.ofLp x) (star (WithLp.ofLp x)) = ρx
    rw [mul_vecMulVec, hPx]
  have hρx : ρx ∈ F := ⟨hρxp, hρxt, hρxP, hX⟩
  have henergy : Continuous fun ρ : Matrix ((a × s) × b) ((a × s) × b) ℂ ↦
      (ρ * (HL ⊗ₖ (1 : Matrix b b ℂ))).trace.re :=
    Complex.continuous_re.comp ((continuous_id.mul continuous_const).matrix_trace)
  obtain ⟨σ, hσ, hmin⟩ := hcompact.exists_isMinOn ⟨ρx, hρx⟩ henergy.continuousOn
  refine ⟨σ, hσ.1, hσ.2.1, hσ.2.2.1, hσ.2.2.2, ?_, hmin hρx, ?_⟩
  · intro ρ hρp hρt hρP hρX
    exact hmin ⟨hρp, hρt, hρP, hρX⟩
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
      _ ≤ 2 * η := by rw [hneg]; linarith [hσ.2.2.2]

end Matrix
