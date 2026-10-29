/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Channel.EntropyIncreasingMaps
import QICLean.Channel.ChoiJamiolkowski
import Mathlib.Analysis.Convex.SpecificFunctions.Deriv
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! Boundary regressions for Wolf Eq. (8.22), using the actual public theorem. -/

open Matrix
open scoped ComplexOrder

noncomputable section

namespace EntropyIncreasingMapsRegression

private theorem quadratic_strictConcave :
    StrictConcaveOn ℝ Set.univ (fun x : ℝ ↦ -(x ^ 2)) :=
  (Even.strictConvexOn_pow (by decide : Even 2) (by decide)).neg

-- The source-facing theorem has no dimension, CP, or invertibility hypothesis.
example {n : Type*} [Fintype n] [DecidableEq n]
    (T : Matrix n n ℂ →ₗ[ℂ] Matrix n n ℂ) (hT : IsPositiveMap T)
    (htr : IsTracePreservingMap T) :
    T 1 = 1 ↔ ∀ (A : Matrix n n ℂ) (hA : A.PosSemidef), trace A = 1 →
      (trace (hA.isHermitian.cfc (fun x ↦ -(x ^ 2)))).re ≤
        (trace ((hT A hA).isHermitian.cfc (fun x ↦ -(x ^ 2)))).re :=
  hT.unital_iff_trace_strictConcave_increasing htr quadratic_strictConcave

-- Empty matrices have no normalized state; the equivalence still applies.
example : ¬ ∃ A : Matrix (Fin 0) (Fin 0) ℂ, trace A = 1 := by simp [trace]

example (T : Matrix (Fin 0) (Fin 0) ℂ →ₗ[ℂ] Matrix (Fin 0) (Fin 0) ℂ)
    (hT : IsPositiveMap T) (htr : IsTracePreservingMap T)
    (h : ℝ → ℝ) (hh : StrictConcaveOn ℝ Set.univ h) :
    ∀ (A : Matrix (Fin 0) (Fin 0) ℂ) (hA : A.PosSemidef), trace A = 1 →
      (trace (hA.isHermitian.cfc h)).re ≤
        (trace ((hT A hA).isHermitian.cfc h)).re :=
  (hT.unital_iff_trace_strictConcave_increasing htr hh).mp (Subsingleton.elim _ _)

-- In dimension one, TP already forces unitality.
example (T : Matrix (Fin 1) (Fin 1) ℂ →ₗ[ℂ] Matrix (Fin 1) (Fin 1) ℂ)
    (hT : IsPositiveMap T) (htr : IsTracePreservingMap T)
    (h : ℝ → ℝ) (hh : StrictConcaveOn ℝ Set.univ h) :
    ∀ (A : Matrix (Fin 1) (Fin 1) ℂ) (hA : A.PosSemidef), trace A = 1 →
      (trace (hA.isHermitian.cfc h)).re ≤
        (trace ((hT A hA).isHermitian.cfc h)).re := by
  apply (hT.unital_iff_trace_strictConcave_increasing htr hh).mp
  ext i j
  fin_cases i
  fin_cases j
  simpa [trace] using htr 1

private abbrev M2 := Matrix (Fin 2) (Fin 2) ℂ

private def pureState : M2 := diagonal ![1, 0]

private theorem pureState_pos : pureState.PosSemidef := by
  apply PosSemidef.diagonal
  intro i
  fin_cases i <;> simp

example : det pureState = 0 := by simp [pureState, det_diagonal, Fin.prod_univ_two]

-- A concrete singular pure state is accepted by the forward implication.
example (T : M2 →ₗ[ℂ] M2) (hT : IsPositiveMap T) (htr : IsTracePreservingMap T)
    (hT1 : T 1 = 1) (h : ℝ → ℝ) (hh : StrictConcaveOn ℝ Set.univ h) :
    (trace (pureState_pos.isHermitian.cfc h)).re ≤
      (trace ((hT pureState pureState_pos).isHermitian.cfc h)).re := by
  exact (hT.unital_iff_trace_strictConcave_increasing htr hh).mp hT1
    pureState pureState_pos (by simp [pureState, trace, Fin.sum_univ_two])

private def reset : M2 →ₗ[ℂ] M2 := (traceLinearMap (Fin 2) ℂ ℂ).smulRight pureState

private theorem reset_pos : IsPositiveMap reset := by
  intro A hA
  exact pureState_pos.smul hA.trace_nonneg

private theorem reset_tp : IsTracePreservingMap reset := by
  intro A
  simp [reset, pureState, trace, Fin.sum_univ_two]

private theorem reset_not_unital : reset 1 ≠ 1 := by
  intro heq
  have he := congrArg (fun A : M2 ↦ A 1 1) heq
  norm_num [reset, pureState] at he

private lemma quadratic_cfc {A : M2} (hA : A.IsHermitian) :
    hA.cfc (fun x ↦ -(x ^ 2)) = -(A ^ 2) := by
  rw [← hA.cfc_eq, cfc_neg, cfc_pow_id (ha := hA.isSelfAdjoint)]

private def mixedState : M2 := (1 / 2 : ℝ) • 1

private theorem mixedState_pos : mixedState.PosSemidef :=
  PosSemidef.one.smul (by norm_num : (0 : ℝ) ≤ 1 / 2)

-- An explicit normalized witness: reset sends I/2 to |0⟩⟨0| and reduces -tr(ρ²).
example : trace mixedState = 1 ∧
    ¬ ((trace (mixedState_pos.isHermitian.cfc (fun x ↦ -(x ^ 2)))).re ≤
      (trace ((reset_pos mixedState mixedState_pos).isHermitian.cfc
        (fun x ↦ -(x ^ 2)))).re) := by
  constructor
  · norm_num [mixedState, trace_smul, trace_one]
  · rw [quadratic_cfc, quadratic_cfc]
    norm_num [reset, mixedState, pureState, trace, Fin.sum_univ_two, pow_two,
      Matrix.mul_apply, Matrix.one_apply]

-- The nonunital positive TP reset map fails quadratic entropy increase.
example : ¬ (∀ (A : M2) (hA : A.PosSemidef), trace A = 1 →
      (trace (hA.isHermitian.cfc (fun x ↦ -(x ^ 2)))).re ≤
        (trace ((reset_pos A hA).isHermitian.cfc (fun x ↦ -(x ^ 2)))).re) := by
  exact fun h ↦ reset_not_unital
    ((reset_pos.unital_iff_trace_strictConcave_increasing reset_tp
      quadratic_strictConcave).mpr h)

-- Transposition increases this entropy even though it is not completely positive.
example : ¬ IsCPMap (transposeLinearMapComplex (Fin 2)) :=
  ChoiJamiolkowski.transposeLinearMapComplex_not_isCPMap (by decide)

example (A : M2) (hA : A.PosSemidef) (htr : trace A = 1)
    (h : ℝ → ℝ) (hh : StrictConcaveOn ℝ Set.univ h) :
    (trace (hA.isHermitian.cfc h)).re ≤
      (trace ((transposeLinearMapComplex_isPositiveMap (n := Fin 2) A hA).isHermitian.cfc
        h)).re :=
  ((transposeLinearMapComplex_isPositiveMap (n := Fin 2)).unital_iff_trace_strictConcave_increasing
    (transposeLinearMapComplex_isTracePreservingMap (n := Fin 2)) hh).mp
      (by simp [transposeLinearMapComplex]) A hA htr

end EntropyIncreasingMapsRegression

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for decl in #[``IsPositiveMap.trace_concave_le,
      ``Matrix.IsHermitian.trace_concave_le_uniform,
      ``Matrix.IsHermitian.eq_smul_one_of_trace_strictConcave_ge,
      ``IsPositiveMap.unital_iff_trace_strictConcave_increasing] do
    unless (← Lean.getEnv).contains decl do
      throwError "Missing declaration {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"
