/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.TraceConvexFunctions
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! Actual-name boundary and standard-foundation checks for Wolf's convex trace functions. -/

open scoped Matrix BigOperators
open Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]
variable {I : Set ℝ} {f : ℝ → ℝ} (hf : ConvexOn ℝ I f)
variable {A B : Matrix n n ℂ} (hA : A.IsHermitian) (hB : B.IsHermitian)
variable (hAI : spectrum ℝ A ⊆ I) (hBI : spectrum ℝ B ⊆ I)

-- Both closed mixing endpoints, with arbitrary f and arbitrary interval.
example : (cfc f ((0 : ℝ) • A + (1 : ℝ) • B)).trace.re ≤
    0 * (hA.cfc f).trace.re + 1 * (hB.cfc f).trace.re :=
  hA.trace_cfc_convex_le hf hB hAI hBI (by norm_num) (by norm_num) (by norm_num)

example : (cfc f ((1 : ℝ) • A + (0 : ℝ) • B)).trace.re ≤
    1 * (hA.cfc f).trace.re + 0 * (hB.cfc f).trace.re :=
  hA.trace_cfc_convex_le hf hB hAI hBI (by norm_num) (by norm_num) (by norm_num)

-- Exact requested t,1-t form; membership is derived, not a premise.
example {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    (t • A + (1 - t) • B) ∈ hermitianSpectralDomain n I ∧
    (cfc f (t • A + (1 - t) • B)).trace.re ≤
      t * (cfc f A).trace.re + (1 - t) * (cfc f B).trace.re := by
  refine ⟨convex_hermitianSpectralDomain hf.1 ⟨hA, hAI⟩ ⟨hB, hBI⟩
    ht.1 (sub_nonneg.mpr ht.2) (by ring), ?_⟩
  simpa only [hA.cfc_eq, hB.cfc_eq] using
    hA.trace_cfc_convex_le hf hB hAI hBI ht.1 (sub_nonneg.mpr ht.2) (by ring)

-- Empty matrix dimension: even the empty interval is a valid spectral domain.
example : (0 : Matrix (Fin 0) (Fin 0) ℂ) ∈
    hermitianSpectralDomain (Fin 0) (∅ : Set ℝ) := by
  exact ⟨isHermitian_zero, by simp⟩

example (g : ℝ → ℝ) :
    ConvexOn ℝ (hermitianSpectralDomain (Fin 0) (∅ : Set ℝ))
      (fun A => (cfc g A).trace.re) :=
  convexOn_trace_cfc ⟨convex_empty, by simp⟩

-- Functional calculus on an empty matrix has trace zero even when g(0) is nonzero.
example (g : ℝ → ℝ) :
    (cfc g (0 : Matrix (Fin 0) (Fin 0) ℂ)).trace.re = 0 := by
  simp [Matrix.trace]

-- Three-term scalar Jensen and domain closure, including a zero weight.
example (C : Fin 3 → Matrix n n ℂ)
    (hC : ∀ i, C i ∈ hermitianSpectralDomain n I) :
    (∑ i : Fin 3, (![0, 1 / 3, 2 / 3] : Fin 3 → ℝ) i • C i) ∈
        hermitianSpectralDomain n I ∧
      (cfc f (∑ i : Fin 3, (![0, 1 / 3, 2 / 3] : Fin 3 → ℝ) i • C i)).trace.re ≤
        ∑ i : Fin 3, (![0, 1 / 3, 2 / 3] : Fin 3 → ℝ) i * (cfc f (C i)).trace.re := by
  apply trace_cfc_sum_le hf Finset.univ _ C
  · intro i _
    fin_cases i <;> norm_num
  · norm_num [Fin.sum_univ_succ]
  · exact fun i _ => hC i

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let declarations := #[
    ``Matrix.hermitianSpectralDomain,
    ``Matrix.IsHermitian.re_dotProduct_mem_of_spectrum_subset,
    ``Matrix.IsHermitian.diagonal_jensen_of_spectrum_subset,
    ``Matrix.convex_hermitianSpectralDomain,
    ``Matrix.IsHermitian.trace_cfc_convex_le,
    ``Matrix.convexOn_trace_cfc,
    ``Matrix.trace_cfc_sum_le]
  for decl in declarations do
    unless (← Lean.getEnv).contains decl do
      throwError "Missing declaration {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"
