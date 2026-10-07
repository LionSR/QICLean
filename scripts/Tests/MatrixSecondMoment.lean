import QICLean.Probability.MatrixSecondMoment

/-!
# Matrix second-moment regressions

The checks retain arbitrary rectangular dimensions, permit empty coefficient
families and test the one-coefficient specialization on an actual probability
measure. The axiom reports check the compiled exported proof dependencies.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators ComplexConjugate Matrix.Norms.Frobenius

example {m n : Type*} [Fintype m] [Fintype n]
    (A : PUnit → Matrix m n ℂ) :
    (∫ _ω : ℝ, ‖∑ i : PUnit, (1 : ℂ) • A i‖ ^ 2 ∂Measure.dirac 0) =
      ∑ i : PUnit, (1 : ℝ) * ‖A i‖ ^ 2 := by
  classical
  exact integral_frobenius_norm_sq_sum_eq_sum
    (fun _ _ => 1) (fun _ => 1)
    (by intro i j; simp)
    (by intro i j; simp [Subsingleton.elim i j]) A

example {m n : Type*} [Fintype m] [Fintype n]
    (A : Fin 0 → Matrix m n ℂ) :
    (∫ _ω : ℝ, ‖∑ i : Fin 0, (1 : ℂ) • A i‖ ^ 2 ∂Measure.dirac 0) =
      ∑ i : Fin 0, (0 : ℝ) * ‖A i‖ ^ 2 := by
  exact integral_frobenius_norm_sq_sum_eq_sum
    (fun _ _ => 1) (fun _ => 0)
    (by intro i; exact Fin.elim0 i)
    (by intro i; exact Fin.elim0 i) A

example {m n : Type*} [Fintype m] [Fintype n]
    (A : PUnit → Matrix m n ℂ) :
    (∫ _ω : ℝ, ‖∑ i : PUnit, (1 : ℂ) • A i‖ ∂Measure.dirac 0) ≤
      Real.sqrt (∑ i : PUnit, (1 : ℝ) * ‖A i‖ ^ 2) := by
  classical
  exact integral_frobenius_norm_sum_le_sqrt
    (fun _ _ => 1) (fun _ => 1)
    (by intro i j; simp)
    (by intro i j; simp [Subsingleton.elim i j]) A

#print axioms ProbabilityTheory.integrable_normSq_sum
#print axioms ProbabilityTheory.integral_normSq_sum_eq_sum
#print axioms ProbabilityTheory.integrable_frobenius_norm_sq_sum
#print axioms ProbabilityTheory.integral_frobenius_norm_sq_sum_eq_sum
#print axioms ProbabilityTheory.integral_frobenius_norm_sum_le_sqrt
