import QICLean.Representation.PairMergeMoment
import QICLean.Analysis.KroneckerExponential
import QICLean.Analysis.TraceDistance

open Matrix PermutationRepresentation
open scoped Kronecker Matrix.Norms.Operator
namespace TensorPower
variable (Q C : Type*) [Fintype Q] [Fintype C] [DecidableEq Q] [DecidableEq C] (m : ℕ)
noncomputable def pairMergeDeficit :
    Matrix ((Fin m → Q) × (Fin m → C)) ((Fin m → Q) × (Fin m → C)) ℂ :=
  labelEntropy (pairCopyLeft Q C m) + labelEntropy (pairCopyRight Q C m) -
    labelEntropy (pairCopyBoth Q C m)

theorem isHermitian_pairMergeDeficit : (pairMergeDeficit Q C m).IsHermitian := by
  exact ((isHermitian_labelObservable _ _).add (isHermitian_labelObservable _ _)).sub
    (isHermitian_labelObservable _ _)

variable (V R : Type*) [Fintype V] [Fintype R] [DecidableEq V] [DecidableEq R]

theorem commute_pairMergeDeficit_lifts :
    Commute (pairMergeDeficit Q C m ⊗ₖ
      (1 : Matrix ((Fin m → V) × (Fin m → R)) ((Fin m → V) × (Fin m → R)) ℂ))
      ((1 : Matrix ((Fin m → Q) × (Fin m → C)) ((Fin m → Q) × (Fin m → C)) ℂ) ⊗ₖ
        pairMergeDeficit V R m) := by
  change _ * _ = _ * _
  rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul]
  simp only [Matrix.one_mul, Matrix.mul_one]

theorem exp_pairMergeDeficit_lifts (a b : ℝ) :
    NormedSpace.exp ((a : ℂ) • (pairMergeDeficit Q C m ⊗ₖ
      (1 : Matrix ((Fin m → V) × (Fin m → R)) ((Fin m → V) × (Fin m → R)) ℂ)) +
      (b : ℂ) • ((1 : Matrix ((Fin m → Q) × (Fin m → C))
        ((Fin m → Q) × (Fin m → C)) ℂ) ⊗ₖ pairMergeDeficit V R m)) =
      NormedSpace.exp ((a : ℂ) • pairMergeDeficit Q C m) ⊗ₖ
        NormedSpace.exp ((b : ℂ) • pairMergeDeficit V R m) := by
  rw [← Matrix.smul_kronecker, ← Matrix.kronecker_smul, Matrix.exp_kronecker_sum]

theorem trace_exp_pairMergeDeficit_left
    (ρ : Matrix (((Fin m → Q) × (Fin m → C)) × ((Fin m → V) × (Fin m → R)))
      (((Fin m → Q) × (Fin m → C)) × ((Fin m → V) × (Fin m → R))) ℂ) (a : ℝ) :
    (ρ * NormedSpace.exp ((a : ℂ) • (pairMergeDeficit Q C m ⊗ₖ
      (1 : Matrix ((Fin m → V) × (Fin m → R)) ((Fin m → V) × (Fin m → R)) ℂ)))).trace =
      (Matrix.partialTraceRight ρ * NormedSpace.exp ((a : ℂ) •
        pairMergeDeficit Q C m)).trace := by
  rw [← Matrix.smul_kronecker, Matrix.exp_kronecker_one,
    ← Matrix.trace_partialTraceRight_mul]

theorem trace_exp_pairMergeDeficit_right
    (ρ : Matrix (((Fin m → Q) × (Fin m → C)) × ((Fin m → V) × (Fin m → R)))
      (((Fin m → Q) × (Fin m → C)) × ((Fin m → V) × (Fin m → R))) ℂ) (b : ℝ) :
    (ρ * NormedSpace.exp ((b : ℂ) • ((1 : Matrix ((Fin m → Q) × (Fin m → C))
      ((Fin m → Q) × (Fin m → C)) ℂ) ⊗ₖ pairMergeDeficit V R m))).trace =
      (Matrix.partialTraceLeft ρ * NormedSpace.exp ((b : ℂ) •
        pairMergeDeficit V R m)).trace := by
  rw [← Matrix.kronecker_smul, Matrix.exp_one_kronecker,
    ← Matrix.trace_partialTraceLeft_mul]
end TensorPower
