/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Channel.Peripheral.IrreducibleSchwarz
import QICLean.Channel.Peripheral.JordanBlocks
import QICLean.Channel.Peripheral.CyclicGroupKraus
import QICLean.Channel.Peripheral.CyclicDecomposition.PeripheralUnitary
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Lean.Util.CollectAxioms

/-! Independent source-meaning checks for Wolf Theorem 6.6. -/

open scoped Matrix ComplexOrder MatrixOrder BigOperators

namespace IrreducibleSchwarzSemanticAudit

-- Match the source's spectrum intersect exp(i R), using finite-dimensional
-- spectral equivalence and polar representation, without positivity premises.
theorem source_spectrum_bridge {V : Type*} [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (T : V →ₗ[ℂ] V) :
    peripheralEigenvalues T = spectrum ℂ T ∩
      Set.range (fun θ : ℝ => Complex.exp ((θ : ℂ) * Complex.I)) := by
  ext z
  simp only [peripheralEigenvalues, Set.mem_ofPred_eq, Set.mem_inter_iff,
    Set.mem_range, Module.End.hasEigenvalue_iff_mem_spectrum,
    Complex.norm_eq_one_iff]

-- The assembled spectral resolution entails the actual spectral eigenrelations.
theorem projection_eigenrelation {D m : ℕ} (γ : ℂ)
    (U : Matrix (Fin D) (Fin D) ℂ) (P : Fin m → Matrix (Fin D) (Fin D) ℂ)
    (hP : ∀ k : Fin m, IsOrthogonalProjection (P k))
    (hOrth : ∀ k l : Fin m, k ≠ l → P k * P l = 0)
    (hSpec : U = ∑ k : Fin m, γ ^ (k : ℕ) • P k) :
    ∀ k : Fin m, U * P k = γ ^ (k : ℕ) • P k := by
  classical
  intro k
  rw [hSpec, Finset.sum_mul]
  simp only [smul_mul_assoc]
  rw [Finset.sum_eq_single k]
  · rw [(hP k).2]
  · intro b _ hbk
    rw [hOrth b k hbk, smul_zero]
  · intro hk
    exact (hk (Finset.mem_univ k)).elim

-- Cyclic action and a faithful stationary weight force every listed
-- spectral projection to be nonzero; the capstone does not merely permit
-- padding a shorter resolution by zero projections.
theorem cyclic_projections_nonzero {D m : ℕ} [NeZero D] [NeZero m]
    (T : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ)
    (ρ : Matrix (Fin D) (Fin D) ℂ) (hρ : ρ.PosDef)
    (hFix : Matrix.traceAdjointMap T ρ = ρ)
    (P : Fin m → Matrix (Fin D) (Fin D) ℂ)
    (hSum : ∑ k, P k = 1) (hCyc : ∀ k, T (P (k + 1)) = P k) :
    ∀ k, P k ≠ 0 := by
  cases m with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ n =>
    let f : Fin (n + 1) → ℂ := fun k => Matrix.trace (ρ * P k)
    have hStep (k : Fin (n + 1)) : f (k + 1) = f k := by
      dsimp [f]
      calc
        Matrix.trace (ρ * P (k + 1)) = Matrix.trace (ρ * T (P (k + 1))) := by
          rw [← Matrix.trace_traceAdjointMap_mul, hFix]
        _ = Matrix.trace (ρ * P k) := by rw [hCyc]
    have hConst (k : Fin (n + 1)) : f k = f 0 := by
      refine Fin.induction rfl (fun i hi => ?_) k
      simpa only [Fin.coeSucc_eq_succ] using (hStep i.castSucc).trans hi
    have hSumTrace : ∑ k, f k = Matrix.trace ρ := by
      dsimp [f]
      rw [← Matrix.trace_sum, ← Finset.mul_sum, hSum, Matrix.mul_one]
    have hNonzero : f 0 ≠ 0 := by
      intro h0
      have hAll (k : Fin (n + 1)) : f k = 0 := (hConst k).trans h0
      simp only [hAll, Finset.sum_const_zero] at hSumTrace
      exact hρ.trace_pos.ne' hSumTrace.symm
    intro k hk
    apply hNonzero
    rw [← hConst k]
    simp [f, hk]

-- The existing positive-unital theorem excludes generalized chains.
-- Thus the ordinary one-dimensional eigenspaces can be strengthened to
-- algebraic simplicity, without needing a TP assumption.
example {D : ℕ} [NeZero D]
    (T : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ)
    (hPos : IsPositiveMap T) (hOne : T 1 = 1) (μ : ℂ) (hμ : ‖μ‖ = 1)
    (k : ℕ) (X : Matrix (Fin D) (Fin D) ℂ)
    (hGen : ((T - μ • (1 : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ]
      Matrix (Fin D) (Fin D) ℂ)) ^ k) X = 0) :
    (T - μ • (1 : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ]
      Matrix (Fin D) (Fin D) ℂ)) X = 0 :=
  hPos.peripheral_Jordan_trivial_of_unital hOne μ hμ k X hGen

run_cmd do
  let expected := #[``propext, ``Classical.choice, ``Quot.sound]
  let names := #[``SchwarzMap.wolf_theorem_6_6,
    ``SchwarzMap.exists_posDef_traceAdjoint_stationaryState,
    ``SchwarzMap.exists_posDef_traceAdjoint_fixedPoint,
    ``exists_posDef_traceAdjointMap_eigenvector_at_perron,
    ``IsIrreducibleMap.traceAdjointMap,
    ``eigenvector_eq_smul_of_irreducible_positive,
    ``SchwarzMap.mem_multiplicativeDomain_of_peripheral_eigenvector,
    ``exists_cyclic_projections_of_peripheral_unitary,
    ``IsPositiveMap.peripheral_Jordan_trivial_of_unital,
    ``IrreducibleSchwarzSemanticAudit.source_spectrum_bridge,
    ``IrreducibleSchwarzSemanticAudit.projection_eigenrelation,
    ``IrreducibleSchwarzSemanticAudit.cyclic_projections_nonzero]
  for name in names do
    let axioms ← Lean.collectAxioms name
    unless axioms.all expected.contains do
      throwError "Unexpected axiom dependency at {name}: {axioms}"
    Lean.logInfo m!"INDEPENDENT AUDIT {name}: {axioms}"

end IrreducibleSchwarzSemanticAudit
