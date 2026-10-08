/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.SourceOnlyDensityError

/-! Edge-case regressions for SourceOnlyDensityError in the compression proof. -/

open scoped Matrix Matrix.Norms.L2Operator

variable {D : ℕ → Type*} [∀ t, Fintype (D t)] [∀ t, DecidableEq (D t)]

-- Zero chronological length gives exact zero error even for arbitrary gates.
example (G H : (t : ℕ) → Matrix (D (t + 1)) (D t) ℂ)
    (ψ : EuclideanSpace ℂ (D 0)) (K : Matrix (Fin 2 × Fin 3) (D 0) ℂ) :
    Matrix.rectangularTraceNorm
      (Matrix.sourceOnlyReadoutDensity G ψ 0 K - Matrix.sourceOnlyReadoutDensity H ψ 0 K) =
      0 := by
  exact Matrix.rectangularTraceNorm_sourceOnlyReadoutDensity_sub_zero G H ψ K

-- No marked nonprivate gates leaves every private stage exact, at any length.
example (G A : (t : ℕ) → Matrix (D (t + 1)) (D t) ℂ)
    (ψ : EuclideanSpace ℂ (D 0)) (n : ℕ) (K : Matrix (Fin 2 × Fin 3) (D n) ℂ)
    (δ : ℝ) : Matrix.rectangularTraceNorm
      (Matrix.sourceOnlyReadoutDensity (Matrix.markedRescaledGateChain G A ∅ δ) ψ n K -
        Matrix.sourceOnlyReadoutDensity G ψ n K) = 0 := by
  exact Matrix.rectangularTraceNorm_sourceOnlyReadoutDensity_marked_empty G A ψ n K δ

-- Memory dimensions change from 1 to 2 to 3 to 4; only stage 1 is marked.
example (G A : (t : ℕ) → Matrix (Fin ((t + 1) + 1)) (Fin (t + 1)) ℂ)
    (ψ : EuclideanSpace ℂ (Fin 1)) (K : Matrix (Fin 2 × Fin 3) (Fin 4) ℂ)
    (ε : ℝ) (hε : 0 ≤ ε) (hG : ∀ t, ‖G t‖ ≤ 1)
    (herror : ‖A 1 - G 1‖ ≤ ε / 8) (hψ : ‖ψ‖ ≤ 1) (hK : ‖K‖ ≤ 1) :
    Matrix.rectangularTraceNorm
      (Matrix.sourceOnlyReadoutDensity (D := fun t ↦ Fin (t + 1))
        (Matrix.markedRescaledGateChain (D := fun t ↦ Fin (t + 1)) G A {1} (ε / 8)) ψ 3 K -
        Matrix.sourceOnlyReadoutDensity (D := fun t ↦ Fin (t + 1)) G ψ 3 K) ≤ ε / 2 := by
  have herror' : ∀ t ∈ ({1} : Finset ℕ), ‖A t - G t‖ ≤ ε / (8 * ({1} : Finset ℕ).card) := by
    intro t ht
    have ht' : t = 1 := Finset.mem_singleton.mp ht
    subst t
    simpa using herror
  simpa using Matrix.rectangularTraceNorm_sourceOnlyReadoutDensity_marked_sub_le_half
    (D := fun t ↦ Fin (t + 1)) G A ψ 3 K {1} ε hε (by simp) hG herror' hψ hK

-- A half-norm input, identity private gates, and just one marked occurrence.
example : Matrix.rectangularTraceNorm
    (Matrix.sourceOnlyReadoutDensity (D := fun _ ↦ Fin 1) (P := Fin 1) (E := Fin 1)
      (Matrix.markedRescaledGateChain
        (D := fun _ ↦ Fin 1) (fun _ ↦ 1) (fun _ ↦ 1) {1} (1 / 8))
      (EuclideanSpace.single (0 : Fin 1) (1 / 2 : ℂ)) 3
      (Matrix.basisRegisterInjection (0 : Fin 1)) -
      Matrix.sourceOnlyReadoutDensity (D := fun _ ↦ Fin 1) (P := Fin 1) (E := Fin 1) (fun _ ↦ 1)
        (EuclideanSpace.single (0 : Fin 1) (1 / 2 : ℂ)) 3
        (Matrix.basisRegisterInjection (0 : Fin 1))) ≤ 1 / 2 := by
  simpa using Matrix.rectangularTraceNorm_sourceOnlyReadoutDensity_marked_sub_le_half
    (D := fun _ ↦ Fin 1) (P := Fin 1) (E := Fin 1)
    (fun _ ↦ 1) (fun _ ↦ 1) (EuclideanSpace.single (0 : Fin 1) (1 / 2 : ℂ)) 3
    (Matrix.basisRegisterInjection (0 : Fin 1)) {1} 1 (by norm_num) (by simp)
    (fun _ ↦ Matrix.l2_opNorm_one_le)
    (by intro t _; simp)
    (by norm_num)
    (Matrix.l2_opNorm_le_one_of_conjTranspose_mul_self_eq_one
      (Matrix.basisRegisterInjection_conjTranspose_mul_self (0 : Fin 1)))

-- Zero input gives exactly zero actual density without input normalization.
example (G : (t : ℕ) → Matrix (D (t + 1)) (D t) ℂ)
    (n : ℕ) (K : Matrix (Fin 2 × Fin 3) (D n) ℂ) :
    Matrix.sourceOnlyReadoutDensity G 0 n K = 0 := by
  ext i j
  simp [Matrix.sourceOnlyReadoutDensity, Matrix.sourceOnlyReadoutVector,
    Matrix.euclideanOuterProduct, Matrix.partialTraceRight_apply]

-- The common readout may have an empty owned register, with no nonempty premise.
example (G A : (t : ℕ) → Matrix (D (t + 1)) (D t) ℂ)
    (ψ : EuclideanSpace ℂ (D 0)) (δ : ℝ) (hδ : 0 ≤ δ)
    (hG : ∀ t, ‖G t‖ ≤ 1) (herror : ∀ t, ‖A t - G t‖ ≤ δ) (hψ : ‖ψ‖ ≤ 1) :
    Matrix.rectangularTraceNorm
      (Matrix.sourceOnlyReadoutDensity (Matrix.rescaledGateChain A δ) ψ 2
        (0 : Matrix (Fin 3 × Fin 0) (D 2) ℂ) -
        Matrix.sourceOnlyReadoutDensity (E := Fin 0) G ψ 2 0) ≤ 4 * 2 * δ := by
  exact Matrix.rectangularTraceNorm_sourceOnlyReadoutDensity_sub_le G A ψ 2 0 δ hδ
    hG herror hψ (by simp)
