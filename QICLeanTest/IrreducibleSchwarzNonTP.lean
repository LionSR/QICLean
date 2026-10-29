/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Channel.Peripheral.IrreducibleSchwarz
import QICLean.Channel.Schwarz.MultiplicativeDomainFull
import QICLean.Channel.KrausMap
import Mathlib.Tactic.FinCases
import Lean.Util.CollectAxioms
import Lean.Elab.Command

/-!
A concrete irreducible unital Schwarz map that fails trace preservation.
Its input state has weights 9/25 and 16/25. The source-general Wolf theorem
and the internally derived faithful stationary state both apply to this map.
-/

open scoped Matrix ComplexOrder MatrixOrder BigOperators
open Matrix

namespace IrreducibleSchwarzNonTP

abbrev Mat := Matrix (Fin 2) (Fin 2) ℂ

noncomputable def T : Mat →ₗ[ℂ] Mat where
  toFun X := ((9 / 25 : ℂ) * X 0 0 + (16 / 25 : ℂ) * X 1 1) • 1
  map_add' X Y := by
    dsimp
    rw [← add_smul]
    congr 1
    ring
  map_smul' c X := by
    dsimp
    rw [smul_smul]
    congr 1
    ring

noncomputable def K : Fin 4 → Mat :=
  ![!![(3 / 5 : ℂ), 0; 0, 0], !![0, (4 / 5 : ℂ); 0, 0],
    !![0, 0; (3 / 5 : ℂ), 0], !![0, 0; 0, (4 / 5 : ℂ)]]

lemma map_eq : Kraus.mapLM K = T := by
  ext X i j
  fin_cases i <;> fin_cases j <;>
    simp [Kraus.mapLM_apply, Kraus.map_apply, K, T, Matrix.mul_apply,
      Fin.sum_univ_succ, Matrix.vecMul, Matrix.conjTranspose_apply, vecHead, vecTail] <;>
    simp only [map_ofNat] <;> ring

lemma unital : T 1 = 1 := by
  ext i j
  simp [T]
  norm_num

lemma positive : IsPositiveMap T := by
  rw [← map_eq]
  exact Kraus.isPositiveMap_mapLM K

lemma schwarz : IsSchwarzMap T := by
  rw [← map_eq]
  apply KadisonSchwarz.krausMap_isSchwarzMap K
  have h := unital
  rw [← map_eq] at h
  simpa [Kraus.mapLM_apply, Kraus.map_apply] using h

noncomputable def ρ : Mat := Matrix.diagonal ![(9 / 25 : ℂ), (16 / 25 : ℂ)]

lemma faithful : ρ.PosDef := by
  apply Matrix.posDef_diagonal_iff.mpr
  intro i
  fin_cases i <;> norm_num [ρ]

lemma weighted_trace (X : Mat) :
    Matrix.trace (ρ * X) = (9 / 25 : ℂ) * X 0 0 + (16 / 25 : ℂ) * X 1 1 := by
  simp [ρ, Matrix.trace, Matrix.mul_apply, Fin.sum_univ_succ]

lemma irreducible : IsIrreducibleMap T := by
  intro P hP hInv
  by_cases hPzero : P = 0
  · exact Or.inl hPzero
  right
  let c : ℂ := (9 / 25 : ℂ) * P 0 0 + (16 / 25 : ℂ) * P 1 1
  have hcpos : 0 < c := by
    change 0 < (9 / 25 : ℂ) * P 0 0 + (16 / 25 : ℂ) * P 1 1
    rw [← weighted_trace P]
    exact faithful.trace_mul_pos_of_posSemidef_of_ne_zero
      (isOrthogonalProjection_posSemidef hP) hPzero
  have h := hInv 1
  simp only [mul_one, hP.2] at h
  change P * (c • 1) * P = c • 1 at h
  rw [mul_smul_comm, smul_mul_assoc, mul_one, hP.2] at h
  exact (smul_right_injective _ hcpos.ne') h

lemma not_tracePreserving : ¬ IsTracePreservingMap T := by
  intro h
  have h0 := h (!![(1 : ℂ), 0; 0, 0])
  norm_num [T, Matrix.trace, Fin.sum_univ_succ] at h0

example : ∃ ρ' : Mat, ρ'.PosDef ∧ ρ'.trace = 1 ∧ Matrix.traceAdjointMap T ρ' = ρ' :=
  SchwarzMap.exists_posDef_traceAdjoint_stationaryState T positive unital irreducible

example : ∃ m : ℕ, 0 < m ∧ m ≤ 4 ∧
    peripheralEigenvalues T = Set.range (fun j : Fin m =>
      Complex.exp (2 * ↑Real.pi * Complex.I / ↑m) ^ (j : ℕ)) := by
  obtain ⟨m, hm, hbound, hset, _⟩ :=
    SchwarzMap.wolf_theorem_6_6 T positive unital schwarz irreducible
  exact ⟨m, hm, by simpa using hbound, hset⟩

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for decl in #[``irreducible, ``not_tracePreserving, ``positive, ``schwarz] do
    let axs ← Lean.collectAxioms decl
    unless axs.all (allowed.contains ·) do
      throwError "Unexpected axioms for {decl}: {axs}"
    Lean.logInfo m!"{decl}: {axs}"

end IrreducibleSchwarzNonTP
