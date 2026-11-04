/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.LiebConvexity
import Lean.Elab.Command
import Lean.Util.CollectAxioms
import Lean.Util.FoldConsts

/-! Independent semantic and actual proof-body audit of Wolf Theorem 5.15. -/

open scoped Matrix ComplexOrder MatrixOrder Kronecker Matrix.Norms.L2Operator
open Matrix

open Lean in
run_cmd do
  let roots := #[``lieb_convexity_variational_le, ``lieb_convexity_posSemidef_posDef,
    ``lieb_convexity_posDef, ``convexOn_re_trace_conj_rpow_mul_rpow]
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let env := (← getEnv).setExporting false
  let mut todo := roots.toList
  let mut seen : NameSet := {}
  let mut axioms : Array Name := #[]
  let mut opaqueDecls : Array Name := #[]
  let mut missing : Array Name := #[]
  while !todo.isEmpty do
    let n := todo.head!
    todo := todo.tail!
    unless seen.contains n do
      seen := seen.insert n
      match env.checked.get.find? n with
      | none => missing := missing.push n
      | some ci =>
        match ci with
        | .axiomInfo _ => axioms := axioms.push n
        | .opaqueInfo _ => opaqueDecls := opaqueDecls.push n
        | _ => pure ()
        todo := ci.getUsedConstantsAsSet.toList ++ todo
  unless missing.isEmpty do
    throwError "Missing constants in actual proof/type closure: {missing}"
  unless axioms.all (allowed.contains ·) do
    throwError "Unexpected actual closure axioms: {axioms}"
  let repoOpaque := opaqueDecls.filter fun n =>
    match env.getModuleIdxFor? n with
    | none => true
    | some i => "QICLean".isPrefixOf (env.header.moduleNames[i.toNat]!).toString
  unless repoOpaque.isEmpty do
    throwError "Repository opaque declarations in actual closure: {repoOpaque}"
  logInfo m!"Actual combined type/body closure: {seen.size} constants; axioms {axioms}; \
    {opaqueDecls.size} upstream opaques with their actual bodies inspected; zero repository opaques"
  for n in opaqueDecls do
    let some ci := env.find? n | throwError "Missing opaque {n}"
    unless (ci.value? (allowOpaque := true)).isSome do
      throwError "Opaque body unavailable: {n}"
  -- Also check the saved per-theorem axiom metadata.
  for n in roots do
    let some (.thmInfo _) := env.find? n | throwError "Not a theorem: {n}"
    let axs ← collectAxioms n
    unless axs.all (allowed.contains ·) do
      throwError "Unexpected transitive axioms: {n}: {axs}"
    logInfo m!"{n}: {axs}"

-- The source tensor/trace identity with independent powers, including negative q.
-- This checks the exact B-transpose convention at arbitrary complex K.
example {D : ℕ} (A B K : Matrix (Fin D) (Fin D) ℂ) (hB : B.PosSemidef) (p q : ℝ) :
    star (vec Kᵀ) ⬝ᵥ (((A ^ p) ⊗ₖ ((Bᵀ) ^ q)) *ᵥ vec Kᵀ) =
      trace (Kᴴ * A ^ p * K * B ^ q) := by
  rw [Matrix.kronecker_mulVec_vec ((Bᵀ) ^ q) Kᵀ (A ^ p),
    Matrix.star_vec_dotProduct_vec, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
    hB.rpow_transpose q, Matrix.transpose_conjTranspose K,
    ← Matrix.trace_transpose (Kᴴ * A ^ p * K * B ^ q)]
  simp only [Matrix.transpose_mul, Matrix.conjTranspose_transpose, Matrix.mul_assoc]
  rw [Matrix.trace_mul_comm (K.map star)]
  simp only [Matrix.mul_assoc]

-- All lower-edge exponents, rather than only triangle vertices.
example {D : ℕ} (K : Matrix (Fin D) (Fin D) ℂ) {x : ℝ}
    (hx : x ∈ Set.Icc (1 : ℝ) 2) :
    ConvexOn ℝ {P : Matrix (Fin D) (Fin D) ℂ × Matrix (Fin D) (Fin D) ℂ |
      P.1.PosDef ∧ P.2.PosDef}
      (fun P => (trace (Kᴴ * P.1 ^ x * K * P.2 ^ (1 - x))).re) :=
  convexOn_re_trace_conj_rpow_mul_rpow K hx ⟨le_rfl, by linarith [hx.1]⟩

-- Both mixing endpoints remain admissible with singular first arguments.
example {D : ℕ} {x y : ℝ} (hx : x ∈ Set.Icc (1 : ℝ) 2)
    (hy : y ∈ Set.Icc (1 - x) 0) (A B C E K : Matrix (Fin D) (Fin D) ℂ)
    (hA : A.PosSemidef) (hC : C.PosSemidef) (hB : B.PosDef) (hE : E.PosDef) :
    (trace (Kᴴ * C ^ x * K * E ^ y)).re ≤
      0 * (trace (Kᴴ * A ^ x * K * B ^ y)).re +
        1 * (trace (Kᴴ * C ^ x * K * E ^ y)).re := by
  simpa only [zero_smul, sub_zero, one_smul, zero_add] using
    (lieb_convexity_posSemidef_posDef hx hy hA hC hB hE (K := K) (t := 0) (by norm_num))

example {D : ℕ} {x y : ℝ} (hx : x ∈ Set.Icc (1 : ℝ) 2)
    (hy : y ∈ Set.Icc (1 - x) 0) (A B C E K : Matrix (Fin D) (Fin D) ℂ)
    (hA : A.PosSemidef) (hC : C.PosSemidef) (hB : B.PosDef) (hE : E.PosDef) :
    (trace (Kᴴ * A ^ x * K * B ^ y)).re ≤
      1 * (trace (Kᴴ * A ^ x * K * B ^ y)).re +
        0 * (trace (Kᴴ * C ^ x * K * E ^ y)).re := by
  simpa only [one_smul, sub_self, zero_smul, add_zero] using
    (lieb_convexity_posSemidef_posDef hx hy hA hC hB hE (K := K) (t := 1) (by norm_num))

-- Taking Re does not weaken the source's scalar trace: the trace is real.
example {D : ℕ} (A B K : Matrix (Fin D) (Fin D) ℂ) (hB : B.PosDef) (p q : ℝ) :
    (trace (Kᴴ * A ^ p * K * B ^ q)).im = 0 := by
  have hP : (A ^ p).PosSemidef := Matrix.nonneg_iff_posSemidef.mp CFC.rpow_nonneg
  have hnonneg := (hP.conjTranspose_mul_mul_same K).trace_mul_nonneg (hB.rpow q).posSemidef
  exact (Complex.le_def.mp hnonneg).2.symm
