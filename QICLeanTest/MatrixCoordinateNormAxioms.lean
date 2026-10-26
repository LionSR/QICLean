/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.EuclideanReindex
import QICLean.Analysis.KroneckerOperatorNorm
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! Standard-axiom checks for coordinate transport and identity-tensor operator norms. -/

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for decl in #[``Matrix.inner_toEuclideanLin_reindex, ``Matrix.l2_opNorm_one_kronecker] do
    unless (← Lean.getEnv).contains decl do
      throwError "Missing declaration {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"

open scoped Kronecker Matrix.Norms.L2Operator InnerProductSpace

example (K : Matrix (Fin 0) (Fin 0) ℂ) :
    ‖(1 : Matrix (Fin 1) (Fin 1) ℂ) ⊗ₖ K‖ = ‖K‖ :=
  Matrix.l2_opNorm_one_kronecker K

example (M : Matrix (Fin 0) (Fin 0) ℂ) (ψ : EuclideanSpace ℂ (Fin 0)) :
    ⟪WithLp.toLp 2 (WithLp.ofLp ψ ∘ (Equiv.refl (Fin 0)).symm),
        Matrix.toEuclideanLin (Matrix.reindex (Equiv.refl _) (Equiv.refl _) M)
          (WithLp.toLp 2 (WithLp.ofLp ψ ∘ (Equiv.refl (Fin 0)).symm))⟫_ℂ =
      ⟪ψ, Matrix.toEuclideanLin M ψ⟫_ℂ :=
  Matrix.inner_toEuclideanLin_reindex (Equiv.refl _) M ψ
