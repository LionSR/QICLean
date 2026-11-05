/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.ViableSubspaceBootstrap
import Mathlib.Tactic.Choose

/-!
# Least dimensions of viable subspaces

In finite dimensions the whole regional space is viable, so the natural
dimensions of viable subspaces have an attained least element. Increasing
the target cannot decrease this minimum. These are the minima used in
ALVV, arXiv:1602.08828v2, Proposition `prop:albootstrap-ld`, lines
1112–1128. They require neither a spectral gap nor a compactness argument.
-/

open scoped TensorProduct InnerProductSpace

namespace Submodule

variable {M F : Type*}
  [NormedAddCommGroup M] [InnerProductSpace ℂ M] [FiniteDimensional ℂ M]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F]

/-- A viable subspace remains viable when the target is decreased.
Auxiliary to ALVV, arXiv:1602.08828v2, Proposition
`prop:albootstrap-ld`, lines 1112–1128. -/
theorem IsViable.of_target_le {delta : ℝ} {S : Submodule ℂ M}
    {Tlo Thi : Submodule ℂ (M ⊗[ℂ] F)} (h : IsViable delta S Thi)
    (hT : Tlo ≤ Thi) : IsViable delta S Tlo := by
  exact isCloseTo_iff.mpr fun x hx ↦ isCloseTo_iff.mp h x (hT hx)

/-- The least natural dimension of a viable subspace is attained by an
actual subspace. This is the minimum used in ALVV,
arXiv:1602.08828v2, Proposition `prop:albootstrap-ld`, lines 1112–1128. -/
theorem exists_isViable_minimal_finrank (delta : ℝ) (hdelta : 0 ≤ delta)
    (T : Submodule ℂ (M ⊗[ℂ] F)) :
    ∃ (p : ℕ) (W : Submodule ℂ M), Module.finrank ℂ W = p ∧
      IsViable delta W T ∧
      (∀ S : Submodule ℂ M, IsViable delta S T → p ≤ Module.finrank ℂ S) ∧
      p ≤ Module.finrank ℂ M := by
  classical
  let P (n : ℕ) : Prop := ∃ W : Submodule ℂ M,
    Module.finrank ℂ W = n ∧ IsViable delta W T
  have hex : ∃ n : ℕ, P n :=
    ⟨Module.finrank ℂ (⊤ : Submodule ℂ M), ⊤, rfl, isViable_top delta hdelta T⟩
  obtain ⟨W, hdim, hW⟩ := Nat.find_spec hex
  refine ⟨Nat.find hex, W, hdim, hW, ?_, ?_⟩
  · intro S hS
    exact Nat.find_min' hex ⟨S, rfl, hS⟩
  · simpa only [finrank_top] using
      Nat.find_min' hex ⟨⊤, rfl, isViable_top delta hdelta T⟩

/-- An increasing sequence of targets has actual minimizing viable spaces
whose natural dimensions do not decrease. The minimizing spaces need not
be nested. This supplies the dimension comparison in ALVV,
arXiv:1602.08828v2, Proposition `prop:albootstrap-ld`, lines 1112–1128. -/
theorem exists_isViable_minimal_sequence (delta : ℝ) (hdelta : 0 ≤ delta)
    (T : ℕ → Submodule ℂ (M ⊗[ℂ] F)) (hT : ∀ j, T j ≤ T (j + 1)) :
    ∃ (p : ℕ → ℕ) (W : ℕ → Submodule ℂ M), ∀ j,
      Module.finrank ℂ (W j) = p j ∧ IsViable delta (W j) (T j) ∧
      (∀ S : Submodule ℂ M, IsViable delta S (T j) → p j ≤ Module.finrank ℂ S) ∧
      p j ≤ Module.finrank ℂ M ∧ p j ≤ p (j + 1) := by
  classical
  choose p W hdim hW hmin hcap using
    fun j ↦ exists_isViable_minimal_finrank delta hdelta (T j)
  refine ⟨p, W, fun j ↦ ⟨hdim j, hW j, hmin j, hcap j, ?_⟩⟩
  simpa only [hdim (j + 1)] using
    hmin j (W (j + 1)) ((hW (j + 1)).of_target_le (hT j))

end Submodule
