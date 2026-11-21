/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Probability.Sampling.ViableSubspaceBootstrap
import Mathlib.Tactic.Choose
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

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

section ViableSubspaceNestedEnlargement

/-!
# Actual image enlargement between two buffered targets

One fixed family sends a constant-viable source for an original upper target
to an actual image viable for an original lower target. Distinct intermediate
upper and lower targets permit a spectral buffer without a gap inside either
target. The operator family and its improving property are explicit hypotheses
of this conditional composition; a physical construction must supply them.

This supports ALVV, arXiv:1602.08828v2, the nested error reduction at
lines 1037–1041 and the low-density approximation in Theorem `thm:al-ld`,
lines 1096–1105. It is not an existence theorem for physical filters.
-/

open scoped BigOperators TensorProduct

namespace Submodule

variable {H M F : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]
  [NormedAddCommGroup M] [InnerProductSpace ℂ M] [FiniteDimensional ℂ M]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F]

/-- A conditional two-target composition retaining the same actual image span.
The original inner target is only required to lie in the original lower band;
no invariance or constant-eigenvalue hypothesis is imposed on it. The family
and improving property are assumptions here, to be discharged by the physical
polynomial construction. ALVV, arXiv:1602.08828v2, lines 1037–1041 and 1096–1105. -/
theorem viable_enlargement_of_close_nested_targets
    (Tm : H ≃ₗᵢ[ℂ] (M ⊗[ℂ] F))
    (Gupper Glower Ginner Tlower Tupper : Submodule ℂ H)
    (W0 : Submodule ℂ M) {N : ℕ} (A : Fin N → M →L[ℂ] M)
    (delta Delta : ℝ) (hdelta : 0 < delta) (hdelta1 : delta ≤ 1)
    (hinner : Ginner ≤ Glower)
    (hW0 : IsViable (F := F) (3 / 200) W0
      (Gupper.map Tm.toLinearEquiv.toLinearMap))
    (hupper : IsCloseTo (delta / 100) Gupper Tupper)
    (hlower : IsCloseTo (delta / 100) Tlower Glower)
    (hDelta : Delta ≤ delta / 8)
    (himprove : ∀ (S : Submodule ℂ M) (epsilon : ℝ),
      IsViable (F := F) epsilon S (Tupper.map Tm.toLinearEquiv.toLinearMap) →
      epsilon < 1 →
      let V := ⨆ j : Fin N, S.map (A j).toLinearMap
      Module.finrank ℂ V ≤ N * Module.finrank ℂ S ∧
        IsViable (F := F) (Delta / (1 - epsilon) ^ 2) V
          (Tlower.map Tm.toLinearEquiv.toLinearMap)) :
    let V := ⨆ j : Fin N, W0.map (A j).toLinearMap
    Module.finrank ℂ V ≤ N * Module.finrank ℂ W0 ∧
      IsViable (F := F) (delta / 2) V (Ginner.map Tm.toLinearEquiv.toLinearMap) := by
  intro V
  have hstart : IsViable (F := F) (1 / 20) W0
      (Tupper.map Tm.toLinearEquiv.toLinearMap) :=
    (IsCloseTo.trans hW0 ((isCloseTo_map_iff Tm).mpr hupper)
      (by norm_num)).of_le (by linarith only [hdelta1])
  obtain ⟨hdim, hraw⟩ := himprove W0 (1 / 20) hstart (by norm_num)
  have hsmall : IsViable (F := F) (delta / 5) V
      (Tlower.map Tm.toLinearEquiv.toLinearMap) :=
    hraw.of_le (by norm_num; linarith only [hDelta, hdelta])
  have hreturn : IsViable (F := F) (delta / 2) V
      (Glower.map Tm.toLinearEquiv.toLinearMap) :=
    (IsCloseTo.trans hsmall ((isCloseTo_map_iff Tm).mpr hlower)
      (by positivity)).of_le (by linarith only [hdelta])
  exact ⟨hdim, hreturn.of_target_le (Submodule.map_mono hinner)⟩

end Submodule

end ViableSubspaceNestedEnlargement
