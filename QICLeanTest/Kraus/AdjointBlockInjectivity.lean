/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Kraus.Injectivity

/-! Adjoint block injectivity: both directions, zero length, and empty dimensions. -/

open scoped Matrix

example {d D L : ℕ} (K : Fin d → Matrix (Fin D) (Fin D) ℂ)
    (hK : Kraus.IsNBlkInjective (fun i ↦ (K i)ᴴ) L) : Kraus.IsNBlkInjective K L :=
  Kraus.isNBlkInjective_of_isNBlkInjective_conjTranspose hK

example {d D L : ℕ} (K : Fin d → Matrix (Fin D) (Fin D) ℂ)
    (hK : Kraus.IsNBlkInjective K L) : Kraus.IsNBlkInjective (fun i ↦ (K i)ᴴ) L :=
  (Kraus.isNBlkInjective_conjTranspose_iff K L).mpr hK

example {d D : ℕ} (K : Fin d → Matrix (Fin D) (Fin D) ℂ) :
    Kraus.IsNBlkInjective (fun i ↦ (K i)ᴴ) 0 ↔ Kraus.IsNBlkInjective K 0 :=
  Kraus.isNBlkInjective_conjTranspose_iff K 0

example {d L : ℕ} (K : Fin d → Matrix (Fin 0) (Fin 0) ℂ) :
    Kraus.IsNBlkInjective (fun i ↦ (K i)ᴴ) L := by
  apply (Kraus.isNBlkInjective_conjTranspose_iff K L).mpr
  exact Subsingleton.elim _ _

example {D L : ℕ} (K : Fin 0 → Matrix (Fin D) (Fin D) ℂ) :
    Kraus.IsNBlkInjective (fun i ↦ (K i)ᴴ) L ↔ Kraus.IsNBlkInjective K L :=
  Kraus.isNBlkInjective_conjTranspose_iff K L

example (K : Fin 0 → Matrix (Fin 1) (Fin 1) ℂ) : ¬ Kraus.IsNBlkInjective K 1 := by
  let : IsEmpty (Fin 1 → Fin 0) := ⟨fun σ ↦ Fin.elim0 (σ 0)⟩
  unfold Kraus.IsNBlkInjective Kraus.wordSpan
  rw [Set.range_eq_empty, Submodule.span_empty]
  exact bot_ne_top
example (K : Fin 0 → Matrix (Fin 1) (Fin 1) ℂ) : Kraus.IsNBlkInjective K 0 := by
  rw [Kraus.IsNBlkInjective, Kraus.wordSpan_zero]
  rw [Submodule.eq_top_iff']
  intro M
  have h : M = M 0 0 • (1 : Matrix (Fin 1) (Fin 1) ℂ) := by
    ext i j
    fin_cases i
    fin_cases j
    simp
  rw [h]
  exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))

set_option linter.hashCommand false

/-- info:
'Kraus.isNBlkInjective_of_isNBlkInjective_conjTranspose' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Kraus.isNBlkInjective_of_isNBlkInjective_conjTranspose

/-- info:
'Kraus.isNBlkInjective_conjTranspose_iff' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Kraus.isNBlkInjective_conjTranspose_iff
