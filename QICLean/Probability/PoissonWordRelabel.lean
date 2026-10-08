/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Probability.PoissonWord

/-!
# Relabeling the actual Poissonized word law

An equivalence of alphabets acts positionwise, preserving word lengths and
atomic weights. Its induced word equivalence therefore preserves the actual
Poissonized measure. This permits a tagged partition to represent a subset of
an original finite alphabet without adding a distributional hypothesis.
-/

open MeasureTheory
open scoped NNReal

namespace PoissonWord

variable {ι κ : Type*}

/-- Apply an alphabet equivalence to every letter, keeping the length. -/
def relabel (e : ι ≃ κ) : Word ι ≃ Word κ :=
  Equiv.sigmaCongrRight fun (m : ℕ) => Equiv.piCongrRight fun (_ : Fin m) => e

@[simp] theorem relabel_apply (e : ι ≃ κ) (m : ℕ) (w : Fin m → ι) :
    relabel e ⟨m, w⟩ = ⟨m, fun j => e (w j)⟩ := rfl

@[simp] theorem length_relabel (e : ι ≃ κ) (w : Word ι) :
    (relabel e w).1 = w.1 := rfl

@[simp] theorem relabel_nil (e : ι ≃ κ) : relabel e nil = nil := by
  change (⟨0, fun j : Fin 0 => e (Fin.elim0 j)⟩ : Word κ) = ⟨0, Fin.elim0⟩
  exact congrArg (fun f : Fin 0 → κ => (⟨0, f⟩ : Word κ)) (Subsingleton.elim _ _)

/-- Relabeling preserves the actual measure, including empty alphabets and zero time. -/
theorem map_relabel [Fintype ι] [Fintype κ] (e : ι ≃ κ) (t : ℝ≥0) :
    (measure ι t).map (relabel e) = measure κ t := by
  apply Measure.ext_of_singleton
  intro w
  rw [Measure.map_apply Measurable.of_discrete (measurableSet_singleton w)]
  have hpre : (relabel e) ⁻¹' {w} = {(relabel e).symm w} := by
    ext u
    exact (relabel e).eq_symm_apply.symm
  rw [hpre, measure_singleton, measure_singleton]
  change ENNReal.ofReal (weight ι t w.1) = ENNReal.ofReal (weight κ t w.1)
  rw [weight, weight, Fintype.card_congr e]

/-- The alphabet transport is measure preserving for the concrete word measures. -/
theorem measurePreserving_relabel [Fintype ι] [Fintype κ] (e : ι ≃ κ) (t : ℝ≥0) :
    MeasurePreserving (relabel e) (measure ι t) (measure κ t) :=
  ⟨Measurable.of_discrete, map_relabel e t⟩

end PoissonWord
