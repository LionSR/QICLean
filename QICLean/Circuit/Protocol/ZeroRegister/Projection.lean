/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Circuit.Gate.ExactSubspaceAmplification
import QICLean.Circuit.Protocol.ZeroRegister.Selected

/-!
# The projection onto configurations with zero flags

The range projection `J J†` of the basis inclusion `J` along an injection of basis sets is the
diagonal indicator of its image. Fixing a selected family of flags to `0` and keeping
arbitrary values on the other sites is such an inclusion, so its range projection is the
diagonal projection onto the configurations whose selected flags are all `0`, an orthogonal
projection, and the selected-flags reflection is the reflection `1 - 2 J J†` about its range.

The declarations restate `TNLean/Circuit/InitializedRegisterProjection.lean` (Apache-2.0). The
changes: the flags are any family of sites instead of an injective one. The circuit for the
reflection about the range is not restated here.

## Main definitions

* `QuantumCircuit.zeroFlagEmbedding` — the inclusion of the configurations of the unselected
  sites, with the selected flags at `0`.

## Main results

* `Matrix.initializedBasisMatrix_mul_conjTranspose` — the range projection of a basis
  inclusion is the indicator of its image.
* `QuantumCircuit.zeroFlagEmbedding_apply_selected`,
  `QuantumCircuit.zeroFlagEmbedding_apply_of_notMem`,
  `QuantumCircuit.mem_range_zeroFlagEmbedding_iff` — the image is the set of configurations
  with zero flags.
* `QuantumCircuit.zeroFlagEmbedding_range_projection`,
  `QuantumCircuit.isStarProjection_zeroFlagEmbedding_range` — the range projection.
* `QuantumCircuit.selectedZeroRegisterLogical_eq_subspaceReflection` — the selected-flags
  reflection is the reflection about the range.
-/

open Matrix

namespace Matrix

/-- The range projection of a basis inclusion is the diagonal indicator of its image. -/
theorem initializedBasisMatrix_mul_conjTranspose {ι κ : Type*} [Fintype κ] [DecidableEq ι]
    (e : κ ↪ ι) [DecidablePred (· ∈ Set.range e)] :
    initializedBasisMatrix e * (initializedBasisMatrix e)ᴴ =
      diagonal fun x ↦ if x ∈ Set.range e then (1 : ℂ) else 0 := by
  ext x y
  by_cases hx : x ∈ Set.range e
  · obtain ⟨u, rfl⟩ := hx
    rw [initializedBasisMatrix_mul_apply_self, conjTranspose_apply, diagonal_apply,
      ite_eq_left (Set.mem_range_self u)]
    simp [initializedBasisMatrix, one_apply, eq_comm]
  · rw [initializedBasisMatrix_mul_apply_of_notMem _ _ hx, diagonal_apply]
    simp [hx]

end Matrix

namespace QuantumCircuit

variable {d n a : ℕ} [NeZero d]

/-- The inclusion of the configurations of the unselected sites, with every selected flag
at `0`. -/
noncomputable def zeroFlagEmbedding (s : Fin a → Fin n) :
    ({i : Fin n // i ∉ Set.range s} → Fin d) ↪ (Fin n → Fin d) where
  toFun u i := by
    classical
    exact if hi : i ∈ Set.range s then 0 else u ⟨i, hi⟩
  inj' u v huv := by
    funext i
    have h := congrFun huv i.1
    simpa only [dite_eq_right i.2] using h

/-- The selected flags of an included configuration are `0`. -/
theorem zeroFlagEmbedding_apply_selected (s : Fin a → Fin n)
    (u : {i : Fin n // i ∉ Set.range s} → Fin d) (j : Fin a) :
    zeroFlagEmbedding s u (s j) = 0 := by
  simp [zeroFlagEmbedding]

/-- The unselected sites of an included configuration carry the configuration. -/
theorem zeroFlagEmbedding_apply_of_notMem (s : Fin a → Fin n)
    (u : {i : Fin n // i ∉ Set.range s} → Fin d) {i : Fin n} (hi : i ∉ Set.range s) :
    zeroFlagEmbedding s u i = u ⟨i, hi⟩ :=
  dite_eq_right hi

/-- The included configurations are exactly those whose selected flags are all `0`; the other
sites are arbitrary. -/
theorem mem_range_zeroFlagEmbedding_iff (s : Fin a → Fin n) (x : Fin n → Fin d) :
    x ∈ Set.range (zeroFlagEmbedding (d := d) s) ↔ ∀ j, x (s j) = 0 := by
  refine ⟨?_, fun hx ↦ ⟨fun i ↦ x i.1, funext fun i ↦ ?_⟩⟩
  · rintro ⟨u, rfl⟩ j
    exact zeroFlagEmbedding_apply_selected s u j
  · by_cases hi : i ∈ Set.range s
    · obtain ⟨j, rfl⟩ := hi
      rw [zeroFlagEmbedding_apply_selected, hx]
    · exact zeroFlagEmbedding_apply_of_notMem s _ hi

/-- The range projection of the zero-flag inclusion is the diagonal projection onto the
configurations whose selected flags are all `0`. -/
theorem zeroFlagEmbedding_range_projection (s : Fin a → Fin n) :
    initializedBasisMatrix (zeroFlagEmbedding (d := d) s) *
        (initializedBasisMatrix (zeroFlagEmbedding (d := d) s))ᴴ =
      diagonal fun x : Fin n → Fin d ↦ if ∀ j, x (s j) = 0 then (1 : ℂ) else 0 := by
  classical
  rw [initializedBasisMatrix_mul_conjTranspose]
  simp only [mem_range_zeroFlagEmbedding_iff]

/-- The range projection of the zero-flag inclusion is an orthogonal projection. -/
theorem isStarProjection_zeroFlagEmbedding_range (s : Fin a → Fin n) :
    IsStarProjection (initializedBasisMatrix (zeroFlagEmbedding (d := d) s) *
      (initializedBasisMatrix (zeroFlagEmbedding (d := d) s))ᴴ) :=
  isStarProjection_mul_conjTranspose_of_isometry _ (initializedBasisMatrix_isIsometry _)

/-- The selected-flags reflection is the reflection about the range of the zero-flag
inclusion. -/
theorem selectedZeroRegisterLogical_eq_subspaceReflection (s : Fin a → Fin n) :
    selectedZeroRegisterLogical (d := d) s =
      subspaceReflection (initializedBasisMatrix (zeroFlagEmbedding (d := d) s) *
        (initializedBasisMatrix (zeroFlagEmbedding (d := d) s))ᴴ) := by
  rw [zeroFlagEmbedding_range_projection, subspaceReflection,
    selectedZeroRegisterLogical_eq_one_sub]

end QuantumCircuit
