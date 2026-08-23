/-
Copyright (c) 2026 Sirui Lu and QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sirui Lu
-/
import QICLean.Analysis.TraceNormContractionCoefficient
import QICLean.Channel.Peripheral.SpectralProjection

/-!
# Trace-norm convergence towards asymptotic states

This file begins the formalization of Wolf's comparison between trace-norm
convergence of states and Hilbert--Schmidt operator-norm convergence of a
positive trace-preserving map.  It proves the exact algebraic identities used
before the norm estimates: the peripheral projection commutes with every
iterate, the phase-weighted peripheral map kills the non-peripheral remainder,
and hence the numerator in Equation (8.114) has Wolf's two equivalent forms.

## References

Michael M. Wolf, *Quantum Channels & Operations: Guided Tour*, Chapter 8,
Proposition "Convergence towards asymptotic states", Equations (8.112)--(8.117);
local source `Notes/WolfNoteTexSource/ch08_distance_measures.tex`, lines 1319--1364.
-/

open scoped Matrix

noncomputable section

namespace Matrix

variable {D : ℕ}

/-- Wolf's `Δ_T(ρ) = ‖ρ - T_φ(ρ)‖₁`: trace-norm distance to the peripheral
spectral projection.

Source: Wolf, Equation (8.112), definition immediately before the displayed
bound; local source lines 1323--1328. -/
def traceNormAsymptoticDistance
    (T : Module.End ℂ (Matrix (Fin D) (Fin D) ℂ))
    (ρ : Matrix (Fin D) (Fin D) ℂ) : ℝ :=
  traceNorm (ρ - T.peripheralProjection ρ)

/-- The peripheral projection commutes with every iterate of `T`.

This is the iterated form of the first identity on Wolf line 1337. -/
theorem peripheralProjection_comp_pow
    (T : Module.End ℂ (Matrix (Fin D) (Fin D) ℂ)) (n : ℕ) :
    T.peripheralProjection ∘ₗ (T ^ n) = (T ^ n) ∘ₗ T.peripheralProjection := by
  simpa only [Module.End.mul_eq_comp] using
    (T.commute_peripheralProjection.pow_right n).eq

/-- The phase-weighted peripheral map annihilates Wolf's non-peripheral
remainder `ρ - T_φ(ρ)`.

This is the identity `T_φ' T_φ = T_φ'` on Wolf line 1337, applied to the
complement of the peripheral projection. -/
@[simp]
theorem peripheralWeightedProjection_apply_sub_peripheralProjection
    (T : Module.End ℂ (Matrix (Fin D) (Fin D) ℂ))
    (ρ : Matrix (Fin D) (Fin D) ℂ) :
    T.peripheralWeightedProjection (ρ - T.peripheralProjection ρ) = 0 := by
  rw [Module.End.peripheralWeightedProjection, LinearMap.comp_apply, map_sub,
    T.peripheralProjection_apply_peripheralProjection, sub_self, map_zero]

/-- Every positive power of the phase-weighted peripheral map annihilates
Wolf's non-peripheral remainder. -/
@[simp]
theorem peripheralWeightedProjection_pow_apply_sub_peripheralProjection
    (T : Module.End ℂ (Matrix (Fin D) (Fin D) ℂ))
    (ρ : Matrix (Fin D) (Fin D) ℂ) {n : ℕ} (hn : 0 < n) :
    (T.peripheralWeightedProjection ^ n) (ρ - T.peripheralProjection ρ) = 0 := by
  cases n with
  | zero => simp at hn
  | succ n =>
      rw [pow_succ, Module.End.mul_apply,
        peripheralWeightedProjection_apply_sub_peripheralProjection, map_zero]

/-- Wolf's numerator identity preceding Equation (8.114): for every positive
iterate, `Δ_T(Tⁿρ)` is the trace norm of `Tⁿ` applied to the non-peripheral
remainder.

Source: Wolf, local source lines 1336--1344. -/
theorem traceNormAsymptoticDistance_pow_eq
    (T : Module.End ℂ (Matrix (Fin D) (Fin D) ℂ))
    (ρ : Matrix (Fin D) (Fin D) ℂ) (n : ℕ) :
    traceNormAsymptoticDistance T ((T ^ n) ρ) =
      traceNorm ((T ^ n) (ρ - T.peripheralProjection ρ)) := by
  have hcomm : T.peripheralProjection ((T ^ n) ρ) =
      (T ^ n) (T.peripheralProjection ρ) := by
    simpa only [LinearMap.comp_apply] using congrArg
      (fun f : Module.End ℂ (Matrix (Fin D) (Fin D) ℂ) ↦ f ρ)
      (peripheralProjection_comp_pow T n)
  rw [traceNormAsymptoticDistance, hcomm, map_sub]

/-- Wolf's second numerator identity preceding Equation (8.114): for every
positive iterate, subtracting the corresponding power of the asymptotic
dynamics does not change its action on the non-peripheral remainder.

Source: Wolf, local source lines 1336--1344. -/
theorem traceNormAsymptoticDistance_pow_eq_sub_peripheralWeightedProjection_pow
    (T : Module.End ℂ (Matrix (Fin D) (Fin D) ℂ))
    (ρ : Matrix (Fin D) (Fin D) ℂ) {n : ℕ} (hn : 0 < n) :
    traceNormAsymptoticDistance T ((T ^ n) ρ) =
      traceNorm (((T ^ n) - T.peripheralWeightedProjection ^ n)
        (ρ - T.peripheralProjection ρ)) := by
  rw [traceNormAsymptoticDistance_pow_eq, LinearMap.sub_apply,
    peripheralWeightedProjection_pow_apply_sub_peripheralProjection T ρ hn, sub_zero]

end Matrix
