/-
Copyright (c) 2026 Sirui Lu and QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sirui Lu
-/
import QICLean.Channel.Peripheral.SpectralProjection
import QICLean.Channel.TransferMatrix

/-!
# Schur-form asymptotic convergence

This file develops Wolf's Schur-decomposition route to the explicit
asymptotic convergence estimate in Equation (8.111).  The peripheral spectral
projection `T_φ` and the phase-weighted peripheral map `T_ϕ = T T_φ` remain
distinct throughout.

The first result transports the exact positive-power identity
`T ^ n - T_ϕ ^ n = (T - T_ϕ) ^ n` to transfer matrices.  The restriction
`0 < n` is essential: at `n = 0` the left-hand side vanishes and the
right-hand side is the identity.  Thus the later natural-exponent condition
`d^2 - 1 ≤ n` must not by itself be used to claim the printed all-`n`
statement when `d = 1`.

## References

Michael M. Wolf, *Quantum Channels & Operations: Guided Tour*, Chapter 8,
Theorem "Asymptotic convergence II", Equation (8.111); local source
`Notes/WolfNoteTexSource/ch08_distance_measures.tex`, lines 1295--1316.
-/

noncomputable section

open Matrix

variable {D : ℕ}

/-- The transfer-matrix form of the positive-power identity underlying Wolf
Equation (8.111):
`T̂ ^ n - T̂_ϕ ^ n = (T - T_ϕ)̂ ^ n` for `0 < n`.

This uses the phase-weighted peripheral map `T_ϕ`, not the projection `T_φ`.
No positivity or complete-positivity hypothesis is needed for the algebraic
identity. -/
theorem transferMatrix_pow_sub_peripheralWeightedProjection_pow
    (T : Module.End ℂ (Matrix (Fin D) (Fin D) ℂ)) {n : ℕ} (hn : 0 < n) :
    transferMatrix T ^ n - transferMatrix T.peripheralWeightedProjection ^ n =
      transferMatrix (T - T.peripheralWeightedProjection) ^ n := by
  rw [← transferMatrix_pow, ← transferMatrix_pow, ← transferMatrix_pow]
  calc
    transferMatrix (T ^ n) - transferMatrix (T.peripheralWeightedProjection ^ n) =
        transferMatrix (T ^ n - T.peripheralWeightedProjection ^ n) :=
      ((transferMatrixLM (D := D)).map_sub _ _).symm
    _ = transferMatrix ((T - T.peripheralWeightedProjection) ^ n) :=
      congrArg transferMatrix (T.pow_sub_peripheralWeightedProjection_pow hn)
