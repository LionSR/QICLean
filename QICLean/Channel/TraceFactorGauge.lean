/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Channel.KrausGauge
import QICLean.Channel.KrausMap
import QICLean.Algebra.MatrixTracePairing

/-!
# Trace-preserving gauges for trace-factorized Kraus maps

If a finite Kraus map has the form `E(X) = trace (L * X) • R`, with
`trace (L * R) = 1`, then its adjoint fixes `L`. When `L` is positive
definite, conjugating the Kraus operators by its positive square root gives
a trace-preserving family.

This is the channel-theoretic normalization used in arXiv:1703.09188,
Proposition IV.5, lines 747–752 and 798–802.
-/

open scoped Matrix ComplexOrder MatrixOrder

namespace Kraus

/-- A normalized trace factor is fixed by the adjoint Kraus map.
This is the left fixed-point equation used in CPSV17, Proposition IV.5,
lines 747–752 and 798–802. -/
theorem mapLM_conjTranspose_eq_self_of_eq_trace_smul {d D : ℕ}
    (A : Fin d → Matrix (Fin D) (Fin D) ℂ)
    (L R : Matrix (Fin D) (Fin D) ℂ)
    (htr : Matrix.trace (L * R) = 1)
    (hmap : ∀ X, Kraus.mapLM A X = Matrix.trace (L * X) • R) :
    Kraus.mapLM (fun i ↦ (A i)ᴴ) L = L := by
  apply Matrix.ext_iff_trace_mul_right.mpr
  exact fun X ↦ (Kraus.trace_mul_mapLM_adjoint A rfl L X).symm.trans (by
    simp only [hmap, Matrix.mul_smul, Matrix.trace_smul, htr, smul_eq_mul, mul_one])

/-- The square-root gauge of the left trace factor is trace preserving.
Source: CPSV17, Proposition IV.5, lines 798–802. -/
theorem tpGauge_isTP_of_mapLM_eq_trace_smul {d D : ℕ}
    (A : Fin d → Matrix (Fin D) (Fin D) ℂ)
    (L R : Matrix (Fin D) (Fin D) ℂ) (hL : L.PosDef)
    (htr : Matrix.trace (L * R) = 1)
    (hmap : ∀ X, Kraus.mapLM A X = Matrix.trace (L * X) • R) :
    Kraus.IsTP (Kraus.tpGauge A L) := by
  exact Kraus.tpGauge_isTP_of_map_conjTranspose_fixedPoint A L hL
    (mapLM_conjTranspose_eq_self_of_eq_trace_smul A L R htr hmap)

end Kraus
