/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Kraus.PrimitiveFixedPoint.Basic
import QICLean.Channel.KrausMap
import QICLean.Channel.Peripheral.Spectrum

/-!
# Peripheral primitivity from a complementary fixed-point gap

This module connects the finite-Kraus complementary-gap predicate to the channel-level
peripheral-spectrum notion of primitivity. If $E_K-P_\rho$ has spectral radius below one,
then every one-modulus eigenvalue of $E_K$ is equal to one.

## Main declaration

* `Kraus.HasComplementaryFixedPointGap.isPrimitive`: complementary fixed-point gap implies
  peripheral-spectrum primitivity of `Kraus.mapLM K`.
-/

open scoped Matrix Matrix.Norms.Operator ComplexOrder BigOperators
open Matrix

namespace Kraus

variable {d D : ℕ} [NeZero D]
variable {K : Fin d → Matrix (Fin D) (Fin D) ℂ}
variable {ρ : Matrix (Fin D) (Fin D) ℂ}

/-- A complementary fixed-point gap makes the finite Kraus map primitive in the
peripheral-spectrum sense: one is its unique eigenvalue of norm one. -/
theorem HasComplementaryFixedPointGap.isPrimitive
    (hP : HasComplementaryFixedPointGap K ρ) :
    _root_.IsPrimitive (mapLM K) :=
  _root_.isPrimitive_of_compl_eigenvalues_lt_one
    (mapLM K) ρ hP.fixedPoint_is_fixed hP.fixedPoint_ne_zero hP.trace_ne_zero
    (isChannel_mapLM K hP.norm).tp hP.complement_eigenvalue_norm_lt_one

end Kraus
