/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Channel.KrausMap
import QICLean.Kraus.MapIterate
import QICLean.Kraus.Transfer

/-!
# Trace identities for finite-Kraus-family transfer maps

For a family $K$, the transfer map is the finite Kraus action
$X\mapsto\sum_i K_iXK_i^\dagger$. This file states trace-preservation, iterate,
and trace-pairing identities in transfer-map notation.

## Main declarations

* `Kraus.trace_transferMap`: trace preservation in transfer-map notation.
* `Kraus.transferMap_pow_apply'`: iterates of a transfer map are sums over Kraus words.
* `Kraus.trace_mul_transferMap_adjoint`: the generic Kraus trace-adjoint identity in
  transfer-map notation.
-/

open scoped Matrix ComplexOrder BigOperators
open Matrix Finset

variable {D : ℕ}

namespace Kraus

variable {d : ℕ}

local notation "Mat" => Matrix (Fin D) (Fin D) ℂ

/-- The standard transfer map preserves trace for a trace-preserving Kraus family. -/
lemma trace_transferMap (A : MPSTensor d D) (Z : Matrix (Fin D) (Fin D) ℂ)
    (hA : ∑ i : Fin d, (A i)ᴴ * A i = 1) :
    Matrix.trace (transferMap (d := d) (D := D) A Z) = Matrix.trace Z :=
  isTracePreservingMap_mapLM_of_isTP A hA Z

/-- Iterating the transfer map gives the sum over word evaluations. -/
theorem transferMap_pow_apply' (A : MPSTensor d D) (N : ℕ) :
    ∀ X : Matrix (Fin D) (Fin D) ℂ,
      ((transferMap (d := d) (D := D) A) ^ N) X =
        ∑ σ : Fin N → Fin d,
          evalWord A (List.ofFn σ) * X * (evalWord A (List.ofFn σ))ᴴ :=
  mapLM_pow_apply A N

/-- The adjoint trace-pairing identity in transfer-map notation.

This is the transfer-map form of `Kraus.trace_mul_mapLM_adjoint`. -/
lemma trace_mul_transferMap_adjoint
    {n : ℕ}
    (K : MPSTensor n D)
    {E : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ}
    (hE_eq : E = transferMap (d := n) (D := D) K)
    (ρ X : Matrix (Fin D) (Fin D) ℂ) :
    Matrix.trace (ρ * E X) =
      Matrix.trace (transferMap (d := n) (D := D) (fun i => (K i)ᴴ) ρ * X) :=
  trace_mul_mapLM_adjoint (K := K) hE_eq ρ X

end Kraus
