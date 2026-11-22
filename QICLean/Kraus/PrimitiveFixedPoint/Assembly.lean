/-
Copyright (c) 2025 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Kraus.PrimitiveFixedPoint.PosDef
import QICLean.Kraus.PrimitiveFixedPoint.Uniqueness
import QICLean.Kraus.CPPrimitive
-- Needed for `IsChannel.exists_posSemidef_fixedPoint`.
-- The fixed-point existence theorem is used explicitly below.
import QICLean.Channel.FixedPoint.Cesaro

/-!
# Quantum Perron–Frobenius Theory for MPS Transfer Operators

This file provides the existence step and the final quantum Perron–Frobenius
theorem from its components:

1. **Positive definiteness** (`QPF.PosDef`): PSD fixed points → PD under injectivity
2. **Uniqueness** (`QPF.Uniqueness`): PSD fixed points are unique up to scalar
3. **Existence** (this file): via Cesàro mean / trace-preserving channel theory
4. **The quantum Perron–Frobenius theorem** (this file): the combined result

Together these formalize the core of **Wolf Theorem 6.3** (Spectral radius of
irreducible maps), specialized to the trace-preserving (spectral radius = 1) setting:
- Existence: there is a nonzero PSD fixed point (Wolf Theorem 6.11 / Proposition 6.3 route)
- PosDef: under irreducibility the fixed point is strictly positive (Wolf Theorem 6.3(2))
- Uniqueness: the eigenvalue 1 is non-degenerate (Wolf Theorem 6.3(2))

## Main results

* `exists_posSemidef_fixedPoint`: existence of a PSD fixed point
* `quantum_perron_frobenius`: the full QPF theorem
* `injective_transfer_unique_fixed_point'`: QPF without the `0 < D` hypothesis

## References

* [M. Wolf, *Quantum Channels & Operations: Guided Tour*, Section 6.2 Theorem 6.3,
  Section 6.4 Theorem 6.11][Wolf2012QChannels]
* [Evans, Høegh-Krohn, *Spectral properties of positive maps*, 1978][Evans1978Spectral]
-/

open scoped Matrix ComplexOrder BigOperators

namespace Kraus

variable {d D : ℕ}

/-! ## Part 3: Existence of PSD fixed point -/

section Existence

/-- Existence of a PSD fixed point for the transfer map of a normalized
MPS tensor.

**Mathematical content**: If `∑ Aᵢ† Aᵢ = 1`, then `transferMap A` is a
trace-preserving channel. Applying `IsChannel.exists_posSemidef_fixedPoint`
produces a nonzero PSD matrix `ρ` with `transferMap A ρ = ρ`.

**Proof method**: The channel fixed-point theorem used here is proved via the
Cesàro averages of iterates of a density matrix, so in the normalized case this
existence statement does not rely on Brouwer or Krein-Rutman.

**Note**: Injectivity is not used in this existence step; it enters later in
the positive-definiteness and uniqueness statements. For a general non-normalized
injective tensor, one instead expects the eigenvector statement
`∃ ρ c, ρ.PosSemidef ∧ ρ ≠ 0 ∧ 0 < c ∧ E(ρ) = c • ρ`, and then rescales to the
fixed-point setting. -/
theorem exists_posSemidef_fixedPoint
    (A : Fin d → Matrix (Fin D) (Fin D) ℂ)
    (hNorm : ∑ i : Fin d, (A i)ᴴ * A i = 1)
    (hD : 0 < D) :
    ∃ ρ : Matrix (Fin D) (Fin D) ℂ, ρ.PosSemidef ∧ ρ ≠ 0 ∧
      transferMap A ρ = ρ :=
  (isChannel_mapLM A hNorm).exists_posSemidef_fixedPoint
    (E := transferMap A) hD

end Existence

/-! ## Part 4: The quantum Perron–Frobenius theorem -/

section PerronFrobenius

/-- **The quantum Perron–Frobenius theorem for MPS transfer operators**
(Wolf Theorem 6.3, specialized to CP maps with spectral radius 1).

The transfer map of an injective MPS tensor has a unique PSD fixed point
(up to scalar), and it is positive definite. -/
theorem quantum_perron_frobenius [DecidableEq (Fin D)]
    (A : Fin d → Matrix (Fin D) (Fin D) ℂ) (hA : IsInjective A)
    (hNorm : ∑ i : Fin d, (A i)ᴴ * A i = 1)
    (hD : 0 < D) :
    ∃ ρ : Matrix (Fin D) (Fin D) ℂ,
      HasUniqueFixedPoint (transferMap A) ρ := by
  have hIrr := injective_implies_irreducibleCP A hA
  obtain ⟨ρ, hρ_psd, hρ_ne, hρ_fix⟩ := exists_posSemidef_fixedPoint A (by convert hNorm) hD
  exact ⟨ρ, {
    fixed := hρ_fix
    pos_def := posSemidef_fixedPoint_isPosDef_of_irreducible A hIrr ρ hρ_psd hρ_ne hρ_fix
    unique := fun σ hσ_psd hσ_fix =>
      posSemidef_fixedPoint_unique_of_irreducible A hIrr ρ σ
        hρ_psd hρ_ne hσ_psd hρ_fix hσ_fix
  }⟩

/-! ### Reduction: handle the `D = 0` edge case

`quantum_perron_frobenius` requires `0 < D`. The theorem below lifts this restriction. -/

/-- **Injectivity implies unique fixed point** (without the `0 < D` hypothesis).
Extends `quantum_perron_frobenius` to the case `D = 0`, which holds vacuously. -/
theorem injective_transfer_unique_fixed_point' [DecidableEq (Fin D)]
    (A : Fin d → Matrix (Fin D) (Fin D) ℂ) (hA : IsInjective A)
    (hNorm : ∑ i : Fin d, (A i)ᴴ * A i = 1) :
    ∃ ρ : Matrix (Fin D) (Fin D) ℂ,
      HasUniqueFixedPoint (transferMap A) ρ := by
  by_cases hD : 0 < D
  · exact quantum_perron_frobenius A hA hNorm hD
  · push Not at hD
    interval_cases D
    exact ⟨0, {
      fixed := by ext i; exact Fin.elim0 i
      pos_def := Matrix.PosDef.of_dotProduct_mulVec_pos Matrix.isHermitian_zero
        (fun x hx => absurd (Subsingleton.elim x 0) hx)
      unique := fun σ _ _ => ⟨0, by ext i; exact Fin.elim0 i⟩
    }⟩

end PerronFrobenius

end Kraus

section Primitive

/-!
# Quantum Perron–Frobenius for irreducible transfer maps

This file weakens the hypothesis of the quantum Perron–Frobenius theorem from
`IsInjective A` (Kraus operators span the full algebra) to
`IsIrreducibleMap (transferMap A)` (the transfer map has no nontrivial
invariant projections).

## Main results

* `quantum_perron_frobenius_irreducible` — QPF under irreducibility of the
  transfer map (weaker than injectivity)

## Mathematical content

The standard QPF theorem in Wolf (Theorem 6.3) is stated for **irreducible**
positive maps, not specifically for injective MPS tensors. The existing
`quantum_perron_frobenius` in `Assembly.lean` uses `IsInjective A` because
that implies `IsIrreducibleMap (transferMap A)` via
`injective_implies_irreducibleCP`. This file provides the direct
irreducibility-based version.

**Hierarchy of hypotheses** (each implies the next):
  `IsInjective A` → `IsPrimitive (transferMap A)` → `IsIrreducibleMap (transferMap A)`

Note: Injectivity implies primitivity (by Wolf Corollary 6.5 / the Wielandt bound),
and primitivity (1 is the only peripheral eigenvalue) implies irreducibility.
The converse fails: an irreducible channel can have period > 1.

## Strengthening relative to the literature

The existing formalization only provides QPF at the `IsInjective` level.
This file exposes the natural generality of Wolf's theorem at the
`IsIrreducibleMap` level, which applies to tensors that are not injective
but whose transfer maps are still irreducible (e.g., after blocking).

## References

* [Wolf2012] M. Wolf, *Quantum Channels & Operations: Guided Tour*,
  Section 6.2, Theorem 6.3 (quantum Perron–Frobenius for irreducible positive maps).
* [EH78] Evans, Høegh-Krohn, *Spectral properties of positive maps*, 1978.
-/

open scoped Matrix ComplexOrder BigOperators

namespace Kraus

variable {d D : ℕ}

/-- **Quantum Perron–Frobenius under irreducibility** (Wolf Theorem 6.3).

If the transfer map `E_A` is irreducible and trace-preserving (`∑ Aᵢ† Aᵢ = I`),
then it has a unique positive definite fixed point.

This is strictly more general than `quantum_perron_frobenius`, which requires
`IsInjective A`. The generalization matters for blocked tensors: after blocking
`n` sites, the resulting tensor may not be injective (the Kraus operators
may not span), but the transfer map can still be irreducible.

**Proof**: The normalization makes the transfer map a channel, so channel fixed-point
existence and uniqueness under irreducibility applies directly. -/
theorem quantum_perron_frobenius_irreducible [DecidableEq (Fin D)]
    (A : Fin d → Matrix (Fin D) (Fin D) ℂ)
    (hIrr : IsIrreducibleMap (transferMap A))
    (hNorm : ∑ i : Fin d, (A i)ᴴ * A i = 1)
    (hD : 0 < D) :
    ∃ ρ : Matrix (Fin D) (Fin D) ℂ,
      HasUniqueFixedPoint (transferMap A) ρ := by
  exact IsChannel.exists_hasUniqueFixedPoint_of_irreducible
    (isChannel_mapLM A (by unfold IsTP; convert hNorm)) hIrr hD

end Kraus

end Primitive
