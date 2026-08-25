/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Channel.Primitive
import QICLean.Channel.Schwarz.Basic
import Mathlib.Analysis.Normed.Operator.CompleteCodomain

/-!
# Primitive fixed points of finite Kraus families

This file defines a complementary fixed-point gap directly for the finite Kraus map

$$E_K(X) = \sum_i K_i X K_i^\dagger.$$

The predicate bundles a trace-preserving Kraus normalization, a nonzero positive-semidefinite
fixed point $\rho$, and the strict spectral-radius bound
$r(E_K - P_\rho) < 1$, where $P_\rho(X) = \operatorname{tr}(X)\rho / \operatorname{tr}(\rho)$.
It is intentionally stated using `Kraus.mapLM`, without an intermediate channel or
matrix-product-state wrapper.

## Main declarations

* `Kraus.HasComplementaryFixedPointGap`: explicit fixed-point and complementary-gap data.
* `Kraus.HasPrimitiveFixedPoint`: existential form of the same data.
* `Kraus.HasComplementaryFixedPointGap.trace_ne_zero`: the fixed point has nonzero trace.
* `Kraus.HasComplementaryFixedPointGap.complement_eigenvalue_norm_lt_one`: every eigenvalue
  of the complementary map has norm strictly below one.
* `Kraus.HasComplementaryFixedPointGap.fixedPoint_unique`: every fixed point is proportional
  to the distinguished fixed point.
* `Kraus.HasComplementaryFixedPointGap.complement_pow_tendsto_zero`: powers of the
  complementary map converge to zero.

The peripheral-spectrum and irreducibility consequences are kept in separate downstream
modules so that this basic layer has the smallest useful dependency surface.
-/

open scoped Matrix Matrix.Norms.Operator ComplexOrder BigOperators
open Matrix

namespace Kraus

/-- A finite Kraus family has a complementary fixed-point gap at $\rho$ if it is
trace-preserving, $\rho$ is a nonzero positive-semidefinite fixed point, and the complement
of the rank-one fixed-point projection has spectral radius strictly smaller than one.

The field names, order, and displayed normalization equality are part of this structure's
public interface. In particular, the normalization is displayed as
$\sum_i K_i^\dagger K_i = I$ rather than through an equivalent predicate. -/
structure HasComplementaryFixedPointGap {d D : ℕ} [NeZero D]
    (K : Fin d → Matrix (Fin D) (Fin D) ℂ)
    (ρ : Matrix (Fin D) (Fin D) ℂ) : Prop where
  /-- Trace-preserving Kraus normalization: $\sum_i K_i^\dagger K_i = I$. -/
  norm : ∑ i : Fin d, (K i)ᴴ * K i = 1
  /-- The distinguished fixed point is nonzero. -/
  fixedPoint_ne_zero : ρ ≠ 0
  /-- The distinguished fixed point is positive semidefinite. -/
  fixedPoint_psd : ρ.PosSemidef
  /-- The finite Kraus map fixes the distinguished point. -/
  fixedPoint_is_fixed : mapLM K ρ = ρ
  /-- The complementary map $E_K-P_\rho$ has spectral radius strictly smaller than one. -/
  complementary_transfer_map_gap :
      spectralRadius ℂ
        ((Module.End.toContinuousLinearMap (Matrix (Fin D) (Fin D) ℂ))
          (mapLM K - fixedPointProj (D := D) ρ
            (by
              intro h
              exact fixedPoint_ne_zero
                ((Matrix.PosSemidef.trace_eq_zero_iff fixedPoint_psd).1 h)))) < 1

/-- A finite Kraus family has a primitive fixed point if some matrix witnesses a
complementary fixed-point gap. -/
def HasPrimitiveFixedPoint {d D : ℕ} [NeZero D]
    (K : Fin d → Matrix (Fin D) (Fin D) ℂ) : Prop :=
  ∃ ρ, HasComplementaryFixedPointGap K ρ

variable {d D : ℕ} [NeZero D]
variable {K : Fin d → Matrix (Fin D) (Fin D) ℂ}
variable {ρ : Matrix (Fin D) (Fin D) ℂ}

/-- The trace of the nonzero positive-semidefinite fixed point is nonzero. -/
theorem HasComplementaryFixedPointGap.trace_ne_zero
    (hP : HasComplementaryFixedPointGap K ρ) :
    trace ρ ≠ 0 := by
  intro h
  exact hP.fixedPoint_ne_zero
    ((Matrix.PosSemidef.trace_eq_zero_iff hP.fixedPoint_psd).1 h)

/-- Every eigenvalue $\nu$ of the complementary map $E_K-P_\rho$ satisfies
$\lVert\nu\rVert<1$.

This is the eigenvalue form of the bundled spectral-radius gap. The proof transports the
eigenvalue into the spectrum of the continuous endomorphism and bounds its norm by the
spectral radius. -/
theorem HasComplementaryFixedPointGap.complement_eigenvalue_norm_lt_one
    (hP : HasComplementaryFixedPointGap K ρ) (ν : ℂ)
    (hν : Module.End.HasEigenvalue
      (mapLM K - fixedPointProj (D := D) ρ hP.trace_ne_zero) ν) :
    ‖ν‖ < 1 := by
  let Ê := mapLM K - fixedPointProj (D := D) ρ hP.trace_ne_zero
  have hν_mem : ν ∈ spectrum ℂ
      ((Module.End.toContinuousLinearMap (Matrix (Fin D) (Fin D) ℂ)) Ê) := by
    rw [AlgEquiv.spectrum_eq]
    exact hν.mem_spectrum
  have hν_le : (‖ν‖₊ : ENNReal) ≤ spectralRadius ℂ
      ((Module.End.toContinuousLinearMap (Matrix (Fin D) (Fin D) ℂ)) Ê) :=
    @le_iSup₂ ENNReal ℂ (· ∈ spectrum ℂ _) _
      (fun z _ ↦ (‖z‖₊ : ENNReal)) ν hν_mem
  have hν_lt : (‖ν‖₊ : ENNReal) < 1 :=
    lt_of_le_of_lt hν_le hP.complementary_transfer_map_gap
  have hν_lt_nn : ‖ν‖₊ < (1 : NNReal) := ENNReal.coe_lt_one_iff.mp hν_lt
  exact_mod_cast hν_lt_nn

/-- Every fixed point of $E_K$ is proportional to $\rho$.

More precisely, if $E_K(\sigma)=\sigma$, then
$\sigma=(\operatorname{tr}(\sigma)/\operatorname{tr}(\rho))\rho$. Subtracting this
multiple produces a traceless fixed point of $E_K$, hence an eigenvector of $E_K-P_\rho$
with eigenvalue one. The complementary eigenvalue bound forces that vector to vanish. -/
theorem HasComplementaryFixedPointGap.fixedPoint_unique
    (hP : HasComplementaryFixedPointGap K ρ)
    (σ : Matrix (Fin D) (Fin D) ℂ) (hσ : mapLM K σ = σ) :
    σ = (trace σ / trace ρ) • ρ := by
  set c := trace σ / trace ρ
  set σ' := σ - c • ρ
  have htr_σ' : trace σ' = 0 := by
    simp [σ', trace_sub, trace_smul, c, div_mul_cancel₀ _ hP.trace_ne_zero]
  have hσ'_fix : mapLM K σ' = σ' := by
    simp [σ', map_sub, hσ, hP.fixedPoint_is_fixed]
  let Ê := mapLM K - fixedPointProj (D := D) ρ hP.trace_ne_zero
  have hÊ_σ' : Ê σ' = σ' := by
    simp [Ê, LinearMap.sub_apply, hσ'_fix, fixedPointProj, htr_σ']
  suffices h0 : σ' = 0 by
    exact sub_eq_zero.mp h0
  by_contra hσ'_ne
  have h_mem : σ' ∈ Module.End.eigenspace Ê 1 := by
    rw [Module.End.mem_eigenspace_iff]
    simp [hÊ_σ']
  have hEig : Module.End.HasEigenvalue Ê 1 := by
    rw [Module.End.hasEigenvalue_iff]
    exact fun h_bot ↦ hσ'_ne ((Submodule.eq_bot_iff _).mp h_bot σ' h_mem)
  have h_one_lt : ‖(1 : ℂ)‖ < 1 :=
    hP.complement_eigenvalue_norm_lt_one 1 hEig
  have : (1 : ℝ) < 1 := by
    simpa only [norm_one] using h_one_lt
  exact (lt_irrefl 1) this

/-- Powers of the complementary map $E_K-P_\rho$ converge to zero in operator norm. -/
theorem HasComplementaryFixedPointGap.complement_pow_tendsto_zero
    (hP : HasComplementaryFixedPointGap K ρ) :
    let V := Matrix (Fin D) (Fin D) ℂ
    let Φ := Module.End.toContinuousLinearMap V
    let Ê := Φ (mapLM K - fixedPointProj (D := D) ρ hP.trace_ne_zero)
    Filter.Tendsto (fun n ↦ Ê ^ n) Filter.atTop (nhds 0) :=
  _root_.pow_tendsto_zero_of_spectralRadius_lt_one _
    hP.complementary_transfer_map_gap

end Kraus
