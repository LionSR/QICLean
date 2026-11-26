/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Channel.FixedPoint.MeanErgodic.FixedPointProjection
import QICLean.Channel.Schwarz.Basic
import Mathlib.Analysis.Normed.Operator.CompleteCodomain
import QICLean.Channel.KrausMap.KrausMap
import QICLean.Channel.Peripheral.Spectrum.Spectrum
import QICLean.Kraus.Transfer

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
* `Kraus.HasComplementaryFixedPointGap.isPrimitive`: peripheral primitivity from a complementary
  fixed-point gap.

Moved from TNLean, `TNLean/MPS/Transfer/Primitivity/PrimitiveFixedPoint.lean`,
`TNLean/MPS/ParentHamiltonian/LocalExpectation/LocalObservableInsertion.lean` at commit `021ba0bd19`
(Apache-2.0).
-/

open scoped Matrix Matrix.Norms.Operator ComplexOrder BigOperators
open Matrix

namespace Kraus

section Basic

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
      ((Module.End.toContinuousLinearMap (Matrix (Fin D) (Fin D) ℂ)) Ê) := by
    rw [spectralRadius_eq_of_unital]
    exact @le_iSup₂ ENNReal ℂ (· ∈ spectrum ℂ _) _
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

end Basic

section Peripheral

/-!
## Peripheral primitivity from a complementary fixed-point gap

This module connects the finite-Kraus complementary-gap predicate to the channel-level
peripheral-spectrum notion of primitivity. If $E_K-P_\rho$ has spectral radius below one,
then every one-modulus eigenvalue of $E_K$ is equal to one.

### Main declaration

* `Kraus.HasComplementaryFixedPointGap.isPrimitive`: complementary fixed-point gap implies
  peripheral-spectrum primitivity of `Kraus.mapLM K`.
-/

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

end Peripheral

end Kraus

section

open scoped Matrix Matrix.Norms.Operator ComplexOrder BigOperators Kraus

/-- The rank-one fixed-point projection \(X\mapsto(\operatorname{tr}X/\operatorname{tr}
\rho)\rho\) is unchanged when the fixed point is rescaled by a nonzero scalar. -/
theorem fixedPointProj_smul {D : ℕ} (ρ : Matrix (Fin D) (Fin D) ℂ) {c : ℂ}
    (hcρ : Matrix.trace (c • ρ) ≠ 0) (hρ : Matrix.trace ρ ≠ 0) :
    fixedPointProj (c • ρ) hcρ = fixedPointProj ρ hρ := by
  have hc : c ≠ 0 := by
    rintro rfl
    simp at hcρ
  ext X i j
  simp only [fixedPointProj, LinearMap.coe_mk, AddHom.coe_mk, Matrix.trace_smul,
    smul_eq_mul, Matrix.smul_apply]
  field_simp

/-- Dividing a matrix of nonzero trace by its own trace produces a matrix of unit
trace: the normalized representative of the ray through it. -/
theorem Matrix.trace_inv_trace_smul {D : ℕ} {ρ : Matrix (Fin D) (Fin D) ℂ}
    (hρ : Matrix.trace ρ ≠ 0) : Matrix.trace ((Matrix.trace ρ)⁻¹ • ρ) = 1 := by
  rw [Matrix.trace_smul, smul_eq_mul, inv_mul_cancel₀ hρ]

/-- Dividing a positive-definite matrix by its own trace, which is a positive real,
leaves it positive definite. -/
theorem Matrix.PosDef.inv_trace_smul {D : ℕ} [NeZero D]
    {ρ : Matrix (Fin D) (Fin D) ℂ}
    (hρ : ρ.PosDef) : ((Matrix.trace ρ)⁻¹ • ρ).PosDef :=
  hρ.smul (inv_pos.mpr hρ.trace_pos)

/-- Rescaling a positive-definite primitive fixed point to unit trace preserves the
complementary fixed-point gap. Only the ray through the fixed point enters the gap
certificate, so the normalized witness carries the same primitivity data. -/
theorem Kraus.HasComplementaryFixedPointGap.smul_inv_trace {d D : ℕ} [NeZero D]
    {A : Fin d → Matrix (Fin D) (Fin D) ℂ} {ρ : Matrix (Fin D) (Fin D) ℂ}
    (hP : Kraus.HasComplementaryFixedPointGap A ρ) (hρ : ρ.PosDef) :
    Kraus.HasComplementaryFixedPointGap A ((Matrix.trace ρ)⁻¹ • ρ) := by
  have htr_ne : Matrix.trace ρ ≠ 0 := ne_of_gt hρ.trace_pos
  have hpd : ((Matrix.trace ρ)⁻¹ • ρ).PosDef := hρ.inv_trace_smul
  have hne : Matrix.trace ((Matrix.trace ρ)⁻¹ • ρ) ≠ 0 := ne_of_gt hpd.trace_pos
  refine ⟨hP.norm, fun h ↦ hne (by rw [h, Matrix.trace_zero]), hpd.posSemidef, ?_, ?_⟩
  · rw [LinearMap.map_smul, hP.fixedPoint_is_fixed]
  · simpa only [fixedPointProj_smul ρ hne htr_ne] using
      hP.complementary_transfer_map_gap

end

section

open Filter

open scoped BigOperators Matrix Topology Matrix.Norms.Operator

section

variable {d D : ℕ}

/-- The powers of a normalized primitive transfer map converge in operator norm
 to its rank-one fixed-point projection. Source: Nachtergaele,
arXiv:cond-mat/9410110, equations (3.1)--(3.2b) and Section 6. -/
theorem Kraus.HasComplementaryFixedPointGap.transferMap_pow_tendsto_fixedPointProj
    [NeZero D] {A : Fin d → Matrix (Fin D) (Fin D) ℂ} {ρ : Matrix (Fin D) (Fin D) ℂ}
    (hP : Kraus.HasComplementaryFixedPointGap A ρ) :
    let Φ := Module.End.toContinuousLinearMap (𝕜 := ℂ) (Matrix (Fin D) (Fin D) ℂ)
    Tendsto (fun n : ℕ => Φ ((Kraus.transferMap A) ^ n)) atTop
      (nhds (Φ (fixedPointProj ρ hP.trace_ne_zero))) := by
  let Φ := Module.End.toContinuousLinearMap (𝕜 := ℂ) (Matrix (Fin D) (Fin D) ℂ)
  have hlim : Tendsto (fun n : ℕ => Φ (fixedPointProj ρ hP.trace_ne_zero) +
      (Φ (Kraus.transferMap A - fixedPointProj ρ hP.trace_ne_zero)) ^ n) atTop
      (nhds (Φ (fixedPointProj ρ hP.trace_ne_zero) + 0)) :=
    tendsto_const_nhds.add hP.complement_pow_tendsto_zero
  simp only [add_zero] at hlim
  apply hlim.congr'
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
  rw [pow_eq_fixedPointProj_add_compl_pow (Kraus.transferMap A) hP.trace_ne_zero
    (Kraus.isTracePreservingMap_mapLM_of_isTP A hP.norm) hP.fixedPoint_is_fixed hn,
    map_add, map_pow]

end

end
