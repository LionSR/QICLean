/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.ManyBody.Replica.Configuration.RegionalPhysicalMarginals
import QICLean.ManyBody.Replica.LowDefect.RegionalLowDefectProjection
import QICLean.ManyBody.Replica.Metric.RegionalReplicaMetric
import QICLean.ManyBody.Replica.Configuration.RegionalFiveFactorCoordinates
import QICLean.Analysis.Order.InverseCompressionLowerPin
import QICLean.ManyBody.Replica.LowDefect.LowDefectSymmetricCoordinates
import QICLean.ManyBody.Replica.LowDefect.ComponentInverseSharp
import QICLean.ManyBody.Replica.Configuration.GoodConfigurationExpectation
import QICLean.ManyBody.Replica.Configuration.GoodPhysicalExponential
import QICLean.Analysis.Real.ExcitationSubsetCounts
import QICLean.Representation.Replica.LowDefectProjection
import QICLean.Analysis.Order.ProjectionQuadraticBound
import QICLean.ManyBody.Replica.Metric.DisjointMetricPositivity

/-!
# Uniform regional lower bounds in one symmetric coordinate space

The original physical vector and auxiliary labels determine one global
low-defect projection. Each regional estimate is transported to this
projection by the actual grouping equivalence. The polynomial constant is
then replaced by a maximum over the finite set of physical cuts, before
the copy number, vector, labels, cutoffs or symmetric coordinates are chosen.

The rough estimate requires no marginal moment hypothesis. The sharp estimate
uses the surprisal moments of the three reductions of the original vector.
The projection transport and inverse-compression bounds are derived from
the original definitions and the regional comparisons.

Source: *A two-dimensional area law from a global spectral gap*, September 24,
2026, `07-comparators.tex`, lines 421--456 and 585--615,
`comparator:lower-pin`, revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.

It also contains the following results.

* `Matrix.replicaLowDefectRoughLowerPin_decidableEqConfig`,
  `Matrix.exists_replicaLowDefectProjection_rough_lower_pin`: the actual rough lower bound in fixed
  symmetric coordinates.
* `Matrix.replicaLowDefectSharpLowerPin_decidableEqConfig`,
  `Matrix.exists_replicaLowDefectProjection_sharp_lower_pin`: the sharp lower bound in fixed
  symmetric coordinates.

## Main results

* `Matrix.replicaComponentInverseRough_decidableEqConfig`,
  `Matrix.exists_replicaExcitationComponent_inverse_rough_le`: the rough inverse estimate on each
  actual excitation component.
* `Matrix.replicaComponentInverseRoughUniform_decidableEqConfig`,
  `Matrix.exists_replicaExcitationComponent_inverse_rough_uniform_le`: A rough component rate
  uniform over the excitation subset.
* `Matrix.replicaInverseRoughCompression_decidableEqConfig`,
  `Matrix.exists_replicaLowDefectProjection_inverse_rough_compression_le`: the rough inverse bound
  on the actual low-defect subspace.
-/

section ComponentInverseRough

/-!
## The rough inverse estimate on each actual excitation component

The inverse metric is evaluated on the component defined by the original
excitation projection. The good-copy expectation equals the trace against
its actual reduced density. Removing the physical deficit there and using
the two merge moments gives the rough estimate, with all polynomial and
binomial factors explicit. No component normalization is necessary.

Source: *A two-dimensional area law from a global spectral gap*, September 24,
2026, `07-comparators.tex`, lines 441–576, `comparator:component-inverse`,
revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

noncomputable section
open TensorPower PermutationRepresentation
open scoped BigOperators Matrix Kronecker ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace Matrix

variable (ι : Fin 5 → Type*) [∀ f, Fintype (ι f)] [∀ f, DecidableEq (ι f)]
variable [∀ f, Nonempty (ι f)]

local instance replicaComponentInverseRough_decidableEqConfig (k : ℕ) :
    DecidableEq (Config k ι) := Fintype.decidablePiFintype

/-- The actual inverse squared band metric obeys the rough component
estimate under the original symmetry and two auxiliary label conditions.
The polynomial constant is chosen before the copy number and vector.
Source: `07-comparators.tex`, lines 441–576, `comparator:component-inverse`.
-/
theorem exists_replicaExcitationComponent_inverse_rough_le
    {t : ℝ} (ht : 0 < t) (htsmall : 4 * t ≤ 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (k : ℕ) (B : Finset (Fin k))
      (Ω : ι 0 × (ι 1 × ι 2) → ℂ), ‖WithLp.toLp 2 Ω‖ = 1 →
      ∀ (ellC ellR : IrrepLabel (Equiv.Perm (Fin k)))
      (u : (Fin k → ι 0 × (ι 1 × ι 2)) ×
        ((Fin k → ι 3) × (Fin k → ι 4)) → ℂ),
      (∀ σ : Equiv.Perm (Fin k),
        (permOp (copyPerm (ι 0 × (ι 1 × ι 2)) k) σ ⊗ₖ
          (permOp (copyPerm (ι 3) k) σ ⊗ₖ
            permOp (copyPerm (ι 4) k) σ)) *ᵥ u = u) →
      (((1 : Matrix (Fin k → ι 0 × (ι 1 × ι 2))
          (Fin k → ι 0 × (ι 1 × ι 2)) ℂ) ⊗ₖ
        (labelProj (copyPerm (ι 3) k) ellC ⊗ₖ
          (1 : Matrix (Fin k → ι 4) (Fin k → ι 4) ℂ))) *ᵥ u = u) →
      (((1 : Matrix (Fin k → ι 0 × (ι 1 × ι 2))
          (Fin k → ι 0 × (ι 1 × ι 2)) ℂ) ⊗ₖ
        ((1 : Matrix (Fin k → ι 3) (Fin k → ι 3) ℂ) ⊗ₖ
          labelProj (copyPerm (ι 4) k) ellR)) *ᵥ u = u) →
      let m := Bᶜ.card
      let w := (replicaExcitationProjection Ω k B ⊗ₖ
        (1 : Matrix ((Fin k → ι 3) × (Fin k → ι 4))
          ((Fin k → ι 3) × (Fin k → ι 4)) ℂ)) *ᵥ u
      let f := w ∘ fiveFactorCopiesEquiv ι k
      let W := replicaMetric ι t k
      let b := Real.log ellC.dim + Real.log ellR.dim -
        (B.card : ℝ) * (Real.log (Fintype.card (ι 3)) + Real.log (Fintype.card (ι 4))) -
          2 * Real.log (k.choose B.card)
      let q := ((((m + 1) ^ ((Fintype.card (ι 0) * Fintype.card (ι 3)) ^ 2) : ℕ) : ℝ) +
        (((m + 1) ^ ((Fintype.card (ι 2) * Fintype.card (ι 4)) ^ 2) : ℕ) : ℝ)) / 2
      (star f ⬝ᵥ ((((W {0, 3})⁻¹ * (W {2, 4})⁻¹ * W {1}) ^ 2)⁻¹ *ᵥ f)).re ≤
        (((k : ℝ) + 2) ^ C * (k.choose B.card : ℝ) ^ (2 * t) *
          Real.exp (-(2 * t) * b) * q) * ‖WithLp.toLp 2 w‖ ^ 2 := by
  obtain ⟨C, hC, hbound⟩ :=
    exists_replicaExcitationComponent_inverse_le_good_expectation ι ht
  refine ⟨C, hC, ?_⟩
  intro k B Ω hΩ ellC ellR u hu huC huR m w f W b q
  have h := hbound k B Ω ellC ellR u hu huC huR
  dsimp only at h
  rw [replicaExcitationComponent_exp_good_without_auxiliary_eq_trace
    ι Ω k B u (2 * t)] at h
  have hm := replicaGoodConfigurationMarginal_exp_merge_sub_physical_le
    ι Ω hΩ k B u hu (show 0 ≤ 2 * t by positivity)
      (show 2 * (2 * t) ≤ 1 by linarith only [htsmall])
  have hp : 0 ≤ ((k : ℝ) + 2) ^ C * (k.choose B.card : ℝ) ^ (2 * t) *
      Real.exp (-(2 * t) * b) := by positivity
  simpa only [mul_assoc] using h.trans (mul_le_mul_of_nonneg_left hm hp)

end Matrix

end

end ComponentInverseRough

section ComponentInverseRoughUniform

/-!
## A rough component rate uniform over the excitation subset

The arithmetic mean of the two merge-moment polynomial losses is bounded
by their larger degree. The summed original auxiliary label bound and
the upper bound on the number of bad copies then give one uniform rough
rate. All three binomial corrections are retained.

The original vector, auxiliary labels and actual excitation component
are unchanged. No one-copy moment hypothesis is required. The fixed
polynomial constant precedes the copy number, state, labels, vector and
cutoff parameters.

Source: *A two-dimensional area law from a global spectral gap*, September 24,
2026, `07-comparators.tex`, lines 550--590, `comparator:component-inverse`
and `comparator:inverse-compression`, revision
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

noncomputable section
open TensorPower PermutationRepresentation
open scoped BigOperators Matrix Kronecker ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace Matrix

variable (ι : Fin 5 → Type*) [∀ f, Fintype (ι f)] [∀ f, DecidableEq (ι f)]
variable [∀ f, Nonempty (ι f)]

local instance replicaComponentInverseRoughUniform_decidableEqConfig (k : ℕ) :
    DecidableEq (Config k ι) := Fintype.decidablePiFintype

/-- The rough inverse estimate is uniform over all actual excitation
subsets of size at most the prescribed fraction. The original symmetry
and two label equations are retained. The only scalar label assumption
is the summed lower bound for their original logarithmic dimensions;
there is no marginal moment hypothesis.
Source: `07-comparators.tex`, lines 550--590. -/
theorem exists_replicaExcitationComponent_inverse_rough_uniform_le
    {t : ℝ} (ht : 0 < t) (htsmall : 4 * t ≤ 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (k : ℕ) (B : Finset (Fin k))
      (Ω : ι 0 × (ι 1 × ι 2) → ℂ), ‖WithLp.toLp 2 Ω‖ = 1 →
      ∀ (ellC ellR : IrrepLabel (Equiv.Perm (Fin k)))
      (u : (Fin k → ι 0 × (ι 1 × ι 2)) ×
        ((Fin k → ι 3) × (Fin k → ι 4)) → ℂ),
      (∀ σ : Equiv.Perm (Fin k),
        (permOp (copyPerm (ι 0 × (ι 1 × ι 2)) k) σ ⊗ₖ
          (permOp (copyPerm (ι 3) k) σ ⊗ₖ
            permOp (copyPerm (ι 4) k) σ)) *ᵥ u = u) →
      (((1 : Matrix (Fin k → ι 0 × (ι 1 × ι 2))
          (Fin k → ι 0 × (ι 1 × ι 2)) ℂ) ⊗ₖ
        (labelProj (copyPerm (ι 3) k) ellC ⊗ₖ
          (1 : Matrix (Fin k → ι 4) (Fin k → ι 4) ℂ))) *ᵥ u = u) →
      (((1 : Matrix (Fin k → ι 0 × (ι 1 × ι 2))
          (Fin k → ι 0 × (ι 1 × ι 2)) ℂ) ⊗ₖ
        ((1 : Matrix (Fin k → ι 3) (Fin k → ι 3) ℂ) ⊗ₖ
          labelProj (copyPerm (ι 4) k) ellR)) *ᵥ u = u) →
      ∀ (τ S ε : ℝ), 0 ≤ τ → τ ≤ 1 / 2 → (B.card : ℝ) ≤ τ * k →
      2 * (k : ℝ) * S - ε ≤ Real.log ellC.dim + Real.log ellR.dim →
      let w := (replicaExcitationProjection Ω k B ⊗ₖ
        (1 : Matrix ((Fin k → ι 3) × (Fin k → ι 4))
          ((Fin k → ι 3) × (Fin k → ι 4)) ℂ)) *ᵥ u
      let f := w ∘ fiveFactorCopiesEquiv ι k
      let W := replicaMetric ι t k
      let d := Real.log (Fintype.card (ι 3)) + Real.log (Fintype.card (ι 4))
      let D := max ((Fintype.card (ι 0) * Fintype.card (ι 3)) ^ 2)
        ((Fintype.card (ι 2) * Fintype.card (ι 4)) ^ 2)
      (star f ⬝ᵥ ((((W {0, 3})⁻¹ * (W {2, 4})⁻¹ * W {1}) ^ 2)⁻¹ *ᵥ f)).re ≤
        (((k : ℝ) + 2) ^ (C + (D : ℝ)) * Real.exp
          (-(k : ℝ) * (2 * t) * (2 * S - τ * d - 3 * Real.binEntropy τ) +
            (2 * t) * ε)) * ‖WithLp.toLp 2 w‖ ^ 2 := by
  obtain ⟨C, hC, hrough⟩ :=
    exists_replicaExcitationComponent_inverse_rough_le ι ht htsmall
  refine ⟨C, hC, ?_⟩
  intro k B Ω hΩ ellC ellR u hu huC huR τ S ε hτ hτhalf hB hlabel w f W d D
  let m := Bᶜ.card
  let nQ := (Fintype.card (ι 0) * Fintype.card (ι 3)) ^ 2
  let nV := (Fintype.card (ι 2) * Fintype.card (ι 4)) ^ 2
  let q := ((((m + 1) ^ nQ : ℕ) : ℝ) + (((m + 1) ^ nV : ℕ) : ℝ)) / 2
  let b := Real.log ellC.dim + Real.log ellR.dim - (B.card : ℝ) * d -
    2 * Real.log (k.choose B.card)
  let p := ((k : ℝ) + 2) ^ C * (k.choose B.card : ℝ) ^ (2 * t) *
    Real.exp (-(2 * t) * b)
  have hp : 0 ≤ p := by dsimp only [p]; positivity
  have hpoly : q ≤ Real.exp ((D : ℝ) * Real.log ((m : ℝ) + 1)) := by
    have hQ : ((m : ℝ) + 1) ^ nQ ≤ ((m : ℝ) + 1) ^ D :=
      pow_le_pow_right₀ (by linarith only [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)])
        (le_max_left nQ nV)
    have hV : ((m : ℝ) + 1) ^ nV ≤ ((m : ℝ) + 1) ^ D :=
      pow_le_pow_right₀ (by linarith only [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)])
        (le_max_right nQ nV)
    have hexp : ((m : ℝ) + 1) ^ D =
        Real.exp ((D : ℝ) * Real.log ((m : ℝ) + 1)) := by
      rw [← Real.rpow_natCast,
        Real.rpow_def_of_pos (by positivity : 0 < (m : ℝ) + 1)]
      congr 1
      ring
    rw [← hexp]
    dsimp only [q]
    push_cast
    linarith only [hQ, hV]
  have hdim (j : Fin 5) : 0 ≤ Real.log (Fintype.card (ι j)) :=
    Real.log_natCast_nonneg _
  have hd : 0 ≤ d := add_nonneg (hdim 3) (hdim 4)
  have hBk : B.card ≤ k := by
    simpa only [Fintype.card_fin] using B.card_le_univ
  have hm : m = k - B.card := by
    dsimp only [m]
    simp only [Finset.card_compl, Fintype.card_fin]
  have hfactor := Real.replica_component_prefactor_le_uniform
    (g := 0) (K := 0) (Λ := (D : ℝ)) hBk hτ hτhalf hB
    (show 0 ≤ 2 * t by positivity) hd le_rfl le_rfl (Nat.cast_nonneg D)
    C S ε (Real.log ellC.dim + Real.log ellR.dim) hlabel
  have hunif : p * Real.exp ((D : ℝ) * Real.log ((m : ℝ) + 1)) ≤
      ((k : ℝ) + 2) ^ (C + (D : ℝ)) * Real.exp
        (-(k : ℝ) * (2 * t) * (2 * S - τ * d - 3 * Real.binEntropy τ) +
          (2 * t) * ε) := by
    simpa only [← hm, mul_zero, zero_mul, zero_add, add_zero] using hfactor
  have h := hrough k B Ω hΩ ellC ellR u hu huC huR
  change (star f ⬝ᵥ ((((W {0, 3})⁻¹ * (W {2, 4})⁻¹ * W {1}) ^ 2)⁻¹ *ᵥ f)).re ≤
    (p * q) * ‖WithLp.toLp 2 w‖ ^ 2 at h
  exact h.trans (mul_le_mul_of_nonneg_right
    ((mul_le_mul_of_nonneg_left hpoly hp).trans hunif) (sq_nonneg ‖WithLp.toLp 2 w‖))

end Matrix

end

end ComponentInverseRoughUniform

section InverseRoughCompression

/-!
## The rough inverse bound on the actual low-defect subspace

The uniform estimate for the literal excitation components gives an
operator bound after compression to simultaneous symmetry, the two
original auxiliary labels, and the physical low-defect cutoff. The
number of retained subsets is bounded by binary entropy. The inverse
metric need not commute with any excitation projection.

All scalar losses are explicit. The lower bound on the original label
logarithms is the input later supplied by the common selected label.
No marginal moment assumption is needed for this rough estimate.

Source: *A two-dimensional area law from a global spectral gap*, September 24,
2026, `07-comparators.tex`, lines 550–590, `comparator:component-inverse`
and `comparator:inverse-compression`, revision
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

noncomputable section
open TensorPower PermutationRepresentation
open scoped BigOperators Matrix Kronecker ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace Matrix

variable (ι : Fin 5 → Type*) [∀ f, Fintype (ι f)] [∀ f, DecidableEq (ι f)]
variable [∀ f, Nonempty (ι f)]

local instance replicaInverseRoughCompression_decidableEqConfig (k : ℕ) :
    DecidableEq (Config k ι) := Fintype.decidablePiFintype

/-- The actual low-defect compression of an inverse band metric obeys
the rough exponential estimate, including the subset-counting factor.
The polynomial constant is fixed before the copy number, ground vector,
labels and cutoff. No component bound is supplied as a premise.
Source: `07-comparators.tex`, lines 550–590. -/
theorem exists_replicaLowDefectProjection_inverse_rough_compression_le
    {t : ℝ} (ht : 0 < t) (htsmall : 4 * t ≤ 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (k : ℕ) (Ω : ι 0 × (ι 1 × ι 2) → ℂ),
      ‖WithLp.toLp 2 Ω‖ = 1 →
      ∀ (ellC ellR : IrrepLabel (Equiv.Perm (Fin k))) (τ S ε : ℝ),
      0 ≤ τ → τ ≤ 1 / 2 →
      2 * (k : ℝ) * S - ε ≤ Real.log ellC.dim + Real.log ellR.dim →
      let e := fiveFactorCopiesEquiv ι k
      let W := replicaMetric ι t k
      let H := submatrix ((((W {0, 3})⁻¹ * (W {2, 4})⁻¹ * W {1}) ^ 2)⁻¹)
        e.symm e.symm
      let P := replicaLowDefectProjection (C := ι 3) (R := ι 4) Ω k ellC ellR τ
      let d := Real.log (Fintype.card (ι 3)) + Real.log (Fintype.card (ι 4))
      let D := max ((Fintype.card (ι 0) * Fintype.card (ι 3)) ^ 2)
        ((Fintype.card (ι 2) * Fintype.card (ι 4)) ^ 2)
      let c := ((k : ℝ) + 2) ^ (C + (D : ℝ)) * Real.exp
        (-(k : ℝ) * (2 * t) * (2 * S - τ * d - 3 * Real.binEntropy τ) +
          (2 * t) * ε)
      P * H * P ≤ (((k : ℝ) + 1) * Real.exp (k * Real.binEntropy τ) * c) • P := by
  obtain ⟨C, hC, hcomponent⟩ :=
    exists_replicaExcitationComponent_inverse_rough_uniform_le ι ht htsmall
  refine ⟨C, hC, ?_⟩
  intro k Ω hΩ ellC ellR τ S ε hτ hτhalf hlabel e W H P d D c
  have hH : H.PosSemidef :=
    (posDef_replicaMetric_disjoint_inv_mul_inv_mul_sq ι ht.le k
      (P := {0, 3}) (F := {2, 4}) (Y := {1})
        (by decide) (by decide) (by decide)).inv.posSemidef.submatrix e.symm
  have hc : 0 ≤ c := by dsimp only [c]; positivity
  apply replicaLowDefectProjection_compression_le_of_component_bounds
    Ω hΩ k ellC ellR hτ hτhalf hc hH
  intro u hu huC huR B hB
  have h := hcomponent k B Ω hΩ ellC ellR u hu huC huR
    τ S ε hτ hτhalf hB hlabel
  dsimp only
  rw [star_dotProduct_submatrix_equiv]
  exact h

end Matrix

end

end InverseRoughCompression

section RegionalLowDefectLowerPin

section LowDefectRoughLowerPin

/-!
## The actual rough lower bound in fixed symmetric coordinates

The actual rough inverse-compression estimate gives a lower bound
on the original squared metric. The same bound holds after compression by
any fixed coordinates for the simultaneous symmetric space. The compressed
low-defect projection is proved to be an orthogonal projection from its
literal definition and the five-factor symmetry action.

The original unit vector, auxiliary labels and scalar label bound are
retained. The polynomial constant is chosen before the copy number, state,
labels and cutoff. No marginal moment assumption, inverse-compression
estimate or metric-cutoff commutation is required.

Source: *A two-dimensional area law from a global spectral gap*, September 24,
2026, `07-comparators.tex`, lines 585--615, `comparator:lower-pin`, revision
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

noncomputable section
open TensorPower PermutationRepresentation
open scoped BigOperators Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace Matrix

variable (ι : Fin 5 → Type*) [∀ f, Fintype (ι f)] [∀ f, DecidableEq (ι f)]
variable [∀ f, Nonempty (ι f)]

local instance replicaLowDefectRoughLowerPin_decidableEqConfig (k : ℕ) :
    DecidableEq (Config k ι) := Fintype.decidablePiFintype

/-- The actual rough lower pin and its compression in the same symmetric
coordinates, with the exact subset-counting and polynomial losses. No
marginal moment hypothesis is needed. Source: `07-comparators.tex`,
`comparator:lower-pin`, lines 585--615. -/
theorem exists_replicaLowDefectProjection_rough_lower_pin
    {t : ℝ} (ht : 0 < t) (htsmall : 4 * t ≤ 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (k : ℕ) (Ω : ι 0 × (ι 1 × ι 2) → ℂ),
      ‖WithLp.toLp 2 Ω‖ = 1 →
      ∀ (ellC ellR : IrrepLabel (Equiv.Perm (Fin k))) (τ S ε : ℝ),
      0 ≤ τ → τ ≤ 1 / 2 →
      2 * (k : ℝ) * S - ε ≤ Real.log ellC.dim + Real.log ellR.dim →
      let e := fiveFactorCopiesEquiv ι k
      let W := replicaMetric ι t k
      let A := ((W {0, 3})⁻¹ * (W {2, 4})⁻¹ * W {1}) ^ 2
      let P := replicaLowDefectProjection (C := ι 3) (R := ι 4) Ω k ellC ellR τ
      let d := Real.log (Fintype.card (ι 3)) + Real.log (Fintype.card (ι 4))
      let D := max ((Fintype.card (ι 0) * Fintype.card (ι 3)) ^ 2)
        ((Fintype.card (ι 2) * Fintype.card (ι 4)) ^ 2)
      let c := ((k : ℝ) + 2) ^ (C + (D : ℝ)) * Real.exp
        (-(k : ℝ) * (2 * t) * (2 * S - τ * d - 3 * Real.binEntropy τ) +
          (2 * t) * ε)
      let b := ((k : ℝ) + 1) * Real.exp (k * Real.binEntropy τ) * c
      b⁻¹ • P.submatrix e e ≤ A ∧
        ∀ (n : ℕ) (Z : Matrix (Config k ι) (Fin n) ℂ),
          Z * Zᴴ = symProj (copyPerm ((f : Fin 5) → ι f) k) →
          IsStarProjection (Zᴴ * P.submatrix e e * Z) ∧
            b⁻¹ • (Zᴴ * P.submatrix e e * Z) ≤ Zᴴ * A * Z := by
  obtain ⟨C, hC, hinverse⟩ :=
    exists_replicaLowDefectProjection_inverse_rough_compression_le ι ht htsmall
  refine ⟨C, hC, ?_⟩
  intro k Ω hΩ ellC ellR τ S ε hτ hτhalf hlabel e W A P d D c b
  have hA : A.PosDef := posDef_replicaMetric_disjoint_inv_mul_inv_mul_sq ι ht.le k
    (by decide) (by decide) (by decide)
  have hP : IsStarProjection P := isStarProjection_replicaLowDefectProjection
    Ω hΩ k ellC ellR τ
  have hb : 0 < b := by dsimp only [b, c]; positivity
  have hinv : P * (A⁻¹).submatrix e.symm e.symm * P ≤ b • P :=
    hinverse k Ω hΩ ellC ellR τ S ε hτ hτhalf hlabel
  have hpin (n : ℕ) (Z : Matrix (Config k ι) (Fin n) ℂ) :
      b⁻¹ • (Zᴴ * P.submatrix e e * Z) ≤ Zᴴ * A * Z :=
    hA.lower_pin_of_reindexed_inverse_compression e hP hb hinv Z
  constructor
  · simpa only [Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one] using
      hA.lower_pin_of_reindexed_inverse_compression e hP hb hinv
        (1 : Matrix (Config k ι) (Config k ι) ℂ)
  · intro n Z hZZ
    exact ⟨isStarProjection_compressed_replicaLowDefectProjection
      ι Ω hΩ k ellC ellR τ Z hZZ, hpin n Z⟩

end Matrix

end

end LowDefectRoughLowerPin

section LowDefectSharpLowerPin

/-!
## The sharp lower bound in fixed symmetric coordinates

The actual sharp inverse compression gives a lower bound on the original
squared metric. The same estimate holds in any fixed symmetric coordinates,
where the original low-defect projection remains an orthogonal projection.
The original marginal moment and auxiliary-label hypotheses are retained;
the inverse-compression estimate is derived from them.

Source: *A two-dimensional area law from a global spectral gap*, September 24,
2026, Section 8, comparator:lower-pin, lines 585--615 of 07-comparators.tex,
revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
-/

noncomputable section
open TensorPower PermutationRepresentation
open scoped BigOperators Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace Matrix

variable (ι : Fin 5 → Type*) [∀ f, Fintype (ι f)] [∀ f, DecidableEq (ι f)]
variable [∀ f, Nonempty (ι f)]

local instance replicaLowDefectSharpLowerPin_decidableEqConfig (k : ℕ) :
    DecidableEq (Config k ι) := Fintype.decidablePiFintype

/-- The actual sharp lower pin and its compression in the same symmetric
coordinates. The moment bounds concern the original three physical
marginals, and the labels are the two original auxiliary labels. Source:
`07-comparators.tex`, `comparator:lower-pin`, lines 585--615. -/
theorem exists_replicaLowDefectProjection_sharp_lower_pin
    {t : ℝ} (ht : 0 < t) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (k : ℕ)
      (Ω : ι 0 × (ι 1 × ι 2) → ℂ), ‖WithLp.toLp 2 Ω‖ = 1 →
      ∀ (ellC ellR : IrrepLabel (Equiv.Perm (Fin k))) (K r : ℝ),
      (∀ j : Fin 3, ∀ v : ℝ, |v| ≤ r →
        Real.log (Entropy.surprisalMoment
          (posSemidef_physicalSingletonDensity ι Ω j).isHermitian.eigenvalues v) ≤
        v * vonNeumannEntropy (physicalSingletonDensity ι Ω j)
          (posSemidef_physicalSingletonDensity ι Ω j).isHermitian + K * v ^ 2) →
      20 * t ≤ r → 20 * t ≤ 1 → 0 ≤ K →
      ∀ (τ S ε : ℝ), 0 ≤ τ → τ ≤ 1 / 2 →
      2 * (k : ℝ) * S - ε ≤ Real.log ellC.dim + Real.log ellR.dim →
      let P := replicaLowDefectProjection (C := ι 3) (R := ι 4) Ω k ellC ellR τ
      let W := replicaMetric ι t k
      let A := ((W {0, 3})⁻¹ * (W {2, 4})⁻¹ * W {1}) ^ 2
      let η := fiveFactorCopiesEquiv ι k
      let Sj := fun j => vonNeumannEntropy (physicalSingletonDensity ι Ω j)
        (posSemidef_physicalSingletonDensity ι Ω j).isHermitian
      let g := Sj 0 + Sj 2 - Sj 1
      let d := Real.log (Fintype.card (ι 3)) + Real.log (Fintype.card (ι 4))
      let D := fun j : Fin 5 => Fintype.card (ι j)
      let Λ := ((((D 0 * D 3) ^ 2 : ℕ) : ℝ) + (((D 2 * D 4) ^ 2 : ℕ) : ℝ) +
        ((D 0 ^ 2 : ℕ) : ℝ) / 2 + ((D 2 ^ 2 : ℕ) : ℝ) / 2) / 5
      let c := ((k : ℝ) + 2) ^ (C + Λ) * Real.exp
        (-(k : ℝ) * (2 * t) *
          (2 * S + (1 - τ) * g - τ * d - 3 * Real.binEntropy τ) +
          (2 * t) * ε + 25 * (k : ℝ) * K * (2 * t) ^ 2)
      let b := ((k : ℝ) + 1) * Real.exp (k * Real.binEntropy τ) * c
      b⁻¹ • P.submatrix η η ≤ A ∧
        ∀ (n : ℕ) (Z : Matrix (Config k ι) (Fin n) ℂ),
          Z * Zᴴ = symProj (copyPerm ((f : Fin 5) → ι f) k) →
          IsStarProjection (Zᴴ * P.submatrix η η * Z) ∧
            b⁻¹ • (Zᴴ * P.submatrix η η * Z) ≤ Zᴴ * A * Z := by
  obtain ⟨C, hC, hinverse⟩ :=
    exists_replicaLowDefectProjection_inverse_sharp_compression_le ι ht
  refine ⟨C, hC, ?_⟩
  intro k Ω hΩ ellC ellR K r hmoment htr htone hK τ S ε hτ hτhalf hlabel
    P W A η Sj g d D Λ c b
  have hA : A.PosDef := posDef_replicaMetric_disjoint_inv_mul_inv_mul_sq ι ht.le k
    (by decide) (by decide) (by decide)
  have hP : IsStarProjection P := isStarProjection_replicaLowDefectProjection
    Ω hΩ k ellC ellR τ
  have hb : 0 < b := by dsimp only [b, c]; positivity
  have hinv : P * (A⁻¹).submatrix η.symm η.symm * P ≤ b • P :=
    hinverse k Ω hΩ ellC ellR K r hmoment htr htone hK τ S ε hτ hτhalf hlabel
  have hpin (n : ℕ) (Z : Matrix (Config k ι) (Fin n) ℂ) :
      b⁻¹ • (Zᴴ * P.submatrix η η * Z) ≤ Zᴴ * A * Z :=
    hA.lower_pin_of_reindexed_inverse_compression η hP hb hinv Z
  constructor
  · simpa only [Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one] using
      hA.lower_pin_of_reindexed_inverse_compression η hP hb hinv
        (1 : Matrix (Config k ι) (Config k ι) ℂ)
  · intro n Z hZZ
    exact ⟨isStarProjection_compressed_replicaLowDefectProjection
      ι Ω hΩ k ellC ellR τ Z hZZ, hpin n Z⟩

end Matrix

end

end LowDefectSharpLowerPin

section RegionalLowDefectLowerPin

universe u

noncomputable section
open TensorPower PermutationRepresentation
open scoped BigOperators Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace Matrix

variable {V : Type u} [Fintype V] [DecidableEq V]
variable (β : V → Type u) (C R : Type u)
variable [∀ v, Fintype (β v)] [∀ v, DecidableEq (β v)]
variable [Fintype C] [DecidableEq C] [Fintype R] [DecidableEq R]

local instance regionalLowerPin_decidableEqPhysical :
    DecidableEq ((v : V) → β v) := Fintype.decidablePiFintype

local instance regionalLowerPin_decidableEqConfig (k : ℕ) :
    DecidableEq (Config k (addedSiteSpace (addedSiteSpace β C) R)) :=
  Fintype.decidablePiFintype

local instance regionalLowerPin_decidableEqGroupedConfig
    (Q Y : Finset V) (k : ℕ) :
    DecidableEq (Config k (regionalFiveFactorSpace β C R Q Y)) :=
  Fintype.decidablePiFintype

private theorem regional_lower_pin_pullback
    (Ω : ((v : V) → β v) → ℂ) (hΩ : ‖WithLp.toLp 2 Ω‖ = 1)
    (Q Y : Finset V) (hQY : Disjoint Q Y) (t : ℝ) (k : ℕ)
    (ellC ellR : IrrepLabel (Equiv.Perm (Fin k))) (τ : ℝ)
    {b₀ b : ℝ} (hb₀ : 0 < b₀) (hbb : b₀ ≤ b)
    (hpin :
      let ι := regionalFiveFactorSpace β C R Q Y
      let ψ := Ω ∘ (ManyBody.regionalPhysicalEquiv β Q Y hQY).symm
      let η := fiveFactorCopiesEquiv ι k
      let P := (replicaLowDefectProjection (C := C) (R := R)
        ψ k ellC ellR τ).submatrix η η
      let W := replicaMetric ι t k
      b₀⁻¹ • P ≤ ((W {0, 3})⁻¹ * (W {2, 4})⁻¹ * W {1}) ^ 2)
    (n : ℕ) (Z : Matrix (Config k (addedSiteSpace (addedSiteSpace β C) R)) (Fin n) ℂ) :
    let P := globalReplicaLowDefectProjection β C R Ω k ellC ellR τ
    let W := replicaMetric (addedSiteSpace (addedSiteSpace β C) R) t k
    let A := ((W (regionalOriginalRegion Q Y {0, 3}))⁻¹ *
      (W (regionalOriginalRegion Q Y {2, 4}))⁻¹ *
        W (regionalOriginalRegion Q Y {1})) ^ 2
    b⁻¹ • (Zᴴ * P * Z) ≤ Zᴴ * A * Z := by
  intro P W A
  let ι := regionalFiveFactorSpace β C R Q Y
  let ψ := Ω ∘ (ManyBody.regionalPhysicalEquiv β Q Y hQY).symm
  let η := fiveFactorCopiesEquiv ι k
  let e := regionalFiveFactorCopyEquiv β C R Q Y hQY k
  let Pc := (replicaLowDefectProjection (C := C) (R := R)
    ψ k ellC ellR τ).submatrix η η
  have hψ : ‖WithLp.toLp 2 ψ‖ = 1 :=
    (ManyBody.norm_regionalPhysicalVector β Ω Q Y hQY).trans hΩ
  have hPc : 0 ≤ Pc := by
    exact ((Matrix.nonneg_iff_posSemidef.mp
      (isStarProjection_replicaLowDefectProjection ψ hψ k ellC ellR τ).nonneg).submatrix η).nonneg
  have hb : 0 < b := hb₀.trans_le hbb
  have hweak : b⁻¹ • Pc ≤
      ((replicaMetric ι t k {0, 3})⁻¹ *
        (replicaMetric ι t k {2, 4})⁻¹ * replicaMetric ι t k {1}) ^ 2 :=
    (smul_le_smul_of_nonneg_right ((inv_le_inv₀ hb hb₀).mpr hbb) hPc).trans hpin
  have hP : Pc.submatrix e e = P :=
    regionalFiveFactor_lowDefectProjection_eq_global β C R Ω hΩ Q Y hQY k ellC ellR τ
  have hA := replicaMetric_inv_mul_inv_mul_sq_submatrix_regionalFiveFactorCopyEquiv
    β C R Q Y hQY t k {0, 3} {2, 4} {1}
  change ((replicaMetric ι t k {0, 3})⁻¹ *
    (replicaMetric ι t k {2, 4})⁻¹ * replicaMetric ι t k {1}) ^ 2 =
      A.submatrix e.symm e.symm at hA
  have hpull : b⁻¹ • P ≤ A := by
    apply Matrix.le_iff.mpr
    simpa only [hA, Matrix.submatrix_sub, Matrix.submatrix_smul,
      Pi.sub_apply, Pi.smul_apply, hP, Matrix.submatrix_submatrix,
      Equiv.symm_comp_self, Matrix.submatrix_id_id] using
        (Matrix.le_iff.mp hweak).submatrix e
  apply Matrix.le_iff.mpr
  simpa only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul] using
    (Matrix.le_iff.mp hpull).conjTranspose_mul_mul_same Z

variable [∀ v, Nonempty (β v)] [Nonempty C] [Nonempty R]

/-- One rough polynomial constant works for all regional cuts, with the
same global low-defect projection and any fixed symmetric coordinates.
Only the original unit vector and original auxiliary-label bound enter;
no marginal moment assumption is imposed. Source: `07-comparators.tex`,
`comparator:lower-pin`, lines 585--615. -/
theorem exists_globalReplicaLowDefectProjection_rough_lower_pin
    {t : ℝ} (ht : 0 < t) (htsmall : 4 * t ≤ 1) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ (k : ℕ) (Ω : ((v : V) → β v) → ℂ),
      ‖WithLp.toLp 2 Ω‖ = 1 →
      ∀ (ellC ellR : IrrepLabel (Equiv.Perm (Fin k))) (τ S ε : ℝ),
      0 ≤ τ → τ ≤ 1 / 2 →
      2 * (k : ℝ) * S - ε ≤ Real.log ellC.dim + Real.log ellR.dim →
      let P := globalReplicaLowDefectProjection β C R Ω k ellC ellR τ
      let d := Real.log (Fintype.card C) + Real.log (Fintype.card R)
      let b := ((k : ℝ) + 1) * Real.exp (k * Real.binEntropy τ) *
        (((k : ℝ) + 2) ^ c * Real.exp
          (-(k : ℝ) * (2 * t) * (2 * S - τ * d - 3 * Real.binEntropy τ) + (2 * t) * ε))
      ∀ (n : ℕ) (Z : Matrix (Config k (addedSiteSpace (addedSiteSpace β C) R)) (Fin n) ℂ),
        Z * Zᴴ = symProj (copyPerm ((v : Option (Option V)) →
          addedSiteSpace (addedSiteSpace β C) R v) k) →
        IsStarProjection (Zᴴ * P * Z) ∧
          ∀ (Q Y : Finset V), Disjoint Q Y →
            let W := replicaMetric (addedSiteSpace (addedSiteSpace β C) R) t k
            let A := ((W (regionalOriginalRegion Q Y {0, 3}))⁻¹ *
              (W (regionalOriginalRegion Q Y {2, 4}))⁻¹ *
                W (regionalOriginalRegion Q Y {1})) ^ 2
            b⁻¹ • (Zᴴ * P * Z) ≤ Zᴴ * A * Z := by
  classical
  let ι := fun p : Finset V × Finset V => regionalFiveFactorSpace β C R p.1 p.2
  choose c₀ _hc₀ hlocal using fun p : Finset V × Finset V =>
    exists_replicaLowDefectProjection_rough_lower_pin (ι p) ht htsmall
  let D := fun p : Finset V × Finset V =>
    max ((Fintype.card (ι p 0) * Fintype.card C) ^ 2)
      ((Fintype.card (ι p 2) * Fintype.card R) ^ 2)
  let f := fun p : Finset V × Finset V => c₀ p + (D p : ℝ)
  let c := max 0 ((Finset.univ : Finset (Finset V × Finset V)).sup'
    Finset.univ_nonempty f)
  have hfc (p : Finset V × Finset V) : f p ≤ c :=
    (Finset.le_sup' f (Finset.mem_univ p)).trans (le_max_right _ _)
  refine ⟨c, le_max_left _ _, ?_⟩
  intro k Ω hΩ ellC ellR τ S ε hτ hτhalf hlabel P d b n Z hZZ
  refine ⟨(globalReplicaLowDefectProjection_properties β C R Ω hΩ k ellC ellR τ).2.2
    n Z hZZ, ?_⟩
  intro Q Y hQY W A
  let ψ := Ω ∘ (ManyBody.regionalPhysicalEquiv β Q Y hQY).symm
  have hψ : ‖WithLp.toLp 2 ψ‖ = 1 :=
    (ManyBody.norm_regionalPhysicalVector β Ω Q Y hQY).trans hΩ
  let b₀ := ((k : ℝ) + 1) * Real.exp (k * Real.binEntropy τ) *
    (((k : ℝ) + 2) ^ f (Q, Y) * Real.exp
      (-(k : ℝ) * (2 * t) * (2 * S - τ * d - 3 * Real.binEntropy τ) + (2 * t) * ε))
  have hb₀ : 0 < b₀ := by dsimp only [b₀]; positivity
  have hbb : b₀ ≤ b := by
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow_of_exponent_le
        (by linarith only [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]) (hfc (Q, Y)))
      (Real.exp_pos _).le
  exact regional_lower_pin_pullback β C R Ω hΩ Q Y hQY t k ellC ellR τ
    hb₀ hbb (hlocal (Q, Y) k ψ hψ ellC ellR τ S ε hτ hτhalf hlabel).1 n Z

/-- One sharp polynomial constant works for all regional cuts. The moment
hypotheses concern the three reductions of the original vector, while the
same global projection and the same symmetric coordinates are used for
every cut. Source: `07-comparators.tex`, `comparator:lower-pin`, lines 585--615. -/
theorem exists_globalReplicaLowDefectProjection_sharp_lower_pin
    {t : ℝ} (ht : 0 < t) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ (k : ℕ) (Ω : ((v : V) → β v) → ℂ),
      ‖WithLp.toLp 2 Ω‖ = 1 →
      ∀ (ellC ellR : IrrepLabel (Equiv.Perm (Fin k))) (τ S ε : ℝ),
      0 ≤ τ → τ ≤ 1 / 2 →
      2 * (k : ℝ) * S - ε ≤ Real.log ellC.dim + Real.log ellR.dim →
      let P := globalReplicaLowDefectProjection β C R Ω k ellC ellR τ
      let d := Real.log (Fintype.card C) + Real.log (Fintype.card R)
      ∀ (n : ℕ) (Z : Matrix (Config k (addedSiteSpace (addedSiteSpace β C) R)) (Fin n) ℂ),
        Z * Zᴴ = symProj (copyPerm ((v : Option (Option V)) →
          addedSiteSpace (addedSiteSpace β C) R v) k) →
        IsStarProjection (Zᴴ * P * Z) ∧
          ∀ (Q Y : Finset V), Disjoint Q Y → ∀ (K r : ℝ),
            (∀ j : Fin 3, ∀ v : ℝ, |v| ≤ r →
              let T := ManyBody.regionalPhysicalRegion Q Y j
              Real.log (Entropy.surprisalMoment
                (ManyBody.regionState_posSemidef T (WithLp.toLp 2 Ω)).isHermitian.eigenvalues
                v) ≤
                  v * ManyBody.regionEntropy (WithLp.toLp 2 Ω) T + K * v ^ 2) →
            20 * t ≤ r → 20 * t ≤ 1 → 0 ≤ K →
            let g := ManyBody.regionEntropy (WithLp.toLp 2 Ω) Q +
              ManyBody.regionEntropy (WithLp.toLp 2 Ω) (Q ∪ Y)ᶜ -
              ManyBody.regionEntropy (WithLp.toLp 2 Ω) Y
            let b := ((k : ℝ) + 1) * Real.exp (k * Real.binEntropy τ) *
              (((k : ℝ) + 2) ^ c * Real.exp
                (-(k : ℝ) * (2 * t) *
                  (2 * S + (1 - τ) * g - τ * d - 3 * Real.binEntropy τ) +
                    (2 * t) * ε + 25 * (k : ℝ) * K * (2 * t) ^ 2))
            let W := replicaMetric (addedSiteSpace (addedSiteSpace β C) R) t k
            let A := ((W (regionalOriginalRegion Q Y {0, 3}))⁻¹ *
              (W (regionalOriginalRegion Q Y {2, 4}))⁻¹ *
                W (regionalOriginalRegion Q Y {1})) ^ 2
            b⁻¹ • (Zᴴ * P * Z) ≤ Zᴴ * A * Z := by
  classical
  let ι := fun p : Finset V × Finset V => regionalFiveFactorSpace β C R p.1 p.2
  choose c₀ _hc₀ hlocal using fun p : Finset V × Finset V =>
    exists_replicaLowDefectProjection_sharp_lower_pin (ι p) ht
  let D := fun (p : Finset V × Finset V) (j : Fin 5) => Fintype.card (ι p j)
  let Λ := fun p : Finset V × Finset V =>
    ((((D p 0 * D p 3) ^ 2 : ℕ) : ℝ) + (((D p 2 * D p 4) ^ 2 : ℕ) : ℝ) +
      ((D p 0 ^ 2 : ℕ) : ℝ) / 2 + ((D p 2 ^ 2 : ℕ) : ℝ) / 2) / 5
  let f := fun p : Finset V × Finset V => c₀ p + Λ p
  let c := max 0 ((Finset.univ : Finset (Finset V × Finset V)).sup'
    Finset.univ_nonempty f)
  have hfc (p : Finset V × Finset V) : f p ≤ c :=
    (Finset.le_sup' f (Finset.mem_univ p)).trans (le_max_right _ _)
  refine ⟨c, le_max_left _ _, ?_⟩
  intro k Ω hΩ ellC ellR τ S ε hτ hτhalf hlabel P d n Z hZZ
  refine ⟨(globalReplicaLowDefectProjection_properties β C R Ω hΩ k ellC ellR τ).2.2
    n Z hZZ, ?_⟩
  intro Q Y hQY K r hmoment htr htone hK g b W A
  let ψ := Ω ∘ (ManyBody.regionalPhysicalEquiv β Q Y hQY).symm
  have hψ : ‖WithLp.toLp 2 ψ‖ = 1 :=
    (ManyBody.norm_regionalPhysicalVector β Ω Q Y hQY).trans hΩ
  have hstats := regional_physicalSingleton_spectral_statistics β C R Ω Q Y hQY
  have hmoment' (j : Fin 3) (v : ℝ) (hv : |v| ≤ r) :
      Real.log (Entropy.surprisalMoment
        (posSemidef_physicalSingletonDensity (ι (Q, Y)) ψ j).isHermitian.eigenvalues v) ≤
      v * vonNeumannEntropy (physicalSingletonDensity (ι (Q, Y)) ψ j)
        (posSemidef_physicalSingletonDensity (ι (Q, Y)) ψ j).isHermitian + K * v ^ 2 := by
    rw [(hstats j).2 v, (hstats j).1]
    exact hmoment j v hv
  have hg :
      vonNeumannEntropy (physicalSingletonDensity (ι (Q, Y)) ψ 0)
          (posSemidef_physicalSingletonDensity (ι (Q, Y)) ψ 0).isHermitian +
        vonNeumannEntropy (physicalSingletonDensity (ι (Q, Y)) ψ 2)
          (posSemidef_physicalSingletonDensity (ι (Q, Y)) ψ 2).isHermitian -
        vonNeumannEntropy (physicalSingletonDensity (ι (Q, Y)) ψ 1)
          (posSemidef_physicalSingletonDensity (ι (Q, Y)) ψ 1).isHermitian = g := by
    rw [(hstats 0).1, (hstats 2).1, (hstats 1).1]
    rfl
  let b₀ := ((k : ℝ) + 1) * Real.exp (k * Real.binEntropy τ) *
    (((k : ℝ) + 2) ^ f (Q, Y) * Real.exp
      (-(k : ℝ) * (2 * t) *
        (2 * S + (1 - τ) * g - τ * d - 3 * Real.binEntropy τ) +
          (2 * t) * ε + 25 * (k : ℝ) * K * (2 * t) ^ 2))
  have hb₀ : 0 < b₀ := by dsimp only [b₀]; positivity
  have hbb : b₀ ≤ b := by
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow_of_exponent_le
        (by linarith only [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]) (hfc (Q, Y)))
      (Real.exp_pos _).le
  apply regional_lower_pin_pullback β C R Ω hΩ Q Y hQY t k ellC ellR τ hb₀ hbb _ n Z
  have h := (hlocal (Q, Y) k ψ hψ ellC ellR K r hmoment' htr htone hK
    τ S ε hτ hτhalf hlabel).1
  dsimp +instances only [ι, regionalFiveFactorSpaceFintype,
    regionalFiveFactorSpaceDecidableEq, regionalLowerPin_decidableEqPhysical] at h ⊢
  simpa only [hg, b₀, f, Λ, D, ψ, ι,
    (show Real.log (Fintype.card (ι (Q, Y) 3)) +
      Real.log (Fintype.card (ι (Q, Y) 4)) = d from rfl)] using! h


end Matrix

end

end RegionalLowDefectLowerPin

end RegionalLowDefectLowerPin
