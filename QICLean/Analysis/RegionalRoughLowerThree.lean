/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sirui Lu
-/
import QICLean.Analysis.RegionalRoughLowerNorm
import QICLean.Analysis.RoughLowerCoefficient
import QICLean.Analysis.MeanTreeSublinearRemainder

/-!
# The rough lower comparison at fixed total band weight

With K bands, choose the metric parameter 2/K and the inverse-power
exponent 1/4. The resulting total weight gives a rough lower comparison
with numerical coefficient three. The physical Hamiltonian, reference
state, initial vector, band product and normalized filtered vector are
retained from the explicit lower estimate.

The entropy parameter and the label error may have either sign. The defect
is proved nonnegative using the original global gap; it is not required to
be bounded by the auxiliary fraction. Both logarithms of two in the
remainder are retained.

This is the fixed-weight consequence of the supplied-vector lower estimate.
Selection of the common auxiliary label and identification with a scanner's
actual root and filtered vector are separate applications.

Source: OpenAI, A two-dimensional area law from a global spectral gap,
07-comparators.tex, lines 153–169 and 585–651, and 08-scanner.tex,
lines 755–769, revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
-/

noncomputable section
open TensorPower PermutationRepresentation
open scoped BigOperators Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace Matrix

variable {V : Type} [Fintype V] [DecidableEq V]
variable (β : V → Type) [∀ x, Fintype (β x)] [∀ x, DecidableEq (β x)]
variable [∀ x, Nonempty (β x)] (d : ℕ) [NeZero d]

local notation "ι₀" => addedSiteSpace (addedSiteSpace β (Fin d)) (Fin d)

local instance regionalRoughLowerThree_decidableEqConfig (k : ℕ) :
    DecidableEq (Config k ι₀) := Fintype.decidablePiFintype

/-- The rough lower estimate with coefficient three and total band weight
four, on the same normalized inverse-power vector as the explicit estimate.
The constants are chosen before the state, label, mean tree and copy number.
Source: 07-comparators.tex, comparator:rough-lower, lines 153–169 and
585–651; 08-scanner.tex, scanner:bootstrap-comparison, lines 755–769,
revision adc7f1241b42e322a6451854ab7e4b4c146bf78a. -/
theorem exists_replicaMetric_symProj_bandProduct_rough_lower_norm_three
    (K : ℕ) (hK : 8 ≤ K) :
    ∃ c Cf : ℝ, 0 ≤ c ∧ 0 ≤ Cf ∧
      ∀ (k n : ℕ), 0 < k →
      ∀ (H : Matrix ((x : V) → β x) ((x : V) → β x) ℂ)
        (Ω : ((x : V) → β x) → ℂ) (E₀ gap : ℝ),
      (H - (E₀ : ℂ) • 1 -
        (gap : ℂ) • (1 - vecMulVec Ω (star Ω))).PosSemidef →
      ‖WithLp.toLp 2 Ω‖ = 1 → 0 < gap →
      ∀ (Z : Matrix (Config k ι₀) (Fin n) ℂ),
      Zᴴ * Z = 1 →
      Z * Zᴴ = symProj (copyPerm ((x : Option (Option V)) → ι₀ x) k) →
      ∀ (J : Type) [Fintype J] [DecidableEq J]
        (Q Y : J → Fin K → Finset V),
      (∀ j g, Disjoint (Q j g) (Y j g)) →
      (∀ j j' g h, g < h → Q j g ∪ Y j g ⊆ Q j' h) →
      ∀ (T : MeanTree J) (ell : IrrepLabel (Equiv.Perm (Fin k))) (S ε : ℝ),
      2 * (k : ℝ) * S - ε ≤ Real.log ell.dim + Real.log ell.dim →
      ∀ ξ : EuclideanSpace ℂ (Config k ι₀), ξ ≠ 0 → ‖ξ‖ ≤ 1 →
      symProj (copyPerm ((x : Option (Option V)) → ι₀ x) k) *ᵥ ξ = ξ →
      labelProj (subsystemPerm k ι₀ {some none}) ell *ᵥ ξ = ξ →
      labelProj (subsystemPerm k ι₀ {none}) ell *ᵥ ξ = ξ →
      let a := 4 / (K : ℝ)
      let t := 2 / (K : ℝ)
      let W := replicaMetric ι₀ t k
      let L := fun j g => insert (some none) ((Q j g).image fun x => some (some x))
      let F := fun j g => insert none
        (((Q j g ∪ Y j g)ᶜ).image fun x => some (some x))
      let E := fun j g => (Y j g).image fun x => some (some x)
      let A := fun j g => ((W (L j g))⁻¹ * (W (F j g))⁻¹ * W (E j g)) ^ 2
      let B := fun j g => Zᴴ * A j g * Z
      let M := (List.ofFn fun g => T.eval (B · g)).prod
      let w := toEuclideanLin (M ^ (-(1 / 4 : ℝ))) (toEuclideanLin Zᴴ ξ)
      let φ := (‖w‖⁻¹ : ℂ) • w
      let v := toEuclideanLin Z φ
      let δ := ((star v ⬝ᵥ (globalReplicaMeanHamiltonian β (Fin d) (Fin d) H k *ᵥ v)).re -
        E₀) / gap
      let r := Real.log ((k : ℝ) + 1) + c * Real.log ((k : ℝ) + 2) + a * ε
      let remainder := ((K : ℝ) / 2 * (2 * |r| + Cf * Real.log ((k : ℝ) + 2) +
        2 * Real.log 2 + Real.log (3 / 2))) / (k : ℝ)
      w ≠ 0 ∧ ‖v‖ = 1 ∧ 0 ≤ δ ∧
        ∀ τ : ℝ, 0 < τ → τ ≤ 1 / 2 →
          4 * S - 6 * (τ * Real.log (d : ℝ) + Real.binEntropy τ / a) -
              3 * (δ / τ) * max 0 (2 * S) - remainder ≤
            -Real.log (‖w‖ ^ 2) / (k : ℝ) := by
  have hKreal : (8 : ℝ) ≤ K := by exact_mod_cast hK
  done

end Matrix
