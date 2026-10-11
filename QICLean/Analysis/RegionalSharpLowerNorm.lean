/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.RegionalLowDefectMass
import QICLean.Analysis.RegionalLowDefectLowerPin
import QICLean.Analysis.RegionalPhysicalMarginals
import QICLean.Analysis.MeanTreeExponentialLowerNorm
import QICLean.Representation.ReplicaSymmetricMetricFloor
import QICLean.Representation.RegionalReplicaMetricRegions

/-!
# An explicit sharp lower norm bound in the original physical coordinates

The sharp regional lower bound, the uniform symmetric floor and the
original physical gap give a lower norm estimate for the same normalized
inverse-power vector. Each entropy difference is computed from the actual
physical marginals. A finite maximum bounds these differences without a
positive number of bands. The polynomial constants precede the state,
region family and moment parameters. The actual defect mass is a conclusion
of the original gap and label conditions.
Source: *A two-dimensional area law from a global spectral gap*, September 24,
2026, `07-comparators.tex`, lines 550--651, revision
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

universe u v

noncomputable section
open TensorPower PermutationRepresentation
open scoped BigOperators Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace Matrix

variable {V : Type u} [Fintype V] [DecidableEq V]
variable (β : V → Type u) (C R : Type u)
variable [∀ x, Fintype (β x)] [∀ x, DecidableEq (β x)]
variable [Fintype C] [DecidableEq C] [Fintype R] [DecidableEq R]

local notation "ι₀" => addedSiteSpace (addedSiteSpace β C) R

local instance regionalSharpLowerNorm_decidableEqPhysical :
    DecidableEq ((x : V) → β x) := Fintype.decidablePiFintype

local instance regionalSharpLowerNorm_decidableEqConfig (k : ℕ) :
    DecidableEq (Config k ι₀) := Fintype.decidablePiFintype

variable [∀ x, Nonempty (β x)] [Nonempty C] [Nonempty R]

open Classical in
/-- An explicit sharp lower norm estimate for the actual common-tree
band product. The moment assumptions concern the three original physical
reductions at each leaf. The same physical state determines the gap,
common defect projection and marginal entropies. The label-dimension
parameter remains separate from these marginal entropies.
Source: `07-comparators.tex`, lines 550--651. -/
theorem exists_replicaMetric_symProj_bandProduct_sharp_lower_norm
    {t : ℝ} (ht : 0 < t) :
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
      ∀ (J : Type v) [Fintype J] [DecidableEq J] (G : ℕ)
        (Q Y : J → Fin G → Finset V),
      (∀ j g, Disjoint (Q j g) (Y j g)) →
      (∀ j j' g h, g < h → Q j g ∪ Y j g ⊆ Q j' h) →
      ∀ (K rMom : ℝ),
      (∀ (j : J) (g : Fin G) (a : Fin 3) (v : ℝ), |v| ≤ rMom →
        let U := FiniteProduct.regionalPhysicalRegion (Q j g) (Y j g) a
        Real.log (Entropy.surprisalMoment
          (FiniteProduct.reducedPure_posSemidef β (WithLp.toLp 2 Ω) U).isHermitian.eigenvalues v) ≤
            v * FiniteProduct.entropy β (WithLp.toLp 2 Ω) U + K * v ^ 2) →
      20 * t ≤ rMom → 20 * t ≤ 1 → 0 ≤ K →
      ∀ (T : MeanTree J) (ellC ellR : IrrepLabel (Equiv.Perm (Fin k)))
        (S ε s : ℝ),
      2 * (k : ℝ) * S - ε ≤ Real.log ellC.dim + Real.log ellR.dim →
      0 ≤ s →
      ∀ ξ : EuclideanSpace ℂ (Config k ι₀), ξ ≠ 0 → ‖ξ‖ ≤ 1 →
      symProj (copyPerm ((x : Option (Option V)) → ι₀ x) k) *ᵥ ξ = ξ →
      labelProj (subsystemPerm k ι₀ {some none}) ellC *ᵥ ξ = ξ →
      labelProj (subsystemPerm k ι₀ {none}) ellR *ᵥ ξ = ξ →
      let W := replicaMetric ι₀ t k
      let L := fun j g => insert (some none) ((Q j g).image fun x => some (some x))
      let F := fun j g => insert none
        (((Q j g ∪ Y j g)ᶜ).image fun x => some (some x))
      let E := fun j g => (Y j g).image fun x => some (some x)
      let A := fun j g => ((W (L j g))⁻¹ * (W (F j g))⁻¹ * W (E j g)) ^ 2
      let B := fun j g => Zᴴ * A j g * Z
      let M := (List.ofFn fun g => T.eval (B · g)).prod
      let w := toEuclideanLin (M ^ (-s)) (toEuclideanLin Zᴴ ξ)
      let φ := (‖w‖⁻¹ : ℂ) • w
      let v := toEuclideanLin Z φ
      let δ := ((star v ⬝ᵥ (globalReplicaMeanHamiltonian β C R H k *ᵥ v)).re - E₀) / gap
      let entropyGap := fun j g =>
        FiniteProduct.entropy β (WithLp.toLp 2 Ω) (Q j g) +
          FiniteProduct.entropy β (WithLp.toLp 2 Ω) (Q j g ∪ Y j g)ᶜ -
          FiniteProduct.entropy β (WithLp.toLp 2 Ω) (Y j g)
      let gaps := (Finset.univ : Finset (J × Fin G)).image
        (fun p => entropyGap p.1 p.2)
      let gmax := (insert (0 : ℝ) gaps).max' (Finset.insert_nonempty _ _)
      let d := Real.log (Fintype.card C) + Real.log (Fintype.card R)
      let r := Real.log ((k : ℝ) + 1) + c * Real.log ((k : ℝ) + 2) + 2 * t * ε
      let b := ((k : ℝ) + 2) ^ (-Cf) / 2
      w ≠ 0 ∧ ‖v‖ = 1 ∧ 0 ≤ δ ∧
        ∀ τ : ℝ, 0 < τ → τ ≤ 1 / 2 →
          let rate := fun g => 2 * S +
            (1 - τ) * (∑ j, T.weight j * entropyGap j g) - τ * d -
              (3 + 1 / (2 * t)) * Real.binEntropy τ - 50 * K * t
          2 * s * (∑ g,
            (2 * t * (k : ℝ) * (rate g - δ / τ * max 0 (2 * S + gmax)) -
              (2 * |r| + |Real.log b| + Real.log 2 + Real.log (3 / 2)))) ≤
            -Real.log (‖w‖ ^ 2) := by
  obtain ⟨c, hc, hlower⟩ :=
    exists_globalReplicaLowDefectProjection_sharp_lower_pin β C R ht
  done

end Matrix
