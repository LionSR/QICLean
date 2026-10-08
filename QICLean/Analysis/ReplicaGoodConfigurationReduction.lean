/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.ReplicaGoodConfigurationDensity
import QICLean.Analysis.ReplicaGoodPairMarginal
import QICLean.Representation.CompatiblePhysicalLabel
import QICLean.Analysis.ReplicaTwoMergeMoment

/-!
# Reductions of the density of the good copies

The five factors are ordered as `Q`, `Y`, `V`, `C`, `R`. The actual density
retains all five factors of the good copies of the same excitation component.
The chosen enumeration of the good copies is the one used in its definition.

Tracing the good `Y` copies, after grouping the remaining factors as `QC` and
`VR`, gives the existing density on these two pairs. The physical symmetric
projection implies that the nonnegative spectral projection of the physical
merge deficit fixes the full density. Finally, the paired exponential-moment
bound transfers to the full density by an explicit rearrangement of coordinates.

The last result is an auxiliary arithmetic-mean polynomial bound. It does not
assert the sharper printed constant or the final metric comparison. Its only
state assumptions are normalization of the one-copy physical state and the
original simultaneous permutation invariance used by the paired moment theorem.
The trace identity requires neither assumption, and the spectral support result
requires only the one-copy normalization. Zero copies, an empty set of good
copies and a zero excitation component are included.

## References

OpenAI, *A two-dimensional area law from a global spectral gap*, September 24,
2026, `07-comparators.tex`, lines 23, 103–110 and 501–555,
`comparator:merge-decomposition` and `comparator:merge-moments`, at source commit
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

open TensorPower PermutationRepresentation
open scoped BigOperators Matrix Kronecker Matrix.Norms.Operator
private def goodPairConfigEquiv (ι : Fin 5 → Type*) (m : ℕ) :
    Config m ι ≃ (((Fin m → ι 0) × (Fin m → ι 3)) ×
      ((Fin m → ι 2) × (Fin m → ι 4))) × (Fin m → ι 1) :=
  (fiveFactorCopiesEquiv ι m).trans
    { toFun := fun x => (((fun j => (x.1 j).1, x.2.1),
          (fun j => (x.1 j).2.2, x.2.2)), fun j => (x.1 j).2.1)
      invFun := fun x => ((fun j => (x.1.1.1 j, (x.2 j, x.1.2.1 j))),
          (x.1.1.2, x.1.2.2))
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

private def goodQCOperatorLift (ι : Fin 5 → Type*) [∀ f, DecidableEq (ι f)] (m : ℕ) :
    Matrix ((Fin m → ι 0) × (Fin m → ι 3)) ((Fin m → ι 0) × (Fin m → ι 3)) ℂ →ₗ[ℂ]
      Matrix ((((Fin m → ι 0) × (Fin m → ι 3)) ×
        ((Fin m → ι 2) × (Fin m → ι 4))) × (Fin m → ι 1))
        ((((Fin m → ι 0) × (Fin m → ι 3)) ×
        ((Fin m → ι 2) × (Fin m → ι 4))) × (Fin m → ι 1)) ℂ :=
  ((Matrix.kroneckerBilinear (R := ℂ)).flip
    (1 : Matrix (Fin m → ι 1) (Fin m → ι 1) ℂ)).comp
      ((Matrix.kroneckerBilinear (R := ℂ)).flip
        (1 : Matrix ((Fin m → ι 2) × (Fin m → ι 4))
          ((Fin m → ι 2) × (Fin m → ι 4)) ℂ))

private def goodVROperatorLift (ι : Fin 5 → Type*) [∀ f, DecidableEq (ι f)] (m : ℕ) :
    Matrix ((Fin m → ι 2) × (Fin m → ι 4)) ((Fin m → ι 2) × (Fin m → ι 4)) ℂ →ₗ[ℂ]
      Matrix ((((Fin m → ι 0) × (Fin m → ι 3)) ×
        ((Fin m → ι 2) × (Fin m → ι 4))) × (Fin m → ι 1))
        ((((Fin m → ι 0) × (Fin m → ι 3)) ×
        ((Fin m → ι 2) × (Fin m → ι 4))) × (Fin m → ι 1)) ℂ :=
  ((Matrix.kroneckerBilinear (R := ℂ)).flip
    (1 : Matrix (Fin m → ι 1) (Fin m → ι 1) ℂ)).comp
      ((Matrix.kroneckerBilinear (R := ℂ))
        (1 : Matrix ((Fin m → ι 0) × (Fin m → ι 3))
          ((Fin m → ι 0) × (Fin m → ι 3)) ℂ))

namespace Matrix

/-- Tracing exactly the good middle physical copies gives the actual density on
`QC` and `VR`, with the same chosen enumeration and the same excitation component.
No normalization or invariance is assumed.

OpenAI, September 24, 2026, `07-comparators.tex`, lines 23, 103–110 and 524–549,
`comparator:merge-moments`. -/
theorem partialTraceRight_replicaGoodConfigurationMarginal (ι : Fin 5 → Type*)
    [∀ f, Fintype (ι f)] [∀ f, DecidableEq (ι f)]
    (Ω : ι 0 × (ι 1 × ι 2) → ℂ) (k : ℕ) (B : Finset (Fin k))
    (u : (Fin k → ι 0 × (ι 1 × ι 2)) × ((Fin k → ι 3) × (Fin k → ι 4)) → ℂ) :
    let m := Bᶜ.card
    let r := fun x : (((Fin m → ι 0) × (Fin m → ι 3)) ×
      ((Fin m → ι 2) × (Fin m → ι 4))) × (Fin m → ι 1) =>
      (fiveFactorCopiesEquiv ι m).symm
        ((fun j => (x.1.1.1 j, (x.2 j, x.1.2.1 j))), (x.1.1.2, x.1.2.2))
    partialTraceRight ((replicaGoodConfigurationMarginal ι Ω k B u).submatrix r r) =
      replicaGoodPairMarginal Ω k B u := by
  intro m r
  ext p q
  simp only [partialTraceRight_apply, submatrix_apply, replicaGoodConfigurationMarginal,
    replicaGoodPairMarginal, vecMulVec_apply, Pi.star_apply]
  simp only [r, m, Equiv.apply_symm_apply, Fintype.sum_prod_type]
private theorem labelEntropy_transport {G X Y Z : Type*} [Group G] [Fintype G]
    [Fintype X] [DecidableEq X]
    [Fintype Z] [DecidableEq Z]
    (e : X ≃ Y) (φ : G →* Equiv.Perm X) (ψ : G →* Equiv.Perm Z)
    (L : Matrix Z Z ℂ →ₗ[ℂ] Matrix Y Y ℂ)
    (h : ∀ g, (permOp φ g).submatrix e.symm e.symm = L (permOp ψ g)) :
    (labelEntropy φ).submatrix e.symm e.symm = L (labelEntropy ψ) := by
  change (reindexLinearEquiv ℂ ℂ e e) (labelEntropy φ) = L (labelEntropy ψ)
  simp only [labelEntropy, labelObservable, labelProj, groupAlgebraRep_eq_sum, map_sum, map_smul]
  simp only [coe_reindexLinearEquiv, reindex_apply, h]


private theorem permOp_transport_left {G X A Z Y : Type*} [Group G]
    [Fintype X] [DecidableEq X] [Fintype A] [DecidableEq A]
    [DecidableEq Z] [DecidableEq Y]
    (e : X ≃ (A × Z) × Y) (φ : G →* Equiv.Perm X) (ψ : G →* Equiv.Perm A)
    (h : ∀ g x, e (φ g x) = ((ψ g (e x).1.1, (e x).1.2), (e x).2)) (g : G) :
    (permOp φ g).submatrix e.symm e.symm =
      (permOp ψ g ⊗ₖ (1 : Matrix Z Z ℂ)) ⊗ₖ (1 : Matrix Y Y ℂ) := by
  ext x y
  simp only [submatrix_apply, permOp_apply_apply, ← e.injective.eq_iff, h,
    Equiv.apply_symm_apply, Prod.ext_iff, kroneckerMap_apply, one_apply]
  split_ifs <;> simp_all

private theorem permOp_transport_right {G X A Z Y : Type*} [Group G]
    [Fintype X] [DecidableEq X] [DecidableEq A]
    [Fintype Z] [DecidableEq Z] [DecidableEq Y]
    (e : X ≃ (A × Z) × Y) (φ : G →* Equiv.Perm X) (ψ : G →* Equiv.Perm Z)
    (h : ∀ g x, e (φ g x) = (((e x).1.1, ψ g (e x).1.2), (e x).2)) (g : G) :
    (permOp φ g).submatrix e.symm e.symm =
      ((1 : Matrix A A ℂ) ⊗ₖ permOp ψ g) ⊗ₖ (1 : Matrix Y Y ℂ) := by
  ext x y
  simp only [submatrix_apply, permOp_apply_apply, ← e.injective.eq_iff, h,
    Equiv.apply_symm_apply, Prod.ext_iff, kroneckerMap_apply, one_apply]
  split_ifs <;> simp_all

private theorem exp_submatrix {X Y : Type*}
    [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
    (e : X ≃ Y) (M : Matrix X X ℂ) :
    (NormedSpace.exp M).submatrix e.symm e.symm =
      NormedSpace.exp (M.submatrix e.symm e.symm) := by
  exact NormedSpace.map_exp (Matrix.reindexRingEquiv ℂ e)
    (continuous_id.matrix_submatrix e.symm e.symm) M

private theorem trace_reindex_kronecker {X A Y : Type*}
    [Fintype X] [Fintype A] [Fintype Y] [DecidableEq Y]
    (e : X ≃ A × Y) (ρ : Matrix X X ℂ) (M : Matrix A A ℂ) :
    (ρ * ((M ⊗ₖ (1 : Matrix Y Y ℂ)).submatrix e e)).trace =
      (partialTraceRight (ρ.submatrix e.symm e.symm) * M).trace := by
  rw [trace_partialTraceRight_mul]
  simpa only [← submatrix_mul_equiv _ _ e.symm e.symm e.symm, submatrix_submatrix,
    Equiv.self_comp_symm, submatrix_id_id] using
    (trace_submatrix_equiv e.symm (ρ * ((M ⊗ₖ (1 : Matrix Y Y ℂ)).submatrix e e))).symm

private theorem trace_good_operator (ι : Fin 5 → Type*)
    [∀ f, Fintype (ι f)] [∀ f, DecidableEq (ι f)]
    (Ω : ι 0 × (ι 1 × ι 2) → ℂ) (k : ℕ) (B : Finset (Fin k))
    (u : (Fin k → ι 0 × (ι 1 × ι 2)) × ((Fin k → ι 3) × (Fin k → ι 4)) → ℂ)
    (M : Matrix (((Fin Bᶜ.card → ι 0) × (Fin Bᶜ.card → ι 3)) ×
      ((Fin Bᶜ.card → ι 2) × (Fin Bᶜ.card → ι 4)))
      (((Fin Bᶜ.card → ι 0) × (Fin Bᶜ.card → ι 3)) ×
      ((Fin Bᶜ.card → ι 2) × (Fin Bᶜ.card → ι 4))) ℂ) :
    (replicaGoodConfigurationMarginal ι Ω k B u *
      ((M ⊗ₖ (1 : Matrix (Fin Bᶜ.card → ι 1) (Fin Bᶜ.card → ι 1) ℂ)).submatrix
        (goodPairConfigEquiv ι Bᶜ.card) (goodPairConfigEquiv ι Bᶜ.card))).trace =
      (replicaGoodPairMarginal Ω k B u * M).trace := by
  rw [trace_reindex_kronecker]
  rw [show partialTraceRight ((replicaGoodConfigurationMarginal ι Ω k B u).submatrix
    (goodPairConfigEquiv ι Bᶜ.card).symm (goodPairConfigEquiv ι Bᶜ.card).symm) =
      replicaGoodPairMarginal Ω k B u from partialTraceRight_replicaGoodConfigurationMarginal ι Ω k B u]

/-- The nonnegative physical merge-deficit projection fixes the actual full
density of the good copies. All good middle physical copies remain present;
no symmetry assumption on the original vector is needed.

OpenAI, September 24, 2026, `07-comparators.tex`, lines 513–517,
`comparator:merge-decomposition`. -/
theorem spectralProjectionGE_physicalMergeDeficit_mul_replicaGoodConfigurationMarginal
    (ι : Fin 5 → Type*)
    [∀ f, Fintype (ι f)] [∀ f, DecidableEq (ι f)]
    (Ω : ι 0 × (ι 1 × ι 2) → ℂ) (hΩ : ‖WithLp.toLp 2 Ω‖ = 1)
    (k : ℕ) (B : Finset (Fin k))
    (u : (Fin k → ι 0 × (ι 1 × ι 2)) × ((Fin k → ι 3) × (Fin k → ι 4)) → ℂ) :
    spectralProjectionGE (physicalMergeDeficit ι Bᶜ.card) 0 *
      replicaGoodConfigurationMarginal ι Ω k B u =
      replicaGoodConfigurationMarginal ι Ω k B u := by
  simpa only [mul_assoc, symProj_mul_replicaGoodConfigurationMarginal ι Ω hΩ k B u] using
    congrArg (fun M => M * replicaGoodConfigurationMarginal ι Ω k B u)
      (spectralProjectionGE_physicalMergeDeficit_mul_symProj ι Bᶜ.card)


private theorem sum_merge_transport (ι : Fin 5 → Type*)
    [∀ f, Fintype (ι f)] [∀ f, DecidableEq (ι f)] (m : ℕ) :
    let e := goodPairConfigEquiv ι m
    let DC := labelEntropy (subsystemPerm m ι {0}) +
      labelEntropy (subsystemPerm m ι {3}) - labelEntropy (subsystemPerm m ι {0, 3})
    let DR := labelEntropy (subsystemPerm m ι {2}) +
      labelEntropy (subsystemPerm m ι {4}) - labelEntropy (subsystemPerm m ι {2, 4})
    (DC + DR).submatrix e.symm e.symm =
      (pairMergeDeficit (ι 0) (ι 3) m ⊗ₖ
        (1 : Matrix ((Fin m → ι 2) × (Fin m → ι 4))
          ((Fin m → ι 2) × (Fin m → ι 4)) ℂ) +
        (1 : Matrix ((Fin m → ι 0) × (Fin m → ι 3))
          ((Fin m → ι 0) × (Fin m → ι 3)) ℂ) ⊗ₖ pairMergeDeficit (ι 2) (ι 4) m) ⊗ₖ
          (1 : Matrix (Fin m → ι 1) (Fin m → ι 1) ℂ) := by
  intro e DC DR
  have h0 : (labelEntropy (subsystemPerm m ι {0})).submatrix e.symm e.symm =
      goodQCOperatorLift ι m (labelEntropy (pairCopyLeft (ι 0) (ι 3) m)) := by
    exact labelEntropy_transport e _ _ _
      (fun σ => permOp_transport_left e _ _ (fun _ _ => rfl) σ)
  have h3 : (labelEntropy (subsystemPerm m ι {3})).submatrix e.symm e.symm =
      goodQCOperatorLift ι m (labelEntropy (pairCopyRight (ι 0) (ι 3) m)) := by
    exact labelEntropy_transport e _ _ _
      (fun σ => permOp_transport_left e _ _ (fun _ _ => rfl) σ)
  have h03 : (labelEntropy (subsystemPerm m ι {0, 3})).submatrix e.symm e.symm =
      goodQCOperatorLift ι m (labelEntropy (pairCopyBoth (ι 0) (ι 3) m)) := by
    exact labelEntropy_transport e _ _ _
      (fun σ => permOp_transport_left e _ _ (fun _ _ => rfl) σ)
  have h2 : (labelEntropy (subsystemPerm m ι {2})).submatrix e.symm e.symm =
      goodVROperatorLift ι m (labelEntropy (pairCopyLeft (ι 2) (ι 4) m)) := by
    exact labelEntropy_transport e _ _ _
      (fun σ => permOp_transport_right e _ _ (fun _ _ => rfl) σ)
  have h4 : (labelEntropy (subsystemPerm m ι {4})).submatrix e.symm e.symm =
      goodVROperatorLift ι m (labelEntropy (pairCopyRight (ι 2) (ι 4) m)) := by
    exact labelEntropy_transport e _ _ _
      (fun σ => permOp_transport_right e _ _ (fun _ _ => rfl) σ)
  have h24 : (labelEntropy (subsystemPerm m ι {2, 4})).submatrix e.symm e.symm =
      goodVROperatorLift ι m (labelEntropy (pairCopyBoth (ι 2) (ι 4) m)) := by
    exact labelEntropy_transport e _ _ _
      (fun σ => permOp_transport_right e _ _ (fun _ _ => rfl) σ)
  calc
    _ = goodQCOperatorLift ι m (pairMergeDeficit (ι 0) (ι 3) m) +
        goodVROperatorLift ι m (pairMergeDeficit (ι 2) (ι 4) m) := by
      simp only [DC, DR, submatrix_add, submatrix_sub, Pi.add_apply, Pi.sub_apply,
        h0, h3, h03, h2, h4, h24, pairMergeDeficit, map_add, map_sub]
    _ = _ := by
      exact (add_kronecker _ _ _).symm

/-- The actual sum of the two merge deficits satisfies the arithmetic-mean
polynomial exponential bound on the full density. The middle physical copies
are retained, and the component mass is its literal squared vector norm.
The exponent may be any real number with `2 * a ≤ 1`.

OpenAI, September 24, 2026, `07-comparators.tex`, lines 524–555,
`comparator:merge-moments`. This is the auxiliary arithmetic-mean consequence
of the two paired moment estimates. -/
theorem replicaGoodConfigurationMarginal_exp_sum_mergeDeficit_le (ι : Fin 5 → Type*)
    [∀ f, Fintype (ι f)] [∀ f, DecidableEq (ι f)]
    (Ω : ι 0 × (ι 1 × ι 2) → ℂ) (hΩ : ‖WithLp.toLp 2 Ω‖ = 1)
    (k : ℕ) (B : Finset (Fin k))
    (u : (Fin k → ι 0 × (ι 1 × ι 2)) × ((Fin k → ι 3) × (Fin k → ι 4)) → ℂ)
    (hu : ∀ σ : Equiv.Perm (Fin k),
      (permOp (copyPerm (ι 0 × (ι 1 × ι 2)) k) σ ⊗ₖ
        (permOp (copyPerm (ι 3) k) σ ⊗ₖ permOp (copyPerm (ι 4) k) σ)) *ᵥ u = u)
    (a : ℝ) (ha : 2 * a ≤ 1) :
    let m := Bᶜ.card
    let DC := labelEntropy (subsystemPerm m ι {0}) +
      labelEntropy (subsystemPerm m ι {3}) - labelEntropy (subsystemPerm m ι {0, 3})
    let DR := labelEntropy (subsystemPerm m ι {2}) +
      labelEntropy (subsystemPerm m ι {4}) - labelEntropy (subsystemPerm m ι {2, 4})
    let w := (replicaExcitationProjection Ω k B ⊗ₖ
      (1 : Matrix ((Fin k → ι 3) × (Fin k → ι 4))
        ((Fin k → ι 3) × (Fin k → ι 4)) ℂ)) *ᵥ u
    (replicaGoodConfigurationMarginal ι Ω k B u *
      NormedSpace.exp ((a : ℂ) • (DC + DR))).trace.re ≤
      ((((m + 1) ^ ((Fintype.card (ι 0) * Fintype.card (ι 3)) ^ 2) : ℕ) : ℝ) +
        (((m + 1) ^ ((Fintype.card (ι 2) * Fintype.card (ι 4)) ^ 2) : ℕ) : ℝ)) / 2 *
          ‖WithLp.toLp 2 w‖ ^ 2 := by
  intro m DC DR w
  let : DecidableEq (Fin m → ι 0) := inferInstance
  let : DecidableEq (Fin m → ι 1) := inferInstance
  let : DecidableEq (Fin m → ι 2) := inferInstance
  let : DecidableEq (Fin m → ι 3) := inferInstance
  let : DecidableEq (Fin m → ι 4) := inferInstance
  let : DecidableEq ((Fin m → ι 0) × (Fin m → ι 3)) := inferInstance
  let : DecidableEq ((Fin m → ι 2) × (Fin m → ι 4)) := inferInstance
  let : DecidableEq (((Fin m → ι 0) × (Fin m → ι 3)) ×
    ((Fin m → ι 2) × (Fin m → ι 4))) := inferInstance
  let e := goodPairConfigEquiv ι m
  let N := pairMergeDeficit (ι 0) (ι 3) m ⊗ₖ
      (1 : Matrix ((Fin m → ι 2) × (Fin m → ι 4))
        ((Fin m → ι 2) × (Fin m → ι 4)) ℂ) +
    (1 : Matrix ((Fin m → ι 0) × (Fin m → ι 3))
      ((Fin m → ι 0) × (Fin m → ι 3)) ℂ) ⊗ₖ pairMergeDeficit (ι 2) (ι 4) m
  have he : (NormedSpace.exp ((a : ℂ) • (DC + DR))).submatrix e.symm e.symm =
      NormedSpace.exp ((a : ℂ) • N) ⊗ₖ (1 : Matrix (Fin m → ι 1) (Fin m → ι 1) ℂ) := by
    rw [exp_submatrix]
    simp only [submatrix_smul, Pi.smul_apply]
    rw [sum_merge_transport ι m, ← smul_kronecker]
    exact exp_kronecker_one (n := Fin m → ι 1) ((a : ℂ) • N)
  have hOp : NormedSpace.exp ((a : ℂ) • (DC + DR)) =
      (NormedSpace.exp ((a : ℂ) • N) ⊗ₖ
        (1 : Matrix (Fin m → ι 1) (Fin m → ι 1) ℂ)).submatrix e e := by
    simpa only [submatrix_submatrix, Equiv.symm_comp_self, submatrix_id_id] using
      congrArg (fun M => M.submatrix e e) he
  rw [hOp, trace_good_operator]
  exact replicaGoodPairMarginal_exp_sum_mergeDeficit_le Ω hΩ k B u hu a ha

end Matrix
