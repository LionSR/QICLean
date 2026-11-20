/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Entropy.MutualInformationPerturbation
import QICLean.Entropy.ReplicaSwap

/-!
# The entropy comparison of the information reset

Let `Ω` be a unit vector on the sites `V`, `Ψ = Ω ⊗ Ω` the doubled vector on `V ⊕ V`, and
`F_D Ψ` the vector exchanged on a region `D`. If a unitary `U` supported away from the first
copies of two cores `R₀ ⊆ D` and `C₀` disjoint from `D` moves `Ψ` to within `δ` of `F_D Ψ`,
then `I_Ω(R₀ : C₀) ≤ 8 √δ log(e |α|^{|R₀|})`: in `Ψ` the two cores carry the mutual information
of `Ω`, the unitary changes neither reduction, and in `F_D Ψ` they have none. Only the
dimension of the core `R₀` enters.

Moved from TNLean, `TNLean/Lattice/RegionalResetEntropy.lean` at commit `e41c3b63`, restated on
the sites `V ⊕ V`. The support of the unitary is any region of `V ⊕ V` disjoint from the first
copies of the cores; TNLean's unitary on paired sites supported on `S` with `S` disjoint from
`R₀ ∪ C₀` is the case `S ⊔ S`, by `ManyBody.reindex_replicaPairEquiv_mem_supportedOperators_iff`.

## Main results

* `ManyBody.regionMutualInformation_cores_le_of_reset_unitary`.

## References

* OpenAI, *Polynomial PEPS approximation of gapped square-grid ground states*, September 24,
  2026, proof of Lemma 3.3 (`lem:reset`), `02-information.tex`, lines 597–630.
* TNLean note, *A one-dimensional area law and matrix product state approximation from a
  global gap*, `part2a`, lines 419–435.
-/

open Matrix ManyBody

namespace ManyBody

variable {V : Type*} [Fintype V] [DecidableEq V] {α : Type*} [Fintype α] [DecidableEq α]

/-- **The entropy comparison of the information reset.** Let `Ω` be a unit vector, `R₀ ⊆ D`
and `C₀` disjoint from `D`, and let `U` be a unitary supported on a region `S` of the two
replicas disjoint from the first copies of `R₀` and `C₀`, with
`‖U (Ω ⊗ Ω) - F_D (Ω ⊗ Ω)‖ ≤ δ`. Then `I_Ω(R₀ : C₀) ≤ 8 √δ log(e |α|^{|R₀|})`. Polynomial PEPS
approximation, `02-information.tex`, lines 597–630. -/
theorem regionMutualInformation_cores_le_of_reset_unitary
    {Ω : EuclideanSpace ℂ (Config fun _ : V ↦ α)} (hΩ : ‖Ω‖ = 1) {D R₀ C₀ : Finset V}
    (hR₀ : R₀ ⊆ D) (hC₀ : Disjoint C₀ D) {S : Finset (V ⊕ V)}
    (hS : Disjoint S ((R₀ ∪ C₀).disjSum ∅))
    {U : Matrix (Config fun _ : V ⊕ V ↦ α) (Config fun _ : V ⊕ V ↦ α) ℂ}
    (hU : U ∈ unitaryGroup _ ℂ) (hUs : U ∈ supportedOperators (fun _ : V ⊕ V ↦ α) S) {δ : ℝ}
    (hδ : ‖toEuclideanLin U (ManyBody.sumSitesProduct (X := fun _ : V ⊕ V ↦ α) Ω Ω) -
      toEuclideanLin (sitePermOp (replicaSwap D))
          (ManyBody.sumSitesProduct (X := fun _ : V ⊕ V ↦ α) Ω Ω)‖
        ≤ δ) :
    ManyBody.regionMutualInformation Ω R₀ C₀ ≤
      8 * √δ * Real.log (Real.exp 1 * (Fintype.card α : ℝ) ^ R₀.card) := by
  set Ψ := ManyBody.sumSitesProduct (X := fun _ : V ⊕ V ↦ α) Ω Ω
  have hΨ : ‖Ψ‖ = 1 := by
    rw [ManyBody.norm_sumSitesProduct, hΩ, mul_one]
  have hF : ‖toEuclideanLin (sitePermOp (α := α) (replicaSwap D)) Ψ‖ = 1 := by
    have h := sitePermOp_mulVec_eq_relabelVector (α := α) (replicaSwap D) Ψ
    change ‖WithLp.toLp 2 (sitePermOp _ *ᵥ WithLp.ofLp Ψ)‖ = 1
    rw [h, norm_relabelVector, hΨ]
  have hXJ : Disjoint (R₀.disjSum (∅ : Finset V)) (C₀.disjSum ∅) := by
    refine Finset.disjoint_left.mpr ?_
    rintro (v | v) hv hv'
    · simp only [Finset.inl_mem_disjSum] at hv hv'
      exact Finset.disjoint_left.mp hC₀ hv' (hR₀ hv)
    · simp at hv
  have hS' : Disjoint S (R₀.disjSum (∅ : Finset V) ∪ C₀.disjSum ∅) := by
    have h : R₀.disjSum (∅ : Finset V) ∪ C₀.disjSum ∅ = (R₀ ∪ C₀).disjSum ∅ := by
      ext w
      rcases w with v | v <;> simp
    rwa [h]
  have hprod := ManyBody.regionMutualInformation_replicaSwap_eq_zero (α := α) hΩ hR₀ hC₀
  have hent := ManyBody.regionMutualInformation_le_of_supported_unitary
      (fun _ : V ⊕ V ↦ α) hΨ hF hXJ hS' hUs
    (mem_unitaryGroup_iff'.mp hU) hprod
  rw
      [ManyBody.regionMutualInformation_sumSitesProduct_inl
      (X := fun _ : V ⊕ V ↦ α) hΩ hΩ R₀ C₀] at hent
  have hpos : (1 : ℝ) ≤ Fintype.card (ManyBody.RegionConfig (fun _ : V ⊕ V ↦ α) (R₀.disjSum ∅)) :=
    Nat.one_le_cast.mpr (Fintype.card_pos_iff.mpr
      (Entropy.Matrix.PosSemidef.nonempty_of_trace_eq_one
          (ManyBody.trace_regionState_eq_one hΨ (D := _))))
  have hcard : Fintype.card (ManyBody.RegionConfig (fun _ : V ⊕ V ↦ α) (R₀.disjSum ∅)) =
      Fintype.card α ^ R₀.card := by
    change Fintype.card (R₀.disjSum (∅ : Finset V) → α) = _
    rw [Fintype.card_fun, Fintype.card_coe, Finset.card_disjSum, Finset.card_empty, add_zero]
  rw [hcard] at hent hpos
  push_cast at hent hpos
  have hlog0 : 0 ≤ Real.log (Real.exp 1 * (Fintype.card α : ℝ) ^ R₀.card) :=
    Real.log_nonneg (one_le_mul_of_one_le_of_one_le (Real.one_le_exp zero_le_one) hpos)
  exact hent.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hδ) (by norm_num)) hlog0)

end ManyBody
