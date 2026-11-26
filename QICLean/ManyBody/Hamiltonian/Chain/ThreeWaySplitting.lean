/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.ManyBody.Hamiltonian.GroundSpace
import QICLean.ManyBody.Hamiltonian.Models
import QICLean.ManyBody.Hamiltonian.NegativeFrequency

/-!
# The three-way splitting of a chain Hamiltonian at a cut

Fix a cut `j` of the chain of `L` sites, the sites `i < j` lying on its left, and a buffer width
`m`. The terms of an interaction with supports of range `R` are sorted by their supports:

* `H_L` collects the terms supported on the sites `i < j - m`;
* `H_R` collects the terms supported on the sites `i ≥ j + m`;
* `H_B` collects all other terms.

Then `H = H_L + H_B + H_R`. A term of the buffer part meets the sites `≥ j - m` and the sites
`< j + m`, so it lies in the window `[j - m - R, j + m + R)`; there are at most
`2 (m + R) 2^{2R+1}` such terms, so `‖H_B‖ ≤ 2 (m + R) 2^{2R+1} J`. No condition on `m`
relative to `R` is needed: the left and right parts lie at distance at least `m` from the cut.

Each part is then centered, by subtracting its expectation in a vector `Ψ₀`. For a unit
eigenvector of energy `E₀` the centered parts sum to `H - E₀ 1`; when `Ψ₀` is a gapped ground
vector, the centered sum has the same gapped ground vector, at energy zero.

The source splits a Hamiltonian of nearest-neighbour terms `H_{i,i+1}` at the distance `l/3`
from the cut, after shifting the ground energy to zero; here the terms have range `R`, and the
buffer width `m` is arbitrary.

## Main definitions

* `ManyBody.cutLeftSupports`, `ManyBody.cutBufferSupports`, `ManyBody.cutRightSupports` — the
  three classes of supports. The parts `H_L`, `H_B`, `H_R` are the partial Hamiltonians
  `ManyBody.Interaction.partialHamiltonian` of these classes.

## Main results

* `ManyBody.ChainInteraction.hamiltonian_eq_leftPart_add_bufferPart_add_rightPart` —
  `H = H_L + H_B + H_R`.
* `ManyBody.ChainInteraction.centeredObservable_parts_sum_of_eigen` — the centered parts sum to
  `H - E₀ 1` for a unit eigenvector of energy `E₀`.
* `ManyBody.ChainInteraction.isGapped_centeredObservable_parts_sum` — the centered sum has the
  same gapped ground vector, at energy zero.
* `ManyBody.ChainInteraction.isSupportedOn_leftPart`, `isSupportedOn_rightPart`,
  `isSupportedOn_bufferPart` — the supports of the parts.
* `ManyBody.ChainInteraction.norm_bufferPart_le` — `‖H_B‖ ≤ 2 (m + R) 2^{2R+1} J`, linear in the
  buffer width.

## References

* M. B. Hastings, *An area law for one-dimensional quantum systems*, J. Stat. Mech. (2007)
  P08024, arXiv:0705.2024v4, `law16.tex`, lines 82–91 (setting), 246–267 (Lemma 1),
  763–790 (the splitting).

Moved from TNLean, `TNLean/MPS/AreaLaw/ProjectorFactorization/ChainLocalizedParts.lean`,
`TNLean/MPS/AreaLaw/ProjectorFactorization/CutoffPair.lean` at commit `021ba0bd19` (Apache-2.0).
-/

open Matrix
open scoped ComplexOrder Matrix.Norms.L2Operator InnerProductSpace

namespace ManyBody

/-! ### The three classes of supports -/

section Supports

variable {L R : ℕ}

/-- The left supports: those contained in the sites `i < j - m`.
Hastings, arXiv:0705.2024v4, `law16.tex`, line 776 (`H_L`). -/
noncomputable def cutLeftSupports (L R j m : ℕ) : Finset (ChainSupport L R) :=
  Finset.univ.filter fun X ↦ X.1 ⊆ interval L 0 (j - m)

/-- The right supports: those contained in the sites `i ≥ j + m`.
Hastings, arXiv:0705.2024v4, `law16.tex`, line 778 (`H_R`). -/
noncomputable def cutRightSupports (L R j m : ℕ) : Finset (ChainSupport L R) :=
  Finset.univ.filter fun X ↦ X.1 ⊆ interval L (j + m) L

/-- The buffer supports: all supports that are neither left nor right.
Hastings, arXiv:0705.2024v4, `law16.tex`, line 777 (`H_B`). -/
noncomputable def cutBufferSupports (L R j m : ℕ) : Finset (ChainSupport L R) :=
  Finset.univ.filter fun X ↦ ¬X.1 ⊆ interval L 0 (j - m) ∧ ¬X.1 ⊆ interval L (j + m) L

/-- Every sum over the supports splits into the left, buffer and right sums.
Hastings, arXiv:0705.2024v4, `law16.tex`, lines 775–779. -/
theorem sum_eq_cutLeftSupports_add_cutBufferSupports_add_cutRightSupports {M : Type*}
    [AddCommMonoid M] (f : ChainSupport L R → M) (j m : ℕ) :
    ∑ X, f X = ∑ X ∈ cutLeftSupports L R j m, f X + ∑ X ∈ cutBufferSupports L R j m, f X +
      ∑ X ∈ cutRightSupports L R j m, f X := by
  classical
  have hright : cutRightSupports L R j m =
      (Finset.univ.filter fun X : ChainSupport L R ↦ ¬X.1 ⊆ interval L 0 (j - m)).filter
        fun X ↦ X.1 ⊆ interval L (j + m) L := by
    ext X
    simp only [cutRightSupports, Finset.filter_filter, Finset.mem_filter, Finset.mem_univ,
      true_and]
    refine ⟨fun hR ↦ ⟨fun hL ↦ ?_, hR⟩, fun h ↦ h.2⟩
    obtain ⟨x, hx⟩ := X.2.1
    have h1 := mem_interval.mp (hL hx)
    have h2 := mem_interval.mp (hR hx)
    omega
  have hbuffer : cutBufferSupports L R j m =
      (Finset.univ.filter fun X : ChainSupport L R ↦ ¬X.1 ⊆ interval L 0 (j - m)).filter
        fun X ↦ ¬X.1 ⊆ interval L (j + m) L := by
    simp [cutBufferSupports, Finset.filter_filter]
  rw [hright, hbuffer, add_assoc, add_comm (∑ X ∈ Finset.filter _ _ with ¬_, f X),
    Finset.sum_filter_add_sum_filter_not, cutLeftSupports, Finset.sum_filter_add_sum_filter_not]

/-- A buffer support lies in the window `[j - m - R, j + m + R)`.
Hastings, arXiv:0705.2024v4, `law16.tex`, line 777. -/
theorem subset_window_of_mem_cutBufferSupports {j m : ℕ} {X : ChainSupport L R}
    (hX : X ∈ cutBufferSupports L R j m) : X.1 ⊆ interval L (j - m - R) (j + m + R) := by
  obtain ⟨hL, hR⟩ := (Finset.mem_filter.mp hX).2
  obtain ⟨x, hxX, hx⟩ := Finset.not_subset.mp hL
  obtain ⟨y, hyX, hy⟩ := Finset.not_subset.mp hR
  rw [mem_interval] at hx hy
  intro z hz
  have hzy := X.2.2 z hz y hyX
  have hxz := X.2.2 x hxX z hz
  have hyz := X.2.2 y hyX z hz
  have hzx := X.2.2 z hz x hxX
  rw [mem_interval]
  have := y.isLt
  omega

/-- There are at most `2 (m + R) 2^{2R+1}` buffer supports, linearly many in the buffer
width. Hastings, arXiv:0705.2024v4, `law16.tex`, line 777. -/
theorem card_cutBufferSupports_le (j m : ℕ) :
    (cutBufferSupports L R j m).card ≤ 2 * (m + R) * 2 ^ (2 * R + 1) := by
  classical
  let W := interval L (j - m - R) (j + m + R)
  have hcover : cutBufferSupports L R j m ⊆
      W.biUnion fun x ↦ Finset.univ.filter fun X : ChainSupport L R ↦ x ∈ X.1 := by
    intro X hX
    obtain ⟨x, hx⟩ := X.2.1
    exact Finset.mem_biUnion.mpr ⟨x, subset_window_of_mem_cutBufferSupports hX hx,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx⟩⟩
  have hW : W.card ≤ 2 * (m + R) := (card_interval_le _ _).trans (by omega)
  calc (cutBufferSupports L R j m).card
      ≤ ∑ x ∈ W, (Finset.univ.filter fun X : ChainSupport L R ↦ x ∈ X.1).card :=
        (Finset.card_le_card hcover).trans Finset.card_biUnion_le
    _ ≤ W.card * 2 ^ (2 * R + 1) := by
        simpa using Finset.sum_le_card_nsmul W _ _ fun x _ ↦ ChainSupport.card_filter_mem_le x
    _ ≤ 2 * (m + R) * 2 ^ (2 * R + 1) := Nat.mul_le_mul_right _ hW

end Supports

section Splitting

variable {L q R : ℕ} {J : ℝ}

/-! ### The parts `H_L`, `H_B`, `H_R`

The left, buffer and right parts are the partial Hamiltonians
`h.partialHamiltonian (cutLeftSupports L R j m)`,
`h.partialHamiltonian (cutBufferSupports L R j m)` and
`h.partialHamiltonian (cutRightSupports L R j m)` of the three classes of supports.
Hastings, arXiv:0705.2024v4, `law16.tex`, lines 775–778. -/

/-- **The three-way splitting.** `H = H_L + H_B + H_R`.
Hastings, arXiv:0705.2024v4, `law16.tex`, lines 775–779. -/
theorem ChainInteraction.hamiltonian_eq_leftPart_add_bufferPart_add_rightPart
    (h : ChainInteraction L q R) (j m : ℕ) :
    h.hamiltonian = h.partialHamiltonian (cutLeftSupports L R j m) +
      h.partialHamiltonian (cutBufferSupports L R j m) +
        h.partialHamiltonian (cutRightSupports L R j m) :=
  sum_eq_cutLeftSupports_add_cutBufferSupports_add_cutRightSupports h.term j m

/-- The centered parts sum to the centered Hamiltonian `H - ⟨Ψ₀, H Ψ₀⟩ 1`, for every
vector `Ψ₀`. Hastings, arXiv:0705.2024v4, `law16.tex`, lines 779–782. -/
theorem ChainInteraction.centeredObservable_parts_sum
    (h : ChainInteraction L q R) (Ψ : EuclideanSpace ℂ (Fin L → Fin q)) (j m : ℕ) :
    centeredObservable Ψ (h.partialHamiltonian (cutLeftSupports L R j m)) +
        centeredObservable Ψ (h.partialHamiltonian (cutBufferSupports L R j m)) +
      centeredObservable Ψ (h.partialHamiltonian (cutRightSupports L R j m)) =
        centeredObservable Ψ h.hamiltonian := by
  rw [← centeredObservable_add, ← centeredObservable_add,
    h.hamiltonian_eq_leftPart_add_bufferPart_add_rightPart j m]

/-- **The centered splitting.** For a unit eigenvector `Ψ₀` of `H` of energy `E₀`, the
centered parts, each of expectation zero in `Ψ₀`, sum to `H - E₀ 1`. With the source's
convention that the ground energy is zero, this is `H = H_L + H_B + H_R` for the centered
parts. Hastings, arXiv:0705.2024v4, `law16.tex`, lines 766–767 and 779–782. -/
theorem ChainInteraction.centeredObservable_parts_sum_of_eigen
    (h : ChainInteraction L q R)
    {Ψ : EuclideanSpace ℂ (Fin L → Fin q)} (hΨ : ‖Ψ‖ = 1) {E₀ : ℝ}
    (hE : toEuclideanLin h.hamiltonian Ψ = (E₀ : ℂ) • Ψ) (j m : ℕ) :
    centeredObservable Ψ (h.partialHamiltonian (cutLeftSupports L R j m)) +
        centeredObservable Ψ (h.partialHamiltonian (cutBufferSupports L R j m)) +
      centeredObservable Ψ (h.partialHamiltonian (cutRightSupports L R j m)) =
        h.hamiltonian - (E₀ : ℂ) • 1 := by
  rw [← coe_toEuclideanCLM_eq_toEuclideanLin] at hE
  rw [h.centeredObservable_parts_sum,
    centeredObservable_of_apply_eq_smul (norm_pos_iff.mp (by rw [hΨ]; exact one_pos))
      hE]

/-- The centered splitting of a gapped Hamiltonian has the same gapped ground vector, at
energy zero: the normalization of the source.
Hastings, arXiv:0705.2024v4, `law16.tex`, lines 766–767 and 779–782. -/
theorem ChainInteraction.isGapped_centeredObservable_parts_sum
    (h : ChainInteraction L q R) {E₀ Δ : ℝ} {Ω : EuclideanSpace ℂ (Fin L → Fin q)}
    (hΩ : ‖Ω‖ = 1) (hgap : IsGapped h.hamiltonian E₀ Δ)
    (hspan : groundSpace h.hamiltonian E₀ = Submodule.span ℂ {Ω}) (j m : ℕ) :
    ‖Ω‖ = 1 ∧
      IsGapped (centeredObservable Ω (h.partialHamiltonian (cutLeftSupports L R j m)) +
        centeredObservable Ω (h.partialHamiltonian (cutBufferSupports L R j m)) +
          centeredObservable Ω (h.partialHamiltonian (cutRightSupports L R j m))) 0 Δ ∧
      groundSpace
          (centeredObservable Ω (h.partialHamiltonian (cutLeftSupports L R j m)) +
            centeredObservable Ω (h.partialHamiltonian (cutBufferSupports L R j m)) +
              centeredObservable Ω (h.partialHamiltonian (cutRightSupports L R j m))) 0 =
        Submodule.span ℂ {Ω} := by
  have hE : toEuclideanLin h.hamiltonian Ω = (E₀ : ℂ) • Ω :=
    mem_groundSpace_iff.mp (hspan ▸ Submodule.mem_span_singleton_self Ω)
  rw [h.centeredObservable_parts_sum_of_eigen hΩ hE]
  exact ⟨hΩ, hgap.sub_smul_one_self, (groundSpace_sub_smul_one_self _ _).trans hspan⟩

/-- The left part is supported on the sites `i < j - m`, at distance at least `m` from the
cut. Hastings, arXiv:0705.2024v4, `law16.tex`, line 776. -/
theorem ChainInteraction.isSupportedOn_leftPart
    (h : ChainInteraction L q R) (j m : ℕ) :
    IsSupportedOn (X := fun _ ↦ Fin q) (h.partialHamiltonian (cutLeftSupports L R j m))
      (interval L 0 (j - m)) := by
  change _ ∈ supportedOperators _ _
  exact h.partialHamiltonian_mem_supportedOperators fun _ hX ↦ (Finset.mem_filter.mp hX).2

/-- The right part is supported on the sites `i ≥ j + m`, at distance at least `m` from the
cut. Hastings, arXiv:0705.2024v4, `law16.tex`, line 778. -/
theorem ChainInteraction.isSupportedOn_rightPart
    (h : ChainInteraction L q R) (j m : ℕ) :
    IsSupportedOn (X := fun _ ↦ Fin q) (h.partialHamiltonian (cutRightSupports L R j m))
      (interval L (j + m) L) := by
  change _ ∈ supportedOperators _ _
  exact h.partialHamiltonian_mem_supportedOperators fun _ hX ↦ (Finset.mem_filter.mp hX).2

/-- The buffer part is supported on the window `[j - m - R, j + m + R)`.
Hastings, arXiv:0705.2024v4, `law16.tex`, line 777. -/
theorem ChainInteraction.isSupportedOn_bufferPart
    (h : ChainInteraction L q R) (j m : ℕ) :
    IsSupportedOn (X := fun _ ↦ Fin q) (h.partialHamiltonian (cutBufferSupports L R j m))
      (interval L (j - m - R) (j + m + R)) := by
  change _ ∈ supportedOperators _ _
  exact h.partialHamiltonian_mem_supportedOperators fun _ hX ↦
    subset_window_of_mem_cutBufferSupports hX

/-- **The norm of the buffer part.** `‖H_B‖ ≤ 2 (m + R) 2^{2R+1} J`, linear in the buffer
width. Hastings, arXiv:0705.2024v4, `law16.tex`, lines 89–91 and 777. -/
theorem ChainInteraction.norm_bufferPart_le (h : ChainInteraction L q R)
    (hhJ : ∀ X, ‖h.term X‖ ≤ J) (hJ : 0 ≤ J)
    (j m : ℕ) :
    ‖h.partialHamiltonian (cutBufferSupports L R j m)‖ ≤
      (2 * (m + R) * 2 ^ (2 * R + 1) : ℕ) * J :=
  (Interaction.norm_partialHamiltonian_le fun X _ ↦ hhJ X).trans
    (mul_le_mul_of_nonneg_right (by exact_mod_cast card_cutBufferSupports_le j m) hJ)

/-- The centered buffer part has norm at most `4 (m + R) 2^{2R+1} J`.
Hastings, arXiv:0705.2024v4, `law16.tex`, lines 777 and 781–782. -/
theorem ChainInteraction.norm_centeredObservable_bufferPart_le
    (h : ChainInteraction L q R) (hhJ : ∀ X, ‖h.term X‖ ≤ J)
    (hJ : 0 ≤ J) {Ψ : EuclideanSpace ℂ (Fin L → Fin q)} (hΨ : ‖Ψ‖ = 1) (j m : ℕ) :
    ‖centeredObservable Ψ (h.partialHamiltonian (cutBufferSupports L R j m))‖ ≤
      2 * ((2 * (m + R) * 2 ^ (2 * R + 1) : ℕ) * J) :=
  (norm_centeredObservable_le (norm_pos_iff.mp (by rw [hΨ]; exact one_pos)) _).trans
    (mul_le_mul_of_nonneg_left (h.norm_bufferPart_le hhJ hJ j m) (by norm_num))

end Splitting

end ManyBody

section

open ManyBody (ChainSupport card_interval_le interval mem_interval ChainInteraction)

open ManyBody
    (cutLeftSupports cutRightSupports cutBufferSupports cutCommutatorConst graphNeighborhood)

open ManyBody
    (gaussianFilteredTerm regionExpectation isHermitian_regionExpectation isHermitian_gaussianFilteredTerm)

open GaussianFilter Matrix QuantumCircuit

open scoped Matrix.Norms.L2Operator

section


section ChainParts

variable {L q R : ℕ} {J : ℝ}

/-- The left part vanishes when `j ≤ m`: the region `[0, j - m)` is then empty, and no
support, being nonempty, is contained in it.
Hastings, arXiv:0705.2024v4, `law16.tex`, appendix, line 776 (`H_L`). -/
theorem ManyBody.ChainInteraction.leftPart_eq_zero_of_le
    (h : ChainInteraction L q R) {j m : ℕ}
    (hjm : j ≤ m) : h.partialHamiltonian (cutLeftSupports L R j m) = 0 := by
  change ∑ X ∈ cutLeftSupports L R j m, h.term X = 0
  refine Finset.sum_eq_zero fun X hX ↦ ?_
  obtain ⟨x, hx⟩ := X.2.1
  have := mem_interval.mp ((Finset.mem_filter.mp hX).2 hx)
  omega

end ChainParts

end

end

section

open ManyBody (interval mem_interval ChainInteraction)

open ManyBody
    (cutLeftSupports cutRightSupports cutBufferSupports cutCommutatorConst graphNeighborhood)

open ManyBody
    (gaussianFilteredTerm regionExpectation isHermitian_regionExpectation isHermitian_gaussianFilteredTerm)

open GaussianFilter Matrix QuantumCircuit

open ManyBody (IsGapped groundSpace)

open scoped Matrix.Norms.L2Operator InnerProductSpace

section


variable {L q R : ℕ} {J : ℝ}

/-- The centered localized part `M = W + E_K(W_tilde - W)` of a part `P` of the Hamiltonian,
with `W = P - ⟨Ω, P Ω⟩` and `W_tilde` its Gaussian filter of variance `s / ΔE²`.
Hastings, arXiv:0705.2024v4, `law16.tex`, appendix, lines 779–828. -/
noncomputable def ManyBody.ChainInteraction.localizedPart (h : ChainInteraction L q R)
    (Ω : EuclideanSpace ℂ (Fin L → Fin q)) (s ΔE : ℝ) (P : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (K : Finset (Fin L)) : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ :=
  ManyBody.centeredObservable Ω P +
    regionExpectation K (gaussianFilteredTerm s ΔE h.hamiltonian
      (ManyBody.centeredObservable Ω P) - ManyBody.centeredObservable Ω P)

section Localized

variable (h : ChainInteraction L q R) (hh : ∀ X, (h.term X).IsHermitian) (hhJ : ∀ X, ‖h.term X‖ ≤ J)
    (Ω : EuclideanSpace ℂ (Fin L → Fin q))
  (s ΔE : ℝ)

include hh in
/-- Centering does not change `W_tilde - W`. -/
theorem ManyBody.ChainInteraction.gaussianFilteredTerm_centeredObservable_sub
    (P : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ) :
    gaussianFilteredTerm s ΔE h.hamiltonian (ManyBody.centeredObservable Ω P) -
        ManyBody.centeredObservable Ω P =
      gaussianFilteredTerm s ΔE h.hamiltonian P - P := by
  rw [ManyBody.centeredObservable]
  exact ManyBody.gaussianFilteredTerm_sub_smul_one_sub s ΔE
      (ManyBody.Interaction.isHermitian_hamiltonian hh) P _

include hh in
/-- The localization error of the centered part equals that of the part. -/
theorem ManyBody.ChainInteraction.gaussianFilteredTerm_centeredObservable_sub_localizedPart
    (P : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ) (K : Finset (Fin L)) :
    gaussianFilteredTerm s ΔE h.hamiltonian (ManyBody.centeredObservable Ω P) -
        h.localizedPart Ω s ΔE P K =
      gaussianFilteredTerm s ΔE h.hamiltonian P -
        (P + regionExpectation K (gaussianFilteredTerm s ΔE h.hamiltonian P - P)) := by
  set D := gaussianFilteredTerm s ΔE h.hamiltonian (ManyBody.centeredObservable Ω P) -
    ManyBody.centeredObservable Ω P
  calc gaussianFilteredTerm s ΔE h.hamiltonian (ManyBody.centeredObservable Ω P) -
        h.localizedPart Ω s ΔE P K
      = D - regionExpectation K D := by
        rw [ManyBody.ChainInteraction.localizedPart]; simp only [D]; abel
    _ = (gaussianFilteredTerm s ΔE h.hamiltonian P - P) -
          regionExpectation K (gaussianFilteredTerm s ΔE h.hamiltonian P - P) := by
        simp only [D, h.gaussianFilteredTerm_centeredObservable_sub hh Ω s ΔE P]
    _ = _ := by abel

/-- The centered localized part of a part supported on `D` is supported on `D ∪ K`. -/
theorem ManyBody.ChainInteraction.isSupportedOn_localizedPart
    {P : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ} {D : Finset (Fin L)}
    (hP : ManyBody.IsSupportedOn (X := fun _ ↦ Fin q) P D) (K : Finset (Fin L)) :
    ManyBody.IsSupportedOn (X := fun _ ↦ Fin q) (h.localizedPart Ω s ΔE P K) (D ∪ K) := by
  change _ ∈ ManyBody.supportedOperators _ _
  refine (add_mem ?_ ?_)
  · have hW : ManyBody.centeredObservable Ω P ∈ ManyBody.supportedOperators (fun _ ↦ Fin q) D :=
      ManyBody.centeredObservable_mem Ω
        (S := Subalgebra.toSubmodule (ManyBody.supportedOperators (fun _ ↦ Fin q) D).toSubalgebra)
        (one_mem (ManyBody.supportedOperators (fun _ ↦ Fin q) D)) hP
    exact ManyBody.supportedOperators_mono (by simp) hW
  · exact ManyBody.supportedOperators_mono (by simp)
      (ManyBody.regionExpectation_mem_supportedOperators K _)

/-- The centered localized part of `0` is `0`. -/
theorem ManyBody.ChainInteraction.localizedPart_zero (K : Finset (Fin L)) :
    h.localizedPart Ω s ΔE 0 K = 0 := by
  have hG : gaussianFilteredTerm s ΔE h.hamiltonian (0 : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
      = 0 := by
    simp [gaussianFilteredTerm, gaussianIntertwiner]
  rw [ManyBody.ChainInteraction.localizedPart, ManyBody.centeredObservable_zero, hG, sub_zero,
    zero_add, ← ManyBody.regionExpectationLM_apply, map_zero]

include hh in
/-- **The localized part nearly annihilates the ground state.** If `‖[H, P]‖ ≤ c_P` and the
localization error is at most `δ`, then `‖M Ω‖ ≤ ΔE⁻¹ e^{-s/2} c_P + δ`.
Hastings, arXiv:0705.2024v4, `law16.tex`, lines 794–828 (eqs. `tighter`, `tighter2` and the
bound on `|M_L Ψ₀|`). -/
theorem ManyBody.ChainInteraction.norm_localizedPart_apply_le {E₀ : ℝ}
    (hΩ : ‖Ω‖ = 1) (hgap : IsGapped h.hamiltonian E₀ ΔE)
    (hspan : groundSpace h.hamiltonian E₀ = Submodule.span ℂ {Ω}) (hΔ : 0 < ΔE) (hs : 0 ≤ s)
    {P : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ} (K : Finset (Fin L))
    {cP δ : ℝ} (hc : ‖h.hamiltonian * P - P * h.hamiltonian‖ ≤ cP)
    (hδ : ‖gaussianFilteredTerm s ΔE h.hamiltonian P -
      (P + regionExpectation K (gaussianFilteredTerm s ΔE h.hamiltonian P - P))‖ ≤ δ) :
    ‖toEuclideanLin (h.localizedPart Ω s ΔE P K) Ω‖ ≤
      ΔE⁻¹ * Real.exp (-s / 2) * cP + δ := by
  have hop (A : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ) : ‖toEuclideanLin A Ω‖ ≤ ‖A‖ := by
    rw [← coe_toEuclideanCLM_eq_toEuclideanLin, ← l2_opNorm_toEuclideanCLM]
    simpa [hΩ] using (toEuclideanCLM (n := Fin L → Fin q) (𝕜 := ℂ) A).le_opNorm Ω
  set W := ManyBody.centeredObservable Ω P
  set G := gaussianFilteredTerm s ΔE h.hamiltonian W
  have hsplit : h.localizedPart Ω s ΔE P K = G - (G - h.localizedPart Ω s ΔE P K) := by abel
  have hG : ‖toEuclideanLin G Ω‖ ≤ ΔE⁻¹ * Real.exp (-s / 2) * cP := by
    refine (ManyBody.norm_gaussianFilteredTerm_apply_le_commutator_of_isGapped hs hΔ
        (ManyBody.Interaction.isHermitian_hamiltonian hh)
      hgap hspan W (by
        rw [← coe_toEuclideanCLM_eq_toEuclideanLin]
        exact ManyBody.inner_centeredObservable_eq_zero
          (norm_pos_iff.mp (by rw [hΩ]; exact one_pos)) P)).trans ?_
    rw [show h.hamiltonian * W - W * h.hamiltonian = h.hamiltonian * P - P * h.hamiltonian by
      simpa only [neg_sub] using
        congrArg Neg.neg (ManyBody.centeredObservable_commutator Ω P h.hamiltonian)]
    gcongr
    exact (hop _).trans hc
  have hR : ‖toEuclideanLin (G - h.localizedPart Ω s ΔE P K) Ω‖ ≤ δ := by
    refine (hop _).trans ?_
    rw [h.gaussianFilteredTerm_centeredObservable_sub_localizedPart hh]
    exact hδ
  rw [hsplit, map_sub, LinearMap.sub_apply]
  exact (norm_sub_le _ _).trans (add_le_add hG hR)

end Localized

end

end
