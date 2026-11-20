/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Entropy.ConditionalEntropy
import QICLean.Entropy.FiniteProductInformation

/-!
# Entropy inequalities for regions of a pure state

Consequences of subadditivity, strong subadditivity and purity for the regional entropies
`S(R)` of a unit vector on a finite tensor product: the Araki–Lieb inequality
`S(R) ≤ S(R ∪ T) + S(T)` for disjoint regions, the dimension bound
`S(R) ≤ log dim R`, and, on a region `P` of zero entropy, `S(P \ X) = S(X)` for `X ⊆ P`,
additivity `S(X ∪ Y) = S(X) + S(Y)` for `X ⊆ P` and `Y` disjoint from `P`, and
`S(A ∆ P) = S(A)`. No geometry of the sites enters.

Moved from TNLean, `TNLean/Lattice/RegionEntropyInequalities.lean` at commit `e41c3b63`,
restated for `FiniteProduct.entropy` on an arbitrary family of local alphabets; the dimension
bound `|R| log q` there is the identical-site case of `ManyBody.regionEntropy_le_log_card`.

## Main results

* `ManyBody.regionEntropy_le_union_add` — the Araki–Lieb inequality.
* `ManyBody.regionEntropy_le_log_card` — the dimension bound.
* `ManyBody.regionEntropy_sdiff_eq_of_eq_zero`, `ManyBody.regionEntropy_union_eq_of_eq_zero`,
  `ManyBody.regionEntropy_symmDiff_eq_of_eq_zero` — regions of zero entropy.

## References

* OpenAI, *A two-dimensional area law from a global spectral gap*, September 24, 2026,
  Section 2 (`sec:prelim`), `01-preliminaries.tex`, lines 10–25, and the proof of
  Theorem 1.1, `10-geometry.tex`, lines 846–851.
* TNLean note, *A one-dimensional area law and matrix product state approximation from a
  global gap*, `part1_arealaw.tex`, Section 2 (`sec:setting`).
-/

open scoped BigOperators symmDiff

namespace ManyBody

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (β : V → Type*) [∀ v, Fintype (β v)] [∀ v, DecidableEq (β v)]
variable {ψ : EuclideanSpace ℂ ((v : V) → β v)}

/-- **The Araki–Lieb inequality.** For disjoint regions `R` and `T` of a unit vector,
`S(R) ≤ S(R ∪ T) + S(T)`. Two-dimensional area law, `01-preliminaries.tex`, lines 10–25. -/
theorem regionEntropy_le_union_add (hψ : ‖ψ‖ = 1) {R T : Finset V} (hRT : Disjoint R T) :
    ManyBody.regionEntropy ψ R ≤ ManyBody.regionEntropy ψ (R ∪ T) + ManyBody.regionEntropy ψ T := by
  have hdisj : Disjoint (R ∪ T)ᶜ T := disjoint_compl_left_iff.mpr Finset.subset_union_right
  have hRc : Rᶜ = (R ∪ T)ᶜ ∪ T := by
    ext v
    have hv : v ∈ R → v ∉ T := fun hv ↦ Finset.disjoint_left.mp hRT hv
    simp only [Finset.mem_compl, Finset.mem_union, not_or]
    tauto
  calc ManyBody.regionEntropy ψ R = ManyBody.regionEntropy ψ ((R ∪ T)ᶜ ∪ T) := by rw
      [← ManyBody.regionEntropy_compl β ψ R, hRc]
    _ ≤ ManyBody.regionEntropy ψ
        (R ∪ T)ᶜ + ManyBody.regionEntropy ψ T := ManyBody.regionEntropy_union_le β ψ hψ _ _ hdisj
    _ = ManyBody.regionEntropy ψ (R ∪ T) + ManyBody.regionEntropy ψ T := by rw
        [ManyBody.regionEntropy_compl]

/-- **The dimension bound.** The entropy of a region of a unit vector is at most the logarithm
of the dimension of its configuration space. -/
theorem regionEntropy_le_log_card (hψ : ‖ψ‖ = 1) (R : Finset V) :
    ManyBody.regionEntropy ψ R ≤ Real.log (Fintype.card (ManyBody.RegionConfig β R)) :=
  Entropy.vonNeumannEntropy_le_log_card (ManyBody.regionState_posSemidef R ψ)
    (ManyBody.trace_regionState_eq_one hψ (D := R))

/-- Inside a region `P` of zero entropy, complementary subregions have equal entropy:
`S(P \ X) = S(X)` for `X ⊆ P`. Two-dimensional area law, `10-geometry.tex`,
lines 846–851. -/
theorem regionEntropy_sdiff_eq_of_eq_zero (hψ : ‖ψ‖ = 1) {P X : Finset V}
    (hP : ManyBody.regionEntropy ψ P = 0) (hX : X ⊆ P) : ManyBody.regionEntropy ψ (P \ X)
        = ManyBody.regionEntropy ψ X := by
  have h1 := ManyBody.regionEntropy_le_union_add β hψ (Finset.disjoint_sdiff (s := X) (t := P))
  have h2 := ManyBody.regionEntropy_le_union_add β hψ (Finset.sdiff_disjoint (s := X) (t := P))
  rw [Finset.union_sdiff_of_subset hX, hP] at h1
  rw [Finset.sdiff_union_of_subset hX, hP] at h2
  linarith

/-- Across a region `P` of zero entropy the entropy is additive: `S(X ∪ Y) = S(X) + S(Y)` for
`X ⊆ P` and `Y` disjoint from `P`. Two-dimensional area law, `10-geometry.tex`,
lines 846–851. -/
theorem regionEntropy_union_eq_of_eq_zero (hψ : ‖ψ‖ = 1) {P X Y : Finset V}
    (hP : ManyBody.regionEntropy ψ P = 0) (hX : X ⊆ P) (hY : Disjoint Y P) :
    ManyBody.regionEntropy ψ (X ∪ Y) = ManyBody.regionEntropy ψ X + ManyBody.regionEntropy ψ Y := by
  have hXY : Disjoint X Y := (hY.mono_right hX).symm
  have hle := ManyBody.regionEntropy_union_le β ψ hψ X Y hXY
  have hsub := ManyBody.regionEntropy_submodular β ψ P (X ∪ Y)
  have hAL := ManyBody.regionEntropy_le_union_add β hψ hY
  have hi : P ∩ (X ∪ Y) = X := by
    ext v
    have hv : v ∈ Y → v ∉ P := fun h ↦ Finset.disjoint_left.mp hY h
    have hv' : v ∈ X → v ∈ P := fun h ↦ hX h
    simp only [Finset.mem_inter, Finset.mem_union]
    tauto
  have hu : P ∪ (X ∪ Y) = Y ∪ P := by
    rw [← Finset.union_assoc, Finset.union_eq_left.mpr hX, Finset.union_comm]
  rw [hi, hu, hP] at hsub
  rw [hP] at hAL
  linarith

/-- **Flipping a region of zero entropy.** If `S(P) = 0`, then `S(A ∆ P) = S(A)` for every
region `A`. Two-dimensional area law, `10-geometry.tex`, lines 846–851. -/
theorem regionEntropy_symmDiff_eq_of_eq_zero (hψ : ‖ψ‖ = 1) {P : Finset V}
    (hP : ManyBody.regionEntropy ψ P = 0) (A : Finset V) : ManyBody.regionEntropy ψ (A ∆ P)
        = ManyBody.regionEntropy ψ A := by
  have hA : A = (A ∩ P) ∪ (A \ P) := by
    ext v
    simp only [Finset.mem_union, Finset.mem_sdiff, Finset.mem_inter]
    tauto
  have hAP : A ∆ P = (P \ (A ∩ P)) ∪ (A \ P) := by
    ext v
    simp only [Finset.mem_symmDiff, Finset.mem_union, Finset.mem_sdiff, Finset.mem_inter]
    tauto
  have hd : Disjoint (A \ P) P := Finset.sdiff_disjoint
  rw [hAP, ManyBody.regionEntropy_union_eq_of_eq_zero β hψ hP Finset.sdiff_subset hd,
    ManyBody.regionEntropy_sdiff_eq_of_eq_zero β hψ hP Finset.inter_subset_right]
  conv_rhs => rw [hA]
  rw [ManyBody.regionEntropy_union_eq_of_eq_zero β hψ hP Finset.inter_subset_right hd]

end ManyBody
