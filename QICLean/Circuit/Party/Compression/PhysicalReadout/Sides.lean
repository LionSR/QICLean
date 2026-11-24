/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Circuit.Party.Original.Density
import QICLean.Circuit.Party.Syntax.OwnerMap

/-!
# The two sides of an affected set of parties

The corrected-source decomposition groups the parties twice: the owner map `affectedOwner A`
keeps every party of the affected set `A` and merges the others into the exterior owner `none`,
and the side of an owner (`Option.isSome`) then separates the affected parties (`true`) from
the exterior (`false`). For a system `Z`, the system `affectedSides A Z` over `Bool` is the
result of the two groupings. The configurations of a set of sides are those of the parties on
these sides (`affectedSideEquiv`, `exteriorSideEquiv`, in the shape of the cut of the side
`true`), so the physical system `fun p ↦ Fin (d p)` keeps the product
of the original local dimensions on each side, even when these differ from party to party, and
no discarded dimension enters (`card_affectedSides_true`, `card_affectedSides_false`). For the
physical system with discarded registers `physicalSystem d V`, a set of sides is read as its
physical configuration and the configuration of its discarded registers
(`affectedSideReadout`, `exteriorSideReadout`).

## Main definitions

* `QuantumCircuit.Party.affectedSides`, `QuantumCircuit.Party.affectedSideEquiv`,
  `QuantumCircuit.Party.exteriorSideEquiv`.
* `QuantumCircuit.Party.affectedSideReadout`, `QuantumCircuit.Party.exteriorSideReadout` and
  their equivalences.

## Main results

* `QuantumCircuit.Party.card_affectedSides_true`, `QuantumCircuit.Party.card_affectedSides_false`.
* `QuantumCircuit.Party.norm_affectedSideReadout_le_one`,
  `QuantumCircuit.Party.toEuclideanLin_affectedSideReadout_apply` and the exterior forms.

## References

* Polynomial-PEPS manuscript (September 24, 2026), Theorem 5.2, `04-compression.tex`,
  lines 137–151, 342–381 and 409–450.
-/

noncomputable section

open Matrix ManyBody
open scoped Matrix.Norms.L2Operator

namespace QuantumCircuit.Party

variable {P : Type} [Fintype P] [DecidableEq P]

omit [Fintype P] in
/-- The system over the two sides of the affected parties of `A`: the blocks of the owner map
`affectedOwner A`, grouped by their side `Option.isSome`. Source: Theorem 5.2,
`04-compression.tex`, lines 342–364 and 409–450. -/
abbrev affectedSides (A : P → Bool) (Z : P → Type) : Bool → Type :=
  blockSystem (fun o : Option {p // A p = true} ↦ o.isSome) (blockSystem (affectedOwner A) Z)

/-- A configuration of the affected side (`true`) is a configuration of the affected parties.
Source: Theorem 5.2, `04-compression.tex`, lines 342–364 and 409–450. -/
def affectedSideEquiv (A : Finset P) (Z : P → Type) :
    RegionConfig (affectedSides (fun p ↦ decide (p ∈ A)) Z) {true} ≃ RegionConfig Z A :=
  (blockRegionConfigEquiv _ _ _).trans ((blockRegionConfigEquiv _ _ _).trans
    (Equiv.piCongrLeft' (fun p : {p // p ∈ blockPreimage (affectedOwner fun p ↦ decide (p ∈ A))
        (blockPreimage (fun o : Option {p // decide (p ∈ A) = true} ↦ o.isSome) {true})} ↦ Z p)
      (Equiv.subtypeEquivRight fun p ↦ by simp)))

/-- The configuration of an affected party, read from the configuration of the affected side. -/
@[simp] theorem affectedSideEquiv_apply (A : Finset P) (Z : P → Type)
    (z : RegionConfig (affectedSides (fun p ↦ decide (p ∈ A)) Z) {true}) (p : {p // p ∈ A}) :
    affectedSideEquiv A Z z p =
      z ⟨(affectedOwner (fun p ↦ decide (p ∈ A)) p).isSome, by simp⟩
        ⟨affectedOwner (fun p ↦ decide (p ∈ A)) p, by simp⟩ ⟨p, by simp⟩ :=
  rfl

/-- A configuration of the exterior side (`false`) is a configuration of the parties outside the
affected set. Source: Theorem 5.2, `04-compression.tex`, lines 342–364 and 409–450. -/
def exteriorSideEquiv (A : Finset P) (Z : P → Type) :
    ComplConfig (affectedSides (fun p ↦ decide (p ∈ A)) Z) {true} ≃ ComplConfig Z A :=
  (complementEquiv _ _).trans ((blockRegionConfigEquiv _ _ _).trans
    ((blockRegionConfigEquiv _ _ _).trans
      (Equiv.piCongrLeft' (fun p : {p // p ∈ blockPreimage (affectedOwner fun p ↦ decide (p ∈ A))
          (blockPreimage (fun o : Option {p // decide (p ∈ A) = true} ↦ o.isSome)
            ({true} : Finset Bool)ᶜ)} ↦ Z p)
        (Equiv.subtypeEquivRight fun p ↦ by simp))))

/-- The physical configurations of the affected side after both groupings are the product of
the original local dimensions of the affected parties. Source: Theorem 5.2,
`04-compression.tex`, lines 137–151 and 356–381. -/
theorem card_affectedSides_true (d : P → ℕ) (A : Finset P) :
    Fintype.card (RegionConfig (affectedSides (fun p ↦ decide (p ∈ A)) fun p ↦ Fin (d p))
      {true}) = ∏ p ∈ A, d p := by
  rw [Fintype.card_congr (affectedSideEquiv A _), card_regionConfig_fin]

/-- The physical configurations of the exterior side after both groupings are the product of
the original local dimensions outside the affected set; no discarded dimension enters. Source:
Theorem 5.2, `04-compression.tex`, lines 137–151 and 356–381. -/
theorem card_affectedSides_false (d : P → ℕ) (A : Finset P) :
    Fintype.card (ComplConfig (affectedSides (fun p ↦ decide (p ∈ A)) fun p ↦ Fin (d p))
      {true}) = ∏ p ∈ Aᶜ, d p := by
  rw [Fintype.card_congr ((exteriorSideEquiv A _).trans (complementEquiv _ _)),
    card_regionConfig_fin]

section Readout

variable (d : P → ℕ) (V : P → Type) [∀ p, Fintype (V p)] [∀ p, DecidableEq (V p)]

/-- The configurations of the affected side of the physical system with discarded registers: the
physical configuration of the affected parties and the configuration of their discarded
registers. Source: Theorem 5.2, `04-compression.tex`, lines 148–150, 419–431 and 445–448. -/
def affectedSideReadoutEquiv (A : Finset P) :
    RegionConfig (affectedSides (fun p ↦ decide (p ∈ A)) (physicalSystem d V)) {true} ≃
      RegionConfig (fun p ↦ Fin (d p)) A × RegionConfig V A :=
  (affectedSideEquiv A _).trans (Equiv.arrowProdEquivProdArrow _ _ _)

/-- The configurations of the exterior side of the physical system with discarded registers.
Source: Theorem 5.2, `04-compression.tex`, lines 148–150, 419–431 and 445–448. -/
def exteriorSideReadoutEquiv (A : Finset P) :
    ComplConfig (affectedSides (fun p ↦ decide (p ∈ A)) (physicalSystem d V)) {true} ≃
      ComplConfig (fun p ↦ Fin (d p)) A × ComplConfig V A :=
  (exteriorSideEquiv A _).trans (Equiv.arrowProdEquivProdArrow _ _ _)

/-- The readout of the affected side of the physical system with discarded registers: the
physical configuration of the affected parties, their discarded registers forming the discarded
factor. Source: Theorem 5.2, `04-compression.tex`, lines 148–150, 419–431 and 445–448. -/
def affectedSideReadout (A : Finset P) :
    Matrix (RegionConfig (fun p ↦ Fin (d p)) A × RegionConfig V A)
      (RegionConfig (affectedSides (fun p ↦ decide (p ∈ A)) (physicalSystem d V)) {true}) ℂ :=
  (affectedSideReadoutEquiv d V A).symm.toPEquiv.toMatrix

/-- The readout of the exterior side of the physical system with discarded registers. Source:
Theorem 5.2, `04-compression.tex`, lines 148–150, 419–431 and 445–448. -/
def exteriorSideReadout (A : Finset P) :
    Matrix (ComplConfig (fun p ↦ Fin (d p)) A × ComplConfig V A)
      (ComplConfig (affectedSides (fun p ↦ decide (p ∈ A)) (physicalSystem d V)) {true}) ℂ :=
  (exteriorSideReadoutEquiv d V A).symm.toPEquiv.toMatrix

/-- The affected side readout is a contraction. -/
theorem norm_affectedSideReadout_le_one (A : Finset P) : ‖affectedSideReadout d V A‖ ≤ 1 :=
  l2_opNorm_toMatrix_toPEquiv_le _

/-- The exterior side readout is a contraction. -/
theorem norm_exteriorSideReadout_le_one (A : Finset P) : ‖exteriorSideReadout d V A‖ ≤ 1 :=
  l2_opNorm_toMatrix_toPEquiv_le _

/-- The affected side readout reads a vector at the side configuration of the physical and
discarded configurations. -/
theorem toEuclideanLin_affectedSideReadout_apply (A : Finset P)
    (x : EuclideanSpace ℂ
      (RegionConfig (affectedSides (fun p ↦ decide (p ∈ A)) (physicalSystem d V)) {true}))
    (s : RegionConfig (fun p ↦ Fin (d p)) A) (i : RegionConfig V A) :
    Matrix.toEuclideanLin (affectedSideReadout d V A) x (s, i) =
      x ((affectedSideReadoutEquiv d V A).symm (s, i)) := by
  change (affectedSideReadout d V A *ᵥ x.ofLp) (s, i) = _
  simp only [affectedSideReadout, PEquiv.toMatrix_toPEquiv_mulVec, Function.comp_apply]

/-- The exterior side readout reads a vector at the side configuration of the physical and
discarded configurations. -/
theorem toEuclideanLin_exteriorSideReadout_apply (A : Finset P)
    (x : EuclideanSpace ℂ
      (ComplConfig (affectedSides (fun p ↦ decide (p ∈ A)) (physicalSystem d V)) {true}))
    (s : ComplConfig (fun p ↦ Fin (d p)) A) (i : ComplConfig V A) :
    Matrix.toEuclideanLin (exteriorSideReadout d V A) x (s, i) =
      x ((exteriorSideReadoutEquiv d V A).symm (s, i)) := by
  change (exteriorSideReadout d V A *ᵥ x.ofLp) (s, i) = _
  simp only [exteriorSideReadout, PEquiv.toMatrix_toPEquiv_mulVec, Function.comp_apply]

end Readout

end QuantumCircuit.Party
