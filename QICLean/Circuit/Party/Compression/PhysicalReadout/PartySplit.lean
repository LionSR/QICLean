/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Circuit.Party.Compression.PhysicalReadout.Sides

/-!
# Readouts that split the register of every party

The output register `Y p` of every party is identified with a physical register of dimension
`d p` and a private register `G p` by an equivalence `e p : Y p ≃ Fin (d p) × G p`. The
*party readout* reads a configuration of `Y` as a physical configuration and a configuration of
the private registers, the second being the discarded factor; for `Y = physicalSystem d G` and
the identity equivalences it is `physicalReadout d G`. For a set `A` of parties, the *regional
party readout* separates both factors further into the parts inside and outside `A`; it is the
party readout followed by a reordering of the physical coordinates and a reordering of the
discarded coordinates, both isometries. The configurations of the two sides of `A`
(`affectedSides`) are read party by party along `e` as well, and the party readout of a
configuration glued from its two sides is the pair of the two side readings.

## Main definitions

* `QuantumCircuit.Party.partyReadoutEquiv`, `QuantumCircuit.Party.partyReadout`.
* `QuantumCircuit.Party.cutMatrix` — the reordering of a configuration into its parts inside
  and outside a set of parties.
* `QuantumCircuit.Party.regionalPartyReadout`.
* `QuantumCircuit.Party.affectedSidePartyEquiv`, `QuantumCircuit.Party.exteriorSidePartyEquiv`.

## Main results

* `QuantumCircuit.Party.partyReadout_refl`, `QuantumCircuit.Party.norm_partyReadout_le_one`.
* `QuantumCircuit.Party.kronecker_toMatrix_mul_partyReadout_mulVec`,
  `QuantumCircuit.Party.regionalPartyReadout_mulVec`.
* `QuantumCircuit.Party.conjTranspose_cutMatrix_mul_self`.
* `QuantumCircuit.Party.exteriorSideEquiv_apply`,
  `QuantumCircuit.Party.partyReadoutEquiv_sideConfig`.

## References

* Polynomial-PEPS manuscript (September 24, 2026), Theorem 5.2, `04-compression.tex`,
  lines 148–150, 356–364 and 419–450.
-/

noncomputable section

open Matrix ManyBody
open scoped Kronecker Matrix.Norms.L2Operator

namespace QuantumCircuit.Party

variable {P : Type} [Fintype P] [DecidableEq P]

section PartyReadout

variable {Y G : P → Type} {d : P → ℕ} (e : ∀ p, Y p ≃ Fin (d p) × G p)

omit [Fintype P] [DecidableEq P] in
/-- A configuration of the registers `Y`, read party by party along `e` as a physical
configuration and a configuration of the private registers. Source: `04-compression.tex`,
lines 148–150. -/
def partyReadoutEquiv : Config Y ≃ Config (fun p ↦ Fin (d p)) × Config G :=
  (Equiv.piCongrRight e).trans (Equiv.arrowProdEquivProdArrow P (fun p ↦ Fin (d p)) G)

omit [Fintype P] [DecidableEq P] in
/-- The two parts of a configuration at a party are the two components of its register. -/
@[simp] theorem partyReadoutEquiv_apply (y : Config Y) :
    partyReadoutEquiv e y = ((fun p ↦ (e p (y p)).1), fun p ↦ (e p (y p)).2) :=
  rfl

variable [∀ p, Fintype (Y p)] [∀ p, DecidableEq (Y p)]

/-- The party readout: the coordinates of `Y` read along `partyReadoutEquiv`, the configuration
of the private registers being the discarded factor. Source: `04-compression.tex`,
lines 148–150. -/
def partyReadout : Matrix (Config (fun p ↦ Fin (d p)) × Config G) (Config Y) ℂ :=
  (partyReadoutEquiv e).symm.toPEquiv.toMatrix

/-- The party readout is a contraction. -/
theorem norm_partyReadout_le_one [∀ p, Fintype (G p)] : ‖partyReadout e‖ ≤ 1 := by
  classical
  exact l2_opNorm_toMatrix_toPEquiv_le _

/-- The party readout reads a vector at the configuration with the given two parts. -/
theorem partyReadout_mulVec (x : Config Y → ℂ) (a : Config (fun p ↦ Fin (d p)) × Config G) :
    (partyReadout e *ᵥ x) a = x ((partyReadoutEquiv e).symm a) := by
  simp only [partyReadout, PEquiv.toMatrix_toPEquiv_mulVec, Function.comp_apply]

/-- The party readout followed by reorderings of the physical and of the discarded coordinates
reads a vector at the configuration with the reordered parts. -/
theorem kronecker_toMatrix_mul_partyReadout_mulVec [∀ p, Fintype (G p)]
    [∀ p, DecidableEq (G p)] {Phys Env : Type}
    (f : Phys ≃ Config fun p ↦ Fin (d p)) (g : Env ≃ Config G) (x : Config Y → ℂ) (a : Phys)
    (b : Env) :
    ((((f.toPEquiv.toMatrix : Matrix Phys _ ℂ) ⊗ₖ (g.toPEquiv.toMatrix : Matrix Env _ ℂ)) *
      partyReadout e) *ᵥ x) (a, b) = x ((partyReadoutEquiv e).symm (f a, g b)) := by
  rw [← mulVec_mulVec, ← toMatrix_toPEquiv_prodCongr f g, PEquiv.toMatrix_toPEquiv_mulVec,
    Function.comp_apply, partyReadout_mulVec]
  rfl

end PartyReadout

omit [DecidableEq P] in
/-- For the physical system with private registers `V` and the identity equivalences, the party
readout is the whole readout `physicalReadout d V`. -/
theorem partyReadout_refl (d : P → ℕ) (V : P → Type) [∀ p, DecidableEq (V p)] :
    partyReadout (Y := physicalSystem d V) (fun _ ↦ Equiv.refl _) = physicalReadout d V :=
  rfl

section Regional

variable (Z : P → Type) (A : Finset P)

omit [Fintype P] in
/-- The reordering of a configuration into its parts inside and outside the set `A` of parties,
as a matrix. Source: `04-compression.tex`, lines 356–364. -/
def cutMatrix [∀ p, DecidableEq (Z p)] :
    Matrix (RegionConfig Z A × ComplConfig Z A) (Config Z) ℂ :=
  (cutEquiv Z A).symm.toPEquiv.toMatrix

/-- The reordering into the parts inside and outside `A` has orthonormal columns. -/
theorem conjTranspose_cutMatrix_mul_self [∀ p, Fintype (Z p)] [∀ p, DecidableEq (Z p)] :
    (cutMatrix Z A)ᴴ * cutMatrix Z A = 1 :=
  conjTranspose_toMatrix_toPEquiv_mul_self _

variable {Y G : P → Type} {d : P → ℕ} (e : ∀ p, Y p ≃ Fin (d p) × G p) [∀ p, Fintype (Y p)]
  [∀ p, DecidableEq (Y p)] [∀ p, Fintype (G p)] [∀ p, DecidableEq (G p)]

/-- The regional party readout: the party readout with the physical and the discarded
coordinates each separated into the parts inside and outside the set `A` of parties. Source:
`04-compression.tex`, lines 356–364 and 419–450. -/
def regionalPartyReadout :
    Matrix ((RegionConfig (fun p ↦ Fin (d p)) A × ComplConfig (fun p ↦ Fin (d p)) A) ×
      (RegionConfig G A × ComplConfig G A)) (Config Y) ℂ :=
  (cutMatrix (fun p ↦ Fin (d p)) A ⊗ₖ cutMatrix G A) * partyReadout e

/-- The regional party readout reads a vector at the configuration with the given four
parts. -/
theorem regionalPartyReadout_mulVec (x : Config Y → ℂ)
    (s : RegionConfig (fun p ↦ Fin (d p)) A × ComplConfig (fun p ↦ Fin (d p)) A)
    (g : RegionConfig G A × ComplConfig G A) :
    (regionalPartyReadout A e *ᵥ x) (s, g) =
      x ((partyReadoutEquiv e).symm
        ((cutEquiv (fun p ↦ Fin (d p)) A).symm s, (cutEquiv G A).symm g)) :=
  kronecker_toMatrix_mul_partyReadout_mulVec e _ _ x s g

end Regional

section Sides

variable (A : Finset P)

/-- The configuration of a party outside the affected set, read from the configuration of the
exterior side. -/
theorem exteriorSideEquiv_apply (Z : P → Type)
    (z : ComplConfig (affectedSides (fun p ↦ decide (p ∈ A)) Z) {true}) (p : {p // p ∉ A}) :
    exteriorSideEquiv A Z z p =
      z ⟨(affectedOwner (fun p ↦ decide (p ∈ A)) p).isSome, by simpa using p.2⟩
        ⟨affectedOwner (fun p ↦ decide (p ∈ A)) p, by simp⟩ ⟨p, by simp⟩ :=
  rfl

variable {Y G : P → Type} {d : P → ℕ} (e : ∀ p, Y p ≃ Fin (d p) × G p)

/-- The configurations of the affected side, read party by party along `e` as the physical
configuration of the affected parties and the configuration of their private registers.
Source: `04-compression.tex`, lines 148–150, 419–431 and 445–448. -/
def affectedSidePartyEquiv :
    RegionConfig (affectedSides (fun p ↦ decide (p ∈ A)) Y) {true} ≃
      RegionConfig (fun p ↦ Fin (d p)) A × RegionConfig G A :=
  (affectedSideEquiv A Y).trans
    ((Equiv.piCongrRight fun p : {p // p ∈ A} ↦ e p).trans
      (Equiv.arrowProdEquivProdArrow {p // p ∈ A} (fun p ↦ Fin (d p)) fun p ↦ G p))

/-- The configurations of the exterior side, read party by party along `e`. Source:
`04-compression.tex`, lines 148–150, 419–431 and 445–448. -/
def exteriorSidePartyEquiv :
    ComplConfig (affectedSides (fun p ↦ decide (p ∈ A)) Y) {true} ≃
      ComplConfig (fun p ↦ Fin (d p)) A × ComplConfig G A :=
  (exteriorSideEquiv A Y).trans
    ((Equiv.piCongrRight fun p : {p // p ∉ A} ↦ e p).trans
      (Equiv.arrowProdEquivProdArrow {p // p ∉ A} (fun p ↦ Fin (d p)) fun p ↦ G p))

/-- **The party readout of a configuration glued from its two sides** has the physical and the
private parts of the two sides as its parts inside and outside `A`. Source:
`04-compression.tex`, lines 419–450. -/
theorem partyReadoutEquiv_sideConfig
    (a : RegionConfig (affectedSides (fun p ↦ decide (p ∈ A)) Y) {true})
    (b : ComplConfig (affectedSides (fun p ↦ decide (p ∈ A)) Y) {true}) :
    partyReadoutEquiv e (blockConfigEquiv (affectedOwner fun p ↦ decide (p ∈ A)) Y
      (blockConfigEquiv (fun o : Option {p // decide (p ∈ A) = true} ↦ o.isSome)
        (blockSystem (affectedOwner fun p ↦ decide (p ∈ A)) Y)
        ((cutEquiv (affectedSides (fun p ↦ decide (p ∈ A)) Y) {true}).symm (a, b)))) =
      ((cutEquiv (fun p ↦ Fin (d p)) A).symm
          ((affectedSidePartyEquiv A e a).1, (exteriorSidePartyEquiv A e b).1),
        (cutEquiv G A).symm
          ((affectedSidePartyEquiv A e a).2, (exteriorSidePartyEquiv A e b).2)) := by
  set T := blockConfigEquiv (affectedOwner fun p ↦ decide (p ∈ A)) Y
    (blockConfigEquiv (fun o : Option {p // decide (p ∈ A) = true} ↦ o.isSome)
      (blockSystem (affectedOwner fun p ↦ decide (p ∈ A)) Y)
      ((cutEquiv (affectedSides (fun p ↦ decide (p ∈ A)) Y) {true}).symm (a, b))) with hTdef
  have hT : ∀ p (hp : p ∈ A), T p = affectedSideEquiv A Y a ⟨p, hp⟩ := fun p hp ↦ by
    rw [affectedSideEquiv_apply]
    change (cutEquiv (affectedSides (fun p ↦ decide (p ∈ A)) Y) {true}).symm (a, b)
      ((affectedOwner (fun p ↦ decide (p ∈ A)) p).isSome)
      ⟨affectedOwner (fun p ↦ decide (p ∈ A)) p, _⟩ ⟨p, _⟩ = _
    rw [cutEquiv_symm_apply_mem a b (by simpa using hp)]
  have hT' : ∀ p (hp : p ∉ A), T p = exteriorSideEquiv A Y b ⟨p, hp⟩ := fun p hp ↦ by
    rw [exteriorSideEquiv_apply]
    change (cutEquiv (affectedSides (fun p ↦ decide (p ∈ A)) Y) {true}).symm (a, b)
      ((affectedOwner (fun p ↦ decide (p ∈ A)) p).isSome)
      ⟨affectedOwner (fun p ↦ decide (p ∈ A)) p, _⟩ ⟨p, _⟩ = _
    rw [cutEquiv_symm_apply_not_mem a b (by simpa using hp)]
  refine Prod.ext (funext fun p ↦ ?_) (funext fun p ↦ ?_)
  · change (e p (T p)).1 = (cutEquiv (fun p ↦ Fin (d p)) A).symm
      ((affectedSidePartyEquiv A e a).1, (exteriorSidePartyEquiv A e b).1) p
    by_cases hp : p ∈ A
    · rw [cutEquiv_symm_apply_mem _ _ hp, hT p hp]
      rfl
    · rw [cutEquiv_symm_apply_not_mem _ _ hp, hT' p hp]
      rfl
  · change (e p (T p)).2 = (cutEquiv G A).symm
      ((affectedSidePartyEquiv A e a).2, (exteriorSidePartyEquiv A e b).2) p
    by_cases hp : p ∈ A
    · rw [cutEquiv_symm_apply_mem _ _ hp, hT p hp]
      rfl
    · rw [cutEquiv_symm_apply_not_mem _ _ hp, hT' p hp]
      rfl

end Sides

end QuantumCircuit.Party
