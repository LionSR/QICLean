/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Circuit.Party.Compression.CorrectedSources.Partition
import QICLean.Circuit.Party.Compression.SourceReplacement.CorrectedTerm
import QICLean.Circuit.Party.Original.Density
import QICLean.Channel.Schmidt.Decomposition

/-!
# Schmidt frames of the product of crossing sources

The corrected sources determine a set of affected parties. An exact source is
crossing when its endpoints lie on opposite sides of that set. Each crossing slot
contributes one basis to each side. Read the product of the crossing vectors in
the two product bases. Its norm is one, so its squared Schmidt coefficients are
probability weights.

Source: polynomial-PEPS, Theorem 5.2, `04-compression.tex`, lines 409–434.
Adapted from TNLean, `TNLean/Lattice/Compression/SourceInputPartition.lean` at
`2417e0a2e4d8a1dc2db0a14e0c9cae4ca735829e`, using the actual slot bases.
-/

open Matrix ManyBody
open scoped ComplexConjugate

namespace QuantumCircuit.Party.SourceCircuit

variable {P : Type} [DecidableEq P] {X Y : P → Type}

/-- The retained slots whose endpoints belong to opposite sides of the affected set: the exact
crossing sources. Source: Theorem 5.2, `04-compression.tex`, lines 409–416. -/
noncomputable def crossingSlots (w : SourceCircuit X Y) (S : Finset w.sourceLocations) :
    Finset (Fin (partialSlots (correctedMask w S) w).length) :=
  Finset.univ.filter fun i ↦
    let e := (partialSlotEquiv (correctedMask w S) w i).1
    correctedMask w S (w.endpoints e).1 ≠ correctedMask w S (w.endpoints e).2

/-- A free slot is either a slot of a corrected source or a crossing slot. -/
theorem correctedFreeSlots_eq_true_iff_mem_union (w : SourceCircuit X Y)
    (S : Finset w.sourceLocations) (i : Fin (partialSlots (correctedMask w S) w).length) :
    correctedFreeSlots w S i = true ↔
      i ∈ selectedPartialSlots (correctedMask w S) w S ∪ w.crossingSlots S := by
  classical
  rw [correctedFreeSlots_eq_true_iff, Finset.mem_union, mem_selectedPartialSlots]
  simp [crossingSlots]

/-- Each corrected source has both endpoints affected, so its slot is disjoint
from the set of crossing slots. -/
theorem disjoint_selectedPartialSlots_crossingSlots (w : SourceCircuit X Y)
    (S : Finset w.sourceLocations) :
    Disjoint (selectedPartialSlots (correctedMask w S) w S) (w.crossingSlots S) := by
  classical
  refine Finset.disjoint_left.mpr fun i hi hc ↦ ?_
  let e := (partialSlotEquiv (correctedMask w S) w i).1
  have he : e ∈ S := (mem_selectedPartialSlots _ _ _ _).mp hi
  have hleft : correctedMask w S (w.endpoints e).1 = true := by
    simp only [correctedMask, decide_eq_true_eq, GateIncidence.mem_correctedParties]
    exact ⟨e, he, Or.inl rfl⟩
  have hright : correctedMask w S (w.endpoints e).2 = true := by
    simp only [correctedMask, decide_eq_true_eq, GateIncidence.mem_correctedParties]
    exact ⟨e, he, Or.inr rfl⟩
  exact (Finset.mem_filter.mp hc).2 (hleft.trans hright.symm)

/-- The basis on the indicated side of one crossing slot; the side `true` is the affected side.
Source: `04-compression.tex`, lines 409–420. -/
noncomputable def crossingSlotBasis (w : SourceCircuit X Y) (S : Finset w.sourceLocations)
    (i : w.crossingSlots S) (side : Bool) : Type :=
  if correctedMask w S (w.endpoints (partialSlotEquiv (correctedMask w S) w i).1).1 = side then
    (partialSlotBases (correctedMask w S) w).left i
  else (partialSlotBases (correctedMask w S) w).right i

/-- The basis on either side of a crossing slot is finite. -/
noncomputable instance (w : SourceCircuit X Y) (S : Finset w.sourceLocations)
    (i : w.crossingSlots S) (side : Bool) : Fintype (w.crossingSlotBasis S i side) := by
  unfold crossingSlotBasis
  split_ifs <;> infer_instance

/-- The basis on either side of a crossing slot has decidable equality. -/
noncomputable instance (w : SourceCircuit X Y) (S : Finset w.sourceLocations)
    (i : w.crossingSlots S) (side : Bool) : DecidableEq (w.crossingSlotBasis S i side) := by
  unfold crossingSlotBasis
  split_ifs <;> infer_instance

/-- The two endpoint bases in the order affected, exterior: the identity when the left
endpoint is affected, the exchange of the two factors otherwise. -/
noncomputable def crossingSlotEquiv (w : SourceCircuit X Y) (S : Finset w.sourceLocations)
    (i : w.crossingSlots S) :
    ((partialSlotBases (correctedMask w S) w).left i ×
      (partialSlotBases (correctedMask w S) w).right i) ≃
        w.crossingSlotBasis S i true × w.crossingSlotBasis S i false :=
  if h : correctedMask w S (w.endpoints (partialSlotEquiv (correctedMask w S) w i).1).1 = true
  then
    (Equiv.cast (by simp [crossingSlotBasis, h])).prodCongr
      (Equiv.cast (by simp [crossingSlotBasis, h]))
  else
    (Equiv.prodComm _ _).trans
      ((Equiv.cast (by simp [crossingSlotBasis, h])).prodCongr
        (Equiv.cast (by simp [crossingSlotBasis, h])))

/-- When the left endpoint of a crossing slot is affected, its affected coordinate is the left
one and its exterior coordinate the right one. -/
theorem crossingSlotEquiv_apply_of_left (w : SourceCircuit X Y) (S : Finset w.sourceLocations)
    (i : w.crossingSlots S)
    (h : correctedMask w S (w.endpoints (partialSlotEquiv (correctedMask w S) w i).1).1 = true)
    (x : (partialSlotBases (correctedMask w S) w).left i ×
      (partialSlotBases (correctedMask w S) w).right i) :
    w.crossingSlotEquiv S i x =
      (cast (by simp [crossingSlotBasis, h]) x.1, cast (by simp [crossingSlotBasis, h]) x.2) := by
  simp only [crossingSlotEquiv, h, ↓reduceDIte]
  rfl

/-- When the left endpoint of a crossing slot is not affected, its affected coordinate is the
right one and its exterior coordinate the left one. -/
theorem crossingSlotEquiv_apply_of_right (w : SourceCircuit X Y) (S : Finset w.sourceLocations)
    (i : w.crossingSlots S)
    (h : ¬correctedMask w S (w.endpoints (partialSlotEquiv (correctedMask w S) w i).1).1 = true)
    (x : (partialSlotBases (correctedMask w S) w).left i ×
      (partialSlotBases (correctedMask w S) w).right i) :
    w.crossingSlotEquiv S i x =
      (cast (by simp [crossingSlotBasis, h]) x.2, cast (by simp [crossingSlotBasis, h]) x.1) := by
  simp only [crossingSlotEquiv, h]
  rfl

/-- The product of exact crossing sources in the two groups of configuration coordinates, the
affected side first. Source: `04-compression.tex`, lines 409–420. -/
noncomputable def sourceCrossingVector (w : SourceCircuit X Y) (S : Finset w.sourceLocations)
    (ξ : Choices (correctedMask w S) w) :
    EuclideanSpace ℂ ((∀ i : w.crossingSlots S, w.crossingSlotBasis S i true) ×
      (∀ i : w.crossingSlots S, w.crossingSlotBasis S i false)) :=
  let e := ((Equiv.piCongrRight (w.crossingSlotEquiv S)).trans
    (Equiv.arrowProdEquivProdArrow _ _ _))
  LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e
    (WithLp.toLp 2 (productVector fun i (x : (partialSlotBases (correctedMask w S) w).left i ×
      (partialSlotBases (correctedMask w S) w).right i) ↦
        partialSlotVector (correctedMask w S) w ξ i x))

/-- The product of the exact crossing sources has norm one, including for an empty set of
crossings. -/
theorem norm_sourceCrossingVector (w : SourceCircuit X Y) (S : Finset w.sourceLocations)
    (ξ : Choices (correctedMask w S) w) : ‖w.sourceCrossingVector S ξ‖ = 1 := by
  rw [sourceCrossingVector, LinearIsometryEquiv.norm_map]
  exact norm_toLp_productVector_eq_one
    (fun i : w.crossingSlots S ↦ partialSlotVector (correctedMask w S) w ξ i)
    (fun i ↦ norm_partialSlotVector (correctedMask w S) w ξ i)

/-- The exact crossing sources have a probability Schmidt expansion in the actual
affected and exterior product bases. The weights are the `τ` of the source and the columns of the
two frames its affected-side Schmidt basis `t` and the exterior one, in configuration
coordinates; both frames are isometries. Source: Theorem 5.2, `04-compression.tex`,
lines 409–425. -/
theorem exists_sourceCrossing_schmidt (w : SourceCircuit X Y) (S : Finset w.sourceLocations)
    (ξ : Choices (correctedMask w S) w) :
    let L := ∀ i : w.crossingSlots S, w.crossingSlotBasis S i true
    let R := ∀ i : w.crossingSlots S, w.crossingSlotBasis S i false
    let n := min (Fintype.card L) (Fintype.card R)
    ∃ (lam : Fin n → ℝ) (F : Matrix L (Fin n) ℂ) (G : Matrix R (Fin n) ℂ),
      (∀ j, 0 ≤ lam j) ∧ ∑ j, lam j = 1 ∧ Fᴴ * F = 1 ∧ Gᴴ * G = 1 ∧
        schmidtFrameVector lam F G = (w.sourceCrossingVector S ξ).ofLp :=
  exists_schmidtFrames_of_norm_eq_one _ (w.norm_sourceCrossingVector S ξ)

end QuantumCircuit.Party.SourceCircuit
