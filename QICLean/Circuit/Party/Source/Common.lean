/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Circuit.Party.Source.Preparation
import QICLean.Algebra.Matrix.DependentBlockDiagonal
import QICLean.Analysis.Isometry.FramePerturbation

/-!
# Common slot bases for a finite family of source inventories

For each endpoint of a source slot, the disjoint union `Σ ξ, α ξ` of the bases of a finite
family of branches is a common basis; the coordinate inclusion of `α ξ` into `Σ ξ, α ξ`
(`Matrix.sigmaBlockInclusion`) is an isometry and its adjoint, the coordinate projection, a
contraction (`commonProjection`). Including both halves of a source keeps its norm, and the
projections recover it (`commonVector`). With these common bases every branch inventory on a fixed
sequence of slots is recovered from one preparation in a fixed system (`prepareSlots`,
`common_ofSlots_expands`, `exists_common_expansions`).

## Main definitions

* `QuantumCircuit.Party.PairSource.commonBasis`, `QuantumCircuit.Party.PairSource.commonProjection`,
  `QuantumCircuit.Party.PairSource.commonVector` — the common bases and the included sources.
* `QuantumCircuit.Party.SourceInventory.slotSystem`,
  `QuantumCircuit.Party.SourceInventory.prepareSlots` — preparation in a fixed slot system.

## Main results

* `QuantumCircuit.Party.SourceInventory.ofSlots_pairMap_expands` — contractions in every slot.
* `QuantumCircuit.Party.SourceInventory.common_ofSlots_expands`,
  `QuantumCircuit.Party.SourceInventory.exists_common_expansions` — common slot bases recover
  every branch.
* `QuantumCircuit.Party.SourceInventory.exists_prepareSlots_recovery`,
  `QuantumCircuit.Party.SourceInventory.exists_prepareSlots_expands` — the recoveries on the
  slot system.

## References

* Polynomial-PEPS manuscript (September 24, 2026), Theorem 5.2, `04-compression.tex`, common
  private slot spaces, lines 253–267.
-/

open Matrix ManyBody
open scoped Kronecker Matrix.Norms.L2Operator

namespace QuantumCircuit.Party

variable {P : Type}

/-! ### Common bases -/

namespace PairSource

variable {ι : Type} [Fintype ι] [DecidableEq ι] (α : ι → Type) [∀ ξ, Fintype (α ξ)]
  [∀ ξ, DecidableEq (α ξ)]

/-- The common basis at one endpoint: the disjoint union of the branch bases. Source: Theorem 5.2,
`04-compression.tex`, lines 253–267. -/
abbrev commonBasis : Type := Σ ξ, α ξ

/-- The coordinate projection onto one branch basis, the adjoint of the isometric inclusion
`Matrix.sigmaBlockInclusion α ξ` of the branch basis into the common basis. Source:
`04-compression.tex`, lines 253–267. -/
def commonProjection (ξ : ι) : Matrix (α ξ) (commonBasis α) ℂ :=
  fun x z ↦ if z = ⟨ξ, x⟩ then 1 else 0

/-- The projection is the adjoint of the inclusion. -/
theorem commonProjection_eq_conjTranspose (ξ : ι) :
    commonProjection α ξ = (Matrix.sigmaBlockInclusion α ξ)ᴴ := by
  ext x z
  simp [commonProjection, Matrix.sigmaBlockInclusion, conjTranspose_apply, apply_ite star]

/-- Projecting the included branch recovers it. Source: `04-compression.tex`, lines 260–267. -/
@[simp] theorem commonProjection_mul_sigmaBlockInclusion (ξ : ι) :
    commonProjection α ξ * Matrix.sigmaBlockInclusion α ξ = 1 := by
  rw [commonProjection_eq_conjTranspose, Matrix.sigmaBlockInclusion_isometry]

/-- Every coordinate projection is a contraction, including on an empty branch basis.
Source: `04-compression.tex`, lines 260–267. -/
theorem norm_commonProjection_le (ξ : ι) : ‖commonProjection α ξ‖ ≤ 1 := by
  rw [commonProjection_eq_conjTranspose, l2_opNorm_conjTranspose]
  exact l2_opNorm_le_one_of_conjTranspose_mul_self_eq_one (Matrix.sigmaBlockInclusion_isometry α ξ)

variable (β : ι → Type) [∀ ξ, Fintype (β ξ)] [∀ ξ, DecidableEq (β ξ)]

/-- A branch source included into the common bases at its two endpoints.
Source: `04-compression.tex`, lines 253–267. -/
noncomputable def commonVector (η : ∀ ξ, EuclideanSpace ℂ (α ξ × β ξ)) (ξ : ι) :
    EuclideanSpace ℂ (commonBasis α × commonBasis β) :=
  EuclideanSpace.pairMap (Matrix.sigmaBlockInclusion α ξ) (Matrix.sigmaBlockInclusion β ξ) (η ξ)

/-- Projecting both halves of the included source recovers it. Source: `04-compression.tex`, lines
260–267. -/
@[simp] theorem pairMap_commonProjection_commonVector
    (η : ∀ ξ, EuclideanSpace ℂ (α ξ × β ξ)) (ξ : ι) :
    EuclideanSpace.pairMap (commonProjection α ξ) (commonProjection β ξ) (commonVector α β η ξ) =
      η ξ := by
  simp only [commonVector, EuclideanSpace.pairMap, mulVec_mulVec, ← mul_kronecker_mul,
    commonProjection_mul_sigmaBlockInclusion, one_kronecker_one, one_mulVec]

/-- Including into the common bases keeps the norm. Source: `04-compression.tex`, lines 253–260. -/
@[simp] theorem norm_commonVector (η : ∀ ξ, EuclideanSpace ℂ (α ξ × β ξ)) (ξ : ι) :
    ‖commonVector α β η ξ‖ = ‖η ξ‖ := by
  refine le_antisymm (EuclideanSpace.norm_pairMap_le
    (l2_opNorm_le_one_of_conjTranspose_mul_self_eq_one (Matrix.sigmaBlockInclusion_isometry α ξ))
    (l2_opNorm_le_one_of_conjTranspose_mul_self_eq_one (Matrix.sigmaBlockInclusion_isometry β ξ))
    _) ?_
  calc ‖η ξ‖ = ‖EuclideanSpace.pairMap (commonProjection α ξ) (commonProjection β ξ)
        (commonVector α β η ξ)‖ := by rw [pairMap_commonProjection_commonVector]
    _ ≤ _ := EuclideanSpace.norm_pairMap_le (norm_commonProjection_le α ξ)
      (norm_commonProjection_le β ξ) _

end PairSource

namespace SourceInventory

/-- The common slot bases of a family of slot bases. -/
def SlotBases.common {n : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι] (B : ι → SlotBases n) :
    SlotBases n where
  left i := PairSource.commonBasis fun ξ ↦ (B ξ).left i
  right i := PairSource.commonBasis fun ξ ↦ (B ξ).right i

variable [DecidableEq P]

/-! ### Preparation in a fixed slot system -/

/-- The system after preparing slots with bases `B`, independent of the vectors. Source: Theorem
5.2, `04-compression.tex`, lines 253–267. -/
def slotSystem : (R : SourceInventory P) → SlotBases R.length → (P → Type) → P → Type
  | [], _, X => X
  | r :: R, B, X => addPair (slotSystem R B.tail X) r.distinct (B.left 0) (B.right 0)

/-- The slot system is the system of every slot inventory. -/
theorem system_ofSlots (R : SourceInventory P) (B : SlotBases R.length)
    (η : ∀ i, EuclideanSpace ℂ (B.left i × B.right i)) (X : P → Type) :
    (ofSlots R B η).system X = slotSystem R B X := by
  induction R generalizing X with
  | nil => rfl
  | cons r R ih =>
      rw [ofSlots_cons, system_cons]
      exact congrArg (fun Z ↦ addPair Z r.distinct (B.left 0) (B.right 0))
        (ih B.tail (fun i ↦ η i.succ) X)

/-- The finiteness of the bases of a slot system. -/
@[instance_reducible] def slotSystemFintype : (R : SourceInventory P) →
    (B : SlotBases R.length) → (X : P → Type) → (∀ p, Fintype (X p)) →
      ∀ p, Fintype (slotSystem R B X p)
  | [], _, _, h => h
  | r :: R, B, X, h =>
      letI := slotSystemFintype R B.tail X h
      fun p ↦ inferInstanceAs (Fintype (addPair (slotSystem R B.tail X) r.distinct (B.left 0)
        (B.right 0) p))

/-- The decidable equality of the bases of a slot system. -/
@[instance_reducible] def slotSystemDecidableEq : (R : SourceInventory P) →
    (B : SlotBases R.length) → (X : P → Type) → (∀ p, DecidableEq (X p)) →
      ∀ p, DecidableEq (slotSystem R B X p)
  | [], _, _, h => h
  | r :: R, B, X, h =>
      letI := slotSystemDecidableEq R B.tail X h
      fun p ↦ inferInstanceAs (DecidableEq (addPair (slotSystem R B.tail X) r.distinct
        (B.left 0) (B.right 0) p))

/-- The bases of a slot system are finite. -/
instance (R : SourceInventory P) (B : SlotBases R.length) (X : P → Type)
    [h : ∀ p, Fintype (X p)] (p : P) : Fintype (slotSystem R B X p) :=
  slotSystemFintype R B X h p

/-- The bases of a slot system have decidable equality. -/
instance (R : SourceInventory P) (B : SlotBases R.length) (X : P → Type)
    [h : ∀ p, DecidableEq (X p)] (p : P) : DecidableEq (slotSystem R B X p) :=
  slotSystemDecidableEq R B X h p

/-- Preparation in the fixed slot system. Source: Theorem 5.2,
`04-compression.tex`, lines 253–267. -/
def prepareSlots (R : SourceInventory P) (B : SlotBases R.length)
    (η : ∀ i, EuclideanSpace ℂ (B.left i × B.right i)) (X : P → Type) [∀ p, Fintype (X p)]
    [∀ p, DecidableEq (X p)] : Word X (slotSystem R B X) :=
  match R with
  | [] => PartyCircuit.done X
  | r :: R =>
      (prepareSlots R B.tail (fun i ↦ η i.succ) X).comp
        (Word.sourceAt r.distinct (B.left 0) (B.right 0) (η 0) (slotSystem R B.tail X))

/-- A pair source after heterogeneously equal words on equal systems. -/
theorem heq_comp_sourceAt {X Z Z' : P → Type} [iF : ∀ p, Fintype (Z p)]
    [iD : ∀ p, DecidableEq (Z p)] [iF' : ∀ p, Fintype (Z' p)] [iD' : ∀ p, DecidableEq (Z' p)]
    (e : Z = Z') {a : Word X Z}
    {a' : Word X Z'} (h : HEq a a') {p q : P} (hpq : p ≠ q) (α β : Type) [Fintype α]
    [DecidableEq α] [Fintype β] [DecidableEq β] (η : EuclideanSpace ℂ (α × β)) :
    HEq (a.comp (Word.sourceAt hpq α β η Z)) (a'.comp (Word.sourceAt hpq α β η Z')) := by
  subst e
  obtain rfl := eq_of_heq h
  obtain rfl : iF = iF' := Subsingleton.elim _ _
  obtain rfl : iD = iD' := Subsingleton.elim _ _
  rfl

/-- The slot preparation is the preparation of any inventory equal to the slot inventory. -/
private theorem prepareSlots_heq_aux {X : P → Type} [∀ p, Fintype (X p)]
    [∀ p, DecidableEq (X p)] : (R : SourceInventory P) → (B : SlotBases R.length) →
    (η : ∀ i, EuclideanSpace ℂ (B.left i × B.right i)) → (L : SourceInventory P) →
    L = ofSlots R B η → HEq (prepareSlots R B η X) (L.prepare X)
  | [], _, _, _, hL => by subst hL; rfl
  | r :: R, B, η, _, hL => by
    rw [ofSlots_cons] at hL
    subst hL
    exact heq_comp_sourceAt (system_ofSlots R B.tail (fun i ↦ η i.succ) X).symm
      (prepareSlots_heq_aux R B.tail (fun i ↦ η i.succ) _ rfl) r.distinct _ _ _

variable {X : P → Type} [∀ p, Fintype (X p)] [∀ p, DecidableEq (X p)]

/-- The slot preparation is the preparation of the slot inventory. -/
theorem prepareSlots_heq (R : SourceInventory P) (B : SlotBases R.length)
    (η : ∀ i, EuclideanSpace ℂ (B.left i × B.right i)) :
    HEq (prepareSlots R B η X) ((ofSlots R B η).prepare X) :=
  prepareSlots_heq_aux R B η _ rfl

/-- The sources of the slot preparation are the slot inventory. -/
@[simp] theorem sources_prepareSlots (R : SourceInventory P) (B : SlotBases R.length)
    (η : ∀ i, EuclideanSpace ℂ (B.left i × B.right i)) :
    (prepareSlots R B η X).sources = ofSlots R B η := by
  induction R with
  | nil => rfl
  | cons r R ih =>
      rw [ofSlots_cons]
      exact congrArg (fun l ↦ _ :: l) (ih B.tail (fun i ↦ η i.succ))

variable [Fintype P]

/-- A relabelling along the identification of equal systems carries a word to a heterogeneously
equal one. -/
theorem op_relabel_cast_mul_of_heq {Z Z' : P → Type} [iF : ∀ p, Fintype (Z p)]
    [iD : ∀ p, DecidableEq (Z p)] [iF' : ∀ p, Fintype (Z' p)] [iD' : ∀ p, DecidableEq (Z' p)]
    (e : Z = Z') {a : Word X Z} {a' : Word X Z'} (h : HEq a a') :
    Word.op (PartyCircuit.relabel (G := SourceGate) fun p ↦ Equiv.cast (congrFun e p).symm) *
      a.op = a'.op := by
  subst e
  obtain rfl := eq_of_heq h
  obtain rfl : iF = iF' := Subsingleton.elim _ _
  obtain rfl : iD = iD' := Subsingleton.elim _ _
  simp only [Word.op, PartyCircuit.op_relabel, Equiv.cast_refl,
    Equiv.piCongrRight_refl, Equiv.toPEquiv_refl, PEquiv.toMatrix_refl, Matrix.one_mul]

/-- Applying contractions in each slot recovers the preparation of the transformed vectors,
using only local operations. Source: Theorem 5.2, `04-compression.tex`, lines 253–267. -/
theorem ofSlots_pairMap_expands (R : SourceInventory P) (B B' : SlotBases R.length)
    (f : ∀ i, Matrix (B'.left i) (B.left i) ℂ) (g : ∀ i, Matrix (B'.right i) (B.right i) ℂ)
    (hf : ∀ i, ‖f i‖ ≤ 1) (hg : ∀ i, ‖g i‖ ≤ 1)
    (η : ∀ i, EuclideanSpace ℂ (B.left i × B.right i)) :
    (ofSlots R B η).Expands (ofSlots R B' fun i ↦ EuclideanSpace.pairMap (f i) (g i) (η i)) := by
  induction R with
  | nil => exact Expands.refl _
  | cons r R ih =>
    rw [ofSlots_cons, ofSlots_cons]
    exact (Expands.cons_mapL r _ _ _ _ (f 0) (g 0) (hf 0) (hg 0) (η 0) _).trans
      (Expands.cons _ (ih B.tail B'.tail (fun i ↦ f i.succ) (fun i ↦ g i.succ)
        (fun i ↦ hf i.succ) (fun i ↦ hg i.succ) (fun i ↦ η i.succ)))

/-- Coordinate projections recover every branch preparation from the common slot bases, by
allowed operations containing no sources. Source: `04-compression.tex`,
lines 253–267. -/
theorem common_ofSlots_expands {ι : Type} [Fintype ι] [DecidableEq ι] (R : SourceInventory P)
    (B : ι → SlotBases R.length) (η : ∀ ξ i, EuclideanSpace ℂ ((B ξ).left i × (B ξ).right i))
    (ξ : ι) :
    (ofSlots R (SlotBases.common B)
        (fun i ↦ PairSource.commonVector (fun ζ ↦ (B ζ).left i) (fun ζ ↦ (B ζ).right i)
          (fun ζ ↦ η ζ i) ξ)).Expands (ofSlots R (B ξ) (η ξ)) := by
  have h := ofSlots_pairMap_expands R (SlotBases.common B) (B ξ)
    (fun i ↦ PairSource.commonProjection (fun ζ ↦ (B ζ).left i) ξ)
    (fun i ↦ PairSource.commonProjection (fun ζ ↦ (B ζ).right i) ξ)
    (fun i ↦ PairSource.norm_commonProjection_le _ ξ)
    (fun i ↦ PairSource.norm_commonProjection_le _ ξ)
    (fun i ↦ PairSource.commonVector (fun ζ ↦ (B ζ).left i) (fun ζ ↦ (B ζ).right i)
      (fun ζ ↦ η ζ i) ξ)
  convert h using 2
  funext i
  exact (PairSource.pairMap_commonProjection_commonVector _ _ (fun ζ ↦ η ζ i) ξ).symm

/-- A finite family of normalized inventories with the same distinct pairs has common slot bases and
normalized vectors recovering each original preparation. Source: `04-compression.tex`, lines
253–267. -/
theorem exists_common_expansions {ι : Type} [Finite ι] (R : SourceInventory P)
    (S : ι → SourceInventory P) (hR : (R.map PairSource.partyPair).Nodup)
    (hS : ∀ ξ, (S ξ).IsNormalized) (hN : ∀ ξ, ((S ξ).map PairSource.partyPair).Nodup)
    (hK : ∀ ξ k, k ∈ R.map PairSource.partyPair ↔ k ∈ (S ξ).map PairSource.partyPair) :
    ∃ (B : SlotBases R.length) (η : ι → ∀ i, EuclideanSpace ℂ (B.left i × B.right i)),
      (∀ ξ i, ‖η ξ i‖ = 1) ∧ ∀ ξ, (ofSlots R B (η ξ)).Expands (S ξ) := by
  classical
  let := Fintype.ofFinite ι
  choose B η hη hE using fun ξ ↦ exists_ofSlots_expands R (S ξ) hR (hS ξ) (hN ξ) (hK ξ)
  refine ⟨SlotBases.common B, fun ξ i ↦ PairSource.commonVector (fun ζ ↦ (B ζ).left i)
    (fun ζ ↦ (B ζ).right i) (fun ζ ↦ η ζ i) ξ, ?_, ?_⟩
  · intro ξ i
    exact (PairSource.norm_commonVector _ _ _ _).trans (hη ξ i)
  · intro ξ
    exact (common_ofSlots_expands R B η ξ).trans (hE ξ)

/-- A recovery from the slot inventory acts on the slot system. Source: `04-compression.tex`, lines
260–267. -/
theorem exists_prepareSlots_recovery (R S : SourceInventory P) (B : SlotBases R.length)
    (η : ∀ i, EuclideanSpace ℂ (B.left i × B.right i)) (hE : (ofSlots R B η).Expands S)
    (X : P → Type) [∀ p, Fintype (X p)] [∀ p, DecidableEq (X p)] :
    ∃ d : Word (slotSystem R B X) (S.system X),
      d.IsAllowed ∧ d.sources = [] ∧ d.op * (prepareSlots R B η X).op = (S.prepare X).op := by
  obtain ⟨w, hw, hs, he⟩ := hE X
  refine ⟨(PartyCircuit.relabel fun p ↦
      Equiv.cast (congrFun (system_ofSlots R B η X).symm p).symm).comp w,
    ⟨Word.isAllowed_relabel _, hw⟩, by rw [Word.sources_comp, hs]; rfl, ?_⟩
  rw [Word.op_comp, Matrix.mul_assoc,
    op_relabel_cast_mul_of_heq (system_ofSlots R B η X).symm (prepareSlots_heq R B η), he]

/-- An expansion between two slot inventories on the same pairs gives an allowed recovery
between their slot preparations. Source:
`04-compression.tex`, lines 260–267. -/
theorem exists_prepareSlots_expands (R : SourceInventory P) (B B' : SlotBases R.length)
    (η : ∀ i, EuclideanSpace ℂ (B.left i × B.right i))
    (η' : ∀ i, EuclideanSpace ℂ (B'.left i × B'.right i))
    (hE : (ofSlots R B η).Expands (ofSlots R B' η')) (X : P → Type) [∀ p, Fintype (X p)]
    [∀ p, DecidableEq (X p)] :
    ∃ d : Word (slotSystem R B X) (slotSystem R B' X),
      d.IsAllowed ∧ d.sources = [] ∧
        d.op * (prepareSlots R B η X).op = (prepareSlots R B' η' X).op := by
  obtain ⟨d, hd, hds, hde⟩ := exists_prepareSlots_recovery R _ B η hE X
  refine ⟨d.comp (PartyCircuit.relabel fun p ↦
      Equiv.cast (congrFun (system_ofSlots R B' η' X) p).symm),
    ⟨hd, Word.isAllowed_relabel _⟩, by rw [Word.sources_comp, hds]; rfl, ?_⟩
  rw [Word.op_comp, Matrix.mul_assoc, hde,
    op_relabel_cast_mul_of_heq (system_ofSlots R B' η' X) (prepareSlots_heq R B' η').symm]

end SourceInventory

end QuantumCircuit.Party
