/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Circuit.Party.Compression.CorrectedSources.SideCoordinates
import QICLean.Circuit.Party.Compression.CorrectedSources.SideInput
import QICLean.Circuit.Party.Compression.CorrectedSources.SchmidtOutput

/-!
# The output of a branch through two local words

Fix a set `S` of source positions of a source circuit, its affected parties, and a branch of the
partial expansion along them. Substitute columns of Schmidt frames for the vectors of the
corrected sources. Read across the two sides of the affected parties, the vector prepared in the
free slots on a product input is one Schmidt sum, with weights independent of the frame columns:
the corrected frame columns and the affected halves of the exact crossing sources enter on the
affected side, the exterior halves on the exterior side. The output of the branch is therefore
a Schmidt output on the registers of the free sources: the same Schmidt sum with isometric
frames through two allowed source-free local words, one on each side, which contain the
preparation of the input and of the other sources
(`SourceCircuit.hasSchmidtOutput_partialSchmidtOutput`).

The frames `E e ξ`, `F e ξ` of the corrected sources are matrices whose rows are indexed by the
bases `w.leftBasis e`, `w.rightBasis e` of the two registers of the source slot `e` and whose
columns are indexed by the Schmidt index; they have orthonormal columns
(`(E e ξ)ᴴ * E e ξ = 1`), as the source's Schmidt vectors `u_a`, `v_a`.

## Main results

* `QuantumCircuit.Party.SourceCircuit.hasSchmidtOutput_partialSchmidtOutput`.

## References

* Polynomial-PEPS manuscript (September 24, 2026), Theorem 5.2, `04-compression.tex`,
  lines 279–289 and 409–480, `eq:compression-exterior-input`.

-/

open Matrix ManyBody
open scoped Kronecker Matrix.Norms.L2Operator

namespace QuantumCircuit.Party

/-- A configuration glued from its two sides is read on the side `true` from the first part. -/
private theorem blockConfigEquiv_cutEquiv_symm_of_true {V : Type} [Fintype V] (f : V → Bool)
    (Z : V → Type) (a : RegionConfig (blockSystem f Z) {true})
    (e e' : ComplConfig (blockSystem f Z) {true}) {q : V} (hq : f q = true) :
    blockConfigEquiv f Z ((cutEquiv (blockSystem f Z) {true}).symm (a, e)) q =
      blockConfigEquiv f Z ((cutEquiv (blockSystem f Z) {true}).symm (a, e')) q := by
  rw [blockConfigEquiv_apply_of_eq f _ hq, blockConfigEquiv_apply_of_eq f _ hq,
    cutEquiv_symm_apply_mem _ _ (Finset.mem_singleton_self true),
    cutEquiv_symm_apply_mem _ _ (Finset.mem_singleton_self true)]

/-- A configuration glued from its two sides is read on the side `false` from the second
part. -/
private theorem blockConfigEquiv_cutEquiv_symm_of_false {V : Type} [Fintype V] (f : V → Bool)
    (Z : V → Type) (a a' : RegionConfig (blockSystem f Z) {true})
    (e : ComplConfig (blockSystem f Z) {true}) {q : V} (hq : f q = false) :
    blockConfigEquiv f Z ((cutEquiv (blockSystem f Z) {true}).symm (a, e)) q =
      blockConfigEquiv f Z ((cutEquiv (blockSystem f Z) {true}).symm (a', e)) q := by
  have hf : false ∉ ({true} : Finset Bool) := by simp
  rw [blockConfigEquiv_apply_of_eq f _ hq, blockConfigEquiv_apply_of_eq f _ hq,
    cutEquiv_symm_apply_not_mem _ _ hf, cutEquiv_symm_apply_not_mem _ _ hf]

/-- A Kronecker product acts on a sum of products of two frames factor by factor. -/
private theorem kronecker_mulVec_sum_mul {m₁ m₂ n₁ n₂ I J : Type} [Fintype n₁] [Fintype n₂]
    [Fintype J] (A : Matrix m₁ n₁ ℂ) (B : Matrix m₂ n₂ ℂ) (Fr : Matrix n₁ (I × J) ℂ)
    (Gr : Matrix n₂ J ℂ) (τ : J → ℂ) (i : I) (y : m₁ × m₂) :
    ((A ⊗ₖ B) *ᵥ fun a : n₁ × n₂ ↦ ∑ j, τ j * (Fr a.1 (i, j) * Gr a.2 j)) y =
      ∑ j, τ j * ((A * Fr) y.1 (i, j) * (B * Gr) y.2 j) := by
  simp only [mulVec, dotProduct, kroneckerMap_apply, Fintype.sum_prod_type, Matrix.mul_apply,
    Finset.mul_sum, Finset.sum_mul]
  refine (Finset.sum_congr rfl fun a _ ↦ Finset.sum_comm).trans ?_
  refine Finset.sum_comm.trans (Finset.sum_congr rfl fun j _ ↦ ?_)
  refine Finset.sum_comm.trans (Finset.sum_congr rfl fun b _ ↦ Finset.sum_congr rfl fun a _ ↦ ?_)
  ring

namespace SourceCircuit

variable {P : Type} [Fintype P] [DecidableEq P] {X Y : P → Type} [∀ p, Fintype (X p)]
  [∀ p, DecidableEq (X p)] (w : SourceCircuit X Y) (S : Finset w.sourceLocations)

local notation "mask" => correctedMask w S
local notation "slots" => selectedPartialSlots mask w S
local notation "basis" => partialSlotBases mask w
local notation "side" => fun (o : Option {p // correctedMask w S p = true}) ↦ Option.isSome o
local notation "Zx" => blockSystem (affectedOwner mask) X
local notation "FS" => SourceInventory.freeSlotSystem (partialSlots mask w) basis
  (correctedFreeSlots w S) (blockSystem (affectedOwner mask) X)

variable
  (E : ∀ e : w.sourceLocations, w.branchLabels e.1 →
    Matrix (w.leftBasis e) (Fin (min (w.sourceDims e).1 (w.sourceDims e).2)) ℂ)
  (F : ∀ e : w.sourceLocations, w.branchLabels e.1 →
    Matrix (w.rightBasis e) (Fin (min (w.sourceDims e).1 (w.sourceDims e).2)) ℂ)

omit [Fintype P] [∀ p, Fintype (X p)] [∀ p, DecidableEq (X p)] in
/-- The slots prepared in advance keep their vectors when frame columns are substituted in the
corrected slots. -/
private theorem fillSourceVectors_partialSchmidtSourceVectors (ξ : Choices mask w)
    (u : PartialSchmidtCoordinates mask w S) :
    SourceInventory.fillSourceVectors basis (correctedFreeSlots w S)
        (fun i _ ↦ partialSlotVector mask w ξ i) (partialSchmidtSourceVectors mask w S E F ξ u) =
      partialSchmidtSourceVectors mask w S E F ξ u := by
  funext i
  unfold SourceInventory.fillSourceVectors
  split_ifs with h
  · have hi : i ∉ slots := fun hi ↦ by
      have hf := (correctedFreeSlots_eq_true_iff w S i).mpr
        (Or.inl ((mem_selectedPartialSlots mask w S i).mp hi))
      simp [h] at hf
    rw [partialSchmidtSourceVectors, dite_eq_right hi]
  · rfl

variable [∀ p, Fintype (Y p)] [∀ p, DecidableEq (Y p)]

local notation "Yb" => blockSystem (affectedOwner mask) Y

/-- The output of a branch from its free-slot input: if the selective preparation followed by
the residual is the Kronecker product of two side operators, and the vector prepared in the
free slots is a sum of products of two frames across the two sides, the output is the same sum
through the two side operators. -/
private theorem partialSchmidtOutput_side_eq_sum (hw : w.IsLocalContractive)
    (p₀ : Word (fun _ ↦ Unit) X) (ξ : Choices mask w) (u : PartialSchmidtCoordinates mask w S)
    (c : Word (P := {b : Bool // b ∈ ({true} : Finset Bool)}) (fun b ↦ blockSystem side FS b)
      (fun b ↦ blockSystem side Yb b))
    (d : Word (P := {b : Bool // b ∉ ({true} : Finset Bool)}) (fun b ↦ blockSystem side FS b)
      (fun b ↦ blockSystem side Yb b))
    (hop : (Word.coarsen side (PartyCircuit.comp
        (SourceInventory.prepareSelected (partialSlots mask w) basis (correctedFreeSlots w S)
          (fun i _ ↦ partialSlotVector mask w ξ i) Zx) (partialResidual mask w ξ) :
          Word FS Yb)).op =
      reindex (cutEquiv (blockSystem side Yb) {true}).symm
        (cutEquiv (blockSystem side FS) {true}).symm (c.op ⊗ₖ d.op))
    {n : ℕ} (lam : Fin n → ℝ)
    (Fr : Matrix (RegionConfig (blockSystem side FS) {true})
      (PartialSchmidtCoordinates mask w S × Fin n) ℂ)
    (Gr : Matrix (ComplConfig (blockSystem side FS) {true}) (Fin n) ℂ)
    (hin : ∀ a : RegionConfig (blockSystem side FS) {true} ×
        ComplConfig (blockSystem side FS) {true},
      ((SourceInventory.prepareFreeSlots (partialSlots mask w) basis (correctedFreeSlots w S)
        (partialSchmidtSourceVectors mask w S E F ξ u) Zx).op *ᵥ
          ((p₀.coarsen (affectedOwner mask)).op *ᵥ fun _ ↦ 1))
          (blockConfigEquiv side FS ((cutEquiv (blockSystem side FS) {true}).symm a)) =
        ∑ j, (Real.sqrt (lam j) : ℂ) * (Fr a.1 (u, j) * Gr a.2 j))
    (y : RegionConfig (blockSystem side Yb) {true} × ComplConfig (blockSystem side Yb) {true}) :
    partialSchmidtOutput mask w S E F ξ u
        (Matrix.toEuclideanLin p₀.op (WithLp.toLp 2 fun _ ↦ 1))
        (blockConfigEquiv (affectedOwner mask) Y (blockConfigEquiv side Yb
          ((cutEquiv (blockSystem side Yb) {true}).symm y))) =
      ∑ j, (Real.sqrt (lam j) : ℂ) * ((c.op * Fr) y.1 (u, j) * (d.op * Gr) y.2 j) := by
  set W : Word FS Yb := PartyCircuit.comp
    (SourceInventory.prepareSelected (partialSlots mask w) basis (correctedFreeSlots w S)
      (fun i _ ↦ partialSlotVector mask w ξ i) Zx) (partialResidual mask w ξ) with hW
  set PF : Word Zx FS := SourceInventory.prepareFreeSlots (partialSlots mask w) basis
    (correctedFreeSlots w S) (partialSchmidtSourceVectors mask w S E F ξ u) Zx with hPF
  set ψZ : Config Zx → ℂ := (p₀.coarsen (affectedOwner mask)).op *ᵥ fun _ ↦ 1 with hψZ
  have hmat : partialSchmidtMatrix mask w S E F ξ u =
      reindex (blockConfigEquiv (affectedOwner mask) Y) (blockConfigEquiv (affectedOwner mask) X)
        (W.op * PF.op) := by
    have hsel := (Word.exists_selective_partition side (partialSlots mask w) basis
      (correctedFreeSlots w S) (fun i _ ↦ partialSlotVector mask w ξ i)
      (fun i _ ↦ norm_partialSlotVector _ w ξ i) (correctedFreeSlots_internal w S) Zx
      (partialResidual mask w ξ) (isAllowed_partialResidual _ w hw ξ)
      (sources_partialResidual _ w ξ)).2 (partialSchmidtSourceVectors mask w S E F ξ u)
    rw [fillSourceVectors_partialSchmidtSourceVectors] at hsel
    rw [partialSchmidtMatrix, Word.preparedMatrix, hsel]
  have hA : ∀ yb : Config Yb, partialSchmidtOutput mask w S E F ξ u
      (Matrix.toEuclideanLin p₀.op (WithLp.toLp 2 fun _ ↦ 1))
      (blockConfigEquiv (affectedOwner mask) Y yb) = ((W.op * PF.op) *ᵥ ψZ) yb := by
    intro yb
    have hout : (partialSchmidtOutput mask w S E F ξ u
        (Matrix.toEuclideanLin p₀.op (WithLp.toLp 2 fun _ ↦ 1))).ofLp =
        partialSchmidtMatrix mask w S E F ξ u *ᵥ (p₀.op *ᵥ fun _ ↦ 1) := by
      simp only [partialSchmidtOutput, Matrix.toLpLin_apply, WithLp.ofLp_toLp]
    change (partialSchmidtOutput mask w S E F ξ u
      (Matrix.toEuclideanLin p₀.op (WithLp.toLp 2 fun _ ↦ 1))).ofLp _ = _
    rw [hout, hmat, reindex_apply, submatrix_mulVec_equiv, hψZ, Word.op_coarsen, reindex_apply,
      submatrix_mulVec_equiv]
    simp only [Equiv.symm_symm, Function.comp_apply, Equiv.symm_apply_apply]
    rfl
  have hB : ∀ (Φ : Config FS → ℂ) (ys : Config (blockSystem side Yb)),
      (W.op *ᵥ Φ) (blockConfigEquiv side Yb ys) =
        ((W.coarsen side).op *ᵥ (Φ ∘ blockConfigEquiv side FS)) ys := by
    intro Φ ys
    rw [Word.op_coarsen, reindex_apply, submatrix_mulVec_equiv]
    simp only [Equiv.symm_symm, Function.comp_apply, Function.comp_assoc, Equiv.self_comp_symm,
      Function.comp_id]
  calc
    _ = ((W.op * PF.op) *ᵥ ψZ)
        (blockConfigEquiv side Yb ((cutEquiv (blockSystem side Yb) {true}).symm y)) := hA _
    _ = (W.op *ᵥ (PF.op *ᵥ ψZ))
        (blockConfigEquiv side Yb ((cutEquiv (blockSystem side Yb) {true}).symm y)) :=
      (congrFun (mulVec_mulVec ψZ W.op PF.op) _).symm
    _ = ((W.coarsen side).op *ᵥ ((PF.op *ᵥ ψZ) ∘ blockConfigEquiv side FS))
        ((cutEquiv (blockSystem side Yb) {true}).symm y) := hB _ _
    _ = ((c.op ⊗ₖ d.op) *ᵥ fun a ↦ (PF.op *ᵥ ψZ) (blockConfigEquiv side FS
        ((cutEquiv (blockSystem side FS) {true}).symm a))) y := by
      rw [hop, reindex_apply, submatrix_mulVec_equiv]
      simp only [Equiv.symm_symm, Function.comp_apply, Equiv.apply_symm_apply]
      rfl
    _ = ((c.op ⊗ₖ d.op) *ᵥ fun a ↦ ∑ j, (Real.sqrt (lam j) : ℂ) * (Fr a.1 (u, j) * Gr a.2 j)) y :=
      congrArg (fun v ↦ ((c.op ⊗ₖ d.op) *ᵥ v) y) (funext fun a ↦ hin a)
    _ = _ := kronecker_mulVec_sum_mul _ _ _ _ _ _ _

end SourceCircuit

end QuantumCircuit.Party

/-! ### The isometric form: a Schmidt output on the free source registers -/

namespace QuantumCircuit.Party

/-- The system over the two sides with basis `A` on the side `true` and `B` on the side
`false`. -/
def sidePair (A B : Type) : Bool → Type
  | true => A
  | false => B

instance (A B : Type) [Fintype A] [Fintype B] (b : Bool) : Fintype (sidePair A B b) := by
  cases b <;> (unfold sidePair; infer_instance)

instance (A B : Type) [DecidableEq A] [DecidableEq B] (b : Bool) :
    DecidableEq (sidePair A B b) := by
  cases b <;> (unfold sidePair; infer_instance)

/-- The configurations of the side `true` of `sidePair A B` are the elements of `A`. -/
private def sidePairTrueEquiv (A B : Type) : RegionConfig (sidePair A B) {true} ≃ A where
  toFun a := a ⟨true, Finset.mem_singleton_self _⟩
  invFun x b := cast (congrArg (sidePair A B) (Finset.mem_singleton.mp b.2).symm) x
  left_inv a := by
    funext ⟨b, hb⟩
    obtain rfl := Finset.mem_singleton.mp hb
    rfl
  right_inv _ := rfl

/-- The configurations of the side `false` of `sidePair A B` are the elements of `B`. -/
private def sidePairFalseEquiv (A B : Type) : ComplConfig (sidePair A B) {true} ≃ B where
  toFun a := a ⟨false, by simp⟩
  invFun x b := cast (congrArg (sidePair A B) (by simpa using b.2 : (b : Bool) = false).symm) x
  left_inv a := by
    funext ⟨b, hb⟩
    obtain rfl : b = false := by simpa using hb
    rfl
  right_inv _ := rfl

/-- Reading rows and columns of a matrix along injective maps does not increase its operator
norm. -/
private theorem l2_opNorm_submatrix_le_of_injective₂ {m n m' n' : Type} [Fintype m] [Fintype n]
    [Fintype m'] [Fintype n'] [DecidableEq n] [DecidableEq n'] (M : Matrix m n ℂ) {r : m' → m}
    {c : n' → n} (hr : Function.Injective r) (hc : Function.Injective c) :
    ‖M.submatrix r c‖ ≤ ‖M‖ := by
  classical
  have h : M.submatrix r c = ((M.submatrix r id)ᴴ.submatrix c id)ᴴ := by
    ext i j
    simp
  rw [h, l2_opNorm_conjTranspose]
  refine (l2_opNorm_submatrix_le_of_injective _ hc).trans ?_
  rw [l2_opNorm_conjTranspose]
  exact l2_opNorm_submatrix_le_of_injective M hr

/-- **A contraction between systems over one party is the operator of an allowed source-free
word.** -/
private theorem exists_word_op_eq {ι : Type} [Fintype ι] [DecidableEq ι] [Unique ι]
    {A B : ι → Type} [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)] [∀ i, Fintype (B i)]
    (N : Matrix (Config B) (Config A) ℂ) (hN : ‖N‖ ≤ 1) :
    ∃ v : Word A B, v.IsAllowed ∧ v.sources = [] ∧ v.op = N := by
  classical
  let single : ∀ (Z : ι → Type) (i : ι), Z i → Config Z := fun Z i z j ↦
    cast (congrArg Z (Subsingleton.elim i j)) z
  have hsingle : ∀ (Z : ι → Type) (a : Config Z) (i : ι), single Z i (a i) = a := by
    intro Z a i
    funext j
    obtain rfl := Subsingleton.elim i j
    rfl
  have hinj : ∀ (Z : ι → Type) (i : ι), Function.Injective (single Z i) := by
    intro Z i z z' h
    exact congrFun h i
  refine ⟨PartyCircuit.localOps fun i ↦ N.submatrix (single B i) (single A i),
    Word.isAllowed_localOps _ fun i ↦
      (l2_opNorm_submatrix_le_of_injective₂ N (hinj B i) (hinj A i)).trans hN, rfl, ?_⟩
  change PartyCircuit.op SourceGate.ev (PartyCircuit.localOps _) = N
  rw [PartyCircuit.op_localOps]
  ext a a'
  rw [piKronecker_apply, Fintype.prod_unique, submatrix_apply, hsingle, hsingle]

namespace SourceCircuit

variable {P : Type} [Fintype P] [DecidableEq P] {X Y : P → Type} [∀ p, Fintype (X p)]
  [∀ p, DecidableEq (X p)] [∀ p, Fintype (Y p)] [∀ p, DecidableEq (Y p)]
  (w : SourceCircuit X Y) (S : Finset w.sourceLocations)

/-- The basis on one side of a crossing slot has decidable equality. -/
noncomputable instance (i : w.crossingSlots S) (b : Bool) :
    DecidableEq (w.crossingSlotBasis S i b) := by
  unfold crossingSlotBasis
  split_ifs <;> infer_instance

local notation "mask" => correctedMask w S
local notation "slots" => selectedPartialSlots mask w S
local notation "cross" => crossingSlots w S
local notation "basis" => partialSlotBases mask w
local notation "side" => fun (o : Option {p // correctedMask w S p = true}) ↦ Option.isSome o
local notation "Zx" => blockSystem (affectedOwner mask) X
local notation "FS" => SourceInventory.freeSlotSystem (partialSlots mask w) basis
  (correctedFreeSlots w S) (blockSystem (affectedOwner mask) X)
local notation "Yb" => blockSystem (affectedOwner mask) Y

variable
  (E : ∀ e : w.sourceLocations, w.branchLabels e.1 →
    Matrix (w.leftBasis e) (Fin (min (w.sourceDims e).1 (w.sourceDims e).2)) ℂ)
  (F : ∀ e : w.sourceLocations, w.branchLabels e.1 →
    Matrix (w.rightBasis e) (Fin (min (w.sourceDims e).1 (w.sourceDims e).2)) ℂ)

/-- **The outputs of a branch on the corrected frame columns have a Schmidt output on the free
source registers.** The inputs are the registers of the free sources alone: on the affected
side the pairs of endpoint coordinates of the corrected slots and the affected coordinates of
the crossing slots, on the exterior side the exterior coordinates of the crossing slots. The
frames are isometric (the corrected source frame times the affected Schmidt frame of the exact
crossing sources, and their exterior Schmidt frame); the preparation of the input and the
other sources are inside the two allowed source-free words. The frames `E e ξ`, `F e ξ` of the
sources have rows indexed by the bases of the two registers of the source slot `e` and columns
indexed by the Schmidt index. Source: Theorem 5.2, `eq:compression-exterior-input`,
`04-compression.tex`, lines 409–480. -/
theorem hasSchmidtOutput_partialSchmidtOutput (hw : w.IsLocalContractive)
    (hE : ∀ e ξ, (E e ξ)ᴴ * E e ξ = 1) (hF : ∀ e ξ, (F e ξ)ᴴ * F e ξ = 1)
    (p₀ : Word (fun _ ↦ Unit) X) (hp₀ : p₀.IsAllowed) (hp₀s : p₀.sources = [])
    (ξ : Choices mask w) :
    Word.HasSchmidtOutput
      (sidePair ((∀ i : slots, (basis).left i × (basis).right i) ×
        (∀ i : cross, w.crossingSlotBasis S i true)) (∀ i : cross, w.crossingSlotBasis S i false))
      (blockSystem side Yb)
      (fun (i : CorrectedSchmidtCoordinates w S) y ↦
        partialSchmidtOutput mask w S E F ξ
          ((partialSchmidtCoordinateEquiv mask w S (w.correctedMask_meets S)).symm i)
          (Matrix.toEuclideanLin p₀.op (WithLp.toLp 2 fun _ ↦ 1))
          (blockConfigEquiv (affectedOwner mask) Y (blockConfigEquiv side Yb
            ((cutEquiv (blockSystem side Yb) {true}).symm y)))) := by
  classical
  let uT : Unique {b : Bool // b ∈ ({true} : Finset Bool)} :=
    ⟨⟨⟨true, Finset.mem_singleton_self _⟩⟩, fun b ↦ Subtype.ext (Finset.mem_singleton.mp b.2)⟩
  let uF : Unique {b : Bool // b ∉ ({true} : Finset Bool)} :=
    ⟨⟨⟨false, by simp⟩⟩, fun b ↦ Subtype.ext (by have := b.2; simpa using this)⟩
  obtain ⟨c, d, hc, hd, hcs, hds, -, -, hop⟩ := exists_corrected_source_partition w hw S ξ
  obtain ⟨cA, cE, hcA, hcE, hψ⟩ := Word.exists_side_product_of_sources_eq_nil side
    (p₀.coarsen (affectedOwner mask)) (Word.isAllowed_coarsen _ hp₀)
    (by rw [Word.sources_coarsen, hp₀s]; rfl)
  obtain ⟨lam, U, V, hlam, hmass, hU, hV, hspec⟩ := w.exists_correctedInputFrames S E F hE hF ξ
  have h1 : ∀ {m : Type} [Fintype m] [DecidableEq m], ‖(1 : Matrix m m ℂ)‖ ≤ 1 := fun {m} _ _ ↦
    (IsStarProjection.one _).norm_le
  let M := reindex (Equiv.refl _) (Equiv.prodPUnit _)
    ((1 : Matrix ((∀ i : slots, (basis).left i × (basis).right i) ×
      (∀ i : cross, w.crossingSlotBasis S i true))
      ((∀ i : slots, (basis).left i × (basis).right i) ×
      (∀ i : cross, w.crossingSlotBasis S i true)) ℂ) ⊗ₖ cA)
  let N := reindex (Equiv.refl _) (Equiv.prodPUnit _)
    ((1 : Matrix (∀ i : cross, w.crossingSlotBasis S i false)
      (∀ i : cross, w.crossingSlotBasis S i false) ℂ) ⊗ₖ cE)
  have hM : ‖M‖ ≤ 1 := (l2_opNorm_reindex_le _ _ _).trans (l2_opNorm_kronecker_le_one h1 hcA)
  have hN : ‖N‖ ≤ 1 := (l2_opNorm_reindex_le _ _ _).trans (l2_opNorm_kronecker_le_one h1 hcE)
  obtain ⟨PA, PE, hPA, hPE, hprod⟩ := Matrix.exists_contraction_of_injective_prod
    (fun a : RegionConfig (blockSystem side FS) {true} ×
        ComplConfig (blockSystem side FS) {true} ↦
      w.freeSideCoordinates S (blockConfigEquiv side FS
        ((cutEquiv (blockSystem side FS) {true}).symm a)))
    ((w.freeSideCoordinates_injective S).comp ((blockConfigEquiv side FS).injective.comp
      (cutEquiv (blockSystem side FS) {true}).symm.injective))
    (fun a e e' ↦ w.freeSideCoordinates_fst_congr S fun q hq ↦
      blockConfigEquiv_cutEquiv_symm_of_true side FS a e e' hq)
    (fun a a' e ↦ w.freeSideCoordinates_snd_congr S fun q hq ↦
      blockConfigEquiv_cutEquiv_symm_of_false side FS a a' e hq) M N hM hN
  have hin : ∀ (u : PartialSchmidtCoordinates mask w S)
      (a : RegionConfig (blockSystem side FS) {true} × ComplConfig (blockSystem side FS) {true}),
      ((SourceInventory.prepareFreeSlots (partialSlots mask w) basis (correctedFreeSlots w S)
        (partialSchmidtSourceVectors mask w S E F ξ u) Zx).op *ᵥ
          ((p₀.coarsen (affectedOwner mask)).op *ᵥ fun _ ↦ 1))
          (blockConfigEquiv side FS ((cutEquiv (blockSystem side FS) {true}).symm a)) =
        ∑ j, (Real.sqrt (lam j) : ℂ) * ((PA * U) a.1 (u, j) * (PE * V) a.2 j) := by
    intro u a
    obtain ⟨a₁, a₂⟩ := a
    set y := blockConfigEquiv side FS ((cutEquiv (blockSystem side FS) {true}).symm (a₁, a₂))
    set cc := w.freeSideCoordinates S y with hcc
    have hz := hψ (cutEquiv (blockSystem side Zx) {true} ((blockConfigEquiv side Zx).symm
      (SourceInventory.freeSlotColumnEquiv (partialSlots mask w) basis
        (correctedFreeSlots w S) Zx y).2))
    rw [Equiv.symm_apply_apply, Equiv.apply_symm_apply] at hz
    have hp : ∀ kl r, PA a₁ kl * PE a₂ r = M cc.1 kl * N cc.2 r := fun kl r ↦
      hprod a₁ a₂ kl r
    have hMe : ∀ kl, M cc.1 kl = if cc.1.1 = kl then cA cc.1.2 () else 0 := fun kl ↦ by
      simp [M, reindex_apply, kroneckerMap_apply, Matrix.one_apply]
    have hNe : ∀ r, N cc.2 r = if cc.2.1 = r then cE cc.2.2 () else 0 := fun r ↦ by
      simp [N, reindex_apply, kroneckerMap_apply, Matrix.one_apply]
    have hA : ∀ j, (PA * U) a₁ (u, j) * (PE * V) a₂ j =
        (cA cc.1.2 () * U cc.1.1 (u, j)) * (cE cc.2.2 () * V cc.2.1 j) := by
      intro j
      calc
        _ = ∑ kl, ∑ r, (PA a₁ kl * PE a₂ r) * (U kl (u, j) * V r j) := by
          simp only [Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum]
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun kl _ ↦ Finset.sum_congr rfl fun r _ ↦ by ring
        _ = _ := by
          simp only [hp, hMe, hNe]
          rw [Finset.sum_eq_single cc.1.1 (fun b _ hb ↦ by simp [Ne.symm hb])
            fun h ↦ absurd (Finset.mem_univ _) h,
            Finset.sum_eq_single cc.2.1 (fun b _ hb ↦ by simp [Ne.symm hb])
              fun h ↦ absurd (Finset.mem_univ _) h]
          simp only [ite_true]
          ring
    calc
      _ = w.correctedSourceFrame S E F ξ cc.1.1.1 u *
            w.sourceCrossingVector S ξ (cc.1.1.2, cc.2.1) *
            ((p₀.coarsen (affectedOwner mask)).op *ᵥ fun _ ↦ 1)
              (SourceInventory.freeSlotColumnEquiv (partialSlots mask w) basis
                (correctedFreeSlots w S) Zx y).2 :=
        w.prepareFreeSlots_partialSchmidt_mulVec S E F ξ u _ y
      _ = (∑ j, (Real.sqrt (lam j) : ℂ) * (U (cc.1.1.1, cc.1.1.2) (u, j) * V cc.2.1 j)) *
            (cA cc.1.2 () * cE cc.2.2 ()) := by
        rw [hz]
        exact congrArg (· * _) (hspec u (cc.1.1.1, cc.1.1.2) cc.2.1)
      _ = _ := by
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun j _ ↦ ?_
        rw [hA j]
        ring
  let eT := sidePairTrueEquiv ((∀ i : slots, (basis).left i × (basis).right i) ×
    (∀ i : cross, w.crossingSlotBasis S i true)) (∀ i : cross, w.crossingSlotBasis S i false)
  let eF := sidePairFalseEquiv ((∀ i : slots, (basis).left i × (basis).right i) ×
    (∀ i : cross, w.crossingSlotBasis S i true)) (∀ i : cross, w.crossingSlotBasis S i false)
  have hnA : ‖PA.submatrix id eT‖ ≤ 1 :=
    (l2_opNorm_submatrix_le_of_injective₂ PA Function.injective_id eT.injective).trans hPA
  have hnE : ‖PE.submatrix id eF‖ ≤ 1 :=
    (l2_opNorm_submatrix_le_of_injective₂ PE Function.injective_id eF.injective).trans hPE
  refine Exists.elim (exists_word_op_eq (ι := {b : Bool // b ∈ ({true} : Finset Bool)})
    (PA.submatrix id eT) hnA) fun c₀ hc₀ ↦ ?_
  refine Exists.elim (exists_word_op_eq (ι := {b : Bool // b ∉ ({true} : Finset Bool)})
    (PE.submatrix id eF) hnE) fun d₀ hd₀ ↦ ?_
  let eqv := partialSchmidtCoordinateEquiv mask w S (w.correctedMask_meets S)
  have hcF : Word.op (PartyCircuit.comp c₀ c) * U.submatrix eT (eqv.symm.prodCongr (Equiv.refl _)) =
      (c.op * (PA * U)).submatrix id (eqv.symm.prodCongr (Equiv.refl _)) := by
    rw [Word.op_comp, hc₀.2.2, Matrix.mul_assoc, submatrix_mul_equiv]
    rfl
  have hdG : Word.op (PartyCircuit.comp d₀ d) * V.submatrix eF id =
      (d.op * (PE * V)).submatrix id id := by
    rw [Word.op_comp, hd₀.2.2, Matrix.mul_assoc, submatrix_mul_equiv]
    rfl
  refine ⟨PartyCircuit.comp c₀ c, PartyCircuit.comp d₀ d, Word.IsAllowed.comp hc₀.1 hc,
    Word.IsAllowed.comp hd₀.1 hd, by rw [Word.sources_comp, hc₀.2.1, hcs]; rfl,
    by rw [Word.sources_comp, hd₀.2.1, hds]; rfl,
    PartyCircuit.norm_op_le_one (G := SourceGate) _ (Word.IsAllowed.comp hc₀.1 hc),
    PartyCircuit.norm_op_le_one (G := SourceGate) _ (Word.IsAllowed.comp hd₀.1 hd), _, lam,
    U.submatrix eT (eqv.symm.prodCongr (Equiv.refl _)), V.submatrix eF id, ?_, ?_, hlam, hmass,
    fun i ↦ funext fun y ↦ ?_⟩
  · rw [conjTranspose_submatrix, submatrix_mul_equiv, hU, submatrix_one_equiv]
  · rw [conjTranspose_submatrix, submatrix_mul_equiv, hV, submatrix_id_id]
  · rw [hcF, hdG]
    exact w.partialSchmidtOutput_side_eq_sum S E F hw p₀ ξ _ c d hop lam (PA * U) (PE * V)
      (hin _) y

end SourceCircuit

end QuantumCircuit.Party
