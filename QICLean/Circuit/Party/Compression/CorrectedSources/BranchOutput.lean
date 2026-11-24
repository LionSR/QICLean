/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Circuit.Party.Compression.CorrectedSources.SideCoordinates
import QICLean.Circuit.Party.Compression.CorrectedSources.SideInput

/-!
# The output of a branch through two local words

Fix a set `S` of source positions of a source circuit, its affected parties, and a branch of the
partial expansion along them. Substitute columns of Schmidt frames for the vectors of the
corrected sources. Read across the two sides of the affected parties, the vector prepared in the
free slots on a product input is one Schmidt sum, with weights independent of the frame columns,
of products of the entries of two contractions (`exists_prepareFreeSlots_side_schmidt`): the
corrected frame columns and the affected halves of the exact crossing sources enter on the
affected side, the exterior halves on the exterior side. The output of the branch is therefore
the same Schmidt sum through two allowed local words, one on each side
(`exists_correctedSchmidtOutput`).

The frames `E e ξ`, `F e ξ` of the corrected sources are matrices whose rows are indexed by the
bases `w.leftBasis e`, `w.rightBasis e` of the two registers of the source slot `e` and whose
columns are indexed by the Schmidt index; they have orthonormal columns
(`(E e ξ)ᴴ * E e ξ = 1`), as the source's Schmidt vectors `u_a`, `v_a`. The frames produced on
the two sides contain the base input, a contraction, and are contractions.

## Main results

* `QuantumCircuit.Party.SourceCircuit.exists_prepareFreeSlots_side_schmidt`.
* `QuantumCircuit.Party.SourceCircuit.exists_correctedSchmidtOutput`.

## References

* Polynomial-PEPS manuscript (September 24, 2026), Theorem 5.2, `04-compression.tex`,
  lines 279–289 and 409–480, `eq:compression-exterior-input`.

The input is a vector prepared from the one-dimensional input and kept inside the frames of the
two sides, so these frames are contractions.
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

/-- **The free-slot input of a branch is a Schmidt sum across the two sides.** For frames with
orthonormal columns and a base input that is a product of two columns of norm at most one, the
vector prepared in the free slots with the frame columns `u` at the corrected slots, read
across the cut of the affected side, is `∑_j √λ_j Fr(a, (u, j)) Gr(b, j)`: probability weights
`λ` and contractions `Fr`, `Gr` chosen before `u`. Source: Theorem 5.2, `04-compression.tex`,
lines 409–434. -/
theorem exists_prepareFreeSlots_side_schmidt
    (hE : ∀ e ξ, (E e ξ)ᴴ * E e ξ = 1) (hF : ∀ e ξ, (F e ξ)ᴴ * F e ξ = 1)
    (ξ : Choices mask w) (cA : Matrix (RegionConfig (blockSystem side Zx) {true}) Unit ℂ)
    (cE : Matrix (ComplConfig (blockSystem side Zx) {true}) Unit ℂ) (hcA : ‖cA‖ ≤ 1)
    (hcE : ‖cE‖ ≤ 1) (ψ : Config Zx → ℂ)
    (hψ : ∀ s : RegionConfig (blockSystem side Zx) {true} ×
        ComplConfig (blockSystem side Zx) {true},
      ψ (blockConfigEquiv side Zx ((cutEquiv (blockSystem side Zx) {true}).symm s)) =
        cA s.1 () * cE s.2 ()) :
    ∃ (n : ℕ) (lam : Fin n → ℝ)
      (Fr : Matrix (RegionConfig (blockSystem side FS) {true})
        (PartialSchmidtCoordinates mask w S × Fin n) ℂ)
      (Gr : Matrix (ComplConfig (blockSystem side FS) {true}) (Fin n) ℂ),
      (∀ j, 0 ≤ lam j) ∧ ∑ j, lam j = 1 ∧ ‖Fr‖ ≤ 1 ∧ ‖Gr‖ ≤ 1 ∧
      ∀ (u : PartialSchmidtCoordinates mask w S)
        (a : RegionConfig (blockSystem side FS) {true} ×
          ComplConfig (blockSystem side FS) {true}),
        ((SourceInventory.prepareFreeSlots (partialSlots mask w) basis (correctedFreeSlots w S)
          (partialSchmidtSourceVectors mask w S E F ξ u) Zx).op *ᵥ ψ)
            (blockConfigEquiv side FS ((cutEquiv (blockSystem side FS) {true}).symm a)) =
          ∑ j, (Real.sqrt (lam j) : ℂ) * (Fr a.1 (u, j) * Gr a.2 j) := by
  classical
  obtain ⟨lam, U, V, hlam, hmass, hU, hV, hspec⟩ := w.exists_correctedInputFrames S E F hE hF ξ
  let M := reindex (Equiv.refl _) (Equiv.prodPUnit _) (U ⊗ₖ cA)
  let N := reindex (Equiv.refl _) (Equiv.prodPUnit _) (V ⊗ₖ cE)
  have hM : ‖M‖ ≤ 1 := (l2_opNorm_reindex_le _ _ _).trans
    (l2_opNorm_kronecker_le_one (l2_opNorm_le_one_of_conjTranspose_mul_self_eq_one hU) hcA)
  have hN : ‖N‖ ≤ 1 := (l2_opNorm_reindex_le _ _ _).trans
    (l2_opNorm_kronecker_le_one (l2_opNorm_le_one_of_conjTranspose_mul_self_eq_one hV) hcE)
  obtain ⟨Fr, Gr, hFr, hGr, hprod⟩ := Matrix.exists_contraction_of_injective_prod
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
  refine ⟨_, lam, Fr, Gr, hlam, hmass, hFr, hGr, fun u a ↦ ?_⟩
  obtain ⟨a₁, a₂⟩ := a
  set y := blockConfigEquiv side FS ((cutEquiv (blockSystem side FS) {true}).symm (a₁, a₂))
  set c := w.freeSideCoordinates S y with hc
  have hz : ψ (SourceInventory.freeSlotColumnEquiv (partialSlots mask w) basis
      (correctedFreeSlots w S) Zx y).2 = cA c.1.2 () * cE c.2.2 () := by
    have h := hψ (cutEquiv (blockSystem side Zx) {true} ((blockConfigEquiv side Zx).symm
      (SourceInventory.freeSlotColumnEquiv (partialSlots mask w) basis
        (correctedFreeSlots w S) Zx y).2))
    rwa [Equiv.symm_apply_apply, Equiv.apply_symm_apply] at h
  calc
    _ = w.correctedSourceFrame S E F ξ c.1.1.1 u * w.sourceCrossingVector S ξ (c.1.1.2, c.2.1) *
          ψ (SourceInventory.freeSlotColumnEquiv (partialSlots mask w) basis
            (correctedFreeSlots w S) Zx y).2 :=
      w.prepareFreeSlots_partialSchmidt_mulVec S E F ξ u ψ y
    _ = (∑ j, (Real.sqrt (lam j) : ℂ) * (U (c.1.1.1, c.1.1.2) (u, j) * V c.2.1 j)) *
          (cA c.1.2 () * cE c.2.2 ()) := by
      rw [hz]
      exact congrArg (· * _) (hspec u (c.1.1.1, c.1.1.2) c.2.1)
    _ = _ := by
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun j _ ↦ ?_
      rw [hprod a₁ a₂ (u, j) j]
      simp only [M, N, reindex_apply, submatrix_apply, kroneckerMap_apply, Equiv.refl_symm,
        Equiv.refl_apply, Equiv.prodPUnit_symm_apply]
      ring

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

/-- **The output of a branch on corrected frame columns is a Schmidt sum through two local
words.** For frames `E`, `F` of the sources with orthonormal columns (rows indexed by the bases
of the two registers of a source slot, columns by the Schmidt index) and an input prepared by an
allowed source-free word from the one-dimensional input, the output of the branch `ξ` at the
frame columns `u`, read across the two sides of the affected parties, is
`∑_j √λ_j (c Fr)(y₁, (u, j)) (d Gr)(y₂, j)`: two allowed words `c`, `d`, one on each side,
probability weights `λ` and contractions `Fr`, `Gr`, all chosen before `u`. Source:
Theorem 5.2, `eq:compression-exterior-input`, `04-compression.tex`, lines 409–480. -/
theorem exists_correctedSchmidtOutput (hw : w.IsLocalContractive)
    (hE : ∀ e ξ, (E e ξ)ᴴ * E e ξ = 1) (hF : ∀ e ξ, (F e ξ)ᴴ * F e ξ = 1)
    (p₀ : Word (fun _ ↦ Unit) X) (hp₀ : p₀.IsAllowed) (hp₀s : p₀.sources = [])
    (ξ : Choices mask w) :
    ∃ (c : Word (P := {b : Bool // b ∈ ({true} : Finset Bool)}) (fun b ↦ blockSystem side FS b)
        (fun b ↦ blockSystem side Yb b))
      (d : Word (P := {b : Bool // b ∉ ({true} : Finset Bool)}) (fun b ↦ blockSystem side FS b)
        (fun b ↦ blockSystem side Yb b)),
      c.IsAllowed ∧ d.IsAllowed ∧ ∃ (n : ℕ) (lam : Fin n → ℝ)
        (Fr : Matrix (RegionConfig (blockSystem side FS) {true})
          (PartialSchmidtCoordinates mask w S × Fin n) ℂ)
        (Gr : Matrix (ComplConfig (blockSystem side FS) {true}) (Fin n) ℂ),
        (∀ j, 0 ≤ lam j) ∧ ∑ j, lam j = 1 ∧ ‖Fr‖ ≤ 1 ∧ ‖Gr‖ ≤ 1 ∧
        ∀ (u : PartialSchmidtCoordinates mask w S)
          (y : RegionConfig (blockSystem side Yb) {true} ×
            ComplConfig (blockSystem side Yb) {true}),
          partialSchmidtOutput mask w S E F ξ u
              (Matrix.toEuclideanLin p₀.op (WithLp.toLp 2 fun _ ↦ 1))
              (blockConfigEquiv (affectedOwner mask) Y (blockConfigEquiv side Yb
                ((cutEquiv (blockSystem side Yb) {true}).symm y))) =
            ∑ j, (Real.sqrt (lam j) : ℂ) * ((c.op * Fr) y.1 (u, j) * (d.op * Gr) y.2 j) := by
  classical
  obtain ⟨c, d, hc, hd, -, -, -, -, hop⟩ := exists_corrected_source_partition w hw S ξ
  obtain ⟨cA, cE, hcA, hcE, hψ⟩ := Word.exists_side_product_of_sources_eq_nil side
    (p₀.coarsen (affectedOwner mask)) (Word.isAllowed_coarsen _ hp₀)
    (by rw [Word.sources_coarsen, hp₀s]; rfl)
  obtain ⟨n, lam, Fr, Gr, hlam, hmass, hFr, hGr, hin⟩ :=
    w.exists_prepareFreeSlots_side_schmidt S E F hE hF ξ cA cE hcA hcE _ hψ
  refine ⟨c, d, hc, hd, n, lam, Fr, Gr, hlam, hmass, hFr, hGr, fun u y ↦ ?_⟩
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
      congrArg (fun v ↦ ((c.op ⊗ₖ d.op) *ᵥ v) y) (funext fun a ↦ hin u a)
    _ = _ := kronecker_mulVec_sum_mul _ _ _ _ _ _ _

end SourceCircuit

end QuantumCircuit.Party
