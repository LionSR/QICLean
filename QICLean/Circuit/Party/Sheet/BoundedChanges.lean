/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Circuit.Party.Sheet.EnvironmentDeath
import QICLean.Circuit.Party.Sheet.PrivateBirthDeath
import QICLean.Spectral.Eigenvalue.MatrixReindexEuclidean

/-!
# Births, deaths and exchanges of sheets for given splitting data

Lemmas 6.5 and 6.6 of the polynomial-PEPS manuscript (Lemmas `lem:birth` and `lem:exchange` of
the one-dimensional note) assert that a homogeneous birth, a homogeneous death and a two-sheet
exchange are bounded changes. Their proofs have two parts: an entropy estimate produces
splitting data `σ` whose error is small (Lemma 6.4), and for any splitting data an explicit
monomial implements the canonical map of `σ` with reference-vector error at most the error of
`σ`. This file is the second part, for sheets:

* a birth (`Sheet.exists_birthWord_of_splittingData`): an allowed word using only `P∘` and `Q∘`
  with at most one normalized pair source, whose operator in canonical coordinates is the
  canonical map `𝐁` of `σ`, moving the reference vector by at most the error of `σ`;
* a death (`Sheet.exists_deathChain_of_splittingData`): the same with a monomial whose gates are
  at most one normalized pair effect;
* an exchange (`Sheet.exists_exchangeWord_of_splittingData`): the renaming `ℛ`, a relabelling of
  the bases of the parties whose sites change sheet, followed by an allowed word without gates
  using only `P∘`, the corrections `D_U F_A`; its operator is `C = D_U F_A F_Y = D_U F_T`
  (`Sheet.exchangeOp_eq`), and it moves `Ω ⊗ Ω` by at most four times the error of `σ`. The set
  `Z` is any set of sites outside of which both owners are `P∘`, as for the hole parts of a frame.

The statements with the hypothesis `I_Ω(T:E) ≤ L^{-2p}` follow by composing these with the
existence of splitting data of error at most `L^{-p}`,
`ManyBody.SplittingData.exists_error_le_rpow`.

## Main definitions

* `QuantumCircuit.Party.Sheet.exchangeOp`: the map `C = D_U F_A F_Y` of an exchange.
* `QuantumCircuit.Party.Sheet.renameWord`, `QuantumCircuit.Party.Sheet.correctionWord`.

## Main results

* `QuantumCircuit.Party.Sheet.exists_birthWord_of_environment`,
  `QuantumCircuit.Party.Sheet.exists_deathChain_of_environment`: a birth and a death for any
  environment `E` disjoint from the born region `T`, outside of which every site is held by `P∘`.
* `QuantumCircuit.Party.Sheet.exists_birthWord_of_splittingData`,
  `QuantumCircuit.Party.Sheet.exists_deathChain_of_splittingData`,
  `QuantumCircuit.Party.Sheet.exists_exchangeWord_of_splittingData`.
* `QuantumCircuit.Party.Sheet.op_renameWord`, `QuantumCircuit.Party.Sheet.op_correctionWord`,
  `QuantumCircuit.Party.Sheet.exchangeOp_eq`.

## References

* Polynomial-PEPS manuscript (September 24, 2026), Lemma 6.4 `lem:splitting`, `05-frames.tex`,
  lines 352–368; Lemma 6.5 `lem:birth`, lines 396–447; Lemma 6.6 `lem:exchange`,
  lines 460–561.
* One-dimensional note, Lemmas `lem:birth` and `lem:exchange`, `part2b_mps_protocol.tex`,
  lines 70–155.
-/
open Matrix ManyBody
open scoped Kronecker Matrix.Norms.L2Operator

namespace QuantumCircuit.Party

namespace Sheet

variable {ι P : Type} [Fintype ι] [DecidableEq ι] [Fintype P] [DecidableEq P] {q : ℕ}

/-- Reading the matrix, the input and the target along bijections does not change the error. -/
private theorem norm_toEuclideanLin_reindex_sub {m n m' n' : Type} [Fintype m] [Fintype n]
    [Fintype m'] [Fintype n'] [DecidableEq n] [DecidableEq n'] (e : m ≃ m') (f : n ≃ n')
    (M : Matrix m n ℂ) (x : EuclideanSpace ℂ n) (y : EuclideanSpace ℂ m) :
    ‖toEuclideanLin (reindex e f M) (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ f x) -
        LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e y‖ = ‖toEuclideanLin M x - y‖ := by
  rw [toEuclideanLin_reindex_piLpCongrLeft₂, ← map_sub, LinearIsometryEquiv.norm_map]

/-! ### Birth and death -/

section Birth

variable (S : Sheet ι P) {T : Finset ι} {P₀ Q : P}

/-- A birth with a prescribed environment is an allowed word using only the
two parties of the birth and at most one pair source. Sites of the central
party can lie in the environment. Its operator is the canonical map of the
splitting data and its error is bounded by the splitting error.
Source: polynomial-PEPS, Lemma 6.5, `05-frames.tex`, lines 396–437. -/
theorem exists_birthWord_of_environment {E : Finset ι}
    (hTE : Disjoint T E) (hTP : ∀ x ∈ T, S.owner x = P₀)
    (hU : ∀ x ∉ T ∪ E, S.owner x = P₀)
    (σ : SplittingData (fun _ : ι ↦ Fin q) T (T ∪ E))
    (Ω : EuclideanSpace ℂ (ι → Fin q)) :
    ∃ w : Word (S.system q) ((S.changeOwner T Q).system q),
      w.IsAllowed ∧ w.UsesOnly {P₀, Q} ∧ w.sourceCount ≤ 1 ∧
      w.op = reindex (blockConfigEquiv (S.changeOwner T Q).owner fun _ ↦ Fin q).symm
        (blockConfigEquiv S.owner fun _ ↦ Fin q).symm
        (configBirthOp Finset.subset_union_left σ) ∧
      ‖toEuclideanLin w.op (S.refVec Ω) - (S.changeOwner T Q).refVec Ω‖ ≤
        σ.error Finset.subset_union_left Ω := by
  have herr : ∀ w : Word (S.system q) ((S.changeOwner T Q).system q),
      w.op = reindex (blockConfigEquiv (S.changeOwner T Q).owner fun _ ↦ Fin q).symm
        (blockConfigEquiv S.owner fun _ ↦ Fin q).symm
        (configBirthOp Finset.subset_union_left σ) →
      ‖toEuclideanLin w.op (S.refVec Ω) - (S.changeOwner T Q).refVec Ω‖ ≤
        σ.error Finset.subset_union_left Ω := fun w hw ↦ by
    rw [hw, refVec, refVec, norm_toEuclideanLin_reindex_sub]
    exact norm_toEuclideanLin_configBirthOp_sub_le _ σ Ω
  by_cases hQP : Q = P₀
  · subst Q
    have hS := S.changeOwner_eq_self hTP
    rw [hS] at herr ⊢
    obtain ⟨w, hA, hR, hn, hop⟩ := exists_privateBirthWord_of_environment hTP hU σ
    exact ⟨w, hA, hR.mono (by simp), hn.trans_le zero_le_one, hop, herr w hop⟩
  · let w := environmentBirthWord hTE hTP hU hQP σ
    have hop := op_environmentBirthWord hTE hTP hU hQP σ
    exact ⟨w, isAllowed_environmentBirthWord hTE hTP hU hQP σ,
      usesOnly_environmentBirthWord hTE hTP hU hQP σ,
      (sourceCount_environmentBirthWord hTE hTP hU hQP σ).le, hop, herr w hop⟩

/-- A death with a prescribed environment is an allowed circuit using only
the two parties of the death, with at most one pair effect and no pair
sources. Its operator and reference-vector error are those of the birth in
the reverse sheet bases. Source: polynomial-PEPS, Lemma 6.5,
`05-frames.tex`, lines 439–446. -/
theorem exists_deathChain_of_environment {E : Finset ι}
    (hTE : Disjoint T E) (hTP : ∀ x ∈ T, S.owner x = P₀)
    (hU : ∀ x ∉ T ∪ E, S.owner x = P₀)
    (σ : SplittingData (fun _ : ι ↦ Fin q) T (T ∪ E))
    (Ω : EuclideanSpace ℂ (ι → Fin q)) :
    ∃ M : PartyCircuit (ChainGate (P := P)) ((S.changeOwner T Q).system q) (S.system q),
      M.IsAllowed chainEv ChainGate.IsAllowed ∧ M.UsesOnly {P₀, Q} ∧
      M.ForallGate (fun _ _ _ g ↦ Sum.isRight g) ∧ M.numGates ≤ 1 ∧
      M.op chainEv = reindex (blockConfigEquiv S.owner fun _ ↦ Fin q).symm
        (blockConfigEquiv (S.changeOwner T Q).owner fun _ ↦ Fin q).symm
        (configBirthOp Finset.subset_union_left σ) ∧
      ‖toEuclideanLin (M.op chainEv) ((S.changeOwner T Q).refVec Ω) - S.refVec Ω‖ ≤
        σ.error Finset.subset_union_left Ω := by
  have herr : ∀ M : PartyCircuit (ChainGate (P := P)) ((S.changeOwner T Q).system q)
      (S.system q), M.op chainEv = reindex (blockConfigEquiv S.owner fun _ ↦ Fin q).symm
        (blockConfigEquiv (S.changeOwner T Q).owner fun _ ↦ Fin q).symm
        (configBirthOp Finset.subset_union_left σ) →
      ‖toEuclideanLin (M.op chainEv) ((S.changeOwner T Q).refVec Ω) - S.refVec Ω‖ ≤
        σ.error Finset.subset_union_left Ω := fun M hM ↦ by
    rw [hM, refVec, refVec, norm_toEuclideanLin_reindex_sub]
    exact norm_toEuclideanLin_configBirthOp_sub_le _ σ Ω
  by_cases hQP : Q = P₀
  · subst Q
    have hS := S.changeOwner_eq_self hTP
    rw [hS] at herr ⊢
    obtain ⟨M, hA, hR, hG, hn, hop⟩ := exists_privateDeathChain_of_environment hTP hU σ
    exact ⟨M, hA, hR.mono (by simp), hG, hn.trans_le zero_le_one, hop, herr M hop⟩
  · let M := environmentDeathChain hTE hTP hU hQP σ
    have hop := op_environmentDeathChain hTE hTP hU hQP σ
    exact ⟨M, isAllowed_environmentDeathChain hTE hTP hU hQP σ,
      usesOnly_environmentDeathChain hTE hTP hU hQP σ,
      forallGate_isRight_environmentDeathChain hTE hTP hU hQP σ,
      (numGates_environmentDeathChain hTE hTP hU hQP σ).le, hop, herr M hop⟩

/-- **Lemma `lem:birth` (birth) for given splitting data: the birth is a bounded change
involving only `P∘` and `Q∘`.** In a sheet `S`, let `T` be a set of sites owned by `P∘`, `E`
the set of sites not owned by `P∘`, and `σ` splitting data for the cut `T`, `E`,
`U = Λ ∖ (T ∪ E)`. There is an allowed word `w` from the sheet `S` to the sheet in which `T` is
owned by `Q∘`, such that:

* `w` uses only `P∘` and `Q∘` and at most one normalized pair source;
* in canonical coordinates the operator of `w` is the canonical map `𝐁` of `σ`;
* the reference-vector error is at most the error of `σ`.

For `Q∘ ≠ P∘` the word prepares the pair state `s` on `T` held by `Q∘` and `B_T` held by `P∘`
and applies `Vᴴ (1_{B_T} ⊗ ⟨s| (1_T ⊗ V))` at `P∘`; for `Q∘ = P∘` it is the private contraction
`Kᴴ K` at `P∘`. Source: Lemma 6.5, `05-frames.tex`, lines 396–407, proof lines 413–433 and
445–446; one-dimensional note, Lemma `lem:birth`, `part2b_mps_protocol.tex`, lines 70–76, proof
lines 82–90. -/
theorem exists_birthWord_of_splittingData (hTP : ∀ x ∈ T, S.owner x = P₀)
    (σ : SplittingData (fun _ : ι ↦ Fin q) T (T ∪ S.birthEnv P₀))
    (Ω : EuclideanSpace ℂ (ι → Fin q)) :
    ∃ w : Word (S.system q) ((S.changeOwner T Q).system q),
      w.IsAllowed ∧ w.UsesOnly {P₀, Q} ∧ w.sourceCount ≤ 1 ∧
      w.op = reindex (blockConfigEquiv (S.changeOwner T Q).owner fun _ ↦ Fin q).symm
        (blockConfigEquiv S.owner fun _ ↦ Fin q).symm
        (configBirthOp Finset.subset_union_left σ) ∧
      ‖toEuclideanLin w.op (S.refVec Ω) - (S.changeOwner T Q).refVec Ω‖ ≤
        σ.error Finset.subset_union_left Ω :=
  S.exists_birthWord_of_environment (S.disjoint_birthEnv hTP) hTP
    (fun x hx ↦ ((S.changeOwner_birth_owners (Q := Q) hTP).1 x (Finset.mem_compl.mpr hx))) σ Ω

/-- **Lemma `lem:birth` (death) for given splitting data: the death is a bounded change
involving only `P∘` and `Q∘`.** Let `S` be the sheet *after* the death, in which `T` is owned
by `P∘`, and `σ` splitting data for the cut `T`, `E` of `S`. There is an allowed monomial from
the sheet in which `T` is owned by `Q∘` to `S`, using only `P∘` and `Q∘`, whose gates are pair
effects and at most one, whose operator in canonical coordinates is the canonical map `𝐁` of
`σ`, with reference-vector error at most the error of `σ`. For `Q∘ ≠ P∘` the monomial applies
`(1_{B_T} ⊗ Kᴴ) V` at `P∘` and the normalized pair effect `⟨s|` on `T` at `Q∘` and `B_T` at
`P∘`; for `Q∘ = P∘` it is the private contraction `Kᴴ K` at `P∘`. Source: Lemma 6.5,
`05-frames.tex`, lines 408–410, proof lines 439–446; one-dimensional note, Lemma `lem:birth`,
`part2b_mps_protocol.tex`, lines 77–80, proof lines 91–93. -/
theorem exists_deathChain_of_splittingData (hTP : ∀ x ∈ T, S.owner x = P₀)
    (σ : SplittingData (fun _ : ι ↦ Fin q) T (T ∪ S.birthEnv P₀))
    (Ω : EuclideanSpace ℂ (ι → Fin q)) :
    ∃ M : PartyCircuit (ChainGate (P := P)) ((S.changeOwner T Q).system q) (S.system q),
      M.IsAllowed chainEv ChainGate.IsAllowed ∧ M.UsesOnly {P₀, Q} ∧
      M.ForallGate (fun _ _ _ g ↦ Sum.isRight g) ∧ M.numGates ≤ 1 ∧
      M.op chainEv = reindex (blockConfigEquiv S.owner fun _ ↦ Fin q).symm
        (blockConfigEquiv (S.changeOwner T Q).owner fun _ ↦ Fin q).symm
        (configBirthOp Finset.subset_union_left σ) ∧
      ‖toEuclideanLin (M.op chainEv) ((S.changeOwner T Q).refVec Ω) - S.refVec Ω‖ ≤
        σ.error Finset.subset_union_left Ω :=
  S.exists_deathChain_of_environment (S.disjoint_birthEnv hTP) hTP
    (fun x hx ↦ ((S.changeOwner_birth_owners (Q := Q) hTP).1 x (Finset.mem_compl.mpr hx))) σ Ω

end Birth

/-! ### Two-sheet exchange -/

section Exchange

variable (S₁ S₂ : Sheet ι P) (Y : Finset ι) (P₀ : P) (Z : Finset ι)

/-- **The map of an exchange, `C = D_U F_A F_Y`**, on two copies of the configurations of the
sites: the swap `F_Y` of the two sheets on `Y`, the private swap `F_A` on `A = Y ∖ Z`, and the
buffer correction `D_U` on the two copies of `U = Λ ∖ Z`, for splitting data of the cut
`T = Z ∩ Y`, `E = Z ∖ Y`. Source: proof of Lemma 6.6, `05-frames.tex`, lines 503–527;
one-dimensional note, `part2b_mps_protocol.tex`, lines 128–142. -/
noncomputable def exchangeOp
    (σ : SplittingData (fun _ : ι ↦ Fin q) (Z ∩ Y) (Z ∩ Y ∪ Z \ Y)) :
    Matrix ((ι → Fin q) × (ι → Fin q)) ((ι → Fin q) × (ι → Fin q)) ℂ :=
  configBufferCorrection Finset.subset_union_left σ *
    reindex (Equiv.arrowProdEquivProdArrow ι _ _) (Equiv.arrowProdEquivProdArrow ι _ _)
      (pairSwapOp (X := fun _ : ι ↦ Fin q) (Y \ Z)) *
    reindex (Equiv.arrowProdEquivProdArrow ι _ _) (Equiv.arrowProdEquivProdArrow ι _ _)
      (pairSwapOp (X := fun _ : ι ↦ Fin q) Y)

omit [Fintype P] in
/-- **The net map of an exchange (`D_U F_A F_Y = D_U F_T`).** Source: `05-frames.tex`,
lines 516–525; one-dimensional note, `part2b_mps_protocol.tex`, lines 136–142. -/
theorem exchangeOp_eq
    (σ : SplittingData (fun _ : ι ↦ Fin q) (Z ∩ Y) (Z ∩ Y ∪ Z \ Y)) :
    exchangeOp Y Z σ =
      configBufferCorrection Finset.subset_union_left σ *
        reindex (Equiv.arrowProdEquivProdArrow ι _ _) (Equiv.arrowProdEquivProdArrow ι _ _)
          (pairSwapOp (X := fun _ : ι ↦ Fin q) (Z ∩ Y)) := by
  rw [exchangeOp, Matrix.mul_assoc, reindex_apply, reindex_apply, reindex_apply,
    submatrix_mul_equiv, pairSwapOp_mul_of_subset Finset.sdiff_subset,
    Finset.sdiff_sdiff_self_left, Finset.inter_comm Y Z]

section SwapIn

omit [Fintype P]

variable {S S' : Sheet ι P} {p : P} {v : ι}

/-- A site of `Y` in the block of `p` of `S'` lies in the block of `p` of `swapIn S S' Y`. -/
private theorem mem_blockPreimage_swapIn_of_mem (hv : v ∈ blockPreimage S'.owner {p})
    (hY : v ∈ Y) : v ∈ blockPreimage (swapIn S S' Y).owner {p} := by
  have h := (mem_blockPreimage_singleton S'.owner).mp hv
  exact (mem_blockPreimage_singleton (swapIn S S' Y).owner).mpr ((ite_eq_left hY).trans h)

/-- A site outside `Y` in the block of `p` of `S` lies in the block of `p` of `swapIn S S' Y`. -/
private theorem mem_blockPreimage_swapIn_of_notMem (hv : v ∈ blockPreimage S.owner {p})
    (hY : v ∉ Y) : v ∈ blockPreimage (swapIn S S' Y).owner {p} := by
  have h := (mem_blockPreimage_singleton S.owner).mp hv
  exact (mem_blockPreimage_singleton (swapIn S S' Y).owner).mpr ((ite_eq_right hY).trans h)

/-- A site of `Y` in the block of `p` of `swapIn S S' Y` lies in the block of `p` of `S'`. -/
private theorem mem_blockPreimage_of_mem_swapIn (hv : v ∈ blockPreimage (swapIn S S' Y).owner {p})
    (hY : v ∈ Y) : v ∈ blockPreimage S'.owner {p} := by
  have h := (mem_blockPreimage_singleton (swapIn S S' Y).owner).mp hv
  exact (mem_blockPreimage_singleton S'.owner).mpr ((ite_eq_left hY).symm.trans h)

/-- A site outside `Y` in the block of `p` of `swapIn S S' Y` lies in the block of `p` of `S`. -/
private theorem mem_blockPreimage_of_mem_swapIn_of_notMem
    (hv : v ∈ blockPreimage (swapIn S S' Y).owner {p}) (hY : v ∉ Y) :
    v ∈ blockPreimage S.owner {p} := by
  have h := (mem_blockPreimage_singleton (swapIn S S' Y).owner).mp hv
  exact (mem_blockPreimage_singleton S.owner).mpr ((ite_eq_right hY).symm.trans h)

end SwapIn

omit [Fintype P] in
/-- **The renaming of an exchange at one party.** The basis of `p` on the two sheets after the
exchange is that on the two sheets before it, the configurations of the sites of `Y` changing
sheet. -/
def swapInEquiv (p : P) :
    (swapIn S₁ S₂ Y).system q p × (swapIn S₂ S₁ Y).system q p ≃
      S₁.system q p × S₂.system q p where
  toFun b := (fun v ↦ if hv : (v : ι) ∈ Y then
        b.2 ⟨v, mem_blockPreimage_swapIn_of_mem Y v.2 hv⟩
      else b.1 ⟨v, mem_blockPreimage_swapIn_of_notMem Y v.2 hv⟩,
    fun v ↦ if hv : (v : ι) ∈ Y then
        b.1 ⟨v, mem_blockPreimage_swapIn_of_mem Y v.2 hv⟩
      else b.2 ⟨v, mem_blockPreimage_swapIn_of_notMem Y v.2 hv⟩)
  invFun a := (fun v ↦ if hv : (v : ι) ∈ Y then
        a.2 ⟨v, mem_blockPreimage_of_mem_swapIn Y v.2 hv⟩
      else a.1 ⟨v, mem_blockPreimage_of_mem_swapIn_of_notMem Y v.2 hv⟩,
    fun v ↦ if hv : (v : ι) ∈ Y then
        a.1 ⟨v, mem_blockPreimage_of_mem_swapIn Y v.2 hv⟩
      else a.2 ⟨v, mem_blockPreimage_of_mem_swapIn_of_notMem Y v.2 hv⟩)
  left_inv b := by
    refine Prod.ext (funext fun v ↦ ?_) (funext fun v ↦ ?_) <;>
      by_cases hv : (v : ι) ∈ Y <;> simp [hv]
  right_inv a := by
    refine Prod.ext (funext fun v ↦ ?_) (funext fun v ↦ ?_) <;>
      by_cases hv : (v : ι) ∈ Y <;> simp [hv]

omit [Fintype P] in
/-- **The renaming `ℛ` of an exchange**: the relabelling of the bases of every party along
`swapInEquiv`; every register keeps its party. Source: proof of Lemma 6.6, `05-frames.tex`,
lines 485–490; one-dimensional note, `part2b_mps_protocol.tex`, lines 128–131. -/
noncomputable def renameWord :
    Word (fun p ↦ S₁.system q p × S₂.system q p)
      (fun p ↦ (swapIn S₁ S₂ Y).system q p × (swapIn S₂ S₁ Y).system q p) :=
  PartyCircuit.relabel (swapInEquiv S₁ S₂ Y)

omit [Fintype P] in
/-- The swap `F_Y` read on the two sheets before and after the exchange is the renaming. -/
private theorem twoConfigEquiv_symm_permCongr_pairSwap
    (y : Config fun p ↦ (swapIn S₁ S₂ Y).system q p × (swapIn S₂ S₁ Y).system q p) :
    (twoConfigEquiv q S₁ S₂).symm ((Equiv.arrowProdEquivProdArrow ι _ _).permCongr
        (pairSwap (X := fun _ : ι ↦ Fin q) Y) (twoConfigEquiv q _ _ y)) =
      Equiv.piCongrRight (swapInEquiv S₁ S₂ Y) y := by
  rw [permCongr_pairSwap_apply]
  funext p
  refine Prod.ext (funext fun v ↦ ?_) (funext fun v ↦ ?_)
  · have hv := (mem_blockPreimage_singleton _).mp v.2
    by_cases hY : (v : ι) ∈ Y
    · exact (ite_eq_left hY).trans ((twoConfigEquiv_snd_eq _ _ y
        (show (swapIn S₂ S₁ Y).owner v = p from
          (ite_eq_left hY).trans hv)).trans (by simp [swapInEquiv, hY]))
    · exact (ite_eq_right hY).trans ((twoConfigEquiv_fst_eq _ _ y
        (show (swapIn S₁ S₂ Y).owner v = p from
          (ite_eq_right hY).trans hv)).trans (by simp [swapInEquiv, hY]))
  · have hv := (mem_blockPreimage_singleton _).mp v.2
    by_cases hY : (v : ι) ∈ Y
    · exact (ite_eq_left hY).trans ((twoConfigEquiv_fst_eq _ _ y
        (show (swapIn S₁ S₂ Y).owner v = p from
          (ite_eq_left hY).trans hv)).trans (by simp [swapInEquiv, hY]))
    · exact (ite_eq_right hY).trans ((twoConfigEquiv_snd_eq _ _ y
        (show (swapIn S₂ S₁ Y).owner v = p from
          (ite_eq_right hY).trans hv)).trans (by simp [swapInEquiv, hY]))

/-- **The renaming in canonical coordinates** is the swap `F_Y` of the two sheets on `Y`.
Source: `05-frames.tex`, lines 490–494; one-dimensional note, `part2b_mps_protocol.tex`,
lines 130–131. -/
theorem op_renameWord :
    (renameWord (q := q) S₁ S₂ Y).op =
      reindex (twoConfigEquiv q (swapIn S₁ S₂ Y) (swapIn S₂ S₁ Y)).symm
        (twoConfigEquiv q S₁ S₂).symm
        (reindex (Equiv.arrowProdEquivProdArrow ι _ _) (Equiv.arrowProdEquivProdArrow ι _ _)
          (pairSwapOp (X := fun _ : ι ↦ Fin q) Y)) := by
  ext y x
  rw [renameWord, Word.op, PartyCircuit.op_relabel, reindex_apply, submatrix_apply,
    Equiv.symm_symm, Equiv.symm_symm, reindex_pairSwapOp]
  simp only [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply, Option.mem_def,
    Option.some.injEq]
  refine if_congr ?_ rfl rfl
  rw [← twoConfigEquiv_symm_permCongr_pairSwap, Equiv.symm_apply_eq]

omit [Fintype P] in
/-- The renaming is allowed. -/
theorem isAllowed_renameWord : (renameWord (q := q) S₁ S₂ Y).IsAllowed :=
  Word.isAllowed_relabel _

omit [Fintype P] in
/-- The renaming has no pair source. -/
theorem sourceCount_renameWord : (renameWord (q := q) S₁ S₂ Y).sourceCount = 0 :=
  rfl

variable (hZ : ∀ x ∉ Z, S₁.owner x = P₀ ∧ S₂.owner x = P₀)

include hZ in
omit [Fintype ι] [Fintype P] [DecidableEq P] in
/-- After an exchange, every site outside `Z` is owned by `P∘` on the first sheet. -/
theorem swapIn_owner_eq_of_notMem_union (x : ι) (hx : x ∉ Z ∩ Y ∪ Z \ Y) :
    (swapIn S₁ S₂ Y).owner x = P₀ :=
  (swapIn_owner_eq_of_notMem S₁ S₂ Y P₀ hZ hx).1

include hZ in
omit [Fintype ι] [Fintype P] [DecidableEq P] in
/-- After an exchange, every site outside `Z` is owned by `P∘` on the second sheet. -/
theorem swapIn_owner_eq_of_notMem_union' (x : ι)
    (hx : x ∉ Z ∩ Y ∪ Z \ Y) : (swapIn S₂ S₁ Y).owner x = P₀ :=
  (swapIn_owner_eq_of_notMem S₁ S₂ Y P₀ hZ hx).2

omit [Fintype P] in
/-- **The basis of `P∘` on the two sheets after an exchange**, read on the sites of `Z` it owns
on each sheet and on the two copies of `U = Λ ∖ Z`. -/
def exchangeEquivP :
    (swapIn S₁ S₂ Y).system q P₀ × (swapIn S₂ S₁ Y).system q P₀ ≃
      (({x // x ∈ Z ∩ Y ∪ Z \ Y ∧ (swapIn S₁ S₂ Y).owner x = P₀} → Fin q) ×
        ({x // x ∈ Z ∩ Y ∪ Z \ Y ∧ (swapIn S₂ S₁ Y).owner x = P₀} → Fin q)) ×
      (ComplConfig (fun _ : ι ↦ Fin q) (Z ∩ Y ∪ Z \ Y) ×
        ComplConfig (fun _ : ι ↦ Fin q) (Z ∩ Y ∪ Z \ Y)) :=
  ((complSplitEquiv q _ (swapIn_owner_eq_of_notMem_union S₁ S₂ Y P₀ Z hZ)).prodCongr
      (complSplitEquiv q _ (swapIn_owner_eq_of_notMem_union' S₁ S₂ Y P₀ Z hZ))).trans
    (Equiv.prodProdProdComm _ _ _ _)

omit [Fintype P] in
/-- **The corrections `D_U F_A` of an exchange at `P∘`**: the matrix `W` of
`ManyBody.correctionMatrix` on the two copies of `U`, the identity on the other sites of `P∘`.
Source: proof of Lemma 6.6, `05-frames.tex`, lines 503–515. -/
noncomputable def correctionAt
    (σ : SplittingData (fun _ : ι ↦ Fin q) (Z ∩ Y) (Z ∩ Y ∪ Z \ Y)) :
    Matrix ((swapIn S₁ S₂ Y).system q P₀ × (swapIn S₂ S₁ Y).system q P₀)
      ((swapIn S₁ S₂ Y).system q P₀ × (swapIn S₂ S₁ Y).system q P₀) ℂ :=
  reindex (exchangeEquivP S₁ S₂ Y P₀ Z hZ).symm (exchangeEquivP S₁ S₂ Y P₀ Z hZ).symm
    ((1 : Matrix _ _ ℂ) ⊗ₖ correctionMatrix σ (Y \ Z))

omit [Fintype P] in
set_option synthInstance.maxSize 512 in
/-- The corrections of an exchange at `P∘` form a contraction. -/
theorem norm_correctionAt_le_one
    (σ : SplittingData (fun _ : ι ↦ Fin q) (Z ∩ Y) (Z ∩ Y ∪ Z \ Y)) :
    ‖correctionAt S₁ S₂ Y P₀ Z hZ σ‖ ≤ 1 :=
  (l2_opNorm_reindex_le (exchangeEquivP S₁ S₂ Y P₀ Z hZ).symm (exchangeEquivP S₁ S₂ Y P₀ Z hZ).symm
    ((1 : Matrix _ _ ℂ) ⊗ₖ correctionMatrix σ (Y \ Z))).trans
      ((l2_opNorm_one_kronecker_le _).trans (norm_correctionMatrix_le_one σ _))

omit [Fintype P] in
/-- **The corrections of an exchange as a word**: the local operation `correctionAt` at `P∘`
and the identity at the other parties. Source: proof of Lemma 6.6, `05-frames.tex`,
lines 503–515; one-dimensional note, `part2b_mps_protocol.tex`, lines 133–137. -/
noncomputable def correctionWord
    (σ : SplittingData (fun _ : ι ↦ Fin q) (Z ∩ Y) (Z ∩ Y ∪ Z \ Y)) :
    Word (fun p ↦ (swapIn S₁ S₂ Y).system q p × (swapIn S₂ S₁ Y).system q p)
      (fun p ↦ (swapIn S₁ S₂ Y).system q p × (swapIn S₂ S₁ Y).system q p) :=
  PartyCircuit.localOps (Function.update (fun _ ↦ 1) P₀ (correctionAt S₁ S₂ Y P₀ Z hZ σ))

/-- **The corrections in canonical coordinates** are `D_U F_A`. Source: `05-frames.tex`,
lines 504–515. -/
theorem op_correctionWord
    (σ : SplittingData (fun _ : ι ↦ Fin q) (Z ∩ Y) (Z ∩ Y ∪ Z \ Y)) :
    (correctionWord S₁ S₂ Y P₀ Z hZ σ).op =
      reindex (twoConfigEquiv q (swapIn S₁ S₂ Y) (swapIn S₂ S₁ Y)).symm
        (twoConfigEquiv q (swapIn S₁ S₂ Y) (swapIn S₂ S₁ Y)).symm
        (configBufferCorrection Finset.subset_union_left σ *
          reindex (Equiv.arrowProdEquivProdArrow ι _ _) (Equiv.arrowProdEquivProdArrow ι _ _)
            (pairSwapOp (X := fun _ : ι ↦ Fin q) (Y \ Z))) := by
  set S₁' := swapIn S₁ S₂ Y
  set S₂' := swapIn S₂ S₁ Y
  have hU₁ := swapIn_owner_eq_of_notMem_union S₁ S₂ Y P₀ Z hZ
  have hU₂ := swapIn_owner_eq_of_notMem_union' S₁ S₂ Y P₀ Z hZ
  have hAB : Z ∩ Y ⊆ Z ∩ Y ∪ Z \ Y := Finset.subset_union_left
  rw [configBufferCorrection_mul_pairSwapOp_eq _ σ (sdiff_subset_compl_inter_union_sdiff Y Z)]
  ext y x
  rw [correctionWord, Word.op, PartyCircuit.op_localOps, piKronecker_apply,
    ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ P₀), Function.update_self,
    Finset.prod_congr rfl fun r hr ↦ by
      rw [Function.update_of_ne (Finset.ne_of_mem_erase hr), one_apply],
    Finset.prod_boole, correctionAt, reindex_apply, submatrix_apply, Equiv.symm_symm,
    kroneckerMap_apply, one_apply, reindex_apply, submatrix_apply, Equiv.symm_symm,
    submatrix_apply, submatrix_apply, kroneckerMap_apply, one_apply, mul_right_comm,
    ite_zero_mul_ite_zero, mul_one]
  -- the parts on the two copies of `U`
  have hW : ∀ z : Config fun p ↦ S₁'.system q p × S₂'.system q p,
      (exchangeEquivP S₁ S₂ Y P₀ Z hZ (z P₀)).2 = (Equiv.prodProdProdComm _ _ _ _
        (threeCutEquiv₂ (X := fun _ : ι ↦ Fin q) hAB (twoConfigEquiv q S₁' S₂' z))).2 := fun z ↦
    Prod.ext (funext fun v ↦ (twoConfigEquiv_fst_eq _ _ z (hU₁ v v.2)).symm)
      (funext fun v ↦ (twoConfigEquiv_snd_eq _ _ z (hU₂ v v.2)).symm)
  -- the agreement on the sites of `Z`
  have hZcut : (Equiv.prodProdProdComm _ _ _ _
        (threeCutEquiv₂ (X := fun _ : ι ↦ Fin q) hAB (twoConfigEquiv q S₁' S₂' y))).1 =
      (Equiv.prodProdProdComm _ _ _ _
        (threeCutEquiv₂ (X := fun _ : ι ↦ Fin q) hAB (twoConfigEquiv q S₁' S₂' x))).1 ↔
      ∀ v ∈ Z ∩ Y ∪ Z \ Y,
        (twoConfigEquiv q S₁' S₂' y).1 v = (twoConfigEquiv q S₁' S₂' x).1 v ∧
          (twoConfigEquiv q S₁' S₂' y).2 v = (twoConfigEquiv q S₁' S₂' x).2 v := by
    constructor
    · intro h v hv
      by_cases hA : v ∈ Z ∩ Y
      · exact ⟨congrFun (congrArg (fun f ↦ f.1.1) h) ⟨v, hA⟩,
          congrFun (congrArg (fun f ↦ f.2.1) h) ⟨v, hA⟩⟩
      · have hM := Finset.mem_sdiff.mpr ⟨hv, hA⟩
        exact ⟨congrFun (congrArg (fun f ↦ f.1.2) h) ⟨v, hM⟩,
          congrFun (congrArg (fun f ↦ f.2.2) h) ⟨v, hM⟩⟩
    · intro h
      refine Prod.ext (Prod.ext (funext fun w ↦ ?_) (funext fun w ↦ ?_))
        (Prod.ext (funext fun w ↦ ?_) (funext fun w ↦ ?_))
      · exact (h w (Finset.mem_union_left _ w.2)).1
      · exact (h w (Finset.mem_sdiff.mp w.2).1).1
      · exact (h w (Finset.mem_union_left _ w.2)).2
      · exact (h w (Finset.mem_sdiff.mp w.2).1).2
  have hP : ((exchangeEquivP S₁ S₂ Y P₀ Z hZ (y P₀)).1 = (exchangeEquivP S₁ S₂ Y P₀ Z hZ (x P₀)).1 ∧
      ∀ r ∈ Finset.univ.erase P₀, y r = x r) ↔
      ∀ v ∈ Z ∩ Y ∪ Z \ Y,
        (twoConfigEquiv q S₁' S₂' y).1 v = (twoConfigEquiv q S₁' S₂' x).1 v ∧
          (twoConfigEquiv q S₁' S₂' y).2 v = (twoConfigEquiv q S₁' S₂' x).2 v := by
    constructor
    · rintro ⟨h₁, h₂⟩ v hv
      constructor
      · by_cases hvP : S₁'.owner v = P₀
        · rw [twoConfigEquiv_fst_eq _ _ y hvP, twoConfigEquiv_fst_eq _ _ x hvP]
          exact congrFun (congrArg (fun f ↦ f.1) h₁) ⟨v, hv, hvP⟩
        · rw [twoConfigEquiv_fst_eq _ _ y rfl, twoConfigEquiv_fst_eq _ _ x rfl,
            h₂ _ (Finset.mem_erase.mpr ⟨hvP, Finset.mem_univ _⟩)]
      · by_cases hvP : S₂'.owner v = P₀
        · rw [twoConfigEquiv_snd_eq _ _ y hvP, twoConfigEquiv_snd_eq _ _ x hvP]
          exact congrFun (congrArg (fun f ↦ f.2) h₁) ⟨v, hv, hvP⟩
        · rw [twoConfigEquiv_snd_eq _ _ y rfl, twoConfigEquiv_snd_eq _ _ x rfl,
            h₂ _ (Finset.mem_erase.mpr ⟨hvP, Finset.mem_univ _⟩)]
    · intro h
      refine ⟨Prod.ext (funext fun w ↦ ?_) (funext fun w ↦ ?_), fun r hr ↦ ?_⟩
      · have h' := (h w w.2.1).1
        rwa [twoConfigEquiv_fst_eq _ _ y w.2.2, twoConfigEquiv_fst_eq _ _ x w.2.2] at h'
      · have h' := (h w w.2.1).2
        rwa [twoConfigEquiv_snd_eq _ _ y w.2.2, twoConfigEquiv_snd_eq _ _ x w.2.2] at h'
      have hrP := Finset.ne_of_mem_erase hr
      refine Prod.ext (funext fun v ↦ ?_) (funext fun v ↦ ?_)
      · have hvr := (mem_blockPreimage_singleton _).mp v.2
        have hvB : (v : ι) ∈ Z ∩ Y ∪ Z \ Y := by
          by_contra hvB
          exact hrP (hvr.symm.trans (hU₁ v hvB))
        have h' := (h v hvB).1
        rwa [twoConfigEquiv_fst_eq _ _ y hvr, twoConfigEquiv_fst_eq _ _ x hvr] at h'
      · have hvr := (mem_blockPreimage_singleton _).mp v.2
        have hvB : (v : ι) ∈ Z ∩ Y ∪ Z \ Y := by
          by_contra hvB
          exact hrP (hvr.symm.trans (hU₂ v hvB))
        have h' := (h v hvB).2
        rwa [twoConfigEquiv_snd_eq _ _ y hvr, twoConfigEquiv_snd_eq _ _ x hvr] at h'
  rw [hW y, hW x]
  split_ifs with h₁ h₂ h₂
  · rfl
  · exact absurd ((hP.trans hZcut.symm).mp h₁) h₂
  · exact absurd ((hP.trans hZcut.symm).mpr h₂) h₁
  · rfl

omit [Fintype P] in
/-- The corrections of an exchange are allowed. -/
theorem isAllowed_correctionWord
    (σ : SplittingData (fun _ : ι ↦ Fin q) (Z ∩ Y) (Z ∩ Y ∪ Z \ Y)) :
    (correctionWord S₁ S₂ Y P₀ Z hZ σ).IsAllowed := by
  intro r
  by_cases hr : r = P₀
  · subst hr
    rw [Function.update_self]
    exact norm_correctionAt_le_one S₁ S₂ Y r Z hZ σ
  · rw [Function.update_of_ne hr, ← PEquiv.toMatrix_refl, ← Equiv.toPEquiv_refl]
    exact l2_opNorm_toMatrix_toPEquiv_le _

omit [Fintype P] in
/-- The corrections of an exchange use only `P∘`. -/
theorem usesOnly_correctionWord
    (σ : SplittingData (fun _ : ι ↦ Fin q) (Z ∩ Y) (Z ∩ Y ∪ Z \ Y)) :
    (correctionWord S₁ S₂ Y P₀ Z hZ σ).UsesOnly {P₀} := fun r hr ↦
  ⟨rfl, fun y x ↦ by
    rw [Function.update_of_ne hr, one_apply, cast_eq]
    split_ifs <;> rfl⟩

omit [Fintype P] in
/-- The corrections of an exchange have no pair source. -/
theorem sourceCount_correctionWord
    (σ : SplittingData (fun _ : ι ↦ Fin q) (Z ∩ Y) (Z ∩ Y ∪ Z \ Y)) :
    (correctionWord S₁ S₂ Y P₀ Z hZ σ).sourceCount = 0 :=
  rfl

/-- **The exchange in canonical coordinates**: the renaming followed by the corrections is
`C = D_U F_A F_Y`. Source: `05-frames.tex`, lines 512–527. -/
theorem op_comp_renameWord_correctionWord
    (σ : SplittingData (fun _ : ι ↦ Fin q) (Z ∩ Y) (Z ∩ Y ∪ Z \ Y)) :
    Word.op (PartyCircuit.comp (renameWord S₁ S₂ Y) (correctionWord S₁ S₂ Y P₀ Z hZ σ)) =
      reindex (twoConfigEquiv q (swapIn S₁ S₂ Y) (swapIn S₂ S₁ Y)).symm
        (twoConfigEquiv q S₁ S₂).symm (exchangeOp Y Z σ) := by
  rw [Word.op_comp, op_correctionWord, op_renameWord, exchangeOp]
  simp only [reindex_apply (twoConfigEquiv q (swapIn S₁ S₂ Y) (swapIn S₂ S₁ Y)).symm]
  exact submatrix_mul_equiv _ _ _ _ _

include hZ in
/-- **Lemma `lem:exchange` (two-sheet exchange) for given splitting data: the exchange is a
relabelling followed by private corrections at `P∘`.** Consider two sheets and a region `Y`.
Inside `Y`, exchange the two ownership assignments; outside `Y`, keep both. Let `P∘` be a party,
`Z` a set of sites containing every site whose two owners are not both `P∘` (in Lemma 6.6 the
set of these sites together with the hole parts `H⁺(F₁) ∪ H⁺(F₂)`; on sheets,
`exchangeEnv S₁ S₂ P∘` with `owner_eq_of_notMem_exchangeEnv`), `T = Z ∩ Y`, `E = Z ∖ Y` and
`U = Λ ∖ Z`, and `σ` splitting data for this cut. Then `C = D_U F_T`, and there is an allowed
word `c` using only `P∘` without pair sources such that the renaming `ℛ` (`renameWord`, a
relabelling of the bases of the parties whose sites change sheet, no register changing party)
followed by `c`:

* has, in canonical coordinates, the operator `C = D_U F_A F_Y`;
* moves `Ω ⊗ Ω` on the two sheets by at most `4` times the error of `σ`, for a unit vector `Ω`.

As in the statement of Lemma 6.6, the exchange uses `P∘` and the owners of the registers being
renamed; it has no gate, so it is a bounded change for every set of participants
(`Word.isBoundedChange_toOriginalCircuit_of_sourceCount_eq_zero`). Source: Lemma 6.6,
`05-frames.tex`, lines 460–479, proof lines 481–561; one-dimensional note, Lemma
`lem:exchange`, `part2b_mps_protocol.tex`, lines 112–126, proof lines 127–155. -/
theorem exists_exchangeWord_of_splittingData {Ω : EuclideanSpace ℂ (ι → Fin q)} (hΩ : ‖Ω‖ = 1)
    (σ : SplittingData (fun _ : ι ↦ Fin q) (Z ∩ Y) (Z ∩ Y ∪ Z \ Y)) :
    exchangeOp Y Z σ =
        configBufferCorrection Finset.subset_union_left σ *
          reindex (Equiv.arrowProdEquivProdArrow ι _ _) (Equiv.arrowProdEquivProdArrow ι _ _)
            (pairSwapOp (X := fun _ : ι ↦ Fin q) (Z ∩ Y)) ∧
      ∃ c : Word (fun p ↦ (swapIn S₁ S₂ Y).system q p × (swapIn S₂ S₁ Y).system q p)
          (fun p ↦ (swapIn S₁ S₂ Y).system q p × (swapIn S₂ S₁ Y).system q p),
        c.IsAllowed ∧ c.UsesOnly {P₀} ∧ c.sourceCount = 0 ∧
        Word.op (PartyCircuit.comp (renameWord S₁ S₂ Y) c) =
          reindex (twoConfigEquiv q (swapIn S₁ S₂ Y) (swapIn S₂ S₁ Y)).symm
            (twoConfigEquiv q S₁ S₂).symm (exchangeOp Y Z σ) ∧
        ‖toEuclideanLin (Word.op (PartyCircuit.comp (renameWord S₁ S₂ Y) c))
            (prodVec (S₁.refVec Ω) (S₂.refVec Ω)) -
          prodVec ((swapIn S₁ S₂ Y).refVec Ω) ((swapIn S₂ S₁ Y).refVec Ω)‖ ≤
            4 * σ.error Finset.subset_union_left Ω := by
  refine ⟨exchangeOp_eq Y Z σ, correctionWord S₁ S₂ Y P₀ Z hZ σ,
    isAllowed_correctionWord S₁ S₂ Y P₀ Z hZ σ, usesOnly_correctionWord S₁ S₂ Y P₀ Z hZ σ,
    sourceCount_correctionWord S₁ S₂ Y P₀ Z hZ σ,
    op_comp_renameWord_correctionWord S₁ S₂ Y P₀ Z hZ σ, ?_⟩
  rw [op_comp_renameWord_correctionWord, prodVec_refVec, prodVec_refVec,
    norm_toEuclideanLin_reindex_sub, exchangeOp_eq]
  exact norm_toEuclideanLin_configBufferCorrection_mul_pairSwapOp_sub_le _ σ hΩ

end Exchange

end Sheet

end QuantumCircuit.Party
