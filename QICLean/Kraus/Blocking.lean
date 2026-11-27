/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Kraus.Word
import QICLean.Kraus.Injectivity
import QICLean.Kraus.Transfer

import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fin.Tuple.Basic

/-!
# Physical blocking of finite Kraus families

Blocking `L` sites of a family $A = (A_i)_{i \in \iota}$ replaces the index set $\iota$ by the
words $w : \{0, \ldots, L - 1\} \to \iota$ of length $L$; the member at $w$ is the ordered
product $A_{w_0} \cdots A_{w_{L-1}}$. The definitions in this file evaluate words of blocks,
compare word spans before and after blocking, and identify the transfer map of the blocked
family with the $L$-th power of the transfer map.

For an index set `Fin d`, the words of length $L$ are also numbered by `Fin (d ^ L)`; the
blocked family on that numbering is the reindexing of the general one.

## Main definitions

* `Kraus.block` groups products of $L$ matrices into one family indexed by words.
* `Kraus.blockPhysDim` is the number of words of length $L$ over `Fin d`.
* `Kraus.decodeBlockEquiv` numbers the words of length $L$ over `Fin d`.
* `Kraus.blockTensor` is `Kraus.block` on that numbering.
* `Kraus.flattenBlockedWord` concatenates a word of numbered blocks.

## Main results

* `Kraus.evalWord_block` evaluates a word of blocks as the concatenated word.
* `Kraus.block_block` blocks twice as blocking once.
* `Kraus.isNBlkInjective_iff_isInjective_block` identifies fixed-length spanning with
  injectivity of the blocked family.
* `Kraus.transferMap_block` the transfer map of the blocked family is the $L$-th power.
* `Kraus.wordSpan_block` identifies blocked word spans with the original word spans at the
  multiplied length.
* `Kraus.IsNormal.block` preserves normality under positive-length
  blocking.
* `Kraus.evalWord_replicate` evaluates a constant word as a matrix power.
-/

open scoped Matrix

namespace Kraus

/-! ### Blocking into words -/

section Block

variable {ι n : Type*} [Fintype n] [DecidableEq n]

/-- Blocking `L` sites: the family indexed by the words `w : Fin L → ι` of length `L`, whose
member at `w` is the ordered product of the letters of `w`. -/
def block (A : ι → Matrix n n ℂ) (L : ℕ) : (Fin L → ι) → Matrix n n ℂ :=
  fun w => evalWord A (List.ofFn w)

@[simp] theorem block_apply (A : ι → Matrix n n ℂ) (L : ℕ) (w : Fin L → ι) :
    block A L w = evalWord A (List.ofFn w) := rfl

/-- A word of blocks evaluates to the concatenated word. -/
theorem evalWord_block (A : ι → Matrix n n ℂ) (L : ℕ) (ws : List (Fin L → ι)) :
    evalWord (block A L) ws = evalWord A (ws.flatMap List.ofFn) := by
  induction ws with
  | nil => rfl
  | cons w ws ih => simp [ih, evalWord_append]

/-- A configuration of `N` blocks of length `L` evaluates to the configuration of `N * L`
sites in which site `k` carries letter `k mod L` of block `k / L`. -/
theorem evalWord_block_ofFn (A : ι → Matrix n n ℂ) (L N : ℕ) (σ : Fin N → Fin L → ι) :
    evalWord (block A L) (List.ofFn σ) =
      evalWord A (List.ofFn fun k : Fin (N * L) => σ k.divNat k.modNat) := by
  rw [evalWord_block, List.ofFn_mul, List.flatMap_def, List.map_ofFn]
  congr 2
  refine congrArg List.ofFn (funext fun i => congrArg List.ofFn (funext fun j => ?_))
  have hlt : (i : ℕ) * L + j < N * L := by
    calc (i : ℕ) * L + j < (i + 1) * L := by rw [Nat.add_mul, one_mul]; omega
      _ ≤ N * L := Nat.mul_le_mul_right _ i.2
  have hdiv : (Fin.divNat (⟨i * L + j, hlt⟩ : Fin (N * L))) = i := by
    ext
    rw [Fin.coe_divNat, Fin.val_mk, Nat.add_comm, Nat.add_mul_div_right _ _ (Fin.pos j),
      Nat.div_eq_of_lt j.2, zero_add]
  have hmod : (Fin.modNat (⟨i * L + j, hlt⟩ : Fin (N * L))) = j := by
    ext; simp [Fin.modNat, Nat.mod_eq_of_lt j.2]
  simp [hdiv, hmod]

/-- Blocking `M` blocks of length `L` is blocking `M * L` sites. -/
theorem block_block (A : ι → Matrix n n ℂ) (L M : ℕ) (σ : Fin M → Fin L → ι) :
    block (block A L) M σ = block A (M * L) (fun k => σ k.divNat k.modNat) := by
  rw [block_apply, evalWord_block_ofFn, block_apply]

/-- Block injectivity at length `N` is injectivity of the family blocked at length `N`. -/
theorem isNBlkInjective_iff_isInjective_block (A : ι → Matrix n n ℂ) (N : ℕ) :
    IsNBlkInjective A N ↔ IsInjective (block A N) := Iff.rfl

/-- The one-letter span of a blocked family is the length-`L` word span of the
original family. -/
@[simp] theorem wordSpan_block_one (A : ι → Matrix n n ℂ) (L : ℕ) :
    wordSpan (block A L) 1 = wordSpan A L := by
  rw [wordSpan_one]
  rfl

/-- Blocking identifies words of length `k` in the blocked family with words
of length `k * L` in the original family. -/
theorem wordSpan_block (A : ι → Matrix n n ℂ) (L k : ℕ) :
    wordSpan (block A L) k = wordSpan A (k * L) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [wordSpan_succ, ih, wordSpan_block_one, ← wordSpan_add, Nat.succ_mul]

/-- Normality is preserved by blocking at a positive length. -/
theorem IsNormal.block {A : ι → Matrix n n ℂ}
    (hA : IsNormal A) {L : ℕ} (hL : 0 < L) :
    IsNormal (Kraus.block A L) := by
  obtain ⟨N, hNpos, hN⟩ := hA
  refine ⟨N, hNpos, ?_⟩
  change wordSpan (Kraus.block A L) N = ⊤
  rw [wordSpan_block]
  exact isNBlkInjective_of_le hNpos hN (Nat.le_mul_of_pos_right N hL)

/-- The transfer map of the family blocked at length `L` is the `L`-th power of the
transfer map. -/
theorem transferMap_block [Fintype ι] (A : ι → Matrix n n ℂ) (L : ℕ) :
    transferMap (block A L) = transferMap A ^ L := by
  classical
  induction L with
  | zero =>
      ext X : 1
      simp
  | succ L ih =>
      ext X : 1
      rw [pow_succ', Module.End.mul_apply, ← ih]
      simp only [transferMap_apply, block_apply, List.ofFn_succ, evalWord_cons,
        Matrix.conjTranspose_mul, Finset.mul_sum, Finset.sum_mul]
      rw [← (Fin.consEquiv (fun _ : Fin (L + 1) => ι)).sum_comp, Fintype.sum_prod_type]
      refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun w _ => ?_
      simp [Fin.consEquiv, Matrix.mul_assoc]

/-- Evaluating a repeated single-letter word gives a matrix power. -/
lemma evalWord_replicate (A : ι → Matrix n n ℂ) (i : ι) (L : ℕ) :
    evalWord A (List.replicate L i) = (A i) ^ L := by
  induction L with
  | zero => simp
  | succ n ih => rw [List.replicate_succ, evalWord, ih, pow_succ']

end Block

/-! ### Words numbered by `Fin (d ^ L)` -/

variable {d L : ℕ} {n : Type*} [Fintype n] [DecidableEq n]

/-- Blocked physical dimension: the number of length-`L` words over an alphabet of size `d`.

We implement this as `Fintype.card (Fin L → Fin d)` to avoid painful casts. -/
noncomputable def blockPhysDim (d L : ℕ) : ℕ :=
  Fintype.card (Fin L → Fin d)

lemma blockPhysDim_eq_pow (d L : ℕ) : blockPhysDim d L = d ^ L := by
  classical
  unfold blockPhysDim
  -- `Fintype.card_fun` gives `card (α → β) = card β ^ card α`.
  simp [Fintype.card_fin]

/-- Blocking preserves nonzero physical dimensions. -/
instance instNeZeroBlockPhysDim [NeZero d] : NeZero (blockPhysDim d L) := ⟨by
  rw [blockPhysDim_eq_pow]
  exact pow_ne_zero L (NeZero.ne d)⟩

/-- The physical alphabet after blocking one site is equivalent to the original alphabet. -/
noncomputable def singleBlockEquiv (d : ℕ) : Fin (blockPhysDim d 1) ≃ Fin d :=
  ((finCongr (blockPhysDim_eq_pow d 1)).trans finFunctionFinEquiv.symm).trans
    (Equiv.funUnique (Fin 1) (Fin d))

/-- Decode a blocked physical index into the corresponding length-`L` word. -/
noncomputable def decodeBlock (d L : ℕ) : Fin (blockPhysDim d L) → (Fin L → Fin d) :=
  finFunctionFinEquiv.symm ∘ Fin.cast (blockPhysDim_eq_pow d L)

/-- Turn a blocked physical index into a list (word) of length `L`. -/
noncomputable def wordOfBlock (d L : ℕ) (i : Fin (blockPhysDim d L)) : List (Fin d) :=
  List.ofFn (decodeBlock d L i)

@[simp] lemma length_wordOfBlock (d L : ℕ) (i : Fin (blockPhysDim d L)) :
    (wordOfBlock d L i).length = L := by
  classical
  simp [wordOfBlock]

@[simp] lemma wordOfBlock_one (d : ℕ) (i : Fin (blockPhysDim d 1)) :
    wordOfBlock d 1 i = [singleBlockEquiv d i] := by
  rfl

/-- `decodeBlock` is a bijection of the blocked index onto length-`L` words. -/
noncomputable def decodeBlockEquiv (d L : ℕ) :
    Fin (blockPhysDim d L) ≃ (Fin L → Fin d) :=
  (finCongr (blockPhysDim_eq_pow d L)).trans finFunctionFinEquiv.symm

@[simp] lemma decodeBlockEquiv_apply (d L : ℕ) (I : Fin (blockPhysDim d L)) :
    decodeBlockEquiv d L I = decodeBlock d L I := rfl

@[simp] lemma decodeBlock_decodeBlockEquiv_symm (d L : ℕ) (w : Fin L → Fin d) :
    decodeBlock d L ((decodeBlockEquiv d L).symm w) = w := by
  rw [← decodeBlockEquiv_apply, Equiv.apply_symm_apply]

/-- The family blocked at length `L`, with the words numbered by `Fin (blockPhysDim d L)`
through `decodeBlockEquiv`. -/
noncomputable def blockTensor (A : Fin d → Matrix n n ℂ) (L : ℕ) :
    Fin (blockPhysDim d L) → Matrix n n ℂ :=
  reindexPhysical (decodeBlockEquiv d L) (block A L)

/-- Numbering the words does not change the set of blocked matrices. -/
theorem range_blockTensor (A : Fin d → Matrix n n ℂ) (L : ℕ) :
    Set.range (blockTensor A L) = Set.range (block A L) :=
  (decodeBlockEquiv d L).surjective.range_comp _

@[simp] lemma blockTensor_one_apply (A : Fin d → Matrix n n ℂ)
    (i : Fin (blockPhysDim d 1)) :
    blockTensor A 1 i = A (singleBlockEquiv d i) := by
  change evalWord A (wordOfBlock d 1 i) = _
  simp [evalWord]

/-- Equivalence between `N`-block injectivity and injectivity of the blocked
tensor `blockTensor A N`. -/
lemma isNBlkInjective_iff_blockTensor_isInjective (A : Fin d → Matrix n n ℂ) (N : ℕ) :
    IsNBlkInjective A N ↔ IsInjective (blockTensor A N) := by
  rw [isNBlkInjective_iff_isInjective_block, IsInjective, IsInjective, range_blockTensor]

/-- Flatten a word in blocked indices into an ordinary word in `Fin d` (list-level). -/
noncomputable def flattenBlockedWord (d L : ℕ) : List (Fin (blockPhysDim d L)) → List (Fin d)
  | w => (w.map (wordOfBlock d L)).flatten

@[simp] lemma flattenBlockedWord_nil (d L : ℕ) : flattenBlockedWord d L [] = [] := by
  simp [flattenBlockedWord]

lemma flattenBlockedWord_cons (d L : ℕ) (i : Fin (blockPhysDim d L))
    (w : List (Fin (blockPhysDim d L))) :
    flattenBlockedWord d L (i :: w) = wordOfBlock d L i ++ flattenBlockedWord d L w := by
  simp [flattenBlockedWord]

@[simp] lemma flattenBlockedWord_one (d : ℕ) (w : List (Fin (blockPhysDim d 1))) :
    flattenBlockedWord d 1 w = w.map (singleBlockEquiv d) := by
  induction w with
  | nil => simp [flattenBlockedWord]
  | cons i w ih => simp [flattenBlockedWord_cons, ih]

lemma evalWord_blockTensor (A : Fin d → Matrix n n ℂ) (L : ℕ)
    (w : List (Fin (blockPhysDim d L))) :
    evalWord (blockTensor A L) w = evalWord A (flattenBlockedWord d L w) := by
  rw [blockTensor, evalWord_reindexPhysical, evalWord_block, flattenBlockedWord,
    List.flatMap_def, List.map_map]
  rfl

/-- The one-letter span of a blocked family is the length-`L` word span of the
original family. -/
@[simp] theorem wordSpan_blockTensor_one (A : Fin d → Matrix n n ℂ) (L : ℕ) :
    wordSpan (blockTensor A L) 1 = wordSpan A L := by
  rw [wordSpan_one, range_blockTensor, ← wordSpan_one, wordSpan_block_one]

/-- Blocking identifies words of length `k` in the blocked family with words
of length `k * L` in the original family. -/
theorem wordSpan_blockTensor (A : Fin d → Matrix n n ℂ) (L k : ℕ) :
    wordSpan (blockTensor A L) k = wordSpan A (k * L) := by
  rw [wordSpan_eq_of_range_eq (range_blockTensor A L), wordSpan_block]

/-- Normality is preserved by blocking at a positive length. -/
theorem IsNormal.blockTensor {A : Fin d → Matrix n n ℂ}
    (hA : IsNormal A) (hL : 0 < L) :
    IsNormal (Kraus.blockTensor A L) := by
  simpa only [IsNormal, IsNBlkInjective, wordSpan_eq_of_range_eq (range_blockTensor A L)]
    using hA.block hL

/-- Length of a flattened blocked word. -/
lemma length_flattenBlockedWord (d L : ℕ) :
    ∀ w : List (Fin (blockPhysDim d L)), (flattenBlockedWord d L w).length = w.length * L := by
  intro w
  induction w with
  | nil =>
      simp [flattenBlockedWord]
  | cons i w ih =>
      -- Flattening splits off the first block word.
      simp [flattenBlockedWord_cons, ih, length_wordOfBlock,
        Nat.succ_mul, Nat.add_comm]

end Kraus
