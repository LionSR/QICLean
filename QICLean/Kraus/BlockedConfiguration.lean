/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Kraus.Blocking

import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Configurations of a blocked chain

Blocking `L` consecutive sites of a chain of `N * L` sites with local dimension `d` gives a
chain of `N` sites whose local labels are the numbered words of length `L`
(`Kraus.decodeBlockEquiv`). A configuration of the blocked chain is the same as a
configuration of the original chain: the blocked site `i` carries the word read on the original
sites `i * L, …, i * L + L - 1`.

## Main definitions

* `Kraus.blockConfigEquiv` identifies the configurations of `N` blocks of length `L` over an
  alphabet `ι` with the configurations of `N * L` sites.
* `Kraus.blockedConfigEquiv` is its composite with `Kraus.decodeBlockEquiv` on the numbered
  alphabet `Fin (blockPhysDim d L)`.

## Main results

* `Kraus.blockConfigEquiv_apply`, `Kraus.ofFn_blockConfigEquiv`: an original site is read
  through the block containing it, and a configuration of blocks reads as their concatenation.
* `Kraus.blockedConfigEquiv_eq` unfolds the numbered form; `Kraus.blockedConfigEquiv_apply`
  and `Kraus.ofFn_blockedConfigEquiv` follow from the generic statements.

## References

* Cirac, Pérez-García, Schuch, Verstraete, *Matrix product states and projected entangled
  pair states: concepts, symmetries, and theorems*, arXiv:1606.00608, lines 318–344 (physical
  blocking).
-/

namespace Kraus

/-- Configurations of `N` blocks of length `L` are configurations of `N * L` sites: the block
`i` carries the letters on the original sites `i * L + r`, `r < L`. This is the
configuration-level identification implicit in physical blocking; see arXiv:1606.00608,
lines 318–344. -/
noncomputable def blockConfigEquiv (ι : Type*) (N L : ℕ) :
    (Fin N → Fin L → ι) ≃ (Fin (N * L) → ι) :=
  (Equiv.curry (Fin N) (Fin L) ι).symm.trans (Equiv.arrowCongr finProdFinEquiv (Equiv.refl ι))

/-- The original site `k` is read from block `k / L`, at position `k % L`
(through `finProdFinEquiv`). -/
theorem blockConfigEquiv_apply {ι : Type*} (N L : ℕ) (σ : Fin N → Fin L → ι)
    (k : Fin (N * L)) :
    blockConfigEquiv ι N L σ k = σ (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2 := by
  simp [blockConfigEquiv, Equiv.arrowCongr, Equiv.curry, Function.comp]

/-- Reading a configuration of blocks through `blockConfigEquiv` gives the concatenation of
the blocks. This is the word-level identification used in the blocking step of
arXiv:1606.00608, lines 318–344. -/
theorem ofFn_blockConfigEquiv {ι : Type*} (N L : ℕ) (σ : Fin N → Fin L → ι) :
    List.ofFn (blockConfigEquiv ι N L σ) = (List.ofFn σ).flatMap List.ofFn := by
  have hfun : blockConfigEquiv ι N L σ =
      fun k : Fin (N * L) => σ (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2 :=
    funext (blockConfigEquiv_apply N L σ)
  rw [hfun, List.ofFn_mul, List.flatMap_def, List.map_ofFn]
  congr 1
  refine congrArg List.ofFn (funext fun i => ?_)
  have hsymm : ∀ j : Fin L,
      finProdFinEquiv.symm
          (⟨(i : ℕ) * L + (j : ℕ),
            by
              calc
                (i : ℕ) * L + (j : ℕ) < ((i : ℕ) + 1) * L := by
                  have := j.isLt
                  rw [Nat.add_mul, Nat.one_mul]
                  omega
                _ ≤ N * L := Nat.mul_le_mul_right _ (by have := i.isLt; omega)⟩ :
            Fin (N * L)) = (i, j) := by
    intro j
    rw [Equiv.symm_apply_eq]
    apply Fin.ext
    change (i : ℕ) * L + (j : ℕ) = (j : ℕ) + L * (i : ℕ)
    rw [Nat.mul_comm L (i : ℕ), Nat.add_comm]
  simp only [hsymm]
  rfl

/-- Blocked configurations on the numbered alphabet `Fin (blockPhysDim d L)`: the composite of
`decodeBlockEquiv` on every block with `blockConfigEquiv`. -/
noncomputable def blockedConfigEquiv (d N L : ℕ) :
    (Fin N → Fin (blockPhysDim d L)) ≃ (Fin (N * L) → Fin d) :=
  (Equiv.arrowCongr (Equiv.refl (Fin N)) (decodeBlockEquiv d L)).trans
    (blockConfigEquiv (Fin d) N L)

/-- `blockedConfigEquiv` decodes every block and applies `blockConfigEquiv`. -/
theorem blockedConfigEquiv_eq (d N L : ℕ) (σ : Fin N → Fin (blockPhysDim d L)) :
    blockedConfigEquiv d N L σ = blockConfigEquiv (Fin d) N L fun i => decodeBlock d L (σ i) :=
  rfl

/-- The original site `k` is read from the blocked site `k / L`, at position `k % L` of its
word (through `finProdFinEquiv`). -/
theorem blockedConfigEquiv_apply (d N L : ℕ) (σ : Fin N → Fin (blockPhysDim d L))
    (k : Fin (N * L)) :
    blockedConfigEquiv d N L σ k =
      decodeBlock d L (σ (finProdFinEquiv.symm k).1) (finProdFinEquiv.symm k).2 := by
  rw [blockedConfigEquiv_eq, blockConfigEquiv_apply]

/-- Reading a blocked configuration through `blockedConfigEquiv` gives the flattened blocked
word. This is the word-level identification used in the blocking step of arXiv:1606.00608,
lines 318–344. -/
theorem ofFn_blockedConfigEquiv (d N L : ℕ) (σ : Fin N → Fin (blockPhysDim d L)) :
    List.ofFn (blockedConfigEquiv d N L σ) = flattenBlockedWord d L (List.ofFn σ) := by
  rw [blockedConfigEquiv_eq, ofFn_blockConfigEquiv, flattenBlockedWord, List.flatMap_def,
    List.map_ofFn, List.map_ofFn]
  rfl

end Kraus
