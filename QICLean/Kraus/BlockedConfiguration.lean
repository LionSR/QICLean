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

* `Kraus.blockedConfigEquiv` identifies the configurations of `N` blocked sites with the
  configurations of `N * L` original sites.

## Main results

* `Kraus.blockedConfigEquiv_apply` reads an original site through the blocked site containing
  it.
* `Kraus.ofFn_blockedConfigEquiv` reads a blocked configuration as the flattened blocked word.

## References

* Cirac, Pérez-García, Schuch, Verstraete, *Matrix product states and projected entangled
  pair states: concepts, symmetries, and theorems*, arXiv:1606.00608, lines 318–344 (physical
  blocking).
-/

namespace Kraus

/-- Blocked configurations of length `N` are equivalent to ordinary configurations of length
`N * L`: the blocked site `i` carries the word on the original sites `i * L + r`, `r < L`.
This is the configuration-level identification implicit in physical blocking; see
arXiv:1606.00608, lines 318–344. -/
noncomputable def blockedConfigEquiv (d N L : ℕ) :
    (Fin N → Fin (blockPhysDim d L)) ≃ (Fin (N * L) → Fin d) :=
  ((Equiv.arrowCongr (Equiv.refl (Fin N)) (decodeBlockEquiv d L)).trans
    (Equiv.curry (Fin N) (Fin L) (Fin d)).symm).trans
    (Equiv.arrowCongr finProdFinEquiv (Equiv.refl (Fin d)))

/-- The original site `k` is read from the blocked site `k / L`, at position `k % L` of its
word (through `finProdFinEquiv`). -/
theorem blockedConfigEquiv_apply (d N L : ℕ) (σ : Fin N → Fin (blockPhysDim d L))
    (k : Fin (N * L)) :
    blockedConfigEquiv d N L σ k =
      decodeBlock d L (σ (finProdFinEquiv.symm k).1) (finProdFinEquiv.symm k).2 := by
  simp [blockedConfigEquiv, Equiv.arrowCongr, Equiv.curry, Function.comp]

/-- Reading a blocked configuration through `blockedConfigEquiv` gives the flattened blocked
word. This is the word-level identification used in the blocking step of arXiv:1606.00608,
lines 318–344. -/
theorem ofFn_blockedConfigEquiv (d N L : ℕ) (σ : Fin N → Fin (blockPhysDim d L)) :
    List.ofFn (blockedConfigEquiv d N L σ) = flattenBlockedWord d L (List.ofFn σ) := by
  have hfun : blockedConfigEquiv d N L σ =
      fun k : Fin (N * L) =>
        decodeBlock d L (σ (finProdFinEquiv.symm k).1) (finProdFinEquiv.symm k).2 :=
    funext (blockedConfigEquiv_apply d N L σ)
  rw [hfun, List.ofFn_mul]
  change _ = ((List.ofFn σ).map (wordOfBlock d L)).flatten
  rw [List.map_ofFn]
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

end Kraus
