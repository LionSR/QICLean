/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Circuit.Party.Compression.CorrectedSources.TensorPartition

/-!
# Schmidt outputs of two local words

For systems `X`, `Y` over the two sides `Bool`, a family of output vectors `v i`, read across the
cut of the side `true`, has a *Schmidt output* when it is an exact Schmidt expansion through two
allowed source-free words, one on each side: probability weights `λ_j` and isometric input
frames `F` (on the side `true`, with the extra coordinate `i`) and `G` (on the side `false`),
chosen before the coordinate `i`, with `v i = ∑_j √λ_j (c F)(i, j) ⊗ (d G) e_j`. A tensor
partitioned word maps inputs with a Schmidt expansion in the cut coordinates to a Schmidt output.

## Main definitions

* `QuantumCircuit.Party.Word.HasSchmidtOutput`.

## Main results

* `QuantumCircuit.Party.Word.hasSchmidtOutput_mulVec_of_isTensorPartitioned`.

## References

* Polynomial-PEPS manuscript (September 24, 2026), Theorem 5.2, `04-compression.tex`,
  lines 409–480, `eq:compression-exterior-input`.
-/

noncomputable section

open Matrix ManyBody
open scoped Kronecker Matrix.Norms.L2Operator

namespace QuantumCircuit.Party.Word

/-- An exact Schmidt expansion of the vectors `v i` through two allowed source-free words on the
two sides: isometric input frames, the local words and probability weights are chosen before
the coordinate `i`. Source: Theorem 5.2, `04-compression.tex`, lines 409–480. -/
def HasSchmidtOutput {I : Type} [DecidableEq I] (X Y : Bool → Type) [∀ b, Fintype (X b)]
    [∀ b, DecidableEq (X b)] [∀ b, Fintype (Y b)]
    (v : I → RegionConfig Y {true} × ComplConfig Y {true} → ℂ) : Prop :=
  ∃ c : Word (P := {b : Bool // b ∈ ({true} : Finset Bool)}) (fun b ↦ X b) (fun b ↦ Y b),
    ∃ d : Word (P := {b : Bool // b ∉ ({true} : Finset Bool)}) (fun b ↦ X b) (fun b ↦ Y b),
      c.IsAllowed ∧ d.IsAllowed ∧ c.sources = [] ∧ d.sources = [] ∧
      ‖c.op‖ ≤ 1 ∧ ‖d.op‖ ≤ 1 ∧
      ∃ r : ℕ, ∃ lam : Fin r → ℝ, ∃ F : Matrix (RegionConfig X {true}) (I × Fin r) ℂ,
        ∃ G : Matrix (ComplConfig X {true}) (Fin r) ℂ,
          Fᴴ * F = 1 ∧ Gᴴ * G = 1 ∧ (∀ j, 0 ≤ lam j) ∧ (∑ j, lam j) = 1 ∧ ∀ i,
            v i = fun y ↦ ∑ j, (Real.sqrt (lam j) : ℂ) *
              ((c.op * F) y.1 (i, j) * (d.op * G) y.2 j)

variable {Q : Type} [Fintype Q] [DecidableEq Q] {X Y : Q → Type} [∀ q, Fintype (X q)]
  [∀ q, DecidableEq (X q)] [∀ q, Fintype (Y q)]

/-- **A tensor partitioned word has a Schmidt output on Schmidt inputs.** If the inputs `x i`,
read across the cut of the side `true`, have one Schmidt expansion with isometric frames, the
outputs of a tensor partitioned word, read across the same cut, have a Schmidt output with the
same weights and frames. Source: Theorem 5.2, `04-compression.tex`, lines 409–480. -/
theorem hasSchmidtOutput_mulVec_of_isTensorPartitioned {I : Type} [DecidableEq I] (f : Q → Bool)
    (W : Word X Y) (hW : W.IsTensorPartitioned f) (x : I → Config (blockSystem f X) → ℂ)
    (hx : ∃ r : ℕ, ∃ lam : Fin r → ℝ,
      ∃ F : Matrix (RegionConfig (blockSystem f X) {true}) (I × Fin r) ℂ,
        ∃ G : Matrix (ComplConfig (blockSystem f X) {true}) (Fin r) ℂ,
          Fᴴ * F = 1 ∧ Gᴴ * G = 1 ∧ (∀ j, 0 ≤ lam j) ∧ (∑ j, lam j) = 1 ∧ ∀ i,
            (fun a ↦ x i ((cutEquiv (blockSystem f X) {true}).symm a)) = fun a ↦
              ∑ j, (Real.sqrt (lam j) : ℂ) * (F a.1 (i, j) * G a.2 j)) :
    HasSchmidtOutput (blockSystem f X) (blockSystem f Y) fun i y ↦
      ((W.coarsen f).op *ᵥ x i) ((cutEquiv (blockSystem f Y) {true}).symm y) := by
  obtain ⟨c, d, hc, hd, hcs, hds, hcn, hdn, hop⟩ := hW
  obtain ⟨r, lam, F, G, hF, hG, hlam, hsum, hxF⟩ := hx
  refine ⟨c, d, hc, hd, hcs, hds, hcn, hdn, r, lam, F, G, hF, hG, hlam, hsum, fun i ↦ ?_⟩
  funext y
  beta_reduce
  rw [hop, reindex_apply, Equiv.symm_symm, Equiv.symm_symm, submatrix_mulVec_equiv,
    Function.comp_apply, Equiv.apply_symm_apply]
  have hxi : x i ∘ (cutEquiv (blockSystem f X) {true}).symm = fun a ↦
      ∑ j, (Real.sqrt (lam j) : ℂ) * (F a.1 (i, j) * G a.2 j) := hxF i
  rw [hxi]
  simp only [mulVec, dotProduct, kroneckerMap_apply, Fintype.sum_prod_type, Matrix.mul_apply,
    Finset.mul_sum, Finset.sum_mul]
  refine (Finset.sum_congr rfl fun a _ ↦ Finset.sum_comm).trans ?_
  refine Finset.sum_comm.trans (Finset.sum_congr rfl fun j _ ↦ ?_)
  refine Finset.sum_comm.trans (Finset.sum_congr rfl fun b _ ↦ Finset.sum_congr rfl fun a _ ↦ ?_)
  ring

end QuantumCircuit.Party.Word
