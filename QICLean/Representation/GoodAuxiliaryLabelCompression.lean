/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Representation.GoodAuxiliaryLabelEntropy

/-!
# The good auxiliary observable on a whole-copy label subspace

Compressing the actual whole-space label inequality by a whole-copy central
projection yields a lower bound for the good-copy label observable on that
subspace. The good-copy observable commutes with the whole-copy projection,
and the whole-copy observable acts there by the logarithm of the actual
irreducible dimension. No occurring-label assumption is needed.

This is the support compression used in *A two-dimensional area law from a
global spectral gap*, `07-comparators.tex`, lines 481–493, equation
`comparator:good-auxiliary`. Preservation of that auxiliary label by a
physical excitation projection is a separate step. No commutation with the
band metric is asserted. The total real logarithm includes empty coordinate
sets and zero copy groups, with \(\log 0=0\).

Independently formalized from the manuscript; no upstream Lean proof text is
reused.
-/

open Matrix PermutationRepresentation
open scoped MatrixOrder ComplexOrder

namespace TensorPower

variable {m r k : ℕ} (e : Fin m ⊕ Fin r ≃ Fin k)
    {C : Type*} [Fintype C] [DecidableEq C]

/-
Original formalization, no upstream Lean proof text reused.
Manuscript: September 24, 2026, comparator:good-auxiliary, lines 481–493.
-/

/-- On an actual whole-copy label subspace, the good-copy logarithmic label
observable is bounded below by the whole-label logarithmic dimension minus
its bad-copy and binomial corrections. It commutes with the whole-label
projection. *A two-dimensional area law from a global spectral gap*,
`07-comparators.tex`, lines 481–493, equation `comparator:good-auxiliary`,
using Lemma 6.1(4), `05-replicas.tex`, lines 116–123. No occurrence assumption
is needed: a label that does not occur has zero central projection. -/
theorem copyPerm_groupedGood_labelEntropy_compression
    (l : IrrepLabel (Equiv.Perm (Fin k))) :
    let P := labelProj (copyPerm C k) l
    let Fg := labelEntropy ((copyPerm C k).comp (groupHom₁ e))
    Commute Fg P ∧
      ((Real.log l.dim - (r : ℝ) * Real.log (Fintype.card C) -
          Real.log (k.choose r) : ℝ) : ℂ) • P ≤ P * Fg * P := by
  classical
  dsimp only
  have hc : Commute (labelEntropy ((copyPerm C k).comp (groupHom₁ e)))
      (labelProj (copyPerm C k) l) :=
    commute_labelObservable_of_forall_commute ((copyPerm C k).comp (groupHom₁ e))
      (fun σ => (commute_labelProj_permOp (copyPerm C k) l (groupHom₁ e σ)).symm) _
  refine ⟨hc, ?_⟩
  have hWhole := (copyPerm_groupedCopies_labelEntropy_bounds (C := C) e).2
  have h := (Matrix.le_iff.mp hWhole).conjTranspose_mul_mul_same
    (labelProj (copyPerm C k) l)
  simp only [(isHermitian_labelProj (copyPerm C k) l).eq, mul_sub, mul_add, sub_mul,
    add_mul, mul_smul_comm, smul_mul_assoc, mul_one, labelProj_mul_self, mul_assoc,
    labelEntropy, labelObservable_mul_labelProj] at h
  rw [Matrix.le_iff]
  convert h using 1
  simp only [labelEntropy, mul_assoc, Complex.ofReal_sub, Complex.ofReal_mul,
    sub_smul, add_smul]
  abel

end TensorPower
