/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.ManyBody.Sites.Placement
import QICLean.Algebra.Unitary.MatrixUnitaryBetween
import QICLean.ManyBody.Sites.Support
import QICLean.Spectral.Gap.DoubledSystemGap

/-!
# Conjugation by on-site unitaries, and the exchange of two copies on a region

A product operator `⊗_v m_v` whose on-site matrices are unitary outside a region `S` maps every
operator supported on `S` by conjugation to an operator supported on `S`
(`ManyBody.piKronecker_mul_mul_conjTranspose_mem_supportedOperators`): it acts site by site and
leaves the identity outside `S` unchanged.

On the system with basis `X v × X v` at every site, which carries two copies of the system `X`
paired at every site, the exchange of the two copies at the sites of a region `A` is the product
operator `ManyBody.pairSwapOp A` of the exchange `(a, b) ↦ (b, a)` at the sites of `A` and the
identity elsewhere. It is a unitary involution supported on `A`, it preserves every support by
conjugation, and it commutes with every operator supported away from `A`. The doubled operator
`h ⊗ 1 + 1 ⊗ h` of an operator `h` supported on `S` is, on paired sites, supported on `S`, so
conjugating the doubled interaction `(hᵢ ⊗ 1 + 1 ⊗ hᵢ)ᵢ` by the exchange gives an interaction
with the same supports. This is the one description of the exchange of two copies; on the sites
`V ⊕ V` of two replicas it is `ManyBody.replicaSwapOp`, its transport along
`ManyBody.replicaPairEquiv`.

These generalize TNLean's `TNLean.Lattice.sheetSwapOp` (`Circuit/RegionalSwap`, at commit
`414a18fb88`), the exchange of the two sheets of `(ι → Fin q) × (ι → Fin q)` at the sites of a
region; the sheets there are the two copies here, paired at every site.

## Main definitions

* `ManyBody.pairSwapOp` — the exchange of the two copies at the sites of a region.

## Main results

* `ManyBody.piKronecker_mul_mul_conjTranspose_mem_supportedOperators` — conjugation by on-site
  unitaries preserves supports.
* `ManyBody.pairSwapOp_mem_supportedOperators`, `ManyBody.pairSwapOp_mem_unitaryGroup`,
  `ManyBody.conjTranspose_pairSwapOp`, `ManyBody.pairSwapOp_mul_self`,
  `ManyBody.pairSwapOp_empty`.
* `ManyBody.pairSwapOp_mul_mul_conjTranspose_mem_supportedOperators`,
  `ManyBody.pairSwapOp_mul_mul_conjTranspose_of_disjoint`.
* `ManyBody.reindex_doubledHamiltonian_mem_supportedOperators` — the doubled operator on paired
  sites keeps the support.
-/

open Matrix

namespace ManyBody

variable {V : Type*} [Fintype V] [DecidableEq V] {X : V → Type*} [∀ v, Fintype (X v)]
  [∀ v, DecidableEq (X v)]

/-- **Conjugation by on-site unitaries preserves supports.** If the on-site matrices `m v` are
unitary at the sites outside `S`, conjugating an operator supported on `S` by the product
operator `⊗_v m_v` gives an operator supported on `S`. -/
theorem piKronecker_mul_mul_conjTranspose_mem_supportedOperators {S : Finset V}
    {m : (v : V) → Matrix (X v) (X v) ℂ} (hm : ∀ v ∉ S, m v * (m v)ᴴ = 1)
    {A : Matrix (Config X) (Config X) ℂ} (hA : A ∈ supportedOperators X S) :
    piKronecker m * A * (piKronecker m)ᴴ ∈ supportedOperators X S := by
  induction hA using supportedOperators_induction with
  | prod n hn =>
    rw [conjTranspose_piKronecker, piKronecker_mul, piKronecker_mul]
    exact piKronecker_mem_supportedOperators fun v hv ↦ by rw [hn v hv, Matrix.mul_one, hm v hv]
  | add A B _ _ ihA ihB =>
    rw [Matrix.mul_add, Matrix.add_mul]
    exact add_mem ihA ihB
  | smul c A _ ihA =>
    rw [Matrix.mul_smul, Matrix.smul_mul]
    exact SMulMemClass.smul_mem c ihA

/-- **The doubled operator keeps the support.** If `h` is supported on `S`, the doubled operator
`h ⊗ 1 + 1 ⊗ h`, with the two copies of every site paired, is supported on `S`. -/
theorem reindex_doubledHamiltonian_mem_supportedOperators {S : Finset V}
    {h : Matrix (Config X) (Config X) ℂ} (hh : h ∈ supportedOperators X S) :
    reindex (Equiv.arrowProdEquivProdArrow V X X).symm (Equiv.arrowProdEquivProdArrow V X X).symm
      (doubledHamiltonian h) ∈ supportedOperators (fun v ↦ X v × X v) S := by
  rw [doubledHamiltonian, reindex_apply, submatrix_add, ← Finset.union_self S]
  exact add_mem (reindex_kronecker_mem_supportedOperators hh (one_mem _))
    (reindex_kronecker_mem_supportedOperators (one_mem _) hh)

/-! ### The exchange of two copies -/

/-- The exchange of the two copies at the sites of `A`: on the system with basis `X v × X v`
at every site `v`, the product operator of the exchange `(a, b) ↦ (b, a)` at the sites of `A`
and the identity at the other sites. -/
noncomputable def pairSwapOp (A : Finset V) :
    Matrix (Config fun v ↦ X v × X v) (Config fun v ↦ X v × X v) ℂ :=
  piKronecker fun v ↦ if v ∈ A then Equiv.Perm.permMatrix ℂ (Equiv.prodComm (X v) (X v)) else 1

private theorem swap_mul_conjTranspose (Y : Type*) [Fintype Y] [DecidableEq Y] :
    Equiv.Perm.permMatrix ℂ (Equiv.prodComm Y Y) *
      (Equiv.Perm.permMatrix ℂ (Equiv.prodComm Y Y))ᴴ = 1 :=
  Matrix.mem_unitaryGroup_iff.mp (Equiv.Perm.permMatrix_mem_unitaryGroup _)

private theorem conjTranspose_swap (Y : Type*) [DecidableEq Y] :
    (Equiv.Perm.permMatrix ℂ (Equiv.prodComm Y Y))ᴴ =
      Equiv.Perm.permMatrix ℂ (Equiv.prodComm Y Y) := by
  rw [conjTranspose_permMatrix]
  rfl

/-- The exchange on `A` is supported on `A`. -/
theorem pairSwapOp_mem_supportedOperators (A : Finset V) :
    pairSwapOp (X := X) A ∈ supportedOperators (fun v ↦ X v × X v) A :=
  piKronecker_mem_supportedOperators fun _ hv ↦ ite_eq_right hv

omit [∀ v, Fintype (X v)] in
/-- The exchange is its own adjoint. -/
theorem conjTranspose_pairSwapOp (A : Finset V) :
    (pairSwapOp (X := X) A)ᴴ = pairSwapOp A := by
  rw [pairSwapOp, conjTranspose_piKronecker]
  congr 1
  funext v
  split_ifs
  · exact conjTranspose_swap (X v)
  · exact conjTranspose_one

/-- The exchange is an involution. -/
theorem pairSwapOp_mul_self (A : Finset V) : pairSwapOp (X := X) A * pairSwapOp A = 1 := by
  nth_rw 2 [← conjTranspose_pairSwapOp]
  rw [pairSwapOp, conjTranspose_piKronecker, piKronecker_mul,
    ← piKronecker_one (ι := fun v ↦ X v × X v)]
  congr 1
  funext v
  split_ifs
  · exact swap_mul_conjTranspose (X v)
  · rw [conjTranspose_one, Matrix.mul_one]

/-- The exchange is unitary. -/
theorem pairSwapOp_mem_unitaryGroup (A : Finset V) :
    pairSwapOp (X := X) A ∈ unitaryGroup (Config fun v ↦ X v × X v) ℂ := by
  rw [mem_unitaryGroup_iff, star_eq_conjTranspose, conjTranspose_pairSwapOp, pairSwapOp_mul_self]

omit [∀ v, Fintype (X v)] in
/-- The exchange on the empty region is the identity. -/
@[simp]
theorem pairSwapOp_empty : pairSwapOp (X := X) ∅ = 1 := by
  simp [pairSwapOp]

/-- **The exchange preserves supports.** Conjugating an operator supported on `S` by the
exchange on any region gives an operator supported on `S`. -/
theorem pairSwapOp_mul_mul_conjTranspose_mem_supportedOperators (A : Finset V) {S : Finset V}
    {B : Matrix (Config fun v ↦ X v × X v) (Config fun v ↦ X v × X v) ℂ}
    (hB : B ∈ supportedOperators (fun v ↦ X v × X v) S) :
    pairSwapOp A * B * (pairSwapOp A)ᴴ ∈ supportedOperators (fun v ↦ X v × X v) S := by
  refine piKronecker_mul_mul_conjTranspose_mem_supportedOperators (fun v _ ↦ ?_) hB
  split_ifs
  · exact swap_mul_conjTranspose (X v)
  · rw [conjTranspose_one, Matrix.mul_one]

/-- The exchange on `A` leaves every operator supported away from `A` unchanged. -/
theorem pairSwapOp_mul_mul_conjTranspose_of_disjoint {A S : Finset V} (h : Disjoint S A)
    {B : Matrix (Config fun v ↦ X v × X v) (Config fun v ↦ X v × X v) ℂ}
    (hB : B ∈ supportedOperators (fun v ↦ X v × X v) S) :
    pairSwapOp A * B * (pairSwapOp A)ᴴ = B := by
  rw [(commute_of_mem_supportedOperators_of_disjoint (pairSwapOp_mem_supportedOperators A) hB
    h.symm).eq, Matrix.mul_assoc, conjTranspose_pairSwapOp, pairSwapOp_mul_self, Matrix.mul_one]

end ManyBody
