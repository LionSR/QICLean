/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import Mathlib.LinearAlgebra.Matrix.Kronecker
import QICLean.Circuit.Gate.PartialIsometryDilation
import QICLean.Circuit.Model.Unitary
import QICLean.ManyBody.Sites.Relabel

/-!
# Unitary implementations with a reusable initialized workspace

Let `J` include a logical space into a larger space, for instance the basis inclusion that puts
a workspace in a fixed initial configuration. The identity `U * J = J * Z` says that the ambient
operator `U` acts as `Z` on every logical input, including inputs entangled with a reference,
and returns the workspace to its initial state. The identity is a matrix identity: it asserts
neither unitarity nor a decomposition into gates. It is preserved by products and powers, and,
when both operators are unitary, by adjoints and inverses; when `J` is an isometry and `U` is
unitary, `Z` is unitary. These facts justify reusing one scratch register in nested reflections.

When every unitary on the configurations of a system is a product of gates of total cost at most
`K` on a geometry `Γ`, every isometry from a space of prescribed basis columns, and every logical
unitary along a basis inclusion, has such an implementation by a product of gates of cost at
most `K`.

For identical sites, the workspace of `a` sites after `n` logical sites, in a fixed
configuration `w`, is preserved by permutations of the logical sites that fix the workspace,
and conjugation by such a permutation preserves the identity.

Source: the reusable scratch register of Section 5 of TNLean
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`.

The declarations restate those of `TNLean/Circuit/CleanUnitaryImplementation.lean`, the
workspace part of `TNLean/Circuit/QuantitativeSitePermutation.lean`, and
`initializedBasisMatrix_zeroWorkspace_mul_apply` of
`TNLean/Circuit/CleanImplementationPlacement.lean`, at commit `414a18fb88` (Apache-2.0). The
changes: membership in `unitaryGroup` for unitarity; the products of neighbouring-pair gates
with the count `38 (d ^ n) ^ 6` become products of gates on any geometry, under the hypothesis
that every unitary on the configurations is such a product; in the first existence result the
isometry is any isometry into the configurations, not an isometry composed with a basis
inclusion; the zero workspace becomes any workspace configuration `w` and the basis `Fin d` any
type; the permutation operator is `ManyBody.sitePermOp`. The clean implementation of the
zero-register reflection is not carried here.

## Main definitions

* `QuantumCircuit.IsCleanImplementation` — the identity `U * J = J * Z`.
* `QuantumCircuit.workspaceEmbedding` — appending a fixed workspace configuration.
* `QuantumCircuit.workspaceFixedSitePerm` — a permutation of the logical sites, fixing the
  workspace sites.

## Main results

* `QuantumCircuit.IsCleanImplementation.mul`, `QuantumCircuit.IsCleanImplementation.pow`,
  `QuantumCircuit.IsCleanImplementation.conjTranspose`,
  `QuantumCircuit.IsCleanImplementation.inv` — closure properties.
* `QuantumCircuit.IsCleanImplementation.logical_mem_unitaryGroup` — the logical operator is
  unitary.
* `QuantumCircuit.IsCleanImplementation.kronecker_one` — a reference system.
* `QuantumCircuit.exists_isGateProduct_mul_basisInclusion_eq`,
  `QuantumCircuit.exists_isGateProduct_isCleanImplementation` — implementations by products of
  gates.
* `QuantumCircuit.isCleanImplementation_sitePermOp_workspaceFixedSitePerm`,
  `QuantumCircuit.IsCleanImplementation.conjugate_workspaceFixedSitePerm` — logical site
  permutations.

Moved from TNLean, `TNLean/MPS/MPU/Circuit/Interval/ColumnCoordinateTransport.lean` at commit
`021ba0bd19` (Apache-2.0).
-/

open Matrix ManyBody
open scoped Kronecker

namespace QuantumCircuit

/-! ### The clean identity -/

section Matrices

/-- `U` implements `Z` cleanly along `J`: `U * J = J * Z`. When `J` is the basis inclusion with a
workspace in its initial configuration, `U` acts as `Z` on every logical input, including inputs
entangled with a reference, and returns the workspace to its initial configuration. The identity
alone does not assert that either operator is unitary.

Source: the reusable scratch register of Section 5 of TNLean
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
def IsCleanImplementation {ι κ : Type*} [Fintype ι] [Fintype κ] (J : Matrix ι κ ℂ)
    (U : Matrix ι ι ℂ) (Z : Matrix κ κ ℂ) : Prop :=
  U * J = J * Z

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

namespace IsCleanImplementation

/-- The identity is clean along every inclusion. -/
theorem one (J : Matrix ι κ ℂ) : IsCleanImplementation J 1 1 := by
  simp [IsCleanImplementation]

omit [DecidableEq ι] [DecidableEq κ] in
/-- Two clean implementations may use the same workspace one after the other. -/
theorem mul {J : Matrix ι κ ℂ} {U V : Matrix ι ι ℂ} {Z W : Matrix κ κ ℂ}
    (hU : IsCleanImplementation J U Z) (hV : IsCleanImplementation J V W) :
    IsCleanImplementation J (U * V) (Z * W) := by
  change U * V * J = J * (Z * W)
  rw [Matrix.mul_assoc, show V * J = J * W from hV, ← Matrix.mul_assoc,
    show U * J = J * Z from hU, Matrix.mul_assoc]

/-- A repeated clean implementation returns the workspace to its initial configuration after
every round. -/
theorem pow {J : Matrix ι κ ℂ} {U : Matrix ι ι ℂ} {Z : Matrix κ κ ℂ}
    (h : IsCleanImplementation J U Z) (k : ℕ) : IsCleanImplementation J (U ^ k) (Z ^ k) := by
  induction k with
  | zero => simpa using one J
  | succ k ih => simpa only [pow_succ] using ih.mul h

/-- The adjoint of a clean implementation of a logical unitary by a unitary is clean. Unitarity
is required on the whole logical space. -/
theorem conjTranspose {J : Matrix ι κ ℂ} {U : Matrix ι ι ℂ} {Z : Matrix κ κ ℂ}
    (h : IsCleanImplementation J U Z) (hU : U ∈ unitaryGroup ι ℂ) (hZ : Z ∈ unitaryGroup κ ℂ) :
    IsCleanImplementation J Uᴴ Zᴴ := by
  change Uᴴ * J = J * Zᴴ
  calc
    Uᴴ * J = Uᴴ * (J * (Z * Zᴴ)) := by
      rw [show Z * Zᴴ = 1 from mem_unitaryGroup_iff.mp hZ, Matrix.mul_one]
    _ = Uᴴ * ((U * J) * Zᴴ) := by rw [show U * J = J * Z from h, Matrix.mul_assoc]
    _ = (Uᴴ * U) * J * Zᴴ := by simp only [Matrix.mul_assoc]
    _ = J * Zᴴ := by rw [show Uᴴ * U = 1 from mem_unitaryGroup_iff'.mp hU, Matrix.one_mul]

/-- The inverse of a clean implementation of a logical unitary by a unitary is clean. -/
theorem inv {J : Matrix ι κ ℂ} {U : Matrix ι ι ℂ} {Z : Matrix κ κ ℂ}
    (h : IsCleanImplementation J U Z) (hU : U ∈ unitaryGroup ι ℂ) (hZ : Z ∈ unitaryGroup κ ℂ) :
    IsCleanImplementation J U⁻¹ Z⁻¹ := by
  rw [Matrix.inv_eq_left_inv (mem_unitaryGroup_iff'.mp hU),
    Matrix.inv_eq_left_inv (mem_unitaryGroup_iff'.mp hZ)]
  exact h.conjTranspose hU hZ

omit [DecidableEq ι] [DecidableEq κ] in
/-- A clean implementation acts as the logical operator on every vector. -/
theorem mulVec {J : Matrix ι κ ℂ} {U : Matrix ι ι ℂ} {Z : Matrix κ κ ℂ}
    (h : IsCleanImplementation J U Z) (v : κ → ℂ) : U *ᵥ (J *ᵥ v) = J *ᵥ (Z *ᵥ v) := by
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
  exact congrArg (· *ᵥ v) h

/-- A unitary implementing `Z` cleanly along an isometry makes `Z` unitary. -/
theorem logical_mem_unitaryGroup {J : Matrix ι κ ℂ} {U : Matrix ι ι ℂ} {Z : Matrix κ κ ℂ}
    (h : IsCleanImplementation J U Z) (hJ : J.IsIsometry) (hU : U ∈ unitaryGroup ι ℂ) :
    Z ∈ unitaryGroup κ ℂ := by
  have hJ' : Jᴴ * J = 1 := hJ
  refine mem_unitaryGroup_iff'.mpr ?_
  change Zᴴ * Z = 1
  calc
    Zᴴ * Z = Zᴴ * (Jᴴ * J) * Z := by rw [hJ', Matrix.mul_one]
    _ = (J * Z)ᴴ * (J * Z) := by simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = (U * J)ᴴ * (U * J) := by rw [show U * J = J * Z from h]
    _ = Jᴴ * (Uᴴ * U) * J := by simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = 1 := by rw [show Uᴴ * U = 1 from mem_unitaryGroup_iff'.mp hU, Matrix.mul_one, hJ']

/-- Along an isometry, the adjoint of a clean unitary implementation is clean. -/
theorem conjTranspose_of_isometry {J : Matrix ι κ ℂ} {U : Matrix ι ι ℂ} {Z : Matrix κ κ ℂ}
    (h : IsCleanImplementation J U Z) (hJ : J.IsIsometry) (hU : U ∈ unitaryGroup ι ℂ) :
    IsCleanImplementation J Uᴴ Zᴴ :=
  h.conjTranspose hU (h.logical_mem_unitaryGroup hJ hU)

omit [DecidableEq ι] [DecidableEq κ] in
/-- A clean implementation stays clean in the presence of any finite reference system. -/
theorem kronecker_one {J : Matrix ι κ ℂ} {U : Matrix ι ι ℂ} {Z : Matrix κ κ ℂ}
    (h : IsCleanImplementation J U Z) (ρ : Type*) [Fintype ρ] [DecidableEq ρ] :
    IsCleanImplementation (J ⊗ₖ (1 : Matrix ρ ρ ℂ)) (U ⊗ₖ (1 : Matrix ρ ρ ℂ))
      (Z ⊗ₖ (1 : Matrix ρ ρ ℂ)) := by
  change (U ⊗ₖ (1 : Matrix ρ ρ ℂ)) * (J ⊗ₖ (1 : Matrix ρ ρ ℂ)) =
    (J ⊗ₖ (1 : Matrix ρ ρ ℂ)) * (Z ⊗ₖ (1 : Matrix ρ ρ ℂ))
  rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul, show U * J = J * Z from h]

end IsCleanImplementation

end Matrices

/-! ### Implementations by products of gates -/

section Gates

variable {S : Type} [Fintype S] [DecidableEq S] {Γ : Geometry S} {X : S → Type}
  [∀ s, Fintype (X s)] [∀ s, DecidableEq (X s)] {K : ℕ}

/-- **Isometries on prescribed columns.** If every unitary on the configurations is a product of
gates of total cost at most `K`, then every isometry `W` from `ℂ^κ` into the configurations is
the restriction of such a product to the basis columns `e k`.

Source: the leaf and merger packets of Section 5 of TNLean
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
theorem exists_isGateProduct_mul_basisInclusion_eq
    (huniv : ∀ U ∈ unitaryGroup (Config X) ℂ, IsGateProduct Γ K U) {κ : Type*} [DecidableEq κ]
    (e : κ ↪ Config X) {W : Matrix (Config X) κ ℂ} (hW : W.IsIsometry) :
    ∃ U, IsGateProduct Γ K U ∧ U * basisInclusion e = W := by
  obtain ⟨U, hU, hUW⟩ := exists_mem_unitaryGroup_apply_embedding_eq hW e
  exact ⟨U, huniv U hU, Matrix.ext fun i k ↦
    (mul_basisInclusion_apply e U i k).trans (hUW i k)⟩

/-- **Clean implementation of a logical unitary.** If every unitary on the configurations is a
product of gates of total cost at most `K`, then every unitary `Z` on `ℂ^κ` has a clean
implementation along the basis inclusion `e` by such a product.

Source: the leaf construction of Section 5 of TNLean
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
theorem exists_isGateProduct_isCleanImplementation
    (huniv : ∀ U ∈ unitaryGroup (Config X) ℂ, IsGateProduct Γ K U) {κ : Type*} [Fintype κ]
    [DecidableEq κ] (e : κ ↪ Config X) {Z : Matrix κ κ ℂ} (hZ : Z ∈ unitaryGroup κ ℂ) :
    ∃ U, IsGateProduct Γ K U ∧ IsCleanImplementation (basisInclusion e) U Z :=
  exists_isGateProduct_mul_basisInclusion_eq huniv e
    ((basisInclusion_isIsometry e).mul _ Z (mem_unitaryGroup_iff'.mp hZ))

end Gates

/-! ### A workspace after the logical sites -/

section Workspace

variable {α : Type*} {n a : ℕ}

/-- The inclusion of the configurations of `n` logical sites into those of `n + a` sites, with
the `a` workspace sites after the logical ones in the configuration `w`.

Source: the clean-workspace convention of Section 5 of TNLean
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`, there with `w = 0`. -/
def workspaceEmbedding (w : Fin a → α) : (Fin n → α) ↪ (Fin (n + a) → α) where
  toFun x := Fin.append x w
  inj' x y h := funext fun i ↦ by simpa only [Fin.append_left] using congrFun h (Fin.castAdd a i)

@[simp] theorem workspaceEmbedding_apply (w : Fin a → α) (x : Fin n → α) :
    workspaceEmbedding w x = Fin.append x w :=
  rfl

variable [Fintype α] [DecidableEq α]

/-- The rows of `J * Z`, for the workspace inclusion `J`: the row of `Z` at the logical part of
a configuration whose workspace part is `w`, and zero otherwise. -/
theorem basisInclusion_workspaceEmbedding_mul_apply {μ : Type*} (w : Fin a → α)
    (Z : Matrix (Fin n → α) μ ℂ) (z : Fin (n + a) → α) (x : μ) :
    (basisInclusion (workspaceEmbedding (n := n) w) * Z) z x =
      if ∀ j, z (Fin.natAdd n j) = w j then Z (fun j ↦ z (Fin.castAdd a j)) x else 0 := by
  split_ifs with hz
  · have hz' : z = workspaceEmbedding w fun j ↦ z (Fin.castAdd a j) :=
      funext fun i ↦ Fin.addCases (fun j ↦ by simp) (fun j ↦ by simp [hz j]) i
    conv_lhs => rw [hz']
    exact basisInclusion_mul_apply_self _ _ _ _
  · refine basisInclusion_mul_apply_of_notMem _ _ ?_ _
    rintro ⟨y, rfl⟩
    exact hz fun j ↦ by simp

/-- The permutation of `n + a` sites acting as `τ` on the first `n` sites and fixing the last `a`
sites.

Source: the regrouping of registers of Section 5 of TNLean
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
def workspaceFixedSitePerm (τ : Equiv.Perm (Fin n)) : Equiv.Perm (Fin (n + a)) :=
  (finSumFinEquiv.symm.trans (Equiv.sumCongr τ (Equiv.refl (Fin a)))).trans finSumFinEquiv

omit [Fintype α] [DecidableEq α] in
@[simp] theorem workspaceFixedSitePerm_castAdd (τ : Equiv.Perm (Fin n)) (i : Fin n) :
    workspaceFixedSitePerm (a := a) τ (Fin.castAdd a i) = Fin.castAdd a (τ i) := by
  simp [workspaceFixedSitePerm]

omit [Fintype α] [DecidableEq α] in
@[simp] theorem workspaceFixedSitePerm_natAdd (τ : Equiv.Perm (Fin n)) (i : Fin a) :
    workspaceFixedSitePerm (a := a) τ (Fin.natAdd n i) = Fin.natAdd n i := by
  simp [workspaceFixedSitePerm]

/-- **Permuting the logical sites.** The permutation of the logical sites by `τ`, fixing the
workspace sites, implements the permutation `τ` of the logical register cleanly, for every
workspace configuration `w`.

Source: the routing in a common pool of Section 5 of TNLean
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
theorem isCleanImplementation_sitePermOp_workspaceFixedSitePerm (w : Fin a → α)
    (τ : Equiv.Perm (Fin n)) :
    IsCleanImplementation (basisInclusion (workspaceEmbedding (n := n) w))
      (sitePermOp (α := α) (workspaceFixedSitePerm τ)) (sitePermOp τ) := by
  ext z x
  rw [mul_basisInclusion_apply, basisInclusion_workspaceEmbedding_mul_apply,
    sitePermOp_apply, workspaceEmbedding_apply]
  have hcfg : Fin.append x w = z ∘ workspaceFixedSitePerm τ ↔
      (∀ j, z (Fin.natAdd n j) = w j) ∧ x = (fun j ↦ z (Fin.castAdd a j)) ∘ τ := by
    refine ⟨fun h ↦ ⟨fun j ↦ ?_, funext fun j ↦ ?_⟩, fun ⟨hw, hx⟩ ↦ funext fun i ↦ ?_⟩
    · simpa using (congrFun h (Fin.natAdd n j)).symm
    · simpa using congrFun h (Fin.castAdd a j)
    · refine Fin.addCases (fun j ↦ ?_) (fun j ↦ ?_) i
      · simpa using congrFun hx j
      · simpa using (hw j).symm
  simp only [hcfg, ite_and, sitePermOp_apply]

/-- **Conjugation by a logical site permutation.** Conjugating a clean implementation by the
permutation of the logical sites fixing the workspace sites gives a clean implementation of the
conjugated logical operator.

Source: the recursive routing in a common pool of Section 5 of TNLean
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
theorem IsCleanImplementation.conjugate_workspaceFixedSitePerm {w : Fin a → α}
    (τ : Equiv.Perm (Fin n)) {U : Matrix (Fin (n + a) → α) (Fin (n + a) → α) ℂ}
    {Z : Matrix (Fin n → α) (Fin n → α) ℂ}
    (h : IsCleanImplementation (basisInclusion (workspaceEmbedding (n := n) w)) U Z) :
    IsCleanImplementation (basisInclusion (workspaceEmbedding (n := n) w))
      (sitePermOp (workspaceFixedSitePerm τ) * U * (sitePermOp (workspaceFixedSitePerm τ))ᴴ)
      (sitePermOp τ * Z * (sitePermOp τ)ᴴ) := by
  have hp := isCleanImplementation_sitePermOp_workspaceFixedSitePerm w τ
  exact (hp.mul h).mul (hp.conjTranspose (sitePermOp_mem_unitary _) (sitePermOp_mem_unitary _))

end Workspace

end QuantumCircuit

section

open Matrix QuantumCircuit

namespace QuantumCircuit.IsCleanImplementation

/-- The ambient initialized columns determine the exact logical initialized columns.

See `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`, §5. -/
theorem logical_columns_of_ambient {ι κ μ : Type*}
    [Fintype ι] [Fintype κ] [DecidableEq κ]
    {J : Matrix ι κ ℂ} {C : Matrix ι ι ℂ} {Z : Matrix κ κ ℂ}
    (h : IsCleanImplementation J C Z) (hJ : J.IsIsometry)
    (E F : Matrix κ μ ℂ) (hc : C * (J * E) = J * F) : Z * E = F := by
  change C * J = J * Z at h
  change Jᴴ * J = 1 at hJ
  have hh : J * (Z * E) = J * F := by
    simpa only [← Matrix.mul_assoc, ← h] using hc
  have hcancel := congrArg (fun M ↦ Jᴴ * M) hh
  simpa only [← Matrix.mul_assoc, hJ, Matrix.one_mul] using hcancel

end QuantumCircuit.IsCleanImplementation

end
