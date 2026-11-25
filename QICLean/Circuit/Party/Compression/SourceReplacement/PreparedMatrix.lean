/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Circuit.Party.Source.Common
import QICLean.Algebra.Matrix.MatrixDensitySum
import QICLean.Analysis.TraceNorm.SubnormalizedPureStateError

/-!
# Words applied after prepared slots, in source coordinates

Preparing a slot inventory with vectors `η i` tensors the product vector `⊗_i η i`
(`SourceInventory.slotVector`) in front of the input, read through the configuration
equivalence `SourceInventory.slotColumnEquiv` (`SourceInventory.op_prepareSlots`). The
preparation is therefore multilinear in the slot vectors, and so is the matrix of a word applied
after it (`Word.preparedMatrix`). Expanding the ket and bra slot vectors separately writes the
mixed density `M ρ M'ᴴ` as a finite sum of density coefficients
(`Word.preparedDensityCoefficient`) weighted by the products of the ket coefficients and the
conjugated bra coefficients; for a weighted gate every pair of branches contributes. The
identities hold for every input matrix `ρ`, for empty slot inventories, and for endpoint
families spanning proper subspaces.

## Main definitions

* `QuantumCircuit.Party.SourceInventory.slotColumnEquiv`,
  `QuantumCircuit.Party.SourceInventory.slotVector` — the source coordinates of a slot system.
* `QuantumCircuit.Party.SourceInventory.slotSiteEquiv` — the coordinates of a slot system at
  one party: the fresh factors of the slots at that party and the basis of the underlying
  system.
* `QuantumCircuit.Party.Word.preparedMatrix`,
  `QuantumCircuit.Party.Word.preparedDensityCoefficient`.

## Main results

* `QuantumCircuit.Party.SourceInventory.op_prepareSlots`,
  `QuantumCircuit.Party.SourceInventory.op_prepareSlots_sum_smul`,
  `QuantumCircuit.Party.SourceInventory.op_prepareSlots_eq_sum_single`.
* `QuantumCircuit.Party.Word.preparedMatrix_density_sum_smul`,
  `QuantumCircuit.Party.Word.preparedMatrix_gate_density_eq_sum_single`.
* `QuantumCircuit.Party.Word.preparedMatrix_eq_sum_unitary`: the expansion in arbitrary
  orthonormal endpoint bases.
* `QuantumCircuit.Party.Word.preparedMatrix_mul_euclideanOuterProduct`.

## References

* Polynomial-PEPS manuscript (September 24, 2026), Theorem 5.2, `04-compression.tex`, source
  preparations and common slots at lines 233–267, the density-source expansion following
  `eq:compression-source-gate` at lines 279–355, pure inputs at lines 137–139 and 409–434.

Adapted from TNLean, `TNLean/Lattice/Compression/SourceGateDensity.lean`,
`TNLean/Lattice/Compression/SourcePreparationCoordinates.lean`,
`TNLean/Lattice/Compression/SourceSlotCoordinates.lean` and
`TNLean/Lattice/Compression/PreparedSourceVectorDensity.lean` (Apache-2.0). Changes: the
endpoint spaces are the Euclidean spaces of the slot bases, so expansions in endpoint bases are
expansions in the coordinates of the bases; matrices are the operators themselves.
-/

open Matrix ManyBody
open scoped ComplexConjugate

namespace QuantumCircuit.Party

variable {P : Type} [DecidableEq P]

namespace SourceInventory

/-! ### Source coordinates of a slot system -/

/-- A configuration of the slot system is a pair of basis elements at every slot, the first slot
first, and a configuration of the underlying system. Source: Theorem 5.2, `04-compression.tex`,
lines 253–267. -/
def slotColumnEquiv : (R : SourceInventory P) → (B : SlotBases R.length) → (Z : P → Type) →
    Config (slotSystem R B Z) ≃ (∀ i, B.left i × B.right i) × Config Z
  | [], _, _ =>
    haveI : IsEmpty (Fin ([] : SourceInventory P).length) := Fin.isEmpty'
    (Equiv.uniqueProd _ _).symm
  | r :: R, B, Z =>
    (addPairConfigEquiv (X := slotSystem R B.tail Z) r.distinct (B.left 0) (B.right 0)).trans
      (((Equiv.refl _).prodCongr (slotColumnEquiv R B.tail Z)).trans
        ((Equiv.prodAssoc _ _ _).symm.trans
          ((Fin.consEquiv fun i ↦ B.left i × B.right i).prodCongr (Equiv.refl _))))

/-- The source coordinates of a configuration of a slot system with one more slot: the fresh
pair of the first slot, then those of the remaining slots. -/
theorem slotColumnEquiv_cons_apply (r : PairSource P) (R : SourceInventory P)
    (B : SlotBases (r :: R).length) (Z : P → Type) (z : Config (slotSystem (r :: R) B Z)) :
    slotColumnEquiv (r :: R) B Z z =
      (Fin.cons (addPairConfigEquiv (X := slotSystem R B.tail Z) r.distinct (B.left 0)
          (B.right 0) z).1
          (slotColumnEquiv R B.tail Z (addPairConfigEquiv (X := slotSystem R B.tail Z)
            r.distinct (B.left 0) (B.right 0) z).2).1,
        (slotColumnEquiv R B.tail Z (addPairConfigEquiv (X := slotSystem R B.tail Z)
          r.distinct (B.left 0) (B.right 0) z).2).2) := by
  simp only [slotColumnEquiv]
  rfl

/-- The product vector `⊗_i η i` of the slot vectors, in the source coordinates. Source:
Theorem 5.2, `04-compression.tex`, lines 233–267 and 342–355. -/
noncomputable def slotVector (R : SourceInventory P) (B : SlotBases R.length)
    (η : ∀ i, EuclideanSpace ℂ (B.left i × B.right i)) :
    EuclideanSpace ℂ (∀ i, B.left i × B.right i) :=
  WithLp.toLp 2 (productVector fun i ↦ η i)

omit [DecidableEq P] in
/-- The coordinates of the slot vector are the products of the coordinates of the slot vectors.
Source: Theorem 5.2, `04-compression.tex`, lines 253–267 and 279–355. -/
@[simp] theorem slotVector_apply (R : SourceInventory P) (B : SlotBases R.length)
    (η : ∀ i, EuclideanSpace ℂ (B.left i × B.right i)) (a : ∀ i, B.left i × B.right i) :
    slotVector R B η a = ∏ i, η i (a i) :=
  rfl

/-- A product over the slots of a tuple with a first entry. -/
private theorem prod_fin_cons {n : ℕ} {α : Fin (n + 1) → Type} (g : ∀ i, α i → ℂ) (a : α 0)
    (f : ∀ i : Fin n, α i.succ) :
    ∏ i, g i (Fin.cons a f i) = g 0 a * ∏ i : Fin n, g i.succ (f i) := by
  rw [Fin.prod_univ_succ]
  simp

/-- A fresh source after a word: the preparation of its vector times the operator of the word. -/
private theorem op_comp_sourceAt [Fintype P] {X Z : P → Type} [∀ p, Fintype (X p)]
    [∀ p, DecidableEq (X p)] [∀ p, Fintype (Z p)] [∀ p, DecidableEq (Z p)] (v : Word X Z)
    {p q : P} (hpq : p ≠ q) (α β : Type) [Fintype α] [DecidableEq α] [Fintype β]
    [DecidableEq β] (η : EuclideanSpace ℂ (α × β)) :
    Word.op (v.comp (Word.sourceAt hpq α β η Z)) =
      prepMatrix (addPairConfigEquiv hpq α β) η * v.op := by
  rw [Word.op_comp, Word.op_sourceAt]

/-- **Preparing the slots tensors the slot vector in front of the input.** Source: Theorem 5.2,
`04-compression.tex`, lines 233–267. -/
theorem op_prepareSlots [Fintype P] (R : SourceInventory P) (B : SlotBases R.length)
    (η : ∀ i, EuclideanSpace ℂ (B.left i × B.right i)) (X : P → Type) [∀ p, Fintype (X p)]
    [∀ p, DecidableEq (X p)] :
    (prepareSlots R B η X).op = prepMatrix (slotColumnEquiv R B X) (slotVector R B η) := by
  induction R with
  | nil =>
    change PartyCircuit.op SourceGate.ev (PartyCircuit.done X) = _
    rw [PartyCircuit.op_done]
    ext y x
    erw [prepMatrix_apply]
    simp only [slotColumnEquiv, Matrix.one_apply, slotVector_apply]
    rfl
  | cons r R ih =>
    ext y x
    rw [prepMatrix_apply, slotColumnEquiv_cons_apply]
    refine (congrFun (congrFun ((op_comp_sourceAt (prepareSlots R B.tail (fun i ↦ η i.succ) X)
      r.distinct (B.left 0) (B.right 0) (η 0)).trans
        (congrArg (_ * ·) (ih B.tail fun i ↦ η i.succ))) y) x).trans ?_
    refine (prepMatrix_mul_apply _ _ _ y x).trans ?_
    simp only [prepMatrix_apply, mul_ite, mul_zero]
    refine if_congr Iff.rfl ?_ rfl
    exact (prod_fin_cons (fun i (z : B.left i × B.right i) ↦ η i z) _ _).symm

omit [DecidableEq P] in
/-- Finite linear combinations in the slots expand the slot vector over the choices of one
component in every slot. Source: Theorem 5.2, `04-compression.tex`, lines 279–355. -/
theorem slotVector_sum_smul (R : SourceInventory P) (B : SlotBases R.length)
    {A : Fin R.length → Type} [∀ i, Fintype (A i)] (c : ∀ i, A i → ℂ)
    (η : ∀ i, A i → EuclideanSpace ℂ (B.left i × B.right i)) :
    slotVector R B (fun i ↦ ∑ a, c i a • η i a) =
      ∑ a : ∀ i, A i, (∏ i, c i (a i)) • slotVector R B fun i ↦ η i (a i) := by
  classical
  ext f
  simp only [slotVector_apply, WithLp.ofLp_sum, WithLp.ofLp_smul, Finset.sum_apply,
    Pi.smul_apply, smul_eq_mul]
  rw [Finset.prod_univ_sum]
  exact Finset.sum_congr rfl fun a _ ↦ Finset.prod_mul_distrib

/-- A preparation is linear in the prepared vector. -/
private theorem prepMatrix_sum_smul {m n α ι : Type} [DecidableEq n] [Fintype ι] (e : m ≃ α × n)
    (c : ι → ℂ)
    (v : ι → EuclideanSpace ℂ α) :
    prepMatrix e (∑ a, c a • v a) = ∑ a, c a • prepMatrix e (v a) := by
  classical
  ext y x
  simp only [prepMatrix_apply, Matrix.sum_apply, Matrix.smul_apply, WithLp.ofLp_sum,
    WithLp.ofLp_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  split_ifs <;> simp

/-- **A finite linear combination in every slot expands the preparation** as the sum over the
choices of one component from each slot, weighted by the product of the coefficients. Source:
Theorem 5.2, `04-compression.tex`, lines 279–355. -/
theorem op_prepareSlots_sum_smul [Fintype P] (R : SourceInventory P) (B : SlotBases R.length)
    {A : Fin R.length → Type} [∀ i, Fintype (A i)] (c : ∀ i, A i → ℂ)
    (η : ∀ i, A i → EuclideanSpace ℂ (B.left i × B.right i)) (X : P → Type)
    [∀ p, Fintype (X p)] [∀ p, DecidableEq (X p)] :
    (prepareSlots R B (fun i ↦ ∑ a, c i a • η i a) X).op =
      ∑ a : ∀ i, A i, (∏ i, c i (a i)) • (prepareSlots R B (fun i ↦ η i (a i)) X).op := by
  simp only [op_prepareSlots, slotVector_sum_smul, prepMatrix_sum_smul]

end SourceInventory

/-- A pair vector is the sum of its coordinates times the products of the basis vectors of the
two endpoints. -/
private theorem eq_sum_vecKron_single {α β : Type} [Fintype α] [DecidableEq α] [Fintype β]
    [DecidableEq β] (x : EuclideanSpace ℂ (α × β)) :
    x = ∑ a : α × β,
      x a • EuclideanSpace.vecKron (EuclideanSpace.single a.1 1) (EuclideanSpace.single a.2 1) := by
  ext ⟨s, t⟩
  simp only [EuclideanSpace.vecKron, WithLp.ofLp_sum, WithLp.ofLp_smul, Finset.sum_apply,
    Pi.smul_apply, smul_eq_mul, PiLp.single_apply]
  rw [Finset.sum_eq_single (s, t)]
  · simp
  · rintro ⟨a, b⟩ - h
    by_cases ha : s = a <;> by_cases hb : t = b <;> simp_all
  · simp

namespace SourceInventory

/-- **The preparation in the coordinates of the slot bases**: the sum over the pairs of basis
elements in every slot of the product of the coordinates of the slot vectors times the
preparation of the basis vectors. Source: Theorem 5.2, `04-compression.tex`, lines 253–267 and
342–355. -/
theorem op_prepareSlots_eq_sum_single [Fintype P] (R : SourceInventory P)
    (B : SlotBases R.length) (η : ∀ i, EuclideanSpace ℂ (B.left i × B.right i)) (X : P → Type)
    [∀ p, Fintype (X p)] [∀ p, DecidableEq (X p)] :
    (prepareSlots R B η X).op =
      ∑ a : ∀ i, B.left i × B.right i, (∏ i, η i (a i)) •
        (prepareSlots R B (fun i ↦ EuclideanSpace.vecKron (EuclideanSpace.single (a i).1 1)
          (EuclideanSpace.single (a i).2 1)) X).op := by
  conv_lhs => rw [show η = fun i ↦ ∑ a, η i a • EuclideanSpace.vecKron
    (EuclideanSpace.single a.1 1) (EuclideanSpace.single a.2 1) from
      funext fun i ↦ eq_sum_vecKron_single (η i)]
  exact op_prepareSlots_sum_smul R B _ _ X

end SourceInventory

/-! ### Words applied after prepared slots -/

namespace Word

variable [Fintype P] {Y : P → Type}

/-- The matrix of a word applied after preparing the slots with the vectors `η`.
Source: Theorem 5.2, `04-compression.tex`, lines 233–267 and 279–317. -/
noncomputable def preparedMatrix (R : SourceInventory P) (B : SourceInventory.SlotBases R.length)
    (η : ∀ i, EuclideanSpace ℂ (B.left i × B.right i)) (X : P → Type) [∀ p, Fintype (X p)]
    [∀ p, DecidableEq (X p)] (v : Word (SourceInventory.slotSystem R B X) Y) :
    Matrix (Config Y) (Config X) ℂ :=
  v.op * (SourceInventory.prepareSlots R B η X).op

variable (R : SourceInventory P) (B : SourceInventory.SlotBases R.length) (X : P → Type)
  [∀ p, Fintype (X p)] [∀ p, DecidableEq (X p)]

/-- Finite sums in the slots give the corresponding finite sum of prepared matrices, with one
coefficient from each slot. Source: Theorem 5.2, `04-compression.tex`, lines 279–355. -/
theorem preparedMatrix_sum_smul {A : Fin R.length → Type} [∀ i, Fintype (A i)]
    (c : ∀ i, A i → ℂ) (η : ∀ i, A i → EuclideanSpace ℂ (B.left i × B.right i))
    (v : Word (SourceInventory.slotSystem R B X) Y) :
    v.preparedMatrix R B (fun i ↦ ∑ a, c i a • η i a) X =
      ∑ a : ∀ i, A i, (∏ i, c i (a i)) • v.preparedMatrix R B (fun i ↦ η i (a i)) X := by
  simp only [preparedMatrix, SourceInventory.op_prepareSlots_sum_smul, Matrix.mul_sum,
    Matrix.mul_smul]

/-- The prepared matrix is the sum of the preparations of the basis vectors of the slots,
weighted by the products of the coordinates of the slot vectors. Source: Theorem 5.2,
`04-compression.tex`, lines 279–355. -/
theorem preparedMatrix_eq_sum_single (η : ∀ i, EuclideanSpace ℂ (B.left i × B.right i))
    (v : Word (SourceInventory.slotSystem R B X) Y) :
    v.preparedMatrix R B η X =
      ∑ a : ∀ i, B.left i × B.right i, (∏ i, η i (a i)) •
        v.preparedMatrix R B (fun i ↦ EuclideanSpace.vecKron
          (EuclideanSpace.single (a i).1 1) (EuclideanSpace.single (a i).2 1)) X := by
  simp only [preparedMatrix, SourceInventory.op_prepareSlots_eq_sum_single R B η X,
    Matrix.mul_sum, Matrix.mul_smul]

/-- **The prepared matrix in any endpoint basis.** For matrices `W i` with `W i * (W i)ᴴ = 1`,
for instance unitaries whose columns form orthonormal bases of the slots, the prepared matrix is
the sum of the preparations of the columns of the `W i`, weighted by the products of the
coordinates `(W i)ᴴ η i` of the slot vectors. Source: Theorem 5.2, `04-compression.tex`,
lines 279–355. -/
theorem preparedMatrix_eq_sum_unitary {K : Fin R.length → Type} [∀ i, Fintype (K i)]
    (W : ∀ i, Matrix (B.left i × B.right i) (K i) ℂ) (hW : ∀ i, W i * (W i)ᴴ = 1)
    (η : ∀ i, EuclideanSpace ℂ (B.left i × B.right i))
    (v : Word (SourceInventory.slotSystem R B X) Y) :
    v.preparedMatrix R B η X =
      ∑ a : ∀ i, K i, (∏ i, ((W i)ᴴ *ᵥ (η i).ofLp) (a i)) •
        v.preparedMatrix R B (fun i ↦ WithLp.toLp 2 ((W i)ᵀ (a i))) X := by
  rw [← preparedMatrix_sum_smul R B X (fun i a ↦ ((W i)ᴴ *ᵥ (η i).ofLp) a)
    (fun i a ↦ WithLp.toLp 2 ((W i)ᵀ a))]
  congr 1
  funext i
  ext x
  have h := congrFun (congrArg (fun M ↦ M *ᵥ (η i).ofLp) (hW i)) x
  simp only [Matrix.one_mulVec, ← Matrix.mulVec_mulVec] at h
  conv_lhs => rw [← h]
  simp [Matrix.mulVec, dotProduct, mul_comm]

/-- The density coefficient obtained by preparing the endpoint vectors `uU i (a i).1 ⊗
uV i (a i).2` in the ket word `v` and `uU' i (b i).1 ⊗ uV' i (b i).2` in the bra word `v'`. No
spanning or orthonormality condition on the endpoint families, nor positivity of the input
matrix, is needed. Source: Theorem 5.2, `04-compression.tex`, lines 279–317. -/
noncomputable def preparedDensityCoefficient {K L K' L' : Fin R.length → Type}
    (uU : ∀ i, K i → EuclideanSpace ℂ (B.left i)) (uV : ∀ i, L i → EuclideanSpace ℂ (B.right i))
    (uU' : ∀ i, K' i → EuclideanSpace ℂ (B.left i))
    (uV' : ∀ i, L' i → EuclideanSpace ℂ (B.right i))
    (v v' : Word (SourceInventory.slotSystem R B X) Y) (ρ : Matrix (Config X) (Config X) ℂ)
    (a : ∀ i, K i × L i) (b : ∀ i, K' i × L' i) : Matrix (Config Y) (Config Y) ℂ :=
  v.preparedMatrix R B (fun i ↦ EuclideanSpace.vecKron (uU i (a i).1) (uV i (a i).2)) X * ρ *
    (v'.preparedMatrix R B (fun i ↦ EuclideanSpace.vecKron (uU' i (b i).1) (uV' i (b i).2)) X)ᴴ

/-- Expanding both sides gives the ket–bra coefficient at each slot. Source: Theorem 5.2,
`04-compression.tex`, lines 279–317. -/
private theorem finite_source_density_expansion {I m n p : Type} [Fintype I] [DecidableEq I]
    [Fintype n] {A A' : I → Type} [∀ i, Fintype (A i)] [∀ i, Fintype (A' i)]
    (η : ∀ i, A i → ℂ) (ζ : ∀ i, A' i → ℂ) (M : (∀ i, A i) → Matrix m n ℂ)
    (M' : (∀ i, A' i) → Matrix p n ℂ) (ρ : Matrix n n ℂ) :
    (∑ a, (∏ i, η i (a i)) • M a) * ρ * (∑ b, (∏ i, ζ i (b i)) • M' b)ᴴ =
      ∑ a, ∑ b, (∏ i, η i (a i) * conj (ζ i (b i))) • (M a * ρ * (M' b)ᴴ) := by
  simpa only [map_prod, Finset.prod_mul_distrib] using
    Matrix.sum_smul_mul_mul_conjTranspose (fun a ↦ ∏ i, η i (a i))
      (fun b ↦ ∏ i, ζ i (b i)) M M' ρ

/-- **Finite endpoint expansions of the ket and bra slot vectors give the density
coefficients.** The endpoint families may span proper subspaces. Source: Theorem 5.2,
`04-compression.tex`, lines 279–355. -/
theorem preparedMatrix_density_sum_smul {K L K' L' : Fin R.length → Type}
    [∀ i, Fintype (K i)] [∀ i, Fintype (L i)] [∀ i, Fintype (K' i)] [∀ i, Fintype (L' i)]
    (uU : ∀ i, K i → EuclideanSpace ℂ (B.left i)) (uV : ∀ i, L i → EuclideanSpace ℂ (B.right i))
    (uU' : ∀ i, K' i → EuclideanSpace ℂ (B.left i))
    (uV' : ∀ i, L' i → EuclideanSpace ℂ (B.right i))
    (c : ∀ i, K i × L i → ℂ) (d : ∀ i, K' i × L' i → ℂ)
    (v v' : Word (SourceInventory.slotSystem R B X) Y) (ρ : Matrix (Config X) (Config X) ℂ) :
    v.preparedMatrix R B
        (fun i ↦ ∑ a, c i a • EuclideanSpace.vecKron (uU i a.1) (uV i a.2)) X * ρ *
        (v'.preparedMatrix R B
          (fun i ↦ ∑ b, d i b • EuclideanSpace.vecKron (uU' i b.1) (uV' i b.2)) X)ᴴ =
      ∑ a : ∀ i, K i × L i, ∑ b : ∀ i, K' i × L' i,
        (∏ i, c i (a i) * conj (d i (b i))) •
          v.preparedDensityCoefficient R B X uU uV uU' uV' v' ρ a b := by
  rw [v.preparedMatrix_sum_smul R B X c, v'.preparedMatrix_sum_smul R B X d]
  exact finite_source_density_expansion _ _ _ _ ρ

/-- The ket and bra prepared matrices in the coordinates of the slot bases: the density
coefficients of the basis vectors weighted by the coordinates of the ket vectors and the
conjugated coordinates of the bra vectors. Source: Theorem 5.2, `04-compression.tex`,
lines 279–355. -/
theorem preparedMatrix_density_eq_sum_single (η ζ : ∀ i, EuclideanSpace ℂ (B.left i × B.right i))
    (v v' : Word (SourceInventory.slotSystem R B X) Y) (ρ : Matrix (Config X) (Config X) ℂ) :
    v.preparedMatrix R B η X * ρ * (v'.preparedMatrix R B ζ X)ᴴ =
      ∑ a : ∀ i, B.left i × B.right i, ∑ b : ∀ i, B.left i × B.right i,
        (∏ i, η i (a i) * conj (ζ i (b i))) •
          v.preparedDensityCoefficient R B X (fun _ a ↦ EuclideanSpace.single a 1)
            (fun _ a ↦ EuclideanSpace.single a 1) (fun _ a ↦ EuclideanSpace.single a 1)
            (fun _ a ↦ EuclideanSpace.single a 1) v' ρ a b := by
  rw [v.preparedMatrix_eq_sum_single R B X, v'.preparedMatrix_eq_sum_single R B X]
  exact finite_source_density_expansion _ _ _ _ ρ

/-- **The density of a weighted gate is the sum over both branches and their coordinates in
the slot bases.** Every coefficient is retained, conjugated on the bra branch. Source:
Theorem 5.2, `04-compression.tex`, lines 233–267 and 279–355. -/
theorem preparedMatrix_gate_density_eq_sum_single {ι : Type} [Fintype ι] (c : ι → ℂ)
    (η : ι → ∀ i, EuclideanSpace ℂ (B.left i × B.right i))
    (v : ι → Word (SourceInventory.slotSystem R B X) Y) (ρ : Matrix (Config X) (Config X) ℂ) :
    (∑ ξ, c ξ • (v ξ).preparedMatrix R B (η ξ) X) * ρ *
        (∑ ξ, c ξ • (v ξ).preparedMatrix R B (η ξ) X)ᴴ =
      ∑ ξ, ∑ ζ, (c ξ * conj (c ζ)) •
        ∑ a : ∀ i, B.left i × B.right i, ∑ b : ∀ i, B.left i × B.right i,
          (∏ i, η ξ i (a i) * conj (η ζ i (b i))) •
            (v ξ).preparedDensityCoefficient R B X (fun _ a ↦ EuclideanSpace.single a 1)
              (fun _ a ↦ EuclideanSpace.single a 1) (fun _ a ↦ EuclideanSpace.single a 1)
              (fun _ a ↦ EuclideanSpace.single a 1) (v ζ) ρ a b := by
  rw [Matrix.sum_smul_mul_mul_conjTranspose]
  refine Finset.sum_congr rfl fun ξ _ ↦ Finset.sum_congr rfl fun ζ _ ↦ ?_
  rw [(v ξ).preparedMatrix_density_eq_sum_single R B X (η ξ) (η ζ) (v ζ) ρ]

/-- A matrix product around an outer product of two vectors is the outer product of their
images. -/
private theorem mul_euclideanOuterProduct_mul_conjTranspose {m m' n : Type} [Fintype n]
    (M : Matrix m n ℂ) (M' : Matrix m' n ℂ) (ψ φ : EuclideanSpace ℂ n) :
    M * euclideanOuterProduct ψ φ * M'ᴴ =
      vecMulVec (M *ᵥ WithLp.ofLp ψ) (star (M' *ᵥ WithLp.ofLp φ)) := by
  rw [euclideanOuterProduct, mul_vecMulVec, vecMulVec_mul, star_mulVec]

/-- **A mixed pure input produces the mixed pair of prepared output vectors.** Source:
Theorem 5.2, `04-compression.tex`, lines 137–139 and 409–434. -/
theorem preparedMatrix_mul_euclideanOuterProduct
    (η ζ : ∀ i, EuclideanSpace ℂ (B.left i × B.right i))
    (v w : Word (SourceInventory.slotSystem R B X) Y) (ψ φ : EuclideanSpace ℂ (Config X)) :
    v.preparedMatrix R B η X * euclideanOuterProduct ψ φ * (w.preparedMatrix R B ζ X)ᴴ =
      euclideanOuterProduct
        (Matrix.toEuclideanLin v.op
          (Matrix.toEuclideanLin (SourceInventory.prepareSlots R B η X).op ψ))
        (Matrix.toEuclideanLin w.op
          (Matrix.toEuclideanLin (SourceInventory.prepareSlots R B ζ X).op φ)) := by
  rw [mul_euclideanOuterProduct_mul_conjTranspose, euclideanOuterProduct]
  simp only [preparedMatrix, Matrix.toLpLin_apply, WithLp.ofLp_toLp, mulVec_mulVec]

/-- Absorbing an input-preparation word `p` gives the outer product of the output vectors of the
two composed words on the one basis vector of the system with one basis vector at every party.
Source: Theorem 5.2, `04-compression.tex`, lines 137–139 and 409–434. -/
theorem preparedMatrix_mul_euclideanOuterProduct_preparedInput
    (η ζ : ∀ i, EuclideanSpace ℂ (B.left i × B.right i))
    (v w : Word (SourceInventory.slotSystem R B X) Y) (p : Word (fun _ ↦ Unit) X) :
    v.preparedMatrix R B η X *
        euclideanOuterProduct (Matrix.toEuclideanLin p.op (WithLp.toLp 2 fun _ ↦ 1))
          (Matrix.toEuclideanLin p.op (WithLp.toLp 2 fun _ ↦ 1)) *
        (w.preparedMatrix R B ζ X)ᴴ =
      euclideanOuterProduct
        (Matrix.toEuclideanLin (Word.op (p.comp ((SourceInventory.prepareSlots R B η X).comp v)))
          (WithLp.toLp 2 fun _ ↦ 1))
        (Matrix.toEuclideanLin (Word.op (p.comp ((SourceInventory.prepareSlots R B ζ X).comp w)))
          (WithLp.toLp 2 fun _ ↦ 1)) := by
  rw [preparedMatrix_mul_euclideanOuterProduct]
  simp only [Word.op_comp, Matrix.toLpLin_apply, mulVec_mulVec, Matrix.mul_assoc]

end Word

end QuantumCircuit.Party

namespace QuantumCircuit.Party.SourceInventory

variable {P : Type} [DecidableEq P]

/-! ### Party coordinates of a slot system -/

/-- The basis of a slot system at one party: the fresh factors of the slots at that party, the
first slot first, and the basis of the underlying system. A slot without an endpoint at the
party contributes a factor with one element. Source: Theorem 5.2, `04-compression.tex`,
lines 253–267 and 409–434. -/
def slotSiteEquiv : (R : SourceInventory P) → (B : SlotBases R.length) → (Z : P → Type) →
    (p : P) → slotSystem R B Z p ≃
      (∀ i, pairFactor (R.get i).distinct (B.left i) (B.right i) p) × Z p
  | [], _, _, _ =>
    haveI : IsEmpty (Fin ([] : SourceInventory P).length) := Fin.isEmpty'
    (Equiv.uniqueProd _ _).symm
  | r :: R, B, Z, p =>
    (addPairSiteEquiv r.distinct (B.left 0) (B.right 0) (slotSystem R B.tail Z) p).trans
      (((Equiv.refl _).prodCongr (slotSiteEquiv R B.tail Z p)).trans
        ((Equiv.prodAssoc _ _ _).symm.trans
          ((Fin.consEquiv fun i ↦ pairFactor ((r :: R).get i).distinct (B.left i)
            (B.right i) p).prodCongr (Equiv.refl _))))

/-- The party coordinates of a slot system with one more slot: the fresh factor of the first
slot, then those of the remaining slots. -/
theorem slotSiteEquiv_cons_apply (r : PairSource P) (R : SourceInventory P)
    (B : SlotBases (r :: R).length) (Z : P → Type) (p : P) (z : slotSystem (r :: R) B Z p) :
    slotSiteEquiv (r :: R) B Z p z =
      (Fin.cons (addPairSiteEquiv r.distinct (B.left 0) (B.right 0)
          (slotSystem R B.tail Z) p z).1
          (slotSiteEquiv R B.tail Z p (addPairSiteEquiv r.distinct (B.left 0) (B.right 0)
            (slotSystem R B.tail Z) p z).2).1,
        (slotSiteEquiv R B.tail Z p (addPairSiteEquiv r.distinct (B.left 0) (B.right 0)
          (slotSystem R B.tail Z) p z).2).2) := by
  simp only [slotSiteEquiv]
  rfl

end QuantumCircuit.Party.SourceInventory
