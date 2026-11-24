/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Circuit.Party.Compression.PhysicalReadout.Components
import QICLean.Analysis.TraceNorm.WeightedBlockCombination
import QICLean.Channel.PartialTrace.Blocks

/-!
# The separated two-word form of a corrected source term

A corrected source term is computed by two words: an affected word `v` (ket side; `w` on the
bra side) on input frames `F : Matrix (Config X) (I × T) ℂ` that need not span the input, and an
exterior word `v'` (ket side; `w'` on the bra side) on input frames `G : Matrix (Config Z) T ℂ`,
the two frames sharing the Schmidt index `t` of weight `τ t`. After the readouts `K` (affected)
and `K'` (exterior), the matched Schmidt summands give the *separated Schmidt output*
`∑_t √τ_t (K v F)_x(i, t) ⊗ (K' v' G) e_t`; its coordinates, with both discarded indices kept,
are the *separated physical coordinates*, and their outer products with complex coefficients
`z`, after tracing both discarded indices, form the *separated physical density*.

Tracing the affected discarded index of the Schmidt physical vectors gives exactly the weighted
combination `Matrix.halfWeightedBlockCombination τ τ' O z` of the blocks of the Gram matrix `O`
of the two affected words in their frames (no coefficient is conjugated, and the transpose is
the ordinary one), and the separated physical density at fixed affected physical indices is the
exterior words applied to this combination, followed by the partial trace. The ket and bra
Schmidt spaces may differ.

## Main definitions

* `QuantumCircuit.Party.Word.physicalFrameGramMatrix`,
  `QuantumCircuit.Party.Word.schmidtPhysicalVector`.
* `QuantumCircuit.Party.Word.separatedSchmidtOutput`,
  `QuantumCircuit.Party.Word.separatedPhysicalCoordinates`,
  `QuantumCircuit.Party.Word.separatedPhysicalDensity`.

## Main results

* `QuantumCircuit.Party.Word.partialTraceRight_mul_op_mul_mul_conjTranspose_apply` — the partial
  trace pairs the input with the Gram matrix in two frames.
* `QuantumCircuit.Party.Word.sum_schmidtPhysicalVector_outer_eq_halfWeightedBlockCombination`.
* `QuantumCircuit.Party.Word.separatedPhysicalDensity_submatrix`, from
  `partialTraceRight_separatedSchmidtOutput_eq_halfWeightedBlockCombination`: the exterior
  action on the weighted block combination.
* `QuantumCircuit.Party.Word.kronecker_mulVec_eq_separatedPhysicalCoordinates`.

## References

* Polynomial-PEPS manuscript (September 24, 2026), Theorem 5.2, `04-compression.tex`,
  lines 409–480, `eq:compression-exterior-input`.
-/

noncomputable section

open Matrix ManyBody
open scoped Matrix.Norms.L2Operator ComplexConjugate Kronecker

namespace QuantumCircuit.Party.Word

variable {P Q : Type} [Fintype P] [DecidableEq P] [Fintype Q] [DecidableEq Q]
  {X X' Y : P → Type} [∀ p, Fintype (X p)] [∀ p, DecidableEq (X p)] [∀ p, Fintype (X' p)]
  [∀ p, DecidableEq (X' p)] [∀ p, Fintype (Y p)]
  {Z Z' W : Q → Type} [∀ q, Fintype (Z q)] [∀ q, DecidableEq (Z q)] [∀ q, Fintype (Z' q)]
  [∀ q, DecidableEq (Z' q)] [∀ q, Fintype (W q)]
  {Phys Env Phys' Env' I L T U : Type} [Fintype Phys] [DecidableEq Phys] [Fintype Env]
  [DecidableEq Env]

/-! ### The Gram matrix in two input frames -/

section FrameGram

variable {n n' : Type}

/-- The Gram matrix of two affected words in their input frames: the frame columns of the bra
component of `w` at `y` paired with those of the ket component of `v` at `x`. The frames need
not span the inputs. Source: Theorem 5.2, `04-compression.tex`, lines 419–443. -/
def physicalFrameGramMatrix (K : Matrix (Phys × Env) (Config Y) ℂ) (x y : Phys) (v : Word X Y)
    (w : Word X' Y) (F : Matrix (Config X) n ℂ) (F' : Matrix (Config X') n' ℂ) :
    Matrix n' n ℂ :=
  (physicalComponent K y w * F')ᴴ * (physicalComponent K x v * F)

/-- The Gram matrix in two frames is the Gram matrix of the words between the frames. -/
theorem physicalFrameGramMatrix_eq (K : Matrix (Phys × Env) (Config Y) ℂ) (x y : Phys)
    (v : Word X Y) (w : Word X' Y) (F : Matrix (Config X) n ℂ)
    (F' : Matrix (Config X') n' ℂ) :
    physicalFrameGramMatrix K x y v w F F' = F'ᴴ * physicalGramMatrix K x y v w * F := by
  simp only [physicalFrameGramMatrix, physicalGramMatrix, conjTranspose_mul, Matrix.mul_assoc]

/-- An entry of the Gram matrix in two frames keeps the bra–ket order of the discarded
vectors. -/
theorem physicalFrameGramMatrix_apply (K : Matrix (Phys × Env) (Config Y) ℂ) (x y : Phys)
    (v : Word X Y) (w : Word X' Y) (F : Matrix (Config X) n ℂ)
    (F' : Matrix (Config X') n' ℂ) (j : n') (i : n) :
    physicalFrameGramMatrix K x y v w F F' j i =
      ∑ e, star ((physicalComponent K y w * F') e j) * (physicalComponent K x v * F) e i := by
  simp only [physicalFrameGramMatrix, Matrix.mul_apply (M := (physicalComponent K y w * F')ᴴ),
    conjTranspose_apply]

/-- Tracing the discarded index of the read outputs of `v` and `w` on the frames `F`, `F'`
around an arbitrary rectangular `ρ` pairs `ρ` with the opposite-index entry of the Gram matrix in
the two frames; with orthonormal input bases as frames this is the identity in those bases.
Source: Theorem 5.2, `04-compression.tex`, lines 469–478. -/
theorem partialTraceRight_mul_op_mul_mul_conjTranspose_apply [Fintype n] [Fintype n']
    (K : Matrix (Phys × Env) (Config Y) ℂ) (x y : Phys) (v : Word X Y) (w : Word X' Y)
    (F : Matrix (Config X) n ℂ) (F' : Matrix (Config X') n' ℂ) (ρ : Matrix n n' ℂ) :
    partialTraceRight (K * v.op * F * ρ * (K * w.op * F')ᴴ) x y =
      ∑ i, ∑ j, ρ i j * physicalFrameGramMatrix K x y v w F F' j i := by
  have hc : ∀ {S : P → Type} [∀ p, Fintype (S p)] [∀ p, DecidableEq (S p)] {m : Type}
      (u : Word S Y) (H : Matrix (Config S) m ℂ) (z : Phys) (e : Env) (k : m),
      (physicalComponent K z u * H) e k = (K * u.op * H) (z, e) k := by
    intro S _ _ m u H z e k
    simp only [mul_apply (M := physicalComponent K z u), physicalComponent_apply,
      mul_apply (M := K * u.op)]
  simp only [partialTraceRight_apply, mul_apply (M := K * v.op * F * ρ),
    mul_apply (M := K * v.op * F), conjTranspose_apply, physicalFrameGramMatrix_apply, hc,
    Finset.mul_sum, Finset.sum_mul]
  conv_lhs => rw [Finset.sum_comm]
  refine (Finset.sum_congr rfl fun j _ ↦ Finset.sum_comm).trans ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦
    Finset.sum_congr rfl fun e _ ↦ ?_
  ring

/-- Contractive (for instance isometric) frames keep the Gram matrix of two allowed words a
contraction, whatever the discarded dimension. Source: Theorem 5.2,
`eq:compression-block-contraction`, `04-compression.tex`, lines 436–442. -/
theorem norm_physicalFrameGramMatrix_le_one [∀ p, DecidableEq (Y p)] [Fintype n] [Fintype n']
    [DecidableEq n] [DecidableEq n']
    (K : Matrix (Phys × Env) (Config Y) ℂ)
    (x y : Phys) (v : Word X Y) (w : Word X' Y) (F : Matrix (Config X) n ℂ)
    (F' : Matrix (Config X') n' ℂ) (hK : ‖K‖ ≤ 1) (hv : v.IsAllowed) (hw : w.IsAllowed)
    (hF : ‖F‖ ≤ 1) (hF' : ‖F'‖ ≤ 1) : ‖physicalFrameGramMatrix K x y v w F F'‖ ≤ 1 := by
  rw [physicalFrameGramMatrix_eq]
  exact l2_opNorm_mul_le_one _ _
    (l2_opNorm_mul_le_one _ _ ((l2_opNorm_conjTranspose F').trans_le hF')
      (norm_physicalGramMatrix_le_one K x y v w hK hv hw)) hF

end FrameGram

/-! ### Schmidt physical vectors -/

/-- The affected output of the Schmidt vector of the frame `F` with weights `τ` at the
corrected coordinate `i`, after the physical component at `x`: the vector
`∑_t √τ_t e_t ⊗ (K v F)_x(i, t)` on the untouched Schmidt index and the discarded index, given by
its coordinates. Source: Theorem 5.2, `04-compression.tex`, lines 383–391, 419–428 and 469–478. -/
def schmidtPhysicalVector (K : Matrix (Phys × Env) (Config Y) ℂ) (x : Phys) (v : Word X Y)
    (F : Matrix (Config X) (I × T) ℂ) (tau : T → ℝ) (i : I) : T × Env → ℂ :=
  fun q ↦ (Real.sqrt (tau q.1) : ℂ) * (physicalComponent K x v * F) q.2 (i, q.1)

/-- The coordinate of a Schmidt physical vector at the untouched index `t` is its own summand,
with no phase change. -/
@[simp] theorem schmidtPhysicalVector_apply (K : Matrix (Phys × Env) (Config Y) ℂ) (x : Phys)
    (v : Word X Y) (F : Matrix (Config X) (I × T) ℂ) (tau : T → ℝ) (i : I) (t : T) (e : Env) :
    schmidtPhysicalVector K x v F tau i (t, e) =
      (Real.sqrt (tau t) : ℂ) * (physicalComponent K x v * F) e (i, t) :=
  rfl

/-- **Tracing the affected discarded index gives the weighted block combination.** The ket and
bra Schmidt spaces may have different dimensions; no correction coefficient is conjugated.
Source: Theorem 5.2, `eq:compression-exterior-input`, `04-compression.tex`, lines 469–481. -/
theorem sum_schmidtPhysicalVector_outer_eq_halfWeightedBlockCombination [Fintype I] [Fintype L]
    [Fintype T] [Fintype U] [DecidableEq T] [DecidableEq U] (K : Matrix (Phys × Env) (Config Y) ℂ)
    (x y : Phys) (v : Word X Y) (w : Word X' Y) (F : Matrix (Config X) (I × T) ℂ)
    (F' : Matrix (Config X') (L × U) ℂ) (tau : T → ℝ) (tau' : U → ℝ) (z : I × L → ℂ) :
    (fun t u ↦ ∑ e : Env, (∑ q : I × L, z q • vecMulVec (schmidtPhysicalVector K x v F tau q.1)
      (fun h ↦ conj (schmidtPhysicalVector K y w F' tau' q.2 h))) (t, e) (u, e)) =
      halfWeightedBlockCombination tau tau' (physicalFrameGramMatrix K x y v w F F') z := by
  ext t u
  simp only [Matrix.sum_apply, Matrix.smul_apply, vecMulVec_apply, smul_eq_mul,
    schmidtPhysicalVector_apply, map_mul, Complex.conj_ofReal, halfWeightedBlockCombination,
    halfWeighted, diagonal_mul, mul_diagonal, transpose_apply, comp_symm_apply,
    physicalFrameGramMatrix_apply, RCLike.star_def]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun q _ ↦ ?_
  simp only [Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun e _ ↦ ?_
  ring

/-! ### Separated outputs and the separated physical density -/

/-- The two local outputs from the matched Schmidt summands at the corrected coordinate `i`,
the affected output projected on the physical index `x`: the coordinates of
`∑_t √τ_t (K v F)_x(i, t) ⊗ (K' v' G) e_t`, indexed by the affected discarded index and the
exterior physical and discarded indices. Source: Theorem 5.2, `04-compression.tex`,
lines 409–451. -/
def separatedSchmidtOutput [Fintype T] (K : Matrix (Phys × Env) (Config Y) ℂ) (x : Phys)
    (v : Word X Y)
    (F : Matrix (Config X) (I × T) ℂ) (tau : T → ℝ) (K' : Matrix (Phys' × Env') (Config W) ℂ)
    (v' : Word Z W) (G : Matrix (Config Z) T ℂ) (i : I) : Env × (Phys' × Env') → ℂ :=
  fun h ↦ ∑ t, (Real.sqrt (tau t) : ℂ) *
    ((physicalComponent K x v * F) h.1 (i, t) * (K' * v'.op * G) h.2 t)

/-- The exterior word acts on the untouched coordinate of the Schmidt physical vector; the two
discarded indices stay separate. -/
theorem separatedSchmidtOutput_eq_mulVec [Fintype T] (K : Matrix (Phys × Env) (Config Y) ℂ)
    (x : Phys) (v : Word X Y) (F : Matrix (Config X) (I × T) ℂ) (tau : T → ℝ)
    (K' : Matrix (Phys' × Env') (Config W) ℂ) (v' : Word Z W) (G : Matrix (Config Z) T ℂ)
    (i : I) (e : Env) (b : Phys' × Env') :
    separatedSchmidtOutput K x v F tau K' v' G i (e, b) =
      ((K' * v'.op * G) *ᵥ fun t ↦ schmidtPhysicalVector K x v F tau i (t, e)) b := by
  simp only [separatedSchmidtOutput, mulVec, dotProduct, schmidtPhysicalVector_apply]
  exact Finset.sum_congr rfl fun t _ ↦ by ring

omit [DecidableEq Env] in
/-- Fixed exterior matrices commute with tracing the affected discarded index; the ket and bra
retained spaces may have different dimensions. -/
private theorem partialTraceRight_sum_vecMulVec_mulVec {M e : Type} [Fintype e]
    [Fintype I] [Fintype L] [Fintype T] [Fintype U]
    (R : Matrix (M × e) T ℂ) (R' : Matrix (M × e) U ℂ) (ψ : I → T × Env → ℂ)
    (φ : L → U × Env → ℂ) (z : I × L → ℂ) :
    partialTraceRight (∑ q, z q • vecMulVec
      (fun h : M × (Env × e) ↦ (R *ᵥ fun t ↦ ψ q.1 (t, h.2.1)) (h.1, h.2.2))
      (fun h : M × (Env × e) ↦ conj ((R' *ᵥ fun u ↦ φ q.2 (u, h.2.1)) (h.1, h.2.2)))) =
      partialTraceRight (R * Matrix.of (fun t u ↦ ∑ h : Env, (∑ q, z q • vecMulVec
        (ψ q.1) (fun r ↦ conj (φ q.2 r))) (t, h) (u, h)) * R'ᴴ) := by
  have hZ : Matrix.of (fun t u ↦ ∑ h : Env, (∑ q, z q • vecMulVec
      (ψ q.1) (fun r ↦ conj (φ q.2 r))) (t, h) (u, h)) =
      ∑ h : Env, ∑ q, z q • vecMulVec (fun t ↦ ψ q.1 (t, h)) (star fun u ↦ φ q.2 (u, h)) := by
    ext t u
    simp only [of_apply, Matrix.sum_apply, Matrix.smul_apply, vecMulVec_apply, smul_eq_mul,
      Pi.star_apply, RCLike.star_def]
  rw [hZ]
  simp_rw [Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_smul, Matrix.smul_mul, mul_vecMulVec,
    vecMulVec_mul, ← star_mulVec]
  ext m m'
  simp only [partialTraceRight_apply, Fintype.sum_prod_type, Matrix.sum_apply, Matrix.smul_apply,
    vecMulVec_apply, smul_eq_mul, Pi.star_apply, RCLike.star_def]
  rw [Finset.sum_comm]

/-- **The separated outputs trace to the exterior action on the weighted block combination.**
Tracing both discarded indices of the outer products of the separated outputs (ket coordinate
`q.1`, bra coordinate `q.2`) gives the exterior words applied to the weighted block combination
of the Gram matrix in the frames; an exact identity for arbitrary complex coefficients, the ket
and bra Schmidt spaces independent. Source: Theorem 5.2, `eq:compression-exterior-input`,
`04-compression.tex`, lines 445–481. -/
theorem partialTraceRight_separatedSchmidtOutput_eq_halfWeightedBlockCombination [Fintype Env']
    [Fintype I] [Fintype L] [Fintype T] [Fintype U] [DecidableEq T] [DecidableEq U]
    (K : Matrix (Phys × Env) (Config Y) ℂ)
    (x y : Phys) (v : Word X Y) (w : Word X' Y) (F : Matrix (Config X) (I × T) ℂ)
    (F' : Matrix (Config X') (L × U) ℂ) (tau : T → ℝ) (tau' : U → ℝ)
    (K' : Matrix (Phys' × Env') (Config W) ℂ) (v' : Word Z W) (w' : Word Z' W)
    (G : Matrix (Config Z) T ℂ) (G' : Matrix (Config Z') U ℂ) (z : I × L → ℂ) :
    partialTraceRight (∑ q, z q • vecMulVec
      (fun h : Phys' × (Env × Env') ↦
        separatedSchmidtOutput K x v F tau K' v' G q.1 (h.2.1, (h.1, h.2.2)))
      (fun h : Phys' × (Env × Env') ↦
        conj (separatedSchmidtOutput K y w F' tau' K' w' G' q.2 (h.2.1, (h.1, h.2.2))))) =
      partialTraceRight (K' * v'.op * G *
        halfWeightedBlockCombination tau tau' (physicalFrameGramMatrix K x y v w F F') z *
          (K' * w'.op * G')ᴴ) := by
  simp only [separatedSchmidtOutput_eq_mulVec]
  rw [partialTraceRight_sum_vecMulVec_mulVec (K' * v'.op * G) (K' * w'.op * G')
    (fun i ↦ schmidtPhysicalVector K x v F tau i) (fun l ↦ schmidtPhysicalVector K y w F' tau' l)
    z, ← sum_schmidtPhysicalVector_outer_eq_halfWeightedBlockCombination]
  rfl

/-- The joint coordinates of all affected physical components and the exterior output at the
corrected coordinate `i`, with both discarded indices kept separately. Source: Theorem 5.2,
`04-compression.tex`, lines 469–481 and 535–538. -/
def separatedPhysicalCoordinates [Fintype T] (K : Matrix (Phys × Env) (Config Y) ℂ)
    (v : Word X Y)
    (F : Matrix (Config X) (I × T) ℂ) (tau : T → ℝ) (K' : Matrix (Phys' × Env') (Config W) ℂ)
    (v' : Word Z W) (G : Matrix (Config Z) T ℂ) (i : I) : (Phys × Phys') × (Env × Env') → ℂ :=
  fun h ↦ separatedSchmidtOutput K h.1.1 v F tau K' v' G i (h.2.1, (h.1.2, h.2.2))

/-- The physical density formed from the separated ket and bra coordinates with complex
coefficients `z`, after tracing both discarded indices. Source: Theorem 5.2,
`04-compression.tex`, lines 469–481 and 535–538. -/
def separatedPhysicalDensity [Fintype Env'] [Fintype I] [Fintype L] [Fintype T] [Fintype U]
    (K : Matrix (Phys × Env) (Config Y) ℂ) (v : Word X Y)
    (w : Word X' Y) (F : Matrix (Config X) (I × T) ℂ) (F' : Matrix (Config X') (L × U) ℂ)
    (tau : T → ℝ) (tau' : U → ℝ) (K' : Matrix (Phys' × Env') (Config W) ℂ) (v' : Word Z W)
    (w' : Word Z' W) (G : Matrix (Config Z) T ℂ) (G' : Matrix (Config Z') U ℂ)
    (z : I × L → ℂ) : Matrix (Phys × Phys') (Phys × Phys') ℂ :=
  partialTraceRight (∑ q, z q • vecMulVec
    (separatedPhysicalCoordinates K v F tau K' v' G q.1)
    (fun h ↦ conj (separatedPhysicalCoordinates K w F' tau' K' w' G' q.2 h)))

/-- **The separated physical density at fixed affected physical indices** is the exterior
action on the weighted block combination of the Gram matrix in the frames, followed by the
partial trace. Source: Theorem 5.2, `eq:compression-exterior-input`, `04-compression.tex`,
lines 469–481 and 535–538. -/
theorem separatedPhysicalDensity_submatrix [Fintype Env'] [Fintype I] [Fintype L] [Fintype T]
    [Fintype U] [DecidableEq T] [DecidableEq U] (K : Matrix (Phys × Env) (Config Y) ℂ)
    (x y : Phys) (v : Word X Y) (w : Word X' Y) (F : Matrix (Config X) (I × T) ℂ)
    (F' : Matrix (Config X') (L × U) ℂ)
    (tau : T → ℝ) (tau' : U → ℝ) (K' : Matrix (Phys' × Env') (Config W) ℂ) (v' : Word Z W)
    (w' : Word Z' W) (G : Matrix (Config Z) T ℂ) (G' : Matrix (Config Z') U ℂ)
    (z : I × L → ℂ) :
    (separatedPhysicalDensity K v w F F' tau tau' K' v' w' G G' z).submatrix
        (fun i ↦ (x, i)) (fun j ↦ (y, j)) =
      partialTraceRight (K' * v'.op * G *
        halfWeightedBlockCombination tau tau' (physicalFrameGramMatrix K x y v w F F') z *
          (K' * w'.op * G')ᴴ) := by
  rw [separatedPhysicalDensity, submatrix_partialTraceRight,
    ← partialTraceRight_separatedSchmidtOutput_eq_halfWeightedBlockCombination]
  congr 1
  ext i j
  simp only [submatrix_apply, Matrix.sum_apply, Matrix.smul_apply, vecMulVec_apply,
    separatedPhysicalCoordinates]

/-- **The product readout of a Schmidt expansion through two words is the separated
coordinate.** If the joint output of the affected and exterior words is the Schmidt sum
`∑_t √τ_t (v F)(k, t) ⊗ (v' G) e_t`, its coordinates in the product readout `K ⊗ K'` are the
separated physical coordinates at `k`; no normalization or contraction is used. Source:
Theorem 5.2, `04-compression.tex`, lines 409–480. -/
theorem kronecker_mulVec_eq_separatedPhysicalCoordinates [Fintype T]
    (K : Matrix (Phys × Env) (Config Y) ℂ) (v : Word X Y) (F : Matrix (Config X) (I × T) ℂ)
    (tau : T → ℝ) (K' : Matrix (Phys' × Env') (Config W) ℂ) (v' : Word Z W)
    (G : Matrix (Config Z) T ℂ)
    (k : I) (x : Phys) (y : Phys') (e : Env) (e' : Env') :
    ((K ⊗ₖ K') *ᵥ fun c : Config Y × Config W ↦
        ∑ t, (Real.sqrt (tau t) : ℂ) * ((v.op * F) c.1 (k, t) * (v'.op * G) c.2 t))
        ((x, e), (y, e')) =
      separatedPhysicalCoordinates K v F tau K' v' G k ((x, y), (e, e')) := by
  have hA (t : T) :
      (physicalComponent K x v * F) e (k, t) = ∑ c, K (x, e) c * (v.op * F) c (k, t) := by
    rw [← Matrix.mul_apply (M := K), ← Matrix.mul_assoc]
    simp only [Matrix.mul_apply, physicalComponent_apply]
  have hB (t : T) : (K' * v'.op * G) (y, e') t = ∑ c, K' (y, e') c * (v'.op * G) c t := by
    rw [Matrix.mul_assoc, Matrix.mul_apply]
  simp only [separatedPhysicalCoordinates, separatedSchmidtOutput, hA, hB, mulVec, dotProduct,
    kroneckerMap_apply, Fintype.sum_prod_type, Finset.mul_sum, Finset.sum_mul]
  refine (Finset.sum_congr rfl fun c _ ↦ Finset.sum_comm).trans ?_
  refine Finset.sum_comm.trans (Finset.sum_congr rfl fun t _ ↦ ?_)
  refine Finset.sum_comm.trans (Finset.sum_congr rfl fun c' _ ↦ Finset.sum_congr rfl fun c _ ↦ ?_)
  ring

end QuantumCircuit.Party.Word
