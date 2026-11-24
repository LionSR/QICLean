/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Circuit.Party.Syntax.Word
import QICLean.Analysis.Norm.VectorPreparation
import QICLean.Analysis.TraceNorm.RectangularTraceNormContraction

/-!
# Physical components of the outputs of words

The output of a word is read through a *readout* `K : Matrix (Phys × Env) (Config Y) ℂ`, which
splits a configuration of the output system into a physical index and a discarded index; the norm
bounds take `‖K‖ ≤ 1`, the identities any `K`. The *physical component* of a word `v` at the
physical index `x` keeps the discarded index: it is the effect `⟨x| ⊗ 1` applied after `K * v.op`.
For two words `v`, `w` with the same output, the *Gram matrix* at the physical indices `x`, `y`
pairs the discarded vectors of `w` at `y` (bra side) with those of `v` at `x` (ket side); tracing
the discarded index of `K v.op ρ (K w.op)ᴴ` pairs an arbitrary rectangular `ρ` with these Gram
matrices. Two allowed words followed by the partial trace over the discarded index contract the
trace norm, with no factor depending on any dimension, also after isometric (or contractive) input
frames.

## Main definitions

* `QuantumCircuit.Party.Word.physicalComponent`, `QuantumCircuit.Party.Word.physicalGramMatrix`.

## Main results

* `QuantumCircuit.Party.Word.norm_physicalComponent_le_one`,
  `QuantumCircuit.Party.Word.norm_physicalGramMatrix_le_one`.
* `QuantumCircuit.Party.Word.partialTraceRight_mul_op_mul_conjTranspose_apply` — the partial
  trace pairs the input with the Gram matrices.
* `QuantumCircuit.Party.Word.rectangularTraceNorm_partialTraceRight_mul_op_le` and its form with
  input frames `_mul_op_mul_le` — the exterior contraction.

## References

* Polynomial-PEPS manuscript (September 24, 2026), Theorem 5.2, `04-compression.tex`,
  lines 419–478 and `eq:compression-exterior-contraction`, lines 445–462.
-/

noncomputable section

open Matrix ManyBody
open scoped Matrix.Norms.L2Operator

namespace QuantumCircuit.Party.Word

variable {P : Type} [Fintype P] [DecidableEq P] {X X' Y : P → Type}
  [∀ p, Fintype (X p)] [∀ p, DecidableEq (X p)] [∀ p, Fintype (X' p)] [∀ p, DecidableEq (X' p)]
  [∀ p, Fintype (Y p)] [∀ p, DecidableEq (Y p)]
  {Phys Env : Type} [Fintype Phys] [DecidableEq Phys] [Fintype Env] [DecidableEq Env]

/-! ### Physical components and Gram matrices -/

/-- The physical component of the output of the word `v` at the physical index `x`, with its
discarded index kept: the effect `⟨x| ⊗ 1` applied after the readout `K` of the output.
Source: Theorem 5.2, `04-compression.tex`, lines 419–435. -/
def physicalComponent (K : Matrix (Phys × Env) (Config Y) ℂ) (x : Phys) (v : Word X Y) :
    Matrix Env (Config X) ℂ :=
  effectMatrix (EuclideanSpace.single x 1) Env * (K * v.op)

omit [∀ p, DecidableEq (Y p)] in
/-- The entries of a physical component are the rows `(x, e)` of the read output. -/
theorem physicalComponent_apply (K : Matrix (Phys × Env) (Config Y) ℂ) (x : Phys)
    (v : Word X Y) (e : Env) (c : Config X) :
    physicalComponent K x v e c = (K * v.op) (x, e) c := by
  simp only [physicalComponent, mul_apply (M := effectMatrix _ Env), effectMatrix_apply,
    PiLp.single_apply, Fintype.sum_prod_type]
  rw [Finset.sum_eq_single x (fun x' _ hx' ↦ by simp [hx']) (by simp)]
  simp

/-- A physical component of an allowed word read through a contraction is a contraction.
Source: Theorem 5.2, `04-compression.tex`, lines 419–435. -/
theorem norm_physicalComponent_le_one (K : Matrix (Phys × Env) (Config Y) ℂ) (x : Phys)
    (v : Word X Y) (hK : ‖K‖ ≤ 1) (hv : v.IsAllowed) : ‖physicalComponent K x v‖ ≤ 1 := by
  have he : ‖effectMatrix (EuclideanSpace.single x (1 : ℂ)) Env‖ ≤ 1 :=
    norm_effectMatrix_le (by simp)
  have hv' := PartyCircuit.norm_op_le_one (G := SourceGate (P := P)) SourceGate.ev hv
  exact l2_opNorm_mul_le_one _ _ he (l2_opNorm_mul_le_one _ _ hK hv')

/-- The Gram matrix of two words with the same output at the physical indices `x` (ket side,
the word `v`) and `y` (bra side, the word `w`): the bra component's adjoint times the ket
component. Source: Theorem 5.2, `eq:compression-block-contraction`,
`04-compression.tex`, lines 436–443. -/
def physicalGramMatrix (K : Matrix (Phys × Env) (Config Y) ℂ) (x y : Phys) (v : Word X Y)
    (w : Word X' Y) : Matrix (Config X') (Config X) ℂ :=
  (physicalComponent K y w)ᴴ * physicalComponent K x v

omit [∀ p, DecidableEq (Y p)] in
/-- An entry of the Gram matrix is the inner product of the discarded vectors of the two
components: the bra column `j` of `w` at `y` against the ket column `i` of `v` at `x`.
Source: Theorem 5.2, `04-compression.tex`, lines 436–443 and 476–478. -/
theorem physicalGramMatrix_apply (K : Matrix (Phys × Env) (Config Y) ℂ) (x y : Phys)
    (v : Word X Y) (w : Word X' Y) (j : Config X') (i : Config X) :
    physicalGramMatrix K x y v w j i = ∑ e, star ((K * w.op) (y, e) j) * (K * v.op) (x, e) i := by
  simp only [physicalGramMatrix, mul_apply (M := (physicalComponent K y w)ᴴ),
    conjTranspose_apply, physicalComponent_apply]

/-- The Gram matrix of two allowed words read through a contraction is a contraction, whatever
the discarded dimension. Source: Theorem 5.2,
`eq:compression-block-contraction`, `04-compression.tex`, lines 436–442. -/
theorem norm_physicalGramMatrix_le_one (K : Matrix (Phys × Env) (Config Y) ℂ) (x y : Phys)
    (v : Word X Y) (w : Word X' Y) (hK : ‖K‖ ≤ 1) (hv : v.IsAllowed) (hw : w.IsAllowed) :
    ‖physicalGramMatrix K x y v w‖ ≤ 1 := by
  exact l2_opNorm_mul_le_one _ _
    ((l2_opNorm_conjTranspose _).trans_le (norm_physicalComponent_le_one K y w hK hw))
    (norm_physicalComponent_le_one K x v hK hv)

/-! ### The partial trace over the discarded index -/

omit [∀ p, DecidableEq (Y p)] in
/-- Tracing the discarded index of the read outputs of `v` (ket side) and `w` (bra side) around
an arbitrary rectangular `ρ` pairs `ρ` with the opposite-index Gram entry; no positivity or
Hermiticity is assumed. Source: Theorem 5.2, `04-compression.tex`, lines 469–478. -/
theorem partialTraceRight_mul_op_mul_conjTranspose_apply (K : Matrix (Phys × Env) (Config Y) ℂ)
    (x y : Phys) (v : Word X Y) (w : Word X' Y) (ρ : Matrix (Config X) (Config X') ℂ) :
    partialTraceRight (K * v.op * ρ * (K * w.op)ᴴ) x y =
      ∑ i, ∑ j, ρ i j * physicalGramMatrix K x y v w j i := by
  simp only [partialTraceRight_apply, mul_apply (M := K * v.op * ρ), mul_apply (M := K * v.op),
    conjTranspose_apply, physicalGramMatrix_apply, Finset.mul_sum, Finset.sum_mul]
  conv_lhs => rw [Finset.sum_comm]
  refine (Finset.sum_congr rfl fun j _ ↦ Finset.sum_comm).trans ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦
    Finset.sum_congr rfl fun e _ ↦ ?_
  ring

omit [DecidableEq Phys] [DecidableEq Env] in
/-- A word read through a contraction and fed through a contractive input frame `F` is a
contraction. Source: Theorem 5.2, `04-compression.tex`, lines 445–451. -/
theorem norm_mul_op_mul_le_one {n : Type} [Fintype n] [DecidableEq n]
    (K : Matrix (Phys × Env) (Config Y) ℂ) (v : Word X Y) (F : Matrix (Config X) n ℂ)
    (hK : ‖K‖ ≤ 1) (hv : v.IsAllowed) (hF : ‖F‖ ≤ 1) : ‖K * v.op * F‖ ≤ 1 := by
  have hv' := PartyCircuit.norm_op_le_one (G := SourceGate (P := P)) SourceGate.ev hv
  exact l2_opNorm_mul_le_one _ _ (l2_opNorm_mul_le_one _ _ hK hv') hF

omit [DecidableEq Env] in
/-- **The exterior contraction.** Two allowed words with the same output, read through a
contraction and followed by the partial trace over the discarded index, contract the trace norm
of an arbitrary rectangular input; the two words need not coincide, and no factor depends on an
input or discarded dimension. Source: Theorem 5.2, `eq:compression-exterior-contraction`,
`04-compression.tex`, lines 445–462. -/
theorem rectangularTraceNorm_partialTraceRight_mul_op_le (K : Matrix (Phys × Env) (Config Y) ℂ)
    (v : Word X Y) (w : Word X' Y) (hK : ‖K‖ ≤ 1) (hv : v.IsAllowed) (hw : w.IsAllowed)
    (Z : Matrix (Config X) (Config X') ℂ) :
    rectangularTraceNorm (partialTraceRight (K * v.op * Z * (K * w.op)ᴴ)) ≤
      rectangularTraceNorm Z := by
  have h1 {W : P → Type} [∀ p, Fintype (W p)] [∀ p, DecidableEq (W p)] :
      ‖(1 : Matrix (Config W) (Config W) ℂ)‖ ≤ 1 :=
    (IsStarProjection.one (Matrix (Config W) (Config W) ℂ)).norm_le
  simpa only [Matrix.mul_one] using
    rectangularTraceNorm_partialTraceRight_mul_conjTranspose_le Z _ _
      (norm_mul_op_mul_le_one K v 1 hK hv h1) (norm_mul_op_mul_le_one K w 1 hK hw h1)

omit [DecidableEq Env] in
/-- The exterior contraction on contractive input frames `F`, `F'` of different dimensions (for
instance isometric Schmidt frames that need not span the inputs). Source: Theorem 5.2,
`eq:compression-exterior-contraction`, `04-compression.tex`, lines 445–462. -/
theorem rectangularTraceNorm_partialTraceRight_mul_op_mul_le {n n' : Type} [Fintype n]
    [Fintype n'] [DecidableEq n] [DecidableEq n'] (K : Matrix (Phys × Env) (Config Y) ℂ)
    (v : Word X Y) (w : Word X' Y)
    (F : Matrix (Config X) n ℂ) (F' : Matrix (Config X') n' ℂ) (hK : ‖K‖ ≤ 1)
    (hv : v.IsAllowed) (hw : w.IsAllowed) (hF : ‖F‖ ≤ 1) (hF' : ‖F'‖ ≤ 1) (Z : Matrix n n' ℂ) :
    rectangularTraceNorm (partialTraceRight (K * v.op * F * Z * (K * w.op * F')ᴴ)) ≤
      rectangularTraceNorm Z :=
  rectangularTraceNorm_partialTraceRight_mul_conjTranspose_le Z _ _
    (norm_mul_op_mul_le_one K v F hK hv hF) (norm_mul_op_mul_le_one K w F' hK hw hF')

end QuantumCircuit.Party.Word
