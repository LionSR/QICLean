/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Entropy.VonNeumann.Entropy
import QICLean.Analysis.Isometry.IsometricCompression
import QICLean.Entropy.Renyi.SandwichedRenyiTwo
import QICLean.Analysis.Support.Compression
import QICLean.Channel.PartialTrace.MarginalSupportAbsorption
import QICLean.Analysis.FunctionalCalculus.MatrixSqrt
import QICLean.Channel.Schwarz.WhitenedChoi

/-!
# Entropy functionals compressed to the reference support

Let $\rho,\omega\geq0$ and assume $\ker\omega\subseteq\ker\rho$.
If the columns of $V$ form an orthonormal basis of the support of $\omega$,
then both matrices are isometric expansions of their compressions by $V$.
The totalized logarithm and negative real powers vanish at zero, so the
nonunital functional calculus shows that quantum relative entropy and the
order-two sandwiched trace functional are unchanged by this compression.

## Main declarations

* `Matrix.PosSemidef.eq_expansion_compression_of_kernel_le_of_mul_conjTranspose_eq_supportProj`
  — support inclusion reconstructs a matrix from its support compression.
* `TNLean.quantumRelativeEntropy_support_compression` — relative entropy is
  invariant under compression to the reference support.
* `TNLean.sandwichedRenyiTwoTrace_support_compression` — the order-two
  sandwiched trace functional is invariant under the same compression.
* `TNLean.quantumRelativeEntropy_le_log_sandwichedRenyiTwoTrace_of_faithful` —
  a faithful-reference density-operator inequality implies the
  support-restricted density-operator inequality.
* `TNLean.quantumRelativeEntropy_le_log_sandwichedRenyiTwoTrace` — the
  logarithmic comparison for a possibly singular reference under support
  inclusion.

The faithful comparison is proved directly in `TNLean.Analysis.SandwichedRenyiTwo`.
The final theorem applies the compression result to extend it to singular
references.
* `TNLean.sandwichedRenyiTwoTrace_product_marginals_le_operatorSchmidtRank_of_marginals_posDef`,
  `TNLean.sandwichedRenyiTwoTrace_product_marginals_le_operatorSchmidtRank`: marginal-support
  whitening.
-/

section SupportCompressedEntropy

open scoped Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator
open Matrix

namespace Matrix

variable {D k : ℕ}

/-- If $\ker\omega\subseteq\ker\rho$, a rectangular matrix whose product with
its adjoint is the support projection of $\omega$ reconstructs $\rho$ exactly
from the corresponding compression and expansion. -/
theorem PosSemidef.eq_expansion_compression_of_kernel_le_of_mul_conjTranspose_eq_supportProj
    {n m : Type*} [Fintype n] [DecidableEq n] [Fintype m]
    {ρ ω : Matrix n n ℂ} (hρ : ρ.PosSemidef) (hω : ω.PosSemidef)
    (hker : ∀ v : n → ℂ, ω *ᵥ v = 0 → ρ *ᵥ v = 0)
    (V : Matrix n m ℂ)
    (hRange : V * Vᴴ = hω.supportProj) :
    V * (Vᴴ * ρ * V) * Vᴴ = ρ := by
  have hright : ρ * hω.supportProj = ρ :=
    hω.isHermitian.mul_supportProj_eq_self_of_mulVec_kernel_le hker
  have hleft : hω.supportProj * ρ = ρ := by
    have hadj := congrArg Matrix.conjTranspose hright
    simpa only [Matrix.conjTranspose_mul, hω.supportProj_isHermitian.eq,
      hρ.isHermitian.eq] using hadj
  calc
    V * (Vᴴ * ρ * V) * Vᴴ = (V * Vᴴ) * ρ * (V * Vᴴ) := by
      simp only [Matrix.mul_assoc]
    _ = hω.supportProj * ρ * hω.supportProj := by rw [hRange]
    _ = ρ := by rw [hleft, hright]

end Matrix

namespace TNLean

noncomputable section

variable {D k : ℕ}

private theorem support_compression_log
    {A : Matrix (Fin D) (Fin D) ℂ} (hA : A.PosSemidef)
    (V : Matrix (Fin D) (Fin k) ℂ) (hV : Vᴴ * V = 1)
    (hexpand : V * (Vᴴ * A * V) * Vᴴ = A) :
    CFC.log A = V * CFC.log (Vᴴ * A * V) * Vᴴ := by
  let Ac := Vᴴ * A * V
  have hAc : Ac.PosSemidef := by
    simpa only [Ac, Matrix.conjTranspose_conjTranspose] using
      hA.mul_mul_conjTranspose_same Vᴴ
  calc
    CFC.log A = CFC.log (V * Ac * Vᴴ) := congrArg CFC.log hexpand.symm
    _ = V * CFC.log Ac * Vᴴ := by
      rw [CFC.log, CFC.log]
      exact Matrix.cfc_conj_isometry_of_zero hAc.isHermitian
        Real.log Real.log_zero V hV

private theorem support_compression_rpow
    {n m : Type*} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]
    {A : Matrix n n ℂ} (hA : A.PosSemidef)
    (s : ℝ) (hs : s ≠ 0) (V : Matrix n m ℂ)
    (hV : Vᴴ * V = 1) (hexpand : V * (Vᴴ * A * V) * Vᴴ = A) :
    A ^ s = V * (Vᴴ * A * V) ^ s * Vᴴ := by
  have hAc : (Vᴴ * A * V).PosSemidef := by
    simpa only [Matrix.conjTranspose_conjTranspose] using
      hA.mul_mul_conjTranspose_same Vᴴ
  calc
    A ^ s = (V * (Vᴴ * A * V) * Vᴴ) ^ s := congrArg (fun X => X ^ s) hexpand.symm
    _ = cfc (fun x : ℝ => x ^ s) (V * (Vᴴ * A * V) * Vᴴ) := by
      rw [CFC.rpow_eq_cfc_real]
    _ = V * cfc (fun x : ℝ => x ^ s) (Vᴴ * A * V) * Vᴴ :=
      Matrix.cfc_conj_isometry_of_zero hAc.isHermitian
        (fun x : ℝ => x ^ s) (Real.zero_rpow hs) V hV
    _ = V * (Vᴴ * A * V) ^ s * Vᴴ := by
      rw [CFC.rpow_eq_cfc_real hAc.nonneg]

/-- Quantum relative entropy is unchanged by compression to the support of its
positive-semidefinite reference.  The kernel inclusion is exactly the finite
relative-entropy support condition; no faithfulness assumption is made on the
ambient reference. -/
theorem quantumRelativeEntropy_support_compression
    {ρ ω : Matrix (Fin D) (Fin D) ℂ} (hρ : ρ.PosSemidef) (hω : ω.PosSemidef)
    (hker : ∀ v : Fin D → ℂ, ω *ᵥ v = 0 → ρ *ᵥ v = 0)
    (V : Matrix (Fin D) (Fin k) ℂ) (hV : Vᴴ * V = 1)
    (hRange : V * Vᴴ = hω.supportProj) :
    quantumRelativeEntropy ρ ω =
      quantumRelativeEntropy (Vᴴ * ρ * V) (Vᴴ * ω * V) := by
  let ρc := Vᴴ * ρ * V
  let ωc := Vᴴ * ω * V
  have hρexpand : V * ρc * Vᴴ = ρ := by
    simpa only [ρc] using
      hρ.eq_expansion_compression_of_kernel_le_of_mul_conjTranspose_eq_supportProj
        hω hker V hRange
  have hωexpand : V * ωc * Vᴴ = ω := by
    simpa only [ωc] using
      hω.eq_expansion_compression_of_kernel_le_of_mul_conjTranspose_eq_supportProj hω
        (fun _ hv => hv) V hRange
  have hlogρ : CFC.log ρ = V * CFC.log ρc * Vᴴ :=
    support_compression_log hρ V hV hρexpand
  have hlogω : CFC.log ω = V * CFC.log ωc * Vᴴ :=
    support_compression_log hω V hV hωexpand
  change quantumRelativeEntropy ρ ω = quantumRelativeEntropy ρc ωc
  rw [quantumRelativeEntropy, quantumRelativeEntropy]
  rw [hlogρ, hlogω, ← hρexpand]
  have hmatrix :
      (V * ρc * Vᴴ) *
          (V * CFC.log ρc * Vᴴ - V * CFC.log ωc * Vᴴ) =
        V * (ρc * (CFC.log ρc - CFC.log ωc)) * Vᴴ := by
    let φ := Matrix.isometryConjNonUnitalStarAlgHom V hV
    change φ ρc * (φ (CFC.log ρc) - φ (CFC.log ωc)) =
      φ (ρc * (CFC.log ρc - CFC.log ωc))
    rw [← map_sub, ← map_mul]
  rw [hmatrix, Matrix.trace_mul_mul_conjTranspose_of_conjTranspose_mul_eq_one V hV]

/-- The order-two sandwiched trace functional is unchanged by compression to
the support of its positive-semidefinite reference under the support inclusion
$\ker\omega\subseteq\ker\rho$.  Negative quarter-powers use the zero-on-kernel
convention on both sides. -/
theorem sandwichedRenyiTwoTrace_support_compression
    {n m : Type*} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]
    {ρ ω : Matrix n n ℂ} (hρ : ρ.PosSemidef) (hω : ω.PosSemidef)
    (hker : ∀ v : n → ℂ, ω *ᵥ v = 0 → ρ *ᵥ v = 0)
    (V : Matrix n m ℂ) (hV : Vᴴ * V = 1)
    (hRange : V * Vᴴ = hω.supportProj) :
    sandwichedRenyiTwoTrace ρ ω =
      sandwichedRenyiTwoTrace (Vᴴ * ρ * V) (Vᴴ * ω * V) := by
  let ρc := Vᴴ * ρ * V
  let ωc := Vᴴ * ω * V
  have hρexpand : V * ρc * Vᴴ = ρ := by
    simpa only [ρc] using
      hρ.eq_expansion_compression_of_kernel_le_of_mul_conjTranspose_eq_supportProj
        hω hker V hRange
  have hωexpand : V * ωc * Vᴴ = ω := by
    simpa only [ωc] using
      hω.eq_expansion_compression_of_kernel_le_of_mul_conjTranspose_eq_supportProj hω
        (fun _ hv => hv) V hRange
  have hq : ω ^ (-(1 / 4 : ℝ)) = V * ωc ^ (-(1 / 4 : ℝ)) * Vᴴ :=
    support_compression_rpow hω (-(1 / 4 : ℝ)) (by norm_num) V hV hωexpand
  change sandwichedRenyiTwoTrace ρ ω = sandwichedRenyiTwoTrace ρc ωc
  rw [sandwichedRenyiTwoTrace, sandwichedRenyiTwoTrace]
  change (Matrix.trace
      ((ω ^ (-(1 / 4 : ℝ)) * ρ * ω ^ (-(1 / 4 : ℝ))) *
        (ω ^ (-(1 / 4 : ℝ)) * ρ * ω ^ (-(1 / 4 : ℝ))))).re =
    (Matrix.trace
      ((ωc ^ (-(1 / 4 : ℝ)) * ρc * ωc ^ (-(1 / 4 : ℝ))) *
        (ωc ^ (-(1 / 4 : ℝ)) * ρc * ωc ^ (-(1 / 4 : ℝ))))).re
  rw [← hρexpand, hq]
  let q := ωc ^ (-(1 / 4 : ℝ))
  let φ := Matrix.isometryConjNonUnitalStarAlgHom V hV
  have hsandwich :
      (V * q * Vᴴ) * (V * ρc * Vᴴ) * (V * q * Vᴴ) =
        V * (q * ρc * q) * Vᴴ := by
    change φ q * φ ρc * φ q = φ (q * ρc * q)
    rw [← map_mul, ← map_mul]
  rw [hsandwich]
  have hsquare :
      (V * (q * ρc * q) * Vᴴ) * (V * (q * ρc * q) * Vᴴ) =
        V * ((q * ρc * q) * (q * ρc * q)) * Vᴴ := by
    change φ (q * ρc * q) * φ (q * ρc * q) =
      φ ((q * ρc * q) * (q * ρc * q))
    rw [← map_mul]
  rw [hsquare, Matrix.trace_mul_mul_conjTranspose_of_conjTranspose_mul_eq_one V hV]

/-- A faithful-reference density-operator proof of
$D(\rho\Vert\omega)\leq\log Q_2(\rho,\omega)$ reduces the support-restricted
case to the support compression.  Both ambient matrices have trace one, and
isometric trace preservation supplies the corresponding normalizations for
the compressed matrices.  The faithful inequality is an explicit hypothesis
and is not proved here. -/
theorem quantumRelativeEntropy_le_log_sandwichedRenyiTwoTrace_of_faithful
    {ρ ω : Matrix (Fin D) (Fin D) ℂ} (hρ : ρ.PosSemidef) (hω : ω.PosSemidef)
    (hρtr : ρ.trace = 1) (hωtr : ω.trace = 1)
    (hker : ∀ v : Fin D → ℂ, ω *ᵥ v = 0 → ρ *ᵥ v = 0)
    (hfaithful : ∀ {d : ℕ} (A B : Matrix (Fin d) (Fin d) ℂ),
      A.PosSemidef → B.PosDef → A.trace = 1 → B.trace = 1 →
        quantumRelativeEntropy A B ≤ Real.log (sandwichedRenyiTwoTrace A B)) :
    quantumRelativeEntropy ρ ω ≤ Real.log (sandwichedRenyiTwoTrace ρ ω) := by
  obtain ⟨k, V, hV, hRange⟩ := hω.isOrthogonalProjection_supportProj.exists_range_isometry
  let ρc := Vᴴ * ρ * V
  let ωc := Vᴴ * ω * V
  have hρc : ρc.PosSemidef := by
    simpa only [ρc, Matrix.conjTranspose_conjTranspose] using
      hρ.mul_mul_conjTranspose_same Vᴴ
  have hωc : ωc.PosDef := by
    simpa only [ωc, Matrix.conjTranspose_conjTranspose] using
      hω.compression_on_support_posDef (V := Vᴴ) (by
        simpa only [Matrix.conjTranspose_conjTranspose] using hV) (by
        simpa only [Matrix.conjTranspose_conjTranspose] using hRange)
  have hρexpand : V * ρc * Vᴴ = ρ := by
    simpa only [ρc] using
      hρ.eq_expansion_compression_of_kernel_le_of_mul_conjTranspose_eq_supportProj
        hω hker V hRange
  have hωexpand : V * ωc * Vᴴ = ω := by
    simpa only [ωc] using
      hω.eq_expansion_compression_of_kernel_le_of_mul_conjTranspose_eq_supportProj hω
        (fun _ hv => hv) V hRange
  have hρctr : ρc.trace = 1 := by
    calc
      ρc.trace = (V * ρc * Vᴴ).trace :=
        (Matrix.trace_mul_mul_conjTranspose_of_conjTranspose_mul_eq_one V hV ρc).symm
      _ = ρ.trace := congrArg Matrix.trace hρexpand
      _ = 1 := hρtr
  have hωctr : ωc.trace = 1 := by
    calc
      ωc.trace = (V * ωc * Vᴴ).trace :=
        (Matrix.trace_mul_mul_conjTranspose_of_conjTranspose_mul_eq_one V hV ωc).symm
      _ = ω.trace := congrArg Matrix.trace hωexpand
      _ = 1 := hωtr
  have hcompressed := hfaithful ρc ωc hρc hωc hρctr hωctr
  calc
    quantumRelativeEntropy ρ ω = quantumRelativeEntropy ρc ωc :=
      quantumRelativeEntropy_support_compression hρ hω hker V hV hRange
    _ ≤ Real.log (sandwichedRenyiTwoTrace ρc ωc) := hcompressed
    _ = Real.log (sandwichedRenyiTwoTrace ρ ω) := congrArg Real.log
      (sandwichedRenyiTwoTrace_support_compression hρ hω hker V hV hRange).symm

/-- The support-restricted order-two sandwiched comparison.

For density matrices \(\rho,\omega\) with
\(\ker\omega\subseteq\ker\rho\), Umegaki relative entropy is bounded by the
logarithm of the order-two sandwiched trace. The proof compresses to the
support of \(\omega\), where the reference is positive definite, and applies
`quantumRelativeEntropy_le_log_sandwichedRenyiTwoTrace_posDef`. -/
theorem quantumRelativeEntropy_le_log_sandwichedRenyiTwoTrace
    {ρ ω : Matrix (Fin D) (Fin D) ℂ} (hρ : ρ.PosSemidef) (hω : ω.PosSemidef)
    (hρtr : ρ.trace = 1) (hωtr : ω.trace = 1)
    (hker : ∀ v : Fin D → ℂ, ω *ᵥ v = 0 → ρ *ᵥ v = 0) :
    quantumRelativeEntropy ρ ω ≤ Real.log (sandwichedRenyiTwoTrace ρ ω) := by
  exact quantumRelativeEntropy_le_log_sandwichedRenyiTwoTrace_of_faithful
    hρ hω hρtr hωtr hker
    (fun A B hA hB hAtr _hBtr =>
      quantumRelativeEntropy_le_log_sandwichedRenyiTwoTrace_posDef hA hB hAtr)

end

end TNLean

end SupportCompressedEntropy

section MarginalSupportWhitenedChoi

/-!
## Marginal-support whitening

A positive-semidefinite bipartite operator is compressed simultaneously to the
supports of its two marginals.  The compressed marginals are faithful, while
the order-two sandwiched trace and ordinary operator-Schmidt rank are unchanged.
The support coordinate spaces may both be zero-dimensional.

### Main declaration

* `TNLean.sandwichedRenyiTwoTrace_product_marginals_le_operatorSchmidtRank`
  is the arbitrary-support whitened Choi estimate.
-/

section FaithfulMarginalWhitenedChoi

/-!
# Faithful marginal whitening in arbitrary coordinates

This file removes the eigenbasis restriction from the faithful-marginal
whitened Choi estimate.  The first marginal is diagonalized explicitly.  The
input transpose forced by the Choi convention therefore disappears only after
that basis change.

## Main declaration

* `TNLean.sandwichedRenyiTwoTrace_product_marginals_le_operatorSchmidtRank_of_marginals_posDef`
  bounds the order-two sandwiched trace by ordinary operator-Schmidt rank when
  both marginals are positive definite.
-/

open scoped Matrix ComplexOrder MatrixOrder Kronecker
open Matrix

noncomputable section

namespace TNLean

variable {α β : Type*} [Fintype α] [DecidableEq α]
  [Fintype β] [DecidableEq β]

/-- For a positive-semidefinite bipartite operator with faithful marginals,
the order-two sandwiched trace against the product of the two marginals is at
most its operator-Schmidt rank.

The first marginal is conjugated by the adjoint of its eigenvector unitary.
Under the Choi convention the input whitening carries a transpose; it becomes
the ordinary diagonal whitening only in this eigenbasis. -/
theorem sandwichedRenyiTwoTrace_product_marginals_le_operatorSchmidtRank_of_marginals_posDef
    (ρ : Matrix (α × β) (α × β) ℂ)
    (hρ : ρ.PosSemidef) (hA : (partialTraceRight ρ).PosDef)
    (hB : (partialTraceLeft ρ).PosDef) :
    sandwichedRenyiTwoTrace ρ
        (partialTraceRight ρ ⊗ₖ partialTraceLeft ρ) ≤
      Matrix.operatorSchmidtRank ρ := by
  let U : unitary (Matrix α α ℂ) :=
    hA.isHermitian.eigenvectorUnitary
  let Kmat : Matrix (α × β) (α × β) ℂ :=
    star (U : Matrix α α ℂ) ⊗ₖ (1 : Matrix β β ℂ)
  have hKmat : Kmat ∈ unitary
      (Matrix (α × β) (α × β) ℂ) := by
    exact Matrix.kronecker_mem_unitary (star U).prop (by simp)
  let K : unitary (Matrix (α × β) (α × β) ℂ) := ⟨Kmat, hKmat⟩
  let ρ' : Matrix (α × β) (α × β) ℂ :=
    Kmat * ρ * Kmatᴴ
  let p : α → ℝ := hA.isHermitian.eigenvalues
  have hρ' : ρ'.PosSemidef := by
    exact hρ.mul_mul_conjTranspose_same Kmat
  have hp : ∀ i, 0 < p i := fun i ↦ hA.eigenvalues_pos i
  have hKA : star (U : Matrix α α ℂ)ᴴ *
      star (U : Matrix α α ℂ) = 1 := by
    rw [star_eq_conjTranspose, Matrix.conjTranspose_conjTranspose]
    exact Unitary.mul_star_self_of_mem U.prop
  have hstarU : (star (U : Matrix α α ℂ))ᴴ =
      (U : Matrix α α ℂ) := by
    rw [star_eq_conjTranspose, Matrix.conjTranspose_conjTranspose]
  have hKB : (1 : Matrix β β ℂ)ᴴ * 1 = 1 := by simp
  have hA' : partialTraceRight ρ' = diagonal fun i ↦ (p i : ℂ) := by
    dsimp only [ρ', Kmat]
    have h := partialTraceRight_kronecker_conj_of_right_isometry
      (star (U : Matrix α α ℂ))
      (1 : Matrix β β ℂ) hKB ρ
    rw [h, hstarU]
    simpa [U, p, Function.comp_def, Unitary.conjStarAlgAut_star_apply] using
      hA.isHermitian.conjStarAlgAut_star_eigenvectorUnitary
  have hB' : partialTraceLeft ρ' = partialTraceLeft ρ := by
    dsimp only [ρ', Kmat]
    have h := partialTraceLeft_kronecker_conj_of_left_isometry
      (star (U : Matrix α α ℂ))
      (1 : Matrix β β ℂ) hKA ρ
    simpa using h
  have hbound := supportedMarginalWhitenedState_trace_sq_re_le_operatorSchmidtRank
    ρ' p hρ' hp hA' (hB' ▸ hB)
  have hdiagPD : (diagonal fun i ↦ (p i : ℂ)).PosDef := by
    rw [posDef_diagonal_iff]
    intro i
    exact_mod_cast hp i
  have hqA :
      (diagonal fun i ↦ (p i : ℂ)) ^ (-(1 / 4 : ℝ)) =
        (diagonalMarginalQuarter p)⁻¹ := by
    rw [hdiagPD.rpow_neg_quarter_eq_inv_sqrt_sqrt,
      sqrt_sqrt_diagonal_eq_diagonalMarginalQuarter p hp]
  have hqB :
      (partialTraceLeft ρ') ^ (-(1 / 4 : ℝ)) =
        (CFC.sqrt (CFC.sqrt (partialTraceLeft ρ')))⁻¹ :=
    (hB' ▸ hB).rpow_neg_quarter_eq_inv_sqrt_sqrt
  have href :
      partialTraceRight ρ' ⊗ₖ partialTraceLeft ρ' =
        (diagonal fun i ↦ (p i : ℂ)) ⊗ₖ partialTraceLeft ρ' := by rw [hA']
  have hq :
      (partialTraceRight ρ' ⊗ₖ partialTraceLeft ρ') ^ (-(1 / 4 : ℝ)) =
        (diagonalMarginalQuarter p)⁻¹ ⊗ₖ
          (CFC.sqrt (CFC.sqrt (partialTraceLeft ρ')))⁻¹ := by
    rw [href, hdiagPD.posSemidef.rpow_kronecker
      (hB' ▸ hB).posSemidef, hqA, hqB]
  let W := (diagonalMarginalQuarter p)⁻¹ ⊗ₖ
    (CFC.sqrt (CFC.sqrt (partialTraceLeft ρ')))⁻¹
  have hW : Wᴴ = W := by
    dsimp only [W]
    rw [← hq]
    exact (Matrix.nonneg_iff_posSemidef.mp CFC.rpow_nonneg).isHermitian.eq
  have hidentify :
      sandwichedRenyiTwoTrace ρ'
          (partialTraceRight ρ' ⊗ₖ partialTraceLeft ρ') =
        (trace (supportedMarginalWhitenedState ρ' p (partialTraceLeft ρ') *
          supportedMarginalWhitenedState ρ' p (partialTraceLeft ρ'))).re := by
    rw [sandwichedRenyiTwoTrace]
    unfold supportedMarginalWhitenedState singleKrausMap
    change (trace
      ((((partialTraceRight ρ' ⊗ₖ partialTraceLeft ρ') ^ (-(1 / 4 : ℝ))) * ρ' *
          ((partialTraceRight ρ' ⊗ₖ partialTraceLeft ρ') ^ (-(1 / 4 : ℝ)))) *
        (((partialTraceRight ρ' ⊗ₖ partialTraceLeft ρ') ^ (-(1 / 4 : ℝ))) * ρ' *
          ((partialTraceRight ρ' ⊗ₖ partialTraceLeft ρ') ^ (-(1 / 4 : ℝ)))))).re =
      (trace ((W * ρ' * Wᴴ) * (W * ρ' * Wᴴ))).re
    rw [hq, hW]
  have hOSR : Matrix.operatorSchmidtRank ρ' = Matrix.operatorSchmidtRank ρ := by
    simpa only [ρ', Kmat] using Matrix.operatorSchmidtRank_local_isometry_conj
      (star (U : Matrix α α ℂ))
      (1 : Matrix β β ℂ) hKA hKB ρ
  have hrefConj :
      Kmat * (partialTraceRight ρ ⊗ₖ partialTraceLeft ρ) * Kmatᴴ =
        partialTraceRight ρ' ⊗ₖ partialTraceLeft ρ' := by
    rw [hA', hB']
    dsimp only [Kmat]
    rw [Matrix.conjTranspose_kronecker,
      ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul]
    simp only [Matrix.conjTranspose_one, Matrix.mul_one, Matrix.one_mul]
    rw [hstarU]
    congr 1
    simpa [U, p, Function.comp_def, Unitary.conjStarAlgAut_star_apply] using
      hA.isHermitian.conjStarAlgAut_star_eigenvectorUnitary
  have hQ2 :
      sandwichedRenyiTwoTrace ρ'
          (partialTraceRight ρ' ⊗ₖ partialTraceLeft ρ') =
        sandwichedRenyiTwoTrace ρ
          (partialTraceRight ρ ⊗ₖ partialTraceLeft ρ) := by
    rw [← hrefConj]
    simpa only [ρ', K, star_eq_conjTranspose] using
      sandwichedRenyiTwoTrace_conj_unitary
        (hA.posSemidef.kronecker hB.posSemidef) K
  calc
    sandwichedRenyiTwoTrace ρ
        (partialTraceRight ρ ⊗ₖ partialTraceLeft ρ) =
      sandwichedRenyiTwoTrace ρ'
        (partialTraceRight ρ' ⊗ₖ partialTraceLeft ρ') := hQ2.symm
    _ = (trace (supportedMarginalWhitenedState ρ' p (partialTraceLeft ρ') *
          supportedMarginalWhitenedState ρ' p (partialTraceLeft ρ'))).re := hidentify
    _ ≤ Matrix.operatorSchmidtRank ρ' := hbound
    _ = Matrix.operatorSchmidtRank ρ := by exact_mod_cast hOSR

end TNLean
end

end FaithfulMarginalWhitenedChoi

open scoped Matrix ComplexOrder MatrixOrder Kronecker
open Matrix

noncomputable section

namespace TNLean

variable {dA dB : ℕ}

/-- For every positive-semidefinite bipartite operator, the order-two
sandwiched trace against the product of its marginals is at most its ordinary
operator-Schmidt rank.

No normalization or positive-dimension assumption is needed.  Simultaneous
compression to the two marginal supports includes the cases where either
support coordinate space is `Fin 0`. -/
theorem sandwichedRenyiTwoTrace_product_marginals_le_operatorSchmidtRank
    (ρ : Matrix (Fin dA × Fin dB) (Fin dA × Fin dB) ℂ)
    (hρ : ρ.PosSemidef) :
    sandwichedRenyiTwoTrace ρ
        (partialTraceRight ρ ⊗ₖ partialTraceLeft ρ) ≤
      Matrix.operatorSchmidtRank ρ := by
  let hA : (partialTraceRight ρ).PosSemidef := hρ.partialTraceRight
  let hB : (partialTraceLeft ρ).PosSemidef := hρ.partialTraceLeft
  obtain ⟨kA, VA, hVA, hRangeA⟩ :=
    hA.isOrthogonalProjection_supportProj.exists_range_isometry
  obtain ⟨kB, VB, hVB, hRangeB⟩ :=
    hB.isOrthogonalProjection_supportProj.exists_range_isometry
  let V : Matrix (Fin dA × Fin dB) (Fin kA × Fin kB) ℂ := VA ⊗ₖ VB
  let ρc : Matrix (Fin kA × Fin kB) (Fin kA × Fin kB) ℂ := Vᴴ * ρ * V
  have hV : Vᴴ * V = 1 := by
    dsimp only [V]
    rw [Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul,
      hVA, hVB, Matrix.one_kronecker_one]
  have hRange : V * Vᴴ = (hA.kronecker hB).supportProj := by
    dsimp only [V]
    rw [Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul,
      hRangeA, hRangeB, hA.supportProj_kronecker hB]
  have hρc : ρc.PosSemidef := hρ.conjTranspose_mul_mul_same V
  have hMarginals :
      (partialTraceRight ρc).PosDef ∧ (partialTraceLeft ρc).PosDef :=
    hρ.marginalSupport_compression_marginals_posDef
      VA VB hVA hVB hRangeA hRangeB
  have hMargA : partialTraceRight ρc = VAᴴ * partialTraceRight ρ * VA :=
    hρ.partialTraceRight_marginalSupport_compression
      VA VB hVA hVB hRangeA hRangeB
  have hMargB : partialTraceLeft ρc = VBᴴ * partialTraceLeft ρ * VB :=
    hρ.partialTraceLeft_marginalSupport_compression
      VA VB hVA hVB hRangeA hRangeB
  let ω := partialTraceRight ρ ⊗ₖ partialTraceLeft ρ
  have hω : ω.PosSemidef := hA.kronecker hB
  have hker : ∀ v : Fin dA × Fin dB → ℂ, ω *ᵥ v = 0 → ρ *ᵥ v = 0 := by
    simpa only [ω] using hρ.productMarginals_kernel_le
  have hωc : Vᴴ * ω * V = partialTraceRight ρc ⊗ₖ partialTraceLeft ρc := by
    dsimp only [V, ω]
    rw [Matrix.conjTranspose_kronecker,
      ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul,
      ← hMargA, ← hMargB]
  have hQ2 := sandwichedRenyiTwoTrace_support_compression
    hρ hω hker V hV hRange
  have hOSR := hρ.operatorSchmidtRank_marginalSupport_compression
    VA VB hVA hVB hRangeA hRangeB
  calc
    sandwichedRenyiTwoTrace ρ
        (partialTraceRight ρ ⊗ₖ partialTraceLeft ρ) =
      sandwichedRenyiTwoTrace ρc
        (partialTraceRight ρc ⊗ₖ partialTraceLeft ρc) := by
          rw [show partialTraceRight ρ ⊗ₖ partialTraceLeft ρ = ω from rfl,
            hQ2, hωc]
    _ ≤ Matrix.operatorSchmidtRank ρc :=
      sandwichedRenyiTwoTrace_product_marginals_le_operatorSchmidtRank_of_marginals_posDef
        ρc hρc hMarginals.1 hMarginals.2
    _ = Matrix.operatorSchmidtRank ρ := by exact_mod_cast hOSR

end TNLean

end

end MarginalSupportWhitenedChoi
