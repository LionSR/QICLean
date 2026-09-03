/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Algebra.ScalarCommutant
import QICLean.Algebra.SkolemNoether
import QICLean.Algebra.StarSubalgebraSemisimple
import Mathlib.Algebra.Central.Basic
import Mathlib.Analysis.Matrix.Order
import Mathlib.RingTheory.SimpleRing.Congr
import Mathlib.RingTheory.SimpleRing.Matrix

/-!
# A ⋆-subalgebra of complex matrices with scalar centre is a full matrix algebra

Let `S` be a ⋆-subalgebra of a nonzero full complex matrix algebra whose centre consists
exactly of the scalar multiples of the identity. Then `S` is ⋆-isomorphic to one full
complex matrix algebra `M_r(ℂ)` with `r ≥ 1`, and its dimension is `r * r`.

This is the concrete full-matrix specialization of the building-block step in the structure
theorem for finite-dimensional C*-algebras: Schumacher--Werner, arXiv:quant-ph/0405174
(`Papers/quant-ph_0405174/qca.tex` in the consuming TNLean checkout), Proposition `Csform`,
lines 2082--2098, which decomposes such an algebra into a direct sum of full matrix algebras by
cutting with the minimal projections of its centre, the summands being exactly the pieces with
trivial centre. Gross--Nesme--Vogts--Werner, arXiv:0910.3675
(`References/0910.3675/QCI12.tex` there), lines 1278--1282, use precisely this consequence: a
support algebra with trivial centre is isomorphic to a full matrix algebra `M_{r(x)}(ℂ)`.

**Scope restriction (Schumacher--Werner `Csform`):** the declarations here are *not* a
formalization of the whole of `Csform`. The source states the direct-sum decomposition of an
abstract finite-dimensional C*-algebra, whereas the results below treat a ⋆-subalgebra of a
matrix algebra and prove only the single-block case. Neither the abstract C*-algebra generality
nor the cut by the minimal central projections is formalized. Recorded in
`docs/paper-gaps/sw04_csform_matrix_scope.tex`.

## Main results

* `Matrix.innerAlgEquiv` — conjugation by an invertible matrix, as an algebra automorphism.
* `StarSubalgebra.exists_starAlgEquiv_of_algEquiv_matrix` — an *algebra* isomorphism of a
  ⋆-subalgebra of complex matrices onto a full matrix algebra can be corrected, by conjugating
  with a positive definite matrix, into a ⋆-algebra isomorphism.
* `StarSubalgebra.isSimpleRing_of_isCentral` — a ⋆-subalgebra with scalar centre is a simple
  ring: the Wedderburn--Artin product has exactly one factor.
* `StarSubalgebra.exists_starAlgEquiv_matrix_of_isCentral` — a ⋆-subalgebra of a nonzero full
  complex matrix algebra with scalar centre is ⋆-isomorphic to `M_r(ℂ)` with `r ≥ 1`.
* `StarSubalgebra.finrank_eq_mul_self_of_starAlgEquiv_matrix` — the dimension of such a
  subalgebra is `r * r`.

## Proof outline

Semisimplicity of a ⋆-subalgebra of complex matrices gives a `ℂ`-algebra isomorphism onto a
finite product of full matrix algebras with positive block sizes. A coordinate idempotent of
that product is central, hence a scalar; comparing two coordinates shows the product has at
most one factor, and nontriviality excludes the empty product. So the subalgebra is a simple
ring, and Wedderburn--Artin over `ℂ` produces an algebra isomorphism `φ` onto `M_r(ℂ)`.

The algebra isomorphism need not preserve adjoints. Transporting the adjoint of the subalgebra
through `φ` produces an algebra automorphism of `M_r(ℂ)`, which by Skolem--Noether is
conjugation by an invertible matrix; writing that matrix as `H` gives
`φ(y⋆) = H⁻¹ φ(y)⋆ H`. Applying this identity twice shows `H⋆` is a scalar multiple of `H`.
Pairing the identity with the trace of `φ⁻¹` on rank-one matrices shows that the Hermitian form
`v ↦ v⋆ H v` never vanishes off `0` and, after `H` is rescaled by a scalar `c`, has constant
sign; the rescaled matrix `c H` is then positive definite. Writing `c H = R⋆ R` with `R`
invertible, the conjugated map `y ↦ R φ(y) R⁻¹` preserves adjoints.
-/

open scoped Matrix ComplexOrder MatrixOrder

namespace Matrix

variable {m : Type*} [Fintype m] [DecidableEq m]

/-- Conjugation by an invertible matrix, as an algebra automorphism of the full matrix algebra;
the inverse is supplied as an explicit second matrix. -/
def innerAlgEquiv {R K : Matrix m m ℂ} (hRK : R * K = 1) (hKR : K * R = 1) :
    Matrix m m ℂ ≃ₐ[ℂ] Matrix m m ℂ where
  toFun X := R * X * K
  invFun X := K * X * R
  left_inv X := by
    change K * (R * X * K) * R = X
    calc K * (R * X * K) * R = (K * R) * X * (K * R) := by simp [mul_assoc]
      _ = X := by rw [hKR, one_mul, mul_one]
  right_inv X := by
    change R * (K * X * R) * K = X
    calc R * (K * X * R) * K = (R * K) * X * (R * K) := by simp [mul_assoc]
      _ = X := by rw [hRK, one_mul, mul_one]
  map_mul' X Y := by
    change R * (X * Y) * K = (R * X * K) * (R * Y * K)
    calc R * (X * Y) * K = R * X * (K * R) * Y * K := by rw [hKR]; simp [mul_assoc]
      _ = (R * X * K) * (R * Y * K) := by simp [mul_assoc]
  map_add' X Y := by
    change R * (X + Y) * K = R * X * K + R * Y * K
    simp [Matrix.mul_add, Matrix.add_mul]
  commutes' r := by
    change R * (algebraMap ℂ (Matrix m m ℂ) r) * K = algebraMap ℂ (Matrix m m ℂ) r
    simp [Algebra.algebraMap_eq_smul_one, hRK]

@[simp]
theorem innerAlgEquiv_apply {R K : Matrix m m ℂ} (hRK : R * K = 1) (hKR : K * R = 1)
    (X : Matrix m m ℂ) : innerAlgEquiv hRK hKR X = R * X * K := rfl

omit [DecidableEq m] in
/-- The Hermitian form of the adjoint matrix is the complex conjugate of the Hermitian form. -/
theorem star_dotProduct_conjTranspose_mulVec (A : Matrix m m ℂ) (v : m → ℂ) :
    star v ⬝ᵥ Aᴴ *ᵥ v = star (star v ⬝ᵥ A *ᵥ v) := by
  rw [star_dotProduct, star_mulVec, conjTranspose_conjTranspose, dotProduct_mulVec]

omit [DecidableEq m] in
/-- Conjugating the rank-one matrix `v w⋆` by a matrix `H` collapses to the Hermitian form of
`H` at `v` times the rank-one matrix `w w⋆`. -/
theorem conjTranspose_vecMulVec_mul_mul_vecMulVec (H : Matrix m m ℂ) (v w : m → ℂ) :
    (vecMulVec v (star w))ᴴ * H * vecMulVec v (star w) =
      (star v ⬝ᵥ H *ᵥ v) • vecMulVec w (star w) := by
  ext s t
  simp only [mul_apply, vecMulVec_apply, conjTranspose_apply, smul_apply, smul_eq_mul,
    Pi.star_apply, star_mul', star_star, dotProduct, mulVec, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun q _ ↦ Finset.sum_congr rfl fun p _ ↦ by ring

end Matrix

namespace StarSubalgebra

variable {n : Type*} [Fintype n] [DecidableEq n]

section StarUpgrade

variable {m : Type*} [Fintype m] [DecidableEq m] [Nonempty m]

/-- **From an algebra isomorphism to a ⋆-algebra isomorphism.** If a ⋆-subalgebra `S` of the
complex matrix algebra is isomorphic, as a `ℂ`-algebra, to a nonzero full matrix algebra, then
it is isomorphic to it as a ⋆-algebra.

Transporting the adjoint of `S` through the isomorphism `φ` gives an algebra automorphism of the
matrix algebra, which Skolem--Noether realizes as conjugation by an invertible matrix `H`, so
that `φ(y⋆) = H⁻¹ φ(y)⋆ H`. Using the identity twice makes `H⋆` a scalar multiple of `H`, and
pairing it with the trace of `φ⁻¹` on rank-one matrices makes a scalar multiple of `H` positive
definite. Factoring that multiple as `R⋆R` with `R` invertible, the corrected isomorphism
`y ↦ R φ(y) R⁻¹` preserves adjoints.

This is the intrinsic building-block step of Schumacher--Werner, arXiv:quant-ph/0405174,
`Papers/quant-ph_0405174/qca.tex`, Proposition `Csform`, lines 2082--2098: the ⋆-structure of a
summand with trivial centre is the ⋆-structure of a full matrix algebra. -/
theorem exists_starAlgEquiv_of_algEquiv_matrix (S : StarSubalgebra ℂ (Matrix n n ℂ))
    (φ : ↥S ≃ₐ[ℂ] Matrix m m ℂ) : Nonempty (↥S ≃⋆ₐ[ℂ] Matrix m m ℂ) := by
  classical
  -- The adjoint of `S`, transported through `φ`, is an algebra automorphism of `M_m(ℂ)`.
  have hbij : Function.Bijective (fun Z : Matrix m m ℂ ↦ star (φ (star (φ.symm Z)))) :=
    Function.bijective_iff_has_inverse.mpr
      ⟨fun Z ↦ φ (star (φ.symm (star Z))), fun Z ↦ by simp, fun Z ↦ by simp⟩
  set ψ : Matrix m m ℂ ≃ₐ[ℂ] Matrix m m ℂ :=
    AlgEquiv.ofBijective
      { toFun := fun Z ↦ star (φ (star (φ.symm Z)))
        map_one' := by simp
        map_mul' := fun Z W ↦ by simp [star_mul]
        map_zero' := by simp
        map_add' := fun Z W ↦ by simp
        commutes' := fun r ↦ by
          simp [Algebra.algebraMap_eq_smul_one, star_smul] }
      hbij with hψ
  obtain ⟨X, hX⟩ := Matrix.skolemNoether_matrix ψ
  -- `H` implements the transported adjoint; `K` is its inverse.
  set H : Matrix m m ℂ := star ((X : Matrix m m ℂ)) with hHdef
  set K : Matrix m m ℂ := star (((X⁻¹ : GL m ℂ) : Matrix m m ℂ)) with hKdef
  have hUV : (X : Matrix m m ℂ) * ((X⁻¹ : GL m ℂ) : Matrix m m ℂ) = 1 := X.mul_inv
  have hVU : ((X⁻¹ : GL m ℂ) : Matrix m m ℂ) * (X : Matrix m m ℂ) = 1 := X.inv_mul
  have hHK : H * K = 1 := by rw [hHdef, hKdef, ← star_mul, hVU, star_one]
  have hKH : K * H = 1 := by rw [hHdef, hKdef, ← star_mul, hUV, star_one]
  have hkey : ∀ y : ↥S, φ (star y) = K * star (φ y) * H := by
    intro y
    have h := hX (φ y)
    rw [hψ] at h
    have h' : star (φ (star y)) =
        (X : Matrix m m ℂ) * φ y * ((X⁻¹ : GL m ℂ) : Matrix m m ℂ) := by
      simpa using h
    have h'' := congrArg star h'
    rw [star_star, star_mul, star_mul, ← hHdef, ← hKdef] at h''
    rw [h'', mul_assoc]
  -- The scalar constant produced by pairing the identity with a trace.
  obtain ⟨j₀⟩ := ‹Nonempty m›
  set w : m → ℂ := Pi.single j₀ 1 with hwdef
  have hw : w ≠ 0 := fun h ↦ by simpa [hwdef, h] using congrFun h j₀
  set W : Matrix m m ℂ := Matrix.vecMulVec w (star w) with hWdef
  set c : ℂ := Matrix.trace ((φ.symm (K * W) : ↥S) : Matrix n n ℂ) with hcdef
  have hq : ∀ v : m → ℂ, v ≠ 0 → 0 < (star v ⬝ᵥ H *ᵥ v) * c := by
    intro v hv
    set Y : Matrix m m ℂ := Matrix.vecMulVec v (star w) with hYdef
    have hY : Y ≠ 0 := by
      intro h
      apply hv
      funext i
      have := congrFun (congrFun h i) j₀
      simpa [hYdef, Matrix.vecMulVec_apply, hwdef, Pi.single_apply] using this
    set y : ↥S := φ.symm Y with hydef
    have hφy : φ y = Y := by rw [hydef, AlgEquiv.apply_symm_apply]
    have hy : (y : Matrix n n ℂ) ≠ 0 := by
      intro h
      apply hY
      rw [← hφy, show y = 0 from Subtype.ext (by simpa using h), map_zero]
    have hmul : star y * y = φ.symm (K * (Yᴴ * H * Y)) := by
      apply φ.injective
      rw [AlgEquiv.apply_symm_apply, map_mul, hkey y, hφy]
      simp [Matrix.star_eq_conjTranspose, mul_assoc]
    have hcoe : ((star y * y : ↥S) : Matrix n n ℂ) =
        ((y : Matrix n n ℂ))ᴴ * (y : Matrix n n ℂ) := by
      push_cast [StarMemClass.coe_star]
      rw [Matrix.star_eq_conjTranspose]
    have hstep : ((y : Matrix n n ℂ))ᴴ * (y : Matrix n n ℂ) =
        (star v ⬝ᵥ H *ᵥ v) • ((φ.symm (K * W) : ↥S) : Matrix n n ℂ) := by
      rw [← hcoe, hmul, hYdef, Matrix.conjTranspose_vecMulVec_mul_mul_vecMulVec,
        Matrix.mul_smul, map_smul, ← hWdef]
      simp
    have htrace : Matrix.trace (((y : Matrix n n ℂ))ᴴ * (y : Matrix n n ℂ))
        = (star v ⬝ᵥ H *ᵥ v) * c := by
      rw [hstep, Matrix.trace_smul, hcdef, smul_eq_mul]
    rw [← htrace]
    refine lt_of_le_of_ne (Matrix.PosSemidef.trace_nonneg
      (Matrix.posSemidef_conjTranspose_mul_self _)) (Ne.symm ?_)
    exact fun h ↦ hy (Matrix.trace_conjTranspose_mul_self_eq_zero_iff.mp h)
  have hqne : ∀ v : m → ℂ, v ≠ 0 → star v ⬝ᵥ H *ᵥ v ≠ 0 := by
    intro v hv h
    have := hq v hv
    rw [h, zero_mul] at this
    exact lt_irrefl 0 this
  have hc : c ≠ 0 := by
    intro h
    have := hq w hw
    rw [h, mul_zero] at this
    exact lt_irrefl 0 this
  -- Applying the identity twice makes the adjoint of `H` a scalar multiple of `H`.
  have hZ : ∀ Z : Matrix m m ℂ, Z = (K * Hᴴ) * Z * (Kᴴ * H) := by
    intro Z
    have h1 : φ (star (φ.symm Z)) = K * Zᴴ * H := by
      have h := hkey (φ.symm Z)
      rwa [AlgEquiv.apply_symm_apply, Matrix.star_eq_conjTranspose] at h
    have h2 := hkey (star (φ.symm Z))
    rw [star_star, AlgEquiv.apply_symm_apply, h1] at h2
    calc Z = K * star (K * Zᴴ * H) * H := h2
      _ = (K * Hᴴ) * Z * (Kᴴ * H) := by
          simp [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_mul, mul_assoc]
  obtain ⟨c₀, hc₀⟩ : ∃ c₀ : ℂ, K * Hᴴ = Matrix.scalar m c₀ := by
    refine Matrix.isScalar_of_commute_span_eq_top _ Submodule.span_univ ?_
    intro Z _
    have hone : (K * Hᴴ) * (Kᴴ * H) = 1 := by simpa using (hZ 1).symm
    have hother : (Kᴴ * H) * (K * Hᴴ) = 1 := mul_eq_one_comm.mp hone
    calc (K * Hᴴ) * Z = (K * Hᴴ) * Z * ((Kᴴ * H) * (K * Hᴴ)) := by rw [hother, mul_one]
      _ = ((K * Hᴴ) * Z * (Kᴴ * H)) * (K * Hᴴ) := by simp [mul_assoc]
      _ = Z * (K * Hᴴ) := by rw [← hZ Z]
  have hscal : Matrix.scalar m c₀ = c₀ • (1 : Matrix m m ℂ) := by
    rw [Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]
  have hHstar : Hᴴ = c₀ • H := by
    have h : H * (K * Hᴴ) = H * Matrix.scalar m c₀ := by rw [hc₀]
    rw [← mul_assoc, hHK, one_mul, hscal, Matrix.mul_smul, mul_one] at h
    exact h
  -- The rescaled matrix `c • H` is positive definite.
  have hPquad : ∀ v : m → ℂ, v ≠ 0 → 0 < star v ⬝ᵥ (c • H) *ᵥ v := by
    intro v hv
    have h := hq v hv
    rwa [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul, mul_comm]
  have hc₀c : star c * c₀ = c := by
    have hpos := hq w hw
    have hq0 : star w ⬝ᵥ H *ᵥ w ≠ 0 := hqne w hw
    have hreal : star ((star w ⬝ᵥ H *ᵥ w) * c) = (star w ⬝ᵥ H *ᵥ w) * c :=
      Complex.conj_eq_iff_im.mpr (Complex.lt_def.mp hpos).2.symm
    have hconj : star (star w ⬝ᵥ H *ᵥ w) = c₀ * (star w ⬝ᵥ H *ᵥ w) := by
      rw [← Matrix.star_dotProduct_conjTranspose_mulVec, hHstar, Matrix.smul_mulVec,
        dotProduct_smul, smul_eq_mul]
    rw [star_mul', hconj] at hreal
    exact mul_right_cancel₀ hq0 (by linear_combination hreal)
  have hPherm : (c • H).IsHermitian := by
    rw [Matrix.IsHermitian, Matrix.conjTranspose_smul, hHstar, smul_smul, hc₀c]
  have hPdef : (c • H).PosDef :=
    Matrix.PosDef.of_dotProduct_mulVec_pos hPherm fun _ hv ↦ hPquad _ hv
  -- Absorb the scalar into the implementing matrix, so that it becomes positive definite.
  obtain ⟨H', K', hH'K', hK'H', hkey', hH'pos⟩ :
      ∃ H' K' : Matrix m m ℂ, H' * K' = 1 ∧ K' * H' = 1 ∧
        (∀ y : ↥S, φ (star y) = K' * star (φ y) * H') ∧ H'.PosDef := by
    refine ⟨c • H, c⁻¹ • K, ?_, ?_, fun y ↦ ?_, hPdef⟩
    · rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, mul_inv_cancel₀ hc, one_smul, hHK]
    · rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, inv_mul_cancel₀ hc, one_smul, hKH]
    · rw [hkey y, Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
        inv_mul_cancel₀ hc, one_smul]
  -- Factor the positive definite implementer and conjugate `φ` by the factor.
  obtain ⟨R, hR⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hH'pos.posSemidef.nonneg
  have hH'eq : H' = Rᴴ * R := by rw [hR, Matrix.star_eq_conjTranspose]
  have hRdet : IsUnit R.det := by
    have hPu : IsUnit H'.det := (Matrix.isUnit_iff_isUnit_det _).mp hH'pos.isUnit
    rw [hH'eq, Matrix.det_mul] at hPu
    exact isUnit_of_mul_isUnit_right hPu
  have hRK : R * R⁻¹ = 1 := Matrix.mul_nonsing_inv R hRdet
  have hKR : R⁻¹ * R = 1 := Matrix.nonsing_inv_mul R hRdet
  have hRHK : Rᴴ * (R⁻¹)ᴴ = 1 := by
    rw [← Matrix.conjTranspose_mul, hKR, Matrix.conjTranspose_one]
  have hK'eq : K' = R⁻¹ * (R⁻¹)ᴴ := by
    have hH'M : H' * (R⁻¹ * (R⁻¹)ᴴ) = 1 := by
      rw [hH'eq]
      calc Rᴴ * R * (R⁻¹ * (R⁻¹)ᴴ) = Rᴴ * (R * R⁻¹) * (R⁻¹)ᴴ := by simp [mul_assoc]
        _ = 1 := by rw [hRK, mul_one, hRHK]
    calc K' = K' * (H' * (R⁻¹ * (R⁻¹)ᴴ)) := by rw [hH'M, mul_one]
      _ = (K' * H') * (R⁻¹ * (R⁻¹)ᴴ) := by rw [mul_assoc]
      _ = R⁻¹ * (R⁻¹)ᴴ := by rw [hK'H', one_mul]
  have hgen : ∀ Z : Matrix m m ℂ, R * (K' * Z * H') * R⁻¹ = (R⁻¹)ᴴ * Z * Rᴴ := by
    intro Z
    rw [hK'eq, hH'eq]
    calc R * (R⁻¹ * (R⁻¹)ᴴ * Z * (Rᴴ * R)) * R⁻¹
        = (R * R⁻¹) * ((R⁻¹)ᴴ * Z * Rᴴ) * (R * R⁻¹) := by simp [mul_assoc]
      _ = (R⁻¹)ᴴ * Z * Rᴴ := by rw [hRK, one_mul, mul_one]
  refine ⟨StarAlgEquiv.ofAlgEquiv (φ.trans (Matrix.innerAlgEquiv hRK hKR)) ?_⟩
  intro y
  change R * φ (star y) * R⁻¹ = star (R * φ y * R⁻¹)
  rw [hkey' y, Matrix.star_eq_conjTranspose (φ y), hgen]
  simp [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_mul, mul_assoc]

end StarUpgrade

/-- **A ⋆-subalgebra with scalar centre is a simple ring.** The Wedderburn--Artin product
decomposition of a ⋆-subalgebra of a nonzero full complex matrix algebra has exactly one factor
when the centre of the subalgebra is the scalar image: a coordinate idempotent of the product is
central, hence a scalar, which is impossible for a product with two or more factors, and the
empty product is excluded by nontriviality.

This is the centre-cutting step of Schumacher--Werner, arXiv:quant-ph/0405174,
`Papers/quant-ph_0405174/qca.tex`, Proposition `Csform`, lines 2082--2098, in the case where the
centre has a single minimal projection. -/
theorem isSimpleRing_of_isCentral [Nonempty n] (S : StarSubalgebra ℂ (Matrix n n ℂ))
    [Algebra.IsCentral ℂ ↥S] : IsSimpleRing ↥S := by
  classical
  have hSnt : Nontrivial ↥S :=
    ⟨⟨1, 0, fun h ↦ one_ne_zero (α := Matrix n n ℂ) (congrArg Subtype.val h)⟩⟩
  obtain ⟨k, d, hd, ⟨e⟩⟩ := S.exists_algEquiv_pi_matrix
  have hsub : Subsingleton (Fin k) := by
    refine ⟨fun i j ↦ ?_⟩
    by_contra hij
    have : NeZero (d i) := hd i
    have : NeZero (d j) := hd j
    have hmem : e.symm (Pi.single i 1) ∈ Subalgebra.center ℂ ↥S := by
      rw [Subalgebra.mem_center_iff]
      intro z
      apply e.injective
      simp only [map_mul, AlgEquiv.apply_symm_apply]
      funext l
      by_cases hl : l = i
      · subst hl; simp
      · simp [hl]
    obtain ⟨a, ha⟩ := (Algebra.IsCentral.mem_center_iff (K := ℂ)).mp hmem
    have ha' : (Pi.single i 1 : Π l, Matrix (Fin (d l)) (Fin (d l)) ℂ) =
        algebraMap ℂ (Π l, Matrix (Fin (d l)) (Fin (d l)) ℂ) a := by
      have := congrArg e ha
      rwa [AlgEquiv.apply_symm_apply, AlgEquiv.commutes] at this
    have hi : (1 : Matrix (Fin (d i)) (Fin (d i)) ℂ) =
        algebraMap ℂ (Matrix (Fin (d i)) (Fin (d i)) ℂ) a := by
      have := congrFun ha' i
      simpa using this
    have hj : (0 : Matrix (Fin (d j)) (Fin (d j)) ℂ) =
        algebraMap ℂ (Matrix (Fin (d j)) (Fin (d j)) ℂ) a := by
      have := congrFun ha' j
      simpa [Pi.single_apply, Ne.symm hij] using this
    have ha1 : a = 1 :=
      (FaithfulSMul.algebraMap_injective ℂ (Matrix (Fin (d i)) (Fin (d i)) ℂ))
        (by rw [← hi, map_one])
    rw [ha1, map_one] at hj
    exact one_ne_zero hj.symm
  have hk : k = 1 := by
    have hle : k ≤ 1 := by
      simpa using Fintype.card_le_one_iff_subsingleton.mpr hsub
    have hne : k ≠ 0 := by
      rintro rfl
      have : Subsingleton (Π i : Fin 0, Matrix (Fin (d i)) (Fin (d i)) ℂ) :=
        ⟨fun a b ↦ funext fun i ↦ absurd i.isLt (by omega)⟩
      have : Subsingleton ↥S := e.toEquiv.subsingleton
      exact false_of_nontrivial_of_subsingleton ↥S
    omega
  subst hk
  have : NeZero (d default) := hd default
  have : Nonempty (Fin (d default)) := ⟨⟨0, Nat.pos_of_ne_zero (NeZero.ne _)⟩⟩
  exact IsSimpleRing.of_ringEquiv
    ((RingEquiv.piUnique fun i : Fin 1 ↦ Matrix (Fin (d i)) (Fin (d i)) ℂ).symm.trans
      e.symm.toRingEquiv) inferInstance

/-- **A ⋆-subalgebra of complex matrices with scalar centre is a full matrix algebra.** Let `S`
be a ⋆-subalgebra of a nonzero full complex matrix algebra whose centre consists of the scalar
multiples of the identity. Then `S` is ⋆-isomorphic to `M_r(ℂ)` for some `r ≥ 1`.

This is the full-matrix specialization of the building-block step of Schumacher--Werner,
arXiv:quant-ph/0405174, `Papers/quant-ph_0405174/qca.tex`, Proposition `Csform`,
lines 2082--2098 -- the summand of a finite-dimensional C*-algebra cut out by a minimal central
projection is a full matrix algebra -- and not a formalization of the direct-sum decomposition
asserted there; see `docs/paper-gaps/sw04_csform_matrix_scope.tex`. It is the consequence used
by Gross--Nesme--Vogts--Werner, arXiv:0910.3675,
`References/0910.3675/QCI12.tex`, lines 1278--1282, where a support algebra with trivial centre
is identified with `M_{r(x)}(ℂ)`. -/
theorem exists_starAlgEquiv_matrix_of_isCentral [Nonempty n]
    (S : StarSubalgebra ℂ (Matrix n n ℂ)) [Algebra.IsCentral ℂ ↥S] :
    ∃ (r : ℕ) (_ : NeZero r), Nonempty (↥S ≃⋆ₐ[ℂ] Matrix (Fin r) (Fin r) ℂ) := by
  have := S.isSimpleRing_of_isCentral
  obtain ⟨r, hr, ⟨φ⟩⟩ := IsSimpleRing.exists_algEquiv_matrix_of_isAlgClosed ℂ ↥S
  have := hr
  have : Nonempty (Fin r) := ⟨⟨0, Nat.pos_of_ne_zero (NeZero.ne _)⟩⟩
  exact ⟨r, hr, S.exists_starAlgEquiv_of_algEquiv_matrix φ⟩

/-- The dimension of a ⋆-subalgebra of complex matrices presented as `M_r(ℂ)` is `r * r`. -/
theorem finrank_eq_mul_self_of_starAlgEquiv_matrix (S : StarSubalgebra ℂ (Matrix n n ℂ))
    {r : ℕ} (e : ↥S ≃⋆ₐ[ℂ] Matrix (Fin r) (Fin r) ℂ) : Module.finrank ℂ ↥S = r * r := by
  rw [e.toAlgEquiv.toLinearEquiv.finrank_eq, Module.finrank_matrix]
  simp

end StarSubalgebra


