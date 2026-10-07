/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.OperatorMean.MatrixPowers
import QICLean.Channel.Schwarz.DiagonalJensen
import Mathlib.Analysis.Convex.SpecificFunctions.Pow

/-!
# The weighted geometric mean of positive definite matrices

For positive definite matrices `A`, `B` and a real weight `p`, the weighted
geometric mean is
\[
  A \#_p B = A^{1/2}\,(A^{-1/2} B A^{-1/2})^p\,A^{1/2}.
\]
For `0 ≤ p ≤ 1` this is the weighted operator geometric mean of the Kubo--Ando
framework. This file proves the one-vertex properties used for finite trees of
matrix means in the two-dimensional area-law argument: positivity, the endpoint
values, invertible congruence, scalar homogeneity, exchange symmetry,
monotonicity in each argument, the vector Jensen inequality, and the
factorization across commuting factors.

All statements are made only for positive definite inputs, the domain on which
the source defines the mean; no extension to singular inputs is used.

## Main definitions

* `Matrix.geomMean p A B` — the weighted geometric mean `A #_p B`.

## Main results

* `Matrix.PosDef.geomMean` — the mean of positive definite matrices is positive definite.
* `Matrix.geomMean_star_conj` — `(S* A S) #_p (S* B S) = S* (A #_p B) S` for invertible `S`.
* `Matrix.geomMean_smul` — `(c A) #_p (d B) = c ^ (1 - p) d ^ p (A #_p B)`.
* `Matrix.geomMean_comm` — `A #_p B = B #_{1-p} A`.
* `Matrix.geomMean_mono_right`, `Matrix.geomMean_mono_left` — monotonicity for
  `0 ≤ p ≤ 1`.
* `Matrix.re_dotProduct_rpow_mulVec_le` — the homogeneous scalar Jensen inequality
  `⟨w, C ^ p w⟩ ≤ ⟨w, w⟩ ^ (1 - p) ⟨w, C w⟩ ^ p`.
* `Matrix.re_dotProduct_geomMean_le` — the vector Jensen inequality
  `⟨z, (A #_p B) z⟩ ≤ ⟨z, A z⟩ ^ (1 - p) ⟨z, B z⟩ ^ p`.
* `Matrix.Commute.geomMean_right` — a matrix commuting with both arguments commutes
  with the mean.
* `Matrix.geomMean_mul_of_commute`, `Matrix.commute_geomMean_of_commute` —
  factorization across commuting factors, and commutation of the factors.

## References

* *A two-dimensional area law from a global spectral gap* (September 24, 2026),
  `build/sections/06-transport.tex`, display `transport:mean-def` (lines 17--22)
  and the one-vertex part of the proof of Lemma 7.1 (`transport:means`,
  lines 64--98 and 120--128). The proofs here are written independently from
  the paper; no code is adapted from the accompanying Lean development.
* F. Kubo and T. Ando, *Means of positive linear operators*, Math. Ann. 246
  (1980).
-/

open scoped Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The weighted geometric mean
`A #_p B = A ^ (1/2) * (A ^ (-1/2) * B * A ^ (-1/2)) ^ p * A ^ (1/2)`.

Area-law paper, `06-transport.tex`, display `transport:mean-def` (lines 17--22).
The source uses it for positive definite `A`, `B` and `0 ≤ p ≤ 1`; every
theorem below carries those hypotheses where they are used. -/
noncomputable def geomMean (p : ℝ) (A B : Matrix n n ℂ) : Matrix n n ℂ :=
  A ^ (1 / 2 : ℝ) * (A ^ (-(1 / 2) : ℝ) * B * A ^ (-(1 / 2) : ℝ)) ^ p * A ^ (1 / 2 : ℝ)

variable {A B : Matrix n n ℂ}

omit [DecidableEq n] in
/-- Conjugating by a positive definite matrix preserves positive definiteness. -/
private theorem PosDef.conj_posDef {X Y : Matrix n n ℂ} (hX : X.PosDef) (hY : Y.PosDef) :
    (X * Y * X).PosDef := by
  classical
  have h := (Matrix.IsUnit.posDef_star_left_conjugate_iff (x := Y) hX.isUnit).mpr hY
  rwa [star_eq_conjTranspose, hX.isHermitian.eq] at h

/-- The whitened second argument `A ^ (-1/2) * B * A ^ (-1/2)` is positive definite. -/
theorem PosDef.whiten (hA : A.PosDef) (hB : B.PosDef) :
    (A ^ (-(1 / 2) : ℝ) * B * A ^ (-(1 / 2) : ℝ)).PosDef :=
  PosDef.conj_posDef (hA.rpow _) hB

/-- The weighted geometric mean of positive definite matrices is positive definite. -/
protected theorem PosDef.geomMean (hA : A.PosDef) (hB : B.PosDef) (p : ℝ) :
    (geomMean p A B).PosDef :=
  PosDef.conj_posDef (hA.rpow _) ((hA.whiten hB).rpow p)

/-- At weight `0` the mean returns its first argument. -/
@[simp] theorem geomMean_zero (hA : A.PosDef) (hB : B.PosDef) : geomMean 0 A B = A := by
  rw [geomMean, (hA.whiten hB).rpow_zero, mul_one, hA.rpow_half_mul_rpow_half]

/-- At weight `1` the mean returns its second argument. -/
@[simp] theorem geomMean_one (hA : A.PosDef) (hB : B.PosDef) : geomMean 1 A B = B := by
  have h1 := hA.rpow_mul_rpow_neg (1 / 2)
  rw [geomMean, (hA.whiten hB).rpow_one]
  calc A ^ (1 / 2 : ℝ) * (A ^ (-(1 / 2) : ℝ) * B * A ^ (-(1 / 2) : ℝ)) * A ^ (1 / 2 : ℝ)
      = (A ^ (1 / 2 : ℝ) * A ^ (-(1 / 2) : ℝ)) * B *
          (A ^ (-(1 / 2) : ℝ) * A ^ (1 / 2 : ℝ)) := by noncomm_ring
    _ = B := by rw [h1, hA.rpow_neg_mul_rpow, one_mul, mul_one]

/-- With the identity as first argument the mean is a real power. -/
@[simp] theorem one_geomMean (p : ℝ) (B : Matrix n n ℂ) : geomMean p 1 B = B ^ p := by
  simp [geomMean, CFC.one_rpow]

/-- **Invertible congruence.** For an invertible matrix `S`,
`(S* A S) #_p (S* B S) = S* (A #_p B) S`.

Area-law paper, Lemma 7.1 (`transport:means`), proof, `06-transport.tex`
lines 65--73: with `Â = S* A S` the matrix `U = A^{1/2} S Â^{-1/2}` is unitary
and conjugates the two whitened arguments into each other. -/
theorem geomMean_star_conj (hA : A.PosDef) (hB : B.PosDef) {S : Matrix n n ℂ}
    (hS : IsUnit S) (p : ℝ) :
    geomMean p (star S * A * S) (star S * B * S) = star S * geomMean p A B * S := by
  have hAh : (star S * A * S).PosDef := (Matrix.IsUnit.posDef_star_left_conjugate_iff hS).mpr hA
  have hC : (A ^ (-(1 / 2) : ℝ) * B * A ^ (-(1 / 2) : ℝ)).PosDef := hA.whiten hB
  have ha := hA.star_rpow (1 / 2)
  have hhi := hAh.star_rpow (-(1 / 2))
  have haai := hA.rpow_mul_rpow_neg (1 / 2)
  have haia := hA.rpow_neg_mul_rpow (1 / 2)
  have hhhi := hAh.rpow_mul_rpow_neg (1 / 2)
  have hhih := hAh.rpow_neg_mul_rpow (1 / 2)
  have haa := hA.rpow_half_mul_rpow_half
  have hhh := hAh.rpow_half_mul_rpow_half
  have hconj : ∀ U : Matrix n n ℂ, star U * U = 1 →
      (star U * (A ^ (-(1 / 2) : ℝ) * B * A ^ (-(1 / 2) : ℝ)) * U) ^ p =
        star U * (A ^ (-(1 / 2) : ℝ) * B * A ^ (-(1 / 2) : ℝ)) ^ p * U := by
    intro U hUU
    have hUU' : U * star U = 1 := mul_eq_one_comm.mp hUU
    let Uu : unitary (Matrix n n ℂ) := ⟨star U, by
      rw [Unitary.mem_iff, star_star]; exact ⟨hUU', hUU⟩⟩
    have := Matrix.rpow_conj_unitary hC.posSemidef p Uu
    simpa [Uu] using this
  unfold geomMean
  generalize A ^ (1 / 2 : ℝ) = a at *
  generalize A ^ (-(1 / 2) : ℝ) = ai at *
  generalize (star S * A * S) ^ (1 / 2 : ℝ) = h at *
  generalize (star S * A * S) ^ (-(1 / 2) : ℝ) = hi at *
  -- The matrix `U = a S hi` is unitary.
  have hUU : star (a * S * hi) * (a * S * hi) = 1 := by
    calc star (a * S * hi) * (a * S * hi) = hi * (star S * (a * a) * S) * hi := by
          simp only [star_mul, ha, hhi]; noncomm_ring
      _ = hi * (h * h) * hi := by rw [haa, hhh]
      _ = (hi * h) * (h * hi) := by noncomm_ring
      _ = 1 := by rw [hhih, hhhi, one_mul]
  -- It carries one whitened second argument to the other.
  have hwhite : hi * (star S * B * S) * hi = star (a * S * hi) * (ai * B * ai) * (a * S * hi) := by
    symm
    calc star (a * S * hi) * (ai * B * ai) * (a * S * hi)
        = hi * star S * (a * ai) * B * (ai * a) * S * hi := by
          simp only [star_mul, ha, hhi]; noncomm_ring
      _ = hi * (star S * B * S) * hi := by rw [haai, haia]; noncomm_ring
  rw [hwhite, hconj _ hUU]
  generalize (ai * B * ai) ^ p = Cp
  calc h * (star (a * S * hi) * Cp * (a * S * hi)) * h
      = (h * hi) * star S * (a * Cp * a) * S * (hi * h) := by
        simp only [star_mul, ha, hhi]; noncomm_ring
    _ = star S * (a * Cp * a) * S := by rw [hhhi, hhih]; noncomm_ring

/-- **Scalar homogeneity at a vertex.** For positive reals `c`, `d`,
`(c A) #_p (d B) = c ^ (1 - p) d ^ p (A #_p B)`.

Area-law paper, Lemma 7.1 (`transport:means`), proof, `06-transport.tex`
lines 87--88. -/
theorem geomMean_smul (hA : A.PosDef) (hB : B.PosDef) {c d : ℝ} (hc : 0 < c) (hd : 0 < d)
    (p : ℝ) :
    geomMean p (c • A) (d • B) = (c ^ (1 - p) * d ^ p) • geomMean p A B := by
  have hwhite : (c • A) ^ (-(1 / 2) : ℝ) * (d • B) * (c • A) ^ (-(1 / 2) : ℝ) =
      (c⁻¹ * d) • (A ^ (-(1 / 2) : ℝ) * B * A ^ (-(1 / 2) : ℝ)) := by
    have h2 : c ^ (-(1 / 2) : ℝ) * c ^ (-(1 / 2) : ℝ) = c⁻¹ := by
      rw [← Real.rpow_add hc]; norm_num [Real.rpow_neg_one]
    rw [hA.smul_rpow hc]
    simp only [smul_mul_assoc, mul_smul_comm, smul_smul]
    congr 1
    linear_combination d * h2
  have hcd : 0 < c⁻¹ * d := mul_pos (inv_pos.mpr hc) hd
  rw [geomMean, hwhite, (hA.whiten hB).smul_rpow hcd, hA.smul_rpow hc, geomMean]
  simp only [smul_mul_assoc, mul_smul_comm, smul_smul]
  congr 1
  rw [Real.mul_rpow (inv_pos.mpr hc).le hd.le, Real.inv_rpow hc.le]
  have hsplit : c ^ (1 - p) = c ^ (1 / 2 : ℝ) * c ^ (1 / 2 : ℝ) * (c ^ p)⁻¹ := by
    rw [← Real.rpow_add hc, ← Real.rpow_neg hc.le, ← Real.rpow_add hc]; norm_num [sub_eq_add_neg]
  rw [hsplit]; ring

/-- **Exchange symmetry.** `A #_p B = B #_{1-p} A`.

Area-law paper, Lemma 7.1 (`transport:means`), proof, `06-transport.tex`
lines 74--76: after congruence to `A = I` the identity reduces to
`C ^ p = C ^ (1/2) (C⁻¹) ^ (1 - p) C ^ (1/2)`. -/
theorem geomMean_comm (hA : A.PosDef) (hB : B.PosDef) (p : ℝ) :
    geomMean p A B = geomMean (1 - p) B A := by
  set S := A ^ (-(1 / 2) : ℝ)
  have hS : S.PosDef := hA.rpow _
  have hSs : star S = S := hA.star_rpow _
  set C := S * B * S
  have hC : C.PosDef := hA.whiten hB
  have hSAS : star S * A * S = 1 := by
    rw [hSs]
    have hh := hA.rpow_half_mul_rpow_half
    calc S * A * S = S * (A ^ (1 / 2 : ℝ) * A ^ (1 / 2 : ℝ)) * S := by rw [hh]
      _ = (S * A ^ (1 / 2 : ℝ)) * (A ^ (1 / 2 : ℝ) * S) := by noncomm_ring
      _ = 1 := by rw [hA.rpow_neg_mul_rpow, hA.rpow_mul_rpow_neg, one_mul]
  have hSBS : star S * B * S = C := by rw [hSs]
  -- Reduce to the case `A = 1`.
  have key : geomMean p 1 C = geomMean (1 - p) C 1 := by
    rw [one_geomMean, geomMean, mul_one, hC.rpow_mul_rpow, hC.rpow_rpow, hC.rpow_mul_rpow,
      hC.rpow_mul_rpow]
    congr 1; ring
  have h1 := geomMean_star_conj hA hB hS.isUnit p
  have h2 := geomMean_star_conj hB hA hS.isUnit (1 - p)
  rw [hSAS, hSBS] at h1 h2
  rw [key, h2] at h1
  -- Cancel the invertible congruence.
  have hcancel : ∀ X Y : Matrix n n ℂ, star S * X * S = star S * Y * S → X = Y := by
    intro X Y hXY
    have hSu : IsUnit (star S) := hS.isUnit.star
    exact (hS.isUnit.mul_left_inj).mp ((hSu.mul_right_inj).mp (by simpa [mul_assoc] using hXY))
  exact (hcancel _ _ h1).symm

/-- **Monotonicity in the second argument** for `0 ≤ p ≤ 1`.

Area-law paper, Lemma 7.1 (`transport:means`), proof, `06-transport.tex`
lines 77--86, using the operator monotonicity of `C ↦ C ^ p`
(`CFC.rpow_le_rpow`). -/
theorem geomMean_mono_right (hA : A.PosDef) {B' : Matrix n n ℂ}
    {p : ℝ} (hp : p ∈ Set.Icc (0 : ℝ) 1) (hBB' : B ≤ B') :
    geomMean p A B ≤ geomMean p A B' := by
  have hwhite : A ^ (-(1 / 2) : ℝ) * B * A ^ (-(1 / 2) : ℝ) ≤
      A ^ (-(1 / 2) : ℝ) * B' * A ^ (-(1 / 2) : ℝ) := by
    have := star_left_conjugate_le_conjugate hBB' (A ^ (-(1 / 2) : ℝ))
    rwa [hA.star_rpow] at this
  have hpow := CFC.rpow_le_rpow hp hwhite
  have := star_left_conjugate_le_conjugate hpow (A ^ (1 / 2 : ℝ))
  rwa [hA.star_rpow] at this

/-- **Monotonicity in the first argument** for `0 ≤ p ≤ 1`, by exchange symmetry.

Area-law paper, Lemma 7.1 (`transport:means`), proof, `06-transport.tex`
line 86. -/
theorem geomMean_mono_left (hA : A.PosDef) (hB : B.PosDef) {A' : Matrix n n ℂ}
    {p : ℝ} (hp : p ∈ Set.Icc (0 : ℝ) 1) (hAA' : A ≤ A') :
    geomMean p A B ≤ geomMean p A' B := by
  have hA' : A'.PosDef := by
    have hd : (A' - A).PosSemidef := Matrix.nonneg_iff_posSemidef.mp (sub_nonneg.mpr hAA')
    simpa using hA.add_posSemidef hd
  rw [geomMean_comm hA hB, geomMean_comm hA' hB]
  exact geomMean_mono_right hB ⟨by linarith [hp.2], by linarith [hp.1]⟩ hAA'

omit [DecidableEq n] in
/-- A quadratic form of a Hermitian sandwich `a * X * a` is the quadratic form of `X` at
`a *ᵥ z`. -/
private theorem dotProduct_sandwich_mulVec {a : Matrix n n ℂ} (ha : a.IsHermitian)
    (X : Matrix n n ℂ) (z : n → ℂ) :
    star z ⬝ᵥ ((a * X * a) *ᵥ z) = star (a *ᵥ z) ⬝ᵥ (X *ᵥ (a *ᵥ z)) := by
  rw [← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec, star_mulVec, ha.eq]

/-- **Scalar Jensen inequality for a real power**, in homogeneous form: for a positive
semidefinite `C`, `0 ≤ p ≤ 1` and every vector `w`,
`⟨w, C ^ p w⟩ ≤ ⟨w, w⟩ ^ (1 - p) ⟨w, C w⟩ ^ p`.

This is the spectral-measure Jensen step in the area-law paper, Lemma 7.1
(`transport:means`), proof, `06-transport.tex` lines 90--98. -/
theorem re_dotProduct_rpow_mulVec_le {C : Matrix n n ℂ} (hC : C.PosSemidef) {p : ℝ}
    (hp : p ∈ Set.Icc (0 : ℝ) 1) (w : n → ℂ) :
    (star w ⬝ᵥ (C ^ p *ᵥ w)).re ≤
      (star w ⬝ᵥ w).re ^ (1 - p) * (star w ⬝ᵥ (C *ᵥ w)).re ^ p := by
  have hww : 0 ≤ (star w ⬝ᵥ w).re := by
    simpa using (PosSemidef.one (n := n) (R := ℂ)).re_dotProduct_nonneg w
  rcases hww.lt_or_eq with hr | hr
  · set r := (star w ⬝ᵥ w).re
    set t : ℂ := (((Real.sqrt r)⁻¹ : ℝ) : ℂ)
    have ht : star t = t := Complex.conj_ofReal _
    have htt : t * t = ((r⁻¹ : ℝ) : ℂ) := by
      simp only [t, ← Complex.ofReal_mul, ← mul_inv, Real.mul_self_sqrt hr.le]
    have hscale : ∀ X : Matrix n n ℂ,
        (star (t • w) ⬝ᵥ (X *ᵥ (t • w))).re = r⁻¹ * (star w ⬝ᵥ (X *ᵥ w)).re := by
      intro X
      rw [star_smul, ht, mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul,
        smul_eq_mul, ← mul_assoc, htt, Complex.re_ofReal_mul]
    have hunit : star (t • w) ⬝ᵥ (t • w) = 1 := by
      rw [star_smul, ht, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul,
        ← mul_assoc, htt]
      have hw : star w ⬝ᵥ w = (r : ℂ) := by
        apply Complex.ext
        · simp [r]
        · simpa using
            (PosSemidef.one (n := n) (R := ℂ)).isHermitian.im_star_dotProduct_mulVec_self w
      rw [hw, ← Complex.ofReal_mul, inv_mul_cancel₀ hr.ne', Complex.ofReal_one]
    have hjensen := diagonal_jensen_of_convexOn (Real.concaveOn_rpow hp.1 hp.2).neg hC hunit
    rw [← hC.isHermitian.cfc_eq, cfc_neg', Pi.neg_apply, Pi.neg_apply,
      ← CFC.rpow_eq_cfc_real hC.nonneg, neg_mulVec,
      dotProduct_neg, Complex.neg_re, neg_le_neg_iff, hscale, hscale] at hjensen
    have hCw : 0 ≤ (star w ⬝ᵥ (C *ᵥ w)).re := hC.re_dotProduct_nonneg w
    calc (star w ⬝ᵥ (C ^ p *ᵥ w)).re
        = r * (r⁻¹ * (star w ⬝ᵥ (C ^ p *ᵥ w)).re) := by field_simp
      _ ≤ r * (r⁻¹ * (star w ⬝ᵥ (C *ᵥ w)).re) ^ p := by gcongr
      _ = r ^ (1 - p) * (star w ⬝ᵥ (C *ᵥ w)).re ^ p := by
        rw [Real.mul_rpow (inv_nonneg.mpr hr.le) hCw, Real.inv_rpow hr.le, ← mul_assoc,
          Real.rpow_sub hr, Real.rpow_one, div_eq_mul_inv]
  · have hw0 : w = 0 := by
      by_contra hw
      have := (PosDef.one (n := n) (R := ℂ)).re_dotProduct_pos hw
      simp only [one_mulVec] at this
      exact absurd hr (ne_of_lt this)
    subst hw0
    simp only [mulVec_zero, dotProduct_zero, Complex.zero_re]
    exact mul_nonneg (Real.rpow_nonneg le_rfl _) (Real.rpow_nonneg le_rfl _)

/-- **The vector Jensen inequality at a vertex.** For `0 ≤ p ≤ 1` and every vector `z`,
`⟨z, (A #_p B) z⟩ ≤ ⟨z, A z⟩ ^ (1 - p) ⟨z, B z⟩ ^ p`.

Area-law paper, Lemma 7.1 (`transport:means`), display
`transport:vector-jensen` and its one-vertex proof, `06-transport.tex`
lines 49--51 and 90--98. The source states the inequality for unit vectors;
both sides are homogeneous of degree two, and it holds for every vector. -/
theorem re_dotProduct_geomMean_le (hA : A.PosDef) (hB : B.PosDef) {p : ℝ}
    (hp : p ∈ Set.Icc (0 : ℝ) 1) (z : n → ℂ) :
    (star z ⬝ᵥ (geomMean p A B *ᵥ z)).re ≤
      (star z ⬝ᵥ (A *ᵥ z)).re ^ (1 - p) * (star z ⬝ᵥ (B *ᵥ z)).re ^ p := by
  have ha : (A ^ (1 / 2 : ℝ)).IsHermitian := hA.rpow_isHermitian _
  have hAeq : A = A ^ (1 / 2 : ℝ) * 1 * A ^ (1 / 2 : ℝ) := by
    rw [mul_one, hA.rpow_half_mul_rpow_half]
  have hBeq : B = A ^ (1 / 2 : ℝ) * (A ^ (-(1 / 2) : ℝ) * B * A ^ (-(1 / 2) : ℝ)) *
      A ^ (1 / 2 : ℝ) := by
    have := geomMean_one hA hB
    rw [geomMean, (hA.whiten hB).rpow_one] at this
    exact this.symm
  have h := re_dotProduct_rpow_mulVec_le (hA.whiten hB).posSemidef hp (A ^ (1 / 2 : ℝ) *ᵥ z)
  rw [geomMean, dotProduct_sandwich_mulVec ha]
  conv_rhs => rw [hAeq, dotProduct_sandwich_mulVec ha, one_mulVec]
  nth_rw 2 [hBeq]
  rwa [dotProduct_sandwich_mulVec ha]

/-- A matrix commuting with both arguments commutes with the mean. -/
theorem Commute.geomMean_right {X : Matrix n n ℂ} (hA : A.PosDef) (hB : B.PosDef)
    (hXA : Commute X A) (hXB : Commute X B) (p : ℝ) : Commute X (geomMean p A B) := by
  have ha : ∀ r : ℝ, Commute X (A ^ r) := fun r ↦ (hA.commute_rpow_left hXA.symm r).symm
  have hC : Commute X (A ^ (-(1 / 2) : ℝ) * B * A ^ (-(1 / 2) : ℝ)) :=
    ((ha _).mul_right hXB).mul_right (ha _)
  have hCp : Commute X ((A ^ (-(1 / 2) : ℝ) * B * A ^ (-(1 / 2) : ℝ)) ^ p) := by
    rw [CFC.rpow_eq_cfc_real (hA.whiten hB).posSemidef.nonneg]
    exact (Commute.cfc_real hC.symm _).symm
  exact ((ha _).mul_right hCp).mul_right (ha _)

omit [DecidableEq n] in
/-- Rearranging a product of two commuting blocks: if `x₂`, `y₂` commute with `x₁`, `y₁`,
then `(x₁ x₂)(y₁ y₂)(x₁ x₂) = (x₁ y₁ x₁)(x₂ y₂ x₂)`. -/
private theorem mul_mul_mul_of_commute {x₁ x₂ y₁ y₂ : Matrix n n ℂ} (hxx : Commute x₂ x₁)
    (hxy : Commute x₂ y₁) (hyx : Commute y₂ x₁) :
    x₁ * x₂ * (y₁ * y₂) * (x₁ * x₂) = x₁ * y₁ * x₁ * (x₂ * y₂ * x₂) := by
  simp only [mul_assoc]
  rw [hxy.left_comm, hyx.left_comm, hxx.left_comm]

/-- **Factorization across commuting factors at a vertex.** If every factor of the first
pair commutes with every factor of the second pair, then
`(A₁ A₂) #_p (B₁ B₂) = (A₁ #_p B₁)(A₂ #_p B₂)`.

Area-law paper, Lemma 7.1 (`transport:means`), proof, `06-transport.tex`
lines 120--128: the inverse square root of the first product factors, the
whitened second argument is a product of commuting positive matrices, and the
`p`th power factors. -/
theorem geomMean_mul_of_commute {A₁ A₂ B₁ B₂ : Matrix n n ℂ} (hA₁ : A₁.PosDef)
    (hA₂ : A₂.PosDef) (hB₁ : B₁.PosDef) (hB₂ : B₂.PosDef) (hAA : Commute A₁ A₂)
    (hAB : Commute A₁ B₂) (hBA : Commute B₁ A₂) (hBB : Commute B₁ B₂) (p : ℝ) :
    geomMean p (A₁ * A₂) (B₁ * B₂) = geomMean p A₁ B₁ * geomMean p A₂ B₂ := by
  -- Commutation of powers across the two pairs.
  have hpow : ∀ r s : ℝ, Commute (A₂ ^ r) (A₁ ^ s) := fun r s ↦
    (hA₁.commute_rpow hA₂ hAA s r).symm
  have hpowB₁ : ∀ r : ℝ, Commute (A₂ ^ r) B₁ := fun r ↦ hA₂.commute_rpow_left hBA.symm r
  have hpowB₂ : ∀ r : ℝ, Commute B₂ (A₁ ^ r) := fun r ↦ (hA₁.commute_rpow_left hAB r).symm
  have hC₁ := hA₁.whiten hB₁
  have hC₂ := hA₂.whiten hB₂
  -- The second whitened argument commutes with everything built from the first pair.
  have hC₂A : ∀ r : ℝ, Commute (A₂ ^ (-(1 / 2) : ℝ) * B₂ * A₂ ^ (-(1 / 2) : ℝ)) (A₁ ^ r) :=
    fun r ↦ ((hpow _ r).mul_left (hpowB₂ r)).mul_left (hpow _ r)
  have hC₂B : Commute (A₂ ^ (-(1 / 2) : ℝ) * B₂ * A₂ ^ (-(1 / 2) : ℝ)) B₁ :=
    ((hpowB₁ _).mul_left hBB.symm).mul_left (hpowB₁ _)
  have hC₂C₁ : Commute (A₂ ^ (-(1 / 2) : ℝ) * B₂ * A₂ ^ (-(1 / 2) : ℝ))
      (A₁ ^ (-(1 / 2) : ℝ) * B₁ * A₁ ^ (-(1 / 2) : ℝ)) :=
    ((hC₂A _).mul_right hC₂B).mul_right (hC₂A _)
  -- Powers of the second whitened argument commute with the first pair as well.
  have hP₂A : ∀ r : ℝ, Commute ((A₂ ^ (-(1 / 2) : ℝ) * B₂ * A₂ ^ (-(1 / 2) : ℝ)) ^ p)
      (A₁ ^ r) := fun r ↦ hC₂.commute_rpow_left (hC₂A r) p
  have hwhite : (A₁ * A₂) ^ (-(1 / 2) : ℝ) * (B₁ * B₂) * (A₁ * A₂) ^ (-(1 / 2) : ℝ) =
      (A₁ ^ (-(1 / 2) : ℝ) * B₁ * A₁ ^ (-(1 / 2) : ℝ)) *
        (A₂ ^ (-(1 / 2) : ℝ) * B₂ * A₂ ^ (-(1 / 2) : ℝ)) := by
    rw [hA₁.mul_rpow_of_commute hA₂ hAA]
    exact mul_mul_mul_of_commute (hpow _ _) (hpowB₁ _) (hpowB₂ _)
  unfold geomMean
  rw [hwhite, hC₁.mul_rpow_of_commute hC₂ hC₂C₁.symm, hA₁.mul_rpow_of_commute hA₂ hAA]
  have hC₁A₂ : ∀ r : ℝ, Commute (A₁ ^ (-(1 / 2) : ℝ) * B₁ * A₁ ^ (-(1 / 2) : ℝ)) (A₂ ^ r) :=
    fun r ↦ (((hpow r _).symm.mul_left (hpowB₁ r).symm).mul_left (hpow r _).symm)
  exact mul_mul_mul_of_commute (hpow _ _) (hC₁.commute_rpow_left (hC₁A₂ _) p).symm (hP₂A _)

/-- The two factors in `Matrix.geomMean_mul_of_commute` commute. -/
theorem commute_geomMean_of_commute {A₁ A₂ B₁ B₂ : Matrix n n ℂ} (hA₁ : A₁.PosDef)
    (hA₂ : A₂.PosDef) (hB₁ : B₁.PosDef) (hB₂ : B₂.PosDef) (hAA : Commute A₁ A₂)
    (hAB : Commute A₁ B₂) (hBA : Commute B₁ A₂) (hBB : Commute B₁ B₂) (p : ℝ) :
    Commute (geomMean p A₁ B₁) (geomMean p A₂ B₂) := by
  have h₁ : Commute A₁ (geomMean p A₂ B₂) := Commute.geomMean_right hA₂ hB₂ hAA hAB p
  have h₂ : Commute B₁ (geomMean p A₂ B₂) := Commute.geomMean_right hA₂ hB₂ hBA hBB p
  exact (Commute.geomMean_right hA₁ hB₁ h₁.symm h₂.symm p).symm

end Matrix
