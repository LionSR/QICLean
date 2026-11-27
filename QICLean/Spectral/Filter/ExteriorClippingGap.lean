/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Spectral.Filter.EnergyTruncation
import QICLean.Spectral.Gap.CodimensionOneGap
import QICLean.Analysis.FunctionalCalculus.OrthogonalResolutionCfc
import QICLean.Analysis.Projection.DetectabilityLemma

/-!
# Gap of a sum of three commuting positive operators after exterior clipping

Let `L`, `N`, `R` be commuting positive semidefinite matrices, the disconnected Hamiltonian of
Arad, Kuwahara, Landau and Vazirani (AKLV, arXiv:1301.1162v1, Section 6.3), and let `A` be a
positive boundary coupling that need not commute with them. Clipping the two exterior operators
separately at a cutoff `t` (`Matrix.twoSidedEnergyTruncation L N R t`) still costs at least `t`
on the high spectral subspace of `L + N + R`, the projected energy is controlled by the clipped
energy, and for `t ≥ 1024 (e + g) / g²` a ground gap `g` of `L + N + R + A` survives as a gap
of at least `g / 2` of the clipped operator.

The statements use only matrices, spectral projections and the functional calculus; the chain
of AKLV enters only when they are applied to the blocks of a chain Hamiltonian.

## Main results

* `Matrix.cutoff_smul_highProjection_le_twoSidedEnergyTruncation`: AKLV Lemma 6.5(1), order form.
* `Matrix.cutoff_mul_sq_norm_highProjection_le_energy`,
  `Matrix.norm_highProjection_le_sqrt_clipped_energy`: the high-energy mass of a vector is
  bounded by its clipped energy.
* `Matrix.projected_energy_le_clipped_energy_add_sqrt`: AKLV Lemma 6.5(2), with the cross term
  entering through its unsquared modulus (the printed proof squares it; the correction is
  recorded in `https://sirui-lu.com/QICLean/paper-gaps/aklv13_robustness_constants.pdf`).
* `Matrix.orthogonal_clipped_energy_ge`, `Matrix.exists_ground_gap_twoSidedEnergyTruncation`:
  AKLV Theorem 6.1(a), the gap of the clipped operator.

Moved from TNLean, `TNLean/MPS/AreaLaw/ChebyshevAGSP/{HighEnergyMass,ProjectionEnergy,
LowSpectrumGap}.lean` (Apache-2.0).
-/

open scoped Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator InnerProductSpace

noncomputable section

namespace Matrix

/-- Separate exterior clipping dominates the high-energy spectral
projection of the disconnected sum. AKLV, arXiv:1301.1162v1,
Lemma 6.5(1). All positivity and commutation assumptions are on the
original regional operators, before clipping. -/
theorem cutoff_smul_highProjection_le_twoSidedEnergyTruncation
    {n : Type*} [Fintype n] [DecidableEq n]
    (L N R : Matrix n n ℂ) (hL : L.PosSemidef) (hN : N.PosSemidef)
    (hR : R.PosSemidef) (hLN : Commute L N) (hLR : Commute L R)
    (hNR : Commute N R) (t : ℝ) (ht : 0 ≤ t) :
    (t : ℂ) • Matrix.spectralProjectionGE (L + N + R) t ≤
      Matrix.twoSidedEnergyTruncation L N R t := by
  classical
  let l := hL.isHermitian
  let m := hN.isHermitian
  let r := hR.isHermitian
  let PL := l.isOrthogonalResolution_spectralProj
  let PN := m.isOrthogonalResolution_spectralProj
  let PR := r.isOrthogonalResolution_spectralProj
  have hcLN (a : l.eigenvalueSet) (b : m.eigenvalueSet) :
      Commute (l.spectralProj a) (m.spectralProj b) :=
    (m.commute_spectralProj (l.commute_spectralProj hLN a).symm b).symm
  let PLN := PL.prod PN hcLN
  have hcR (p : l.eigenvalueSet × m.eigenvalueSet) (c : r.eigenvalueSet) :
      Commute (l.spectralProj p.1 * m.spectralProj p.2) (r.spectralProj c) :=
    ((r.commute_spectralProj (l.commute_spectralProj hLR p.1).symm c).symm).mul_left
      ((r.commute_spectralProj (m.commute_spectralProj hNR p.2).symm c).symm)
  let P := PLN.prod PR hcR
  have hherm (p : (l.eigenvalueSet × m.eigenvalueSet) × r.eigenvalueSet) :
      ((l.spectralProj p.1.1 * m.spectralProj p.1.2) * r.spectralProj p.2).IsHermitian :=
    (((l.isHermitian_spectralProj p.1.1).commute_iff
      (m.isHermitian_spectralProj p.1.2)).mp (hcLN p.1.1 p.1.2)).commute_iff
      (r.isHermitian_spectralProj p.2) |>.mp (hcR p.1 p.2)
  have hLhom : P.hom (fun p ↦ ((p.1.1 : ℝ) : ℂ)) = L :=
    (PLN.prod_hom_fst PR P _).trans ((PL.prod_hom_fst PN PLN _).trans l.eq_hom.symm)
  have hNhom : P.hom (fun p ↦ ((p.1.2 : ℝ) : ℂ)) = N :=
    (PLN.prod_hom_fst PR P _).trans ((PL.prod_hom_snd PN PLN _).trans m.eq_hom.symm)
  have hRhom : P.hom (fun p ↦ ((p.2 : ℝ) : ℂ)) = R :=
    (PLN.prod_hom_snd PR P _).trans r.eq_hom.symm
  let b : ((l.eigenvalueSet × m.eigenvalueSet) × r.eigenvalueSet) → ℝ :=
    fun p ↦ (p.1.1 : ℝ) + (p.1.2 : ℝ) + (p.2 : ℝ)
  let k : ((l.eigenvalueSet × m.eigenvalueSet) × r.eigenvalueSet) → ℝ :=
    fun p ↦ min (p.1.1 : ℝ) t + (p.1.2 : ℝ) + min (p.2 : ℝ) t
  let J := (l.eigenvalueSet × m.eigenvalueSet) × r.eigenvalueSet
  have hBhom : P.hom (fun p ↦ (b p : ℂ)) = L + N + R := by
    have hfun : (fun p ↦ (b p : ℂ)) =
        (((fun p : J ↦ ((p.1.1 : ℝ) : ℂ)) +
          (fun p ↦ ((p.1.2 : ℝ) : ℂ))) + (fun p ↦ ((p.2 : ℝ) : ℂ))) := by
      ext p
      simp only [b, Pi.add_apply, Complex.ofReal_add]
    rw [hfun, map_add, map_add, hLhom, hNhom, hRhom]
  have hKhom : P.hom (fun p ↦ (k p : ℂ)) = Matrix.twoSidedEnergyTruncation L N R t := by
    have hLt : P.hom (fun p ↦ ((min (p.1.1 : ℝ) t : ℝ) : ℂ)) =
        Matrix.energyTruncation L t :=
      (P.cfc_hom hherm (fun x ↦ min x t) (fun p ↦ (p.1.1 : ℝ))).symm.trans
        (congrArg (cfc (fun x : ℝ ↦ min x t)) hLhom)
    have hRt : P.hom (fun p ↦ ((min (p.2 : ℝ) t : ℝ) : ℂ)) =
        Matrix.energyTruncation R t :=
      (P.cfc_hom hherm (fun x ↦ min x t) (fun p ↦ (p.2 : ℝ))).symm.trans
        (congrArg (cfc (fun x : ℝ ↦ min x t)) hRhom)
    have hfun : (fun p ↦ (k p : ℂ)) =
        (((fun p : J ↦ ((min (p.1.1 : ℝ) t : ℝ) : ℂ)) +
          (fun p ↦ ((p.1.2 : ℝ) : ℂ))) +
          (fun p ↦ ((min (p.2 : ℝ) t : ℝ) : ℂ))) := by
      ext p
      simp only [k, Pi.add_apply, Complex.ofReal_add]
    rw [hfun, map_add, map_add, hLt, hNhom, hRt, Matrix.twoSidedEnergyTruncation]
  have hQhom : Matrix.spectralProjectionGE (L + N + R) t =
      P.hom (fun p ↦ ((if t ≤ b p then 1 else 0 : ℝ) : ℂ)) := by
    rw [Matrix.spectralProjectionGE, ← hBhom, P.cfc_hom hherm]
  have hnonneg (A : Matrix n n ℂ) (hA : A.PosSemidef)
      (u : hA.isHermitian.eigenvalueSet) : 0 ≤ (u : ℝ) := by
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp u.property
    rw [← hi]
    exact spectrum_nonneg_of_nonneg hA.nonneg (hA.isHermitian.eigenvalues_mem_spectrum_real i)
  rw [hQhom, ← hKhom, Matrix.le_iff]
  have hscale : (t : ℂ) • P.hom (fun p ↦ ((if t ≤ b p then 1 else 0 : ℝ) : ℂ)) =
      P.hom (fun p ↦ ((t * if t ≤ b p then 1 else 0 : ℝ) : ℂ)) := by
    rw [← map_smul]
    congr 1
    ext p
    simp only [Pi.smul_apply, smul_eq_mul, Complex.ofReal_mul]
  rw [hscale, ← map_sub]
  convert P.posSemidef_hom hherm (f := fun p ↦ k p - t * if t ≤ b p then 1 else 0) ?_ using 1
  · congr 1
    ext p
    simp only [Pi.sub_apply, Complex.ofReal_sub]
  · intro p
    have hl0 := hnonneg L hL p.1.1
    have hn0 := hnonneg N hN p.1.2
    have hr0 := hnonneg R hR p.2
    dsimp only [k, b]
    split_ifs with hsum
    · by_cases hl : t ≤ (p.1.1 : ℝ)
      · rw [min_eq_right hl]
        have hmin := le_min hr0 ht
        linarith
      · by_cases hr : t ≤ (p.2 : ℝ)
        · rw [min_eq_right hr]
          have hmin := le_min hl0 ht
          linarith
        · rw [min_eq_left (le_of_not_ge hl), min_eq_left (le_of_not_ge hr)]
          linarith
    · have hl := le_min hl0 ht
      have hr := le_min hr0 ht
      linarith

end Matrix

namespace Matrix

/-- The high-energy mass of any vector is bounded by its actual clipped
energy. This is AKLV, arXiv:1301.1162v1, Lemma 6.5(1), before division
by the cutoff. The positive boundary coupling need not commute with any
of the three disconnected blocks. -/
theorem cutoff_mul_sq_norm_highProjection_le_energy
    {n : Type*} [Fintype n] [DecidableEq n]
    (L N R A : Matrix n n ℂ) (hL : L.PosSemidef) (hN : N.PosSemidef)
    (hR : R.PosSemidef) (hA : A.PosSemidef)
    (hLN : Commute L N) (hLR : Commute L R) (hNR : Commute N R)
    (t : ℝ) (ht : 0 ≤ t) (x : EuclideanSpace ℂ n) :
    let ι := Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ)
    let Q := Matrix.spectralProjectionGE (L + N + R) t
    let K := Matrix.twoSidedEnergyTruncation L (N + A) R t
    t * ‖ι Q x‖ ^ 2 ≤ (⟪x, ι K x⟫_ℂ).re := by
  intro ι Q K
  have hbase := cutoff_smul_highProjection_le_twoSidedEnergyTruncation
    L N R hL hN hR hLN hLR hNR t ht
  have hK : K = Matrix.twoSidedEnergyTruncation L N R t + A := by
    dsimp [K, Matrix.twoSidedEnergyTruncation]
    abel
  have hle : (t : ℂ) • Q ≤ K :=
    hbase.trans (by rw [hK]; exact le_add_of_nonneg_right hA.nonneg)
  have hQ : IsStarProjection (ι Q) :=
    ((hL.isHermitian.add hN.isHermitian).add hR.isHermitian
      |>.isStarProjection_spectralProjectionGE t).map ι
  have hpositive : (ι (K - (t : ℂ) • Q)).IsPositive :=
    (Matrix.le_iff.mp hle).isPositive_toEuclideanCLM
  have h := hpositive.re_inner_nonneg_right x
  rw [map_sub, map_smul] at h
  change 0 ≤ (⟪x, ι K x - (t : ℂ) • ι Q x⟫_ℂ).re at h
  rw [inner_sub_right, inner_smul_right, Complex.sub_re, Complex.re_ofReal_mul] at h
  have hinner := ContinuousLinearMap.IsStarProjection.re_inner_apply_self hQ x
  change (⟪x, ι Q x⟫_ℂ).re = ‖ι Q x‖ ^ 2 at hinner
  rw [hinner] at h
  linarith

/-- The high-energy norm bound of AKLV, arXiv:1301.1162v1, Lemma 6.5(1),
for the actual two-sided energy truncation. No normalization is needed. -/
theorem norm_highProjection_le_sqrt_clipped_energy
    {n : Type*} [Fintype n] [DecidableEq n]
    (L N R A : Matrix n n ℂ) (hL : L.PosSemidef) (hN : N.PosSemidef)
    (hR : R.PosSemidef) (hA : A.PosSemidef)
    (hLN : Commute L N) (hLR : Commute L R) (hNR : Commute N R)
    (t : ℝ) (ht : 0 < t) (x : EuclideanSpace ℂ n) :
    let ι := Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ)
    let Q := Matrix.spectralProjectionGE (L + N + R) t
    let K := Matrix.twoSidedEnergyTruncation L (N + A) R t
    ‖ι Q x‖ ≤ Real.sqrt ((⟪x, ι K x⟫_ℂ).re / t) := by
  intro ι Q K
  have h := cutoff_mul_sq_norm_highProjection_le_energy
    L N R A hL hN hR hA hLN hLR hNR t ht.le x
  have hsq : ‖ι Q x‖ ^ 2 ≤ (⟪x, ι K x⟫_ℂ).re / t :=
    (le_div_iff₀ ht).mpr (by simpa only [mul_comm] using h)
  calc
    _ = Real.sqrt (‖ι Q x‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
    _ ≤ _ := Real.sqrt_le_sqrt hsq

/-- A positive matrix bounded above by `c • 1` has operator norm at most `c`. This is
how the two removed boundary bonds `0 ≤ hₐ + h_b ≤ 2` enter the AKLV estimates. -/
theorem PosSemidef.norm_le_of_le_smul_one {n : Type*} [Fintype n]
    [DecidableEq n] {A : Matrix n n ℂ} (hA : A.PosSemidef) {c : ℝ} (hc : 0 ≤ c)
    (hAc : A ≤ (c : ℂ) • 1) : ‖A‖ ≤ c :=
  (CStarAlgebra.norm_le_iff_le_algebraMap A hc hA.nonneg).mpr
    (by simpa [Algebra.algebraMap_eq_smul_one, ← Complex.coe_smul] using hAc)

/-- The corrected Cauchy--Schwarz bound in AKLV, arXiv:1301.1162v1,
the proof of Lemma 6.5(2): the unsquared modulus is at most twice the
square root of clipped energy divided by the cutoff. The source typo is
recorded in `https://sirui-lu.com/QICLean/paper-gaps/aklv13_robustness_constants.pdf`. -/
theorem norm_low_high_boundary_inner_le_sqrt_clipped_energy
    {n : Type*} [Fintype n] [DecidableEq n]
    (L N R A : Matrix n n ℂ) (hL : L.PosSemidef) (hN : N.PosSemidef)
    (hR : R.PosSemidef) (hA : A.PosSemidef)
    (hLN : Commute L N) (hLR : Commute L R) (hNR : Commute N R)
    (hAcap : A ≤ (2 : ℂ) • 1) (t : ℝ) (ht : 0 < t)
    (x : EuclideanSpace ℂ n) (hx : ‖x‖ = 1) :
    let ι := Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ)
    let Q := Matrix.spectralProjectionGE (L + N + R) t
    let K := Matrix.twoSidedEnergyTruncation L (N + A) R t
    ‖⟪ι (1 - Q) x, ι A (ι Q x)⟫_ℂ‖ ≤
      2 * Real.sqrt ((⟪x, ι K x⟫_ℂ).re / t) := by
  intro ι Q K
  have hQ : IsStarProjection (ι (1 - Q)) :=
    (((hL.isHermitian.add hN.isHermitian).add hR.isHermitian
      |>.isStarProjection_spectralProjectionGE t).one_sub).map ι
  have hlow : ‖ι (1 - Q) x‖ ≤ 1 := by
    simpa only [hx] using ContinuousLinearMap.IsStarProjection.norm_apply_le hQ x
  have hnormA : ‖A‖ ≤ 2 := hA.norm_le_of_le_smul_one (by norm_num) (by simpa using hAcap)
  have hhigh := norm_highProjection_le_sqrt_clipped_energy
    L N R A hL hN hR hA hLN hLR hNR t ht x
  calc
    _ ≤ ‖ι (1 - Q) x‖ * ‖ι A (ι Q x)‖ := norm_inner_le_norm _ _
    _ ≤ 1 * (2 * Real.sqrt ((⟪x, ι K x⟫_ℂ).re / t)) := by
      apply mul_le_mul hlow
        (((ι A).le_opNorm _).trans (mul_le_mul hnormA hhigh (norm_nonneg _) (by norm_num)))
        (norm_nonneg _) zero_le_one
    _ = _ := one_mul _

end Matrix

namespace ContinuousLinearMap

/-- Dropping the positive energy of one summand costs at most twice the
modulus of the cross term. Auxiliary to AKLV, Lemma 6.5(2). -/
theorem re_inner_left_le_energy_add_cross {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (K : E →L[ℂ] E) (hK : K.IsPositive) (p q : E) :
    (⟪p, K p⟫_ℂ).re ≤ (⟪p + q, K (p + q)⟫_ℂ).re + 2 * ‖⟪p, K q⟫_ℂ‖ := by
  have hcross : (⟪q, K p⟫_ℂ).re = (⟪p, K q⟫_ℂ).re := by
    calc
      _ = (⟪K p, q⟫_ℂ).re := by
        simpa only [RCLike.re_to_complex] using inner_re_symm (𝕜 := ℂ) q (K p)
      _ = _ := congrArg Complex.re (hK.isSymmetric p q)
  have hsplit : (⟪p + q, K (p + q)⟫_ℂ).re =
      (⟪p, K p⟫_ℂ).re + (⟪q, K q⟫_ℂ).re + 2 * (⟪p, K q⟫_ℂ).re := by
    simp only [map_add, inner_add_left, inner_add_right, Complex.add_re, hcross]
    ring
  have hnonneg := hK.re_inner_nonneg_right q
  change 0 ≤ (⟪q, K q⟫_ℂ).re at hnonneg
  have habs := Complex.abs_re_le_norm (⟪p, K q⟫_ℂ)
  have hneg := neg_abs_le (⟪p, K q⟫_ℂ).re
  rw [hsplit]
  linarith

end ContinuousLinearMap

namespace Matrix

/-- Positivity and domination by the original Hamiltonian require no
budget for the middle term. Auxiliary to AKLV, Sections 6.1 and 6.3. -/
theorem twoSidedEnergyTruncation_posSemidef_le
    {n : Type*} [Fintype n] [DecidableEq n]
    (L M R : Matrix n n ℂ) (hL : L.PosSemidef) (hM : M.PosSemidef)
    (hR : R.PosSemidef) (t : ℝ) (ht : 0 ≤ t) :
    (Matrix.twoSidedEnergyTruncation L M R t).PosSemidef ∧
      Matrix.twoSidedEnergyTruncation L M R t ≤ L + M + R := by
  have hcap : M ≤ (‖M‖ : ℂ) • 1 := by
    simpa only [Algebra.algebraMap_eq_smul_one, Complex.coe_smul] using
      IsSelfAdjoint.le_algebraMap_norm_self M hM.isHermitian.isSelfAdjoint
  obtain ⟨hpos, hle, _⟩ := Matrix.twoSidedEnergyTruncation_bounds L M R hL hM hR t ‖M‖ ht hcap
  exact ⟨hpos, hle⟩

/-- The original regional commutations imply commutation of the clipped
disconnected Hamiltonian with the original disconnected sum.
Auxiliary to AKLV, arXiv:1301.1162v1, Section 6.3. -/
theorem commute_twoSidedEnergyTruncation_disconnected
    {n : Type*} [Fintype n] [DecidableEq n]
    (L N R : Matrix n n ℂ) (hLN : Commute L N) (hLR : Commute L R)
    (hNR : Commute N R) (t : ℝ) :
    Commute (Matrix.twoSidedEnergyTruncation L N R t) (L + N + R) := by
  have hLB := ((Commute.refl L).add_right hLN).add_right hLR
  have hNB := (hLN.symm.add_right (Commute.refl N)).add_right hNR
  have hRB := (hLR.symm.add_right hNR.symm).add_right (Commute.refl R)
  exact ((hLB.cfc_real (fun x : ℝ ↦ min x t)).add_left hNB).add_left
    (hRB.cfc_real (fun x : ℝ ↦ min x t))

/-- The actual clipping agrees with the original operator below the
cutoff of the disconnected sum. All reducing-subspace and order
conditions are derived from the original positive regional blocks.
AKLV, arXiv:1301.1162v1, equation (8). -/
theorem twoSidedEnergyTruncation_mul_lowProjection_eq_of_commuting
    {n : Type*} [Fintype n] [DecidableEq n]
    (L N R A : Matrix n n ℂ) (hL : L.PosSemidef) (hN : N.PosSemidef)
    (hR : R.PosSemidef) (hLN : Commute L N) (hLR : Commute L R)
    (hNR : Commute N R) (t : ℝ) :
    Matrix.twoSidedEnergyTruncation L (N + A) R t *
        (1 - Matrix.spectralProjectionGE (L + N + R) t) =
      (L + (N + A) + R) * (1 - Matrix.spectralProjectionGE (L + N + R) t) := by
  have hLB := ((Commute.refl L).add_right hLN).add_right hLR
  have hRB := (hLR.symm.add_right hNR.symm).add_right (Commute.refl R)
  apply Matrix.twoSidedEnergyTruncation_mul_lowProjection_eq L (N + A) R (L + N + R)
    hL.isHermitian hR.isHermitian ((hL.isHermitian.add hN.isHermitian).add hR.isHermitian)
    hLB hRB
  · exact (le_add_of_nonneg_right hN.nonneg).trans (le_add_of_nonneg_right hR.nonneg)
  · exact le_add_of_nonneg_left (add_nonneg hL.nonneg hN.nonneg)

/-- Only the boundary coupling contributes to the low-high cross block
of the actual clipped Hamiltonian. AKLV, Lemma 6.5(2). -/
theorem lowProjection_mul_clipped_mul_highProjection_eq
    {n : Type*} [Fintype n] [DecidableEq n]
    (L N R A : Matrix n n ℂ) (hL : L.IsHermitian) (hN : N.IsHermitian)
    (hR : R.IsHermitian) (hLN : Commute L N) (hLR : Commute L R)
    (hNR : Commute N R) (t : ℝ) :
    let Q := Matrix.spectralProjectionGE (L + N + R) t
    (1 - Q) * Matrix.twoSidedEnergyTruncation L (N + A) R t * Q = (1 - Q) * A * Q := by
  intro Q
  let K₀ := Matrix.twoSidedEnergyTruncation L N R t
  have hK : Matrix.twoSidedEnergyTruncation L (N + A) R t = K₀ + A := by
    dsimp [K₀, Matrix.twoSidedEnergyTruncation]
    abel
  have hcomm : Commute K₀ Q :=
    ((commute_twoSidedEnergyTruncation_disconnected L N R hLN hLR hNR t).symm.cfc_real
      (fun x : ℝ ↦ if t ≤ x then 1 else 0)).symm
  have hQQ := ((hL.add hN).add hR).isStarProjection_spectralProjectionGE t
  have hPQ : (1 - Q) * Q = 0 := by
    rw [sub_mul, one_mul, hQQ.isIdempotentElem.eq, sub_self]
  rw [hK, mul_add, add_mul, mul_assoc, hcomm.eq, ← mul_assoc, hPQ, zero_mul, zero_add]

/-- The projected energy of the original Hamiltonian is bounded by the
actual clipped energy plus four times the high-energy norm. This is the explicit corrected
version of AKLV, arXiv:1301.1162v1, Lemma 6.5(2), for unit vectors.
No projection norm estimate or compatibility identity is assumed. -/
theorem projected_energy_le_clipped_energy_add_tail
    {n : Type*} [Fintype n] [DecidableEq n]
    (L N R A : Matrix n n ℂ) (hL : L.PosSemidef) (hN : N.PosSemidef)
    (hR : R.PosSemidef) (hA : A.PosSemidef)
    (hLN : Commute L N) (hLR : Commute L R) (hNR : Commute N R)
    (hAcap : A ≤ (2 : ℂ) • 1) (t : ℝ) (ht : 0 < t)
    (x : EuclideanSpace ℂ n) (hx : ‖x‖ = 1) :
    let ι := Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ)
    let P := 1 - Matrix.spectralProjectionGE (L + N + R) t
    let H := L + (N + A) + R
    let K := Matrix.twoSidedEnergyTruncation L (N + A) R t
    (⟪ι P x, ι H (ι P x)⟫_ℂ).re ≤ (⟪x, ι K x⟫_ℂ).re +
      4 * ‖ι (Matrix.spectralProjectionGE (L + N + R) t) x‖ := by
  intro ι P H K
  let Q := Matrix.spectralProjectionGE (L + N + R) t
  have hP : IsStarProjection (ι P) :=
    (((hL.isHermitian.add hN.isHermitian).add hR.isHermitian)
      |>.isStarProjection_spectralProjectionGE t).one_sub.map ι
  have hpos : (ι K).IsPositive :=
    (twoSidedEnergyTruncation_posSemidef_le L (N + A) R hL (hN.add hA) hR t ht.le).1
      |>.isPositive_toEuclideanCLM
  have hsplit : ι P x + ι Q x = x := by
    rw [← _root_.add_apply, ← map_add, sub_add_cancel, map_one, one_apply_eq_self]
  have hlow : ι H (ι P x) = ι K (ι P x) := by
    rw [← mul_apply_eq_comp, ← mul_apply_eq_comp, ← map_mul, ← map_mul]
    exact congrArg (fun M : Matrix n n ℂ ↦ ι M x)
      (twoSidedEnergyTruncation_mul_lowProjection_eq_of_commuting
        L N R A hL hN hR hLN hLR hNR t).symm
  have hcross : ⟪ι P x, ι K (ι Q x)⟫_ℂ = ⟪ι P x, ι A (ι Q x)⟫_ℂ := by
    rw [ContinuousLinearMap.IsStarProjection.inner_apply_left hP,
      ContinuousLinearMap.IsStarProjection.inner_apply_left hP]
    simp only [← mul_apply_eq_comp, ← map_mul]
    rw [← Matrix.mul_assoc, lowProjection_mul_clipped_mul_highProjection_eq
      L N R A hL.isHermitian hN.isHermitian hR.isHermitian hLN hLR hNR t]
    simp only [Matrix.mul_assoc]
    rfl
  have henergy := ContinuousLinearMap.re_inner_left_le_energy_add_cross
    (ι K) hpos (ι P x) (ι Q x)
  rw [hsplit, hcross] at henergy
  have hnormA : ‖A‖ ≤ 2 := hA.norm_le_of_le_smul_one (by norm_num) (by simpa using hAcap)
  have hnormP : ‖ι P x‖ ≤ 1 := by
    simpa only [hx] using ContinuousLinearMap.IsStarProjection.norm_apply_le hP x
  have hbound : ‖⟪ι P x, ι A (ι Q x)⟫_ℂ‖ ≤ 2 * ‖ι Q x‖ := by
    calc
      _ ≤ ‖ι P x‖ * ‖ι A (ι Q x)‖ := norm_inner_le_norm _ _
      _ ≤ 1 * (2 * ‖ι Q x‖) :=
        mul_le_mul hnormP (((ι A).le_opNorm _).trans
          (mul_le_mul_of_nonneg_right hnormA (norm_nonneg _)))
          (norm_nonneg _) zero_le_one
      _ = _ := one_mul _
  rw [hlow]
  linarith

/-- The square-root form of AKLV, Lemma 6.5(2), with explicit constant four. -/
theorem projected_energy_le_clipped_energy_add_sqrt
    {n : Type*} [Fintype n] [DecidableEq n]
    (L N R A : Matrix n n ℂ) (hL : L.PosSemidef) (hN : N.PosSemidef)
    (hR : R.PosSemidef) (hA : A.PosSemidef)
    (hLN : Commute L N) (hLR : Commute L R) (hNR : Commute N R)
    (hAcap : A ≤ (2 : ℂ) • 1) (t : ℝ) (ht : 0 < t)
    (x : EuclideanSpace ℂ n) (hx : ‖x‖ = 1) :
    let ι := Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ)
    let P := 1 - Matrix.spectralProjectionGE (L + N + R) t
    let H := L + (N + A) + R
    let K := Matrix.twoSidedEnergyTruncation L (N + A) R t
    (⟪ι P x, ι H (ι P x)⟫_ℂ).re ≤ (⟪x, ι K x⟫_ℂ).re +
      4 * Real.sqrt ((⟪x, ι K x⟫_ℂ).re / t) := by
  intro ι P H K
  have he := projected_energy_le_clipped_energy_add_tail
    L N R A hL hN hR hA hLN hLR hNR hAcap t ht x hx
  have ht := norm_highProjection_le_sqrt_clipped_energy
    L N R A hL hN hR hA hLN hLR hNR t ht x
  exact he.trans (by linarith)

end Matrix

namespace Matrix

/-- The cutoff condition makes every sufficiently low-energy vector's
high-energy norm at most `g/32`. Auxiliary scalar estimate for AKLV,
Theorem 6.1(a). -/
private theorem high_norm_le_gap_div_thirtyTwo (e g t q E : ℝ)
    (he : 0 ≤ e) (hg : 0 < g) (hq : 0 ≤ q)
    (hcut : 1024 * (e + g) ≤ t * g ^ 2)
    (hmass : t * q ^ 2 ≤ E) (hE : E ≤ e + g / 2) : q ≤ g / 32 := by
  have hep : 0 < e + g := by linarith
  have h1 := mul_le_mul_of_nonneg_right hcut (sq_nonneg q)
  have h2 := mul_le_mul_of_nonneg_right (hmass.trans hE) (sq_nonneg g)
  have hsq : (e + g) * (1024 * q ^ 2) ≤ (e + g) * g ^ 2 := by
    nlinarith [mul_nonneg (sq_nonneg g) hg.le]
  have hsq' := le_of_mul_le_mul_left hsq hep
  nlinarith

/-- Every vector orthogonal to the original ground vector has clipped
energy at least `e+g/2` times its squared norm. This is the variational
step in AKLV, arXiv:1301.1162v1, Theorem 6.1(a). -/
theorem orthogonal_clipped_energy_ge
    {n : Type*} [Fintype n] [DecidableEq n]
    (L N R A : Matrix n n ℂ) (hL : L.PosSemidef) (hN : N.PosSemidef)
    (hR : R.PosSemidef) (hA : A.PosSemidef)
    (hLN : Commute L N) (hLR : Commute L R) (hNR : Commute N R)
    (hAcap : A ≤ (2 : ℂ) • 1) (Ω : EuclideanSpace ℂ n) (hΩ : ‖Ω‖ = 1)
    (e g t : ℝ) (he0 : 0 ≤ e) (he6 : e ≤ 6) (hg : 0 < g) (hg1 : g ≤ 1)
    (ht : 0 < t) (hcut : 1024 * (e + g) ≤ t * g ^ 2)
    (hgap : ∀ y : EuclideanSpace ℂ n,
      g * (‖y‖ ^ 2 - ‖⟪Ω, y⟫_ℂ‖ ^ 2) ≤
        (⟪y, Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ) (L + (N + A) + R) y⟫_ℂ).re -
          e * ‖y‖ ^ 2) :
    let ι := Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ)
    let K := Matrix.twoSidedEnergyTruncation L (N + A) R t
    ∀ x : EuclideanSpace ℂ n, ⟪Ω, x⟫_ℂ = 0 →
      (e + g / 2) * ‖x‖ ^ 2 ≤ (⟪x, ι K x⟫_ℂ).re := by
  intro ι K
  apply ContinuousLinearMap.re_inner_lower_of_unit_orthogonal_lower (ι K) Ω (e + g / 2)
  intro x hx horth
  let Q := Matrix.spectralProjectionGE (L + N + R) t
  let P := 1 - Q
  let q := ‖ι Q x‖
  let E := (⟪x, ι K x⟫_ℂ).re
  by_contra hnot
  have hE : E ≤ e + g / 2 := (not_le.mp hnot).le
  have hmass := cutoff_mul_sq_norm_highProjection_le_energy
    L N R A hL hN hR hA hLN hLR hNR t ht.le x
  have hq : q ≤ g / 32 := high_norm_le_gap_div_thirtyTwo e g t q E
    he0 hg (norm_nonneg _) hcut hmass hE
  have hQ : IsStarProjection (ι Q) :=
    (((hL.isHermitian.add hN.isHermitian).add hR.isHermitian)
      |>.isStarProjection_spectralProjectionGE t).map ι
  have hPx : ι P x = x - ι Q x := by
    rw [map_sub, map_one]
    rfl
  have hPnorm : ‖ι P x‖ ^ 2 = 1 - q ^ 2 := by
    have h := ContinuousLinearMap.IsStarProjection.norm_sq_eq hQ x
    rw [hx, one_pow, ← hPx] at h
    change 1 = q ^ 2 + ‖ι P x‖ ^ 2 at h
    linarith
  have hinner : ⟪Ω, ι P x⟫_ℂ = -⟪Ω, ι Q x⟫_ℂ := by
    rw [hPx, inner_sub_right, horth, zero_sub]
  have hover : ‖⟪Ω, ι P x⟫_ℂ‖ ≤ q := by
    rw [hinner, norm_neg]
    simpa only [hΩ, one_mul] using norm_inner_le_norm (𝕜 := ℂ) Ω (ι Q x)
  have hover2 : ‖⟪Ω, ι P x⟫_ℂ‖ ^ 2 ≤ q ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) hover 2
  have hG := hgap (ι P x)
  rw [hPnorm] at hG
  have hproj := projected_energy_le_clipped_energy_add_tail
    L N R A hL hN hR hA hLN hLR hNR hAcap t ht x hx
  have hmul := mul_le_mul_of_nonneg_left hover2 hg.le
  have hnecessary : g ≤ g / 2 + 4 * q + (e + 2 * g) * q ^ 2 := by
    nlinarith
  have hcoef : (e + 2 * g) * q ^ 2 ≤ 8 * q ^ 2 :=
    mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg q)
  have hq0 : 0 ≤ q := norm_nonneg _
  have hq2 : q ^ 2 ≤ g / 1024 := by
    nlinarith [sq_nonneg (g / 32 - q)]
  nlinarith

/-- A lower bound `e+g/2` on the clipped energy orthogonal to the original
ground vector gives the clipped Hamiltonian a unit ground vector of energy at
most `e` and gap at least `g/2`. Shared final step of AKLV, arXiv:1301.1162v1,
Theorem 6.1(a), for every cutoff that yields the orthogonal bound. -/
theorem exists_ground_gap_twoSidedEnergyTruncation_of_orthogonal
    {n : Type*} [Fintype n] [DecidableEq n]
    (L N R A : Matrix n n ℂ) (hL : L.PosSemidef) (hN : N.PosSemidef)
    (hR : R.PosSemidef) (hA : A.PosSemidef) (Ω : EuclideanSpace ℂ n) (hΩ : ‖Ω‖ = 1)
    (e g t : ℝ) (hg : 0 < g) (ht : 0 ≤ t)
    (heig : Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ) (L + (N + A) + R) Ω = (e : ℂ) • Ω)
    (horth : ∀ x : EuclideanSpace ℂ n, ⟪Ω, x⟫_ℂ = 0 →
      (e + g / 2) * ‖x‖ ^ 2 ≤ (⟪x, Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ)
        (Matrix.twoSidedEnergyTruncation L (N + A) R t) x⟫_ℂ).re) :
    let ι := Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ)
    let K := Matrix.twoSidedEnergyTruncation L (N + A) R t
    ∃ (e' : ℝ) (φ : EuclideanSpace ℂ n), ‖φ‖ = 1 ∧ ι K φ = (e' : ℂ) • φ ∧
      0 ≤ e' ∧ e' ≤ e ∧
      (∀ x : EuclideanSpace ℂ n,
        (e + g / 2 - e') * (‖x‖ ^ 2 - ‖⟪φ, x⟫_ℂ‖ ^ 2) ≤
          (⟪x, ι K x⟫_ℂ).re - e' * ‖x‖ ^ 2) ∧
      (∀ x : EuclideanSpace ℂ n, ⟪φ, x⟫_ℂ = 0 →
        (e + g / 2) * ‖x‖ ^ 2 ≤ (⟪x, ι K x⟫_ℂ).re) := by
  intro ι K
  obtain ⟨hKpos, hKle⟩ :=
    twoSidedEnergyTruncation_posSemidef_le L (N + A) R hL (hN.add hA) hR t ht
  have hpositive : (ι K).IsPositive := hKpos.isPositive_toEuclideanCLM
  have htest : (⟪Ω, ι K Ω⟫_ℂ).re ≤ e := by
    have h := (Matrix.isPositive_toEuclideanLin_iff.mpr (Matrix.le_iff.mp hKle))
      |>.re_inner_nonneg_right Ω
    change 0 ≤ (⟪Ω, ι (L + (N + A) + R - K) Ω⟫_ℂ).re at h
    rw [map_sub] at h
    change 0 ≤ (⟪Ω, ι (L + (N + A) + R) Ω - ι K Ω⟫_ℂ).re at h
    rw [inner_sub_right, Complex.sub_re, heig, inner_smul_right,
      Complex.re_ofReal_mul, inner_self_eq_norm_sq_to_K, hΩ] at h
    norm_num at h
    exact h
  exact ContinuousLinearMap.exists_ground_gap_of_orthogonal_lower (ι K) hpositive Ω hΩ e (e + g / 2)
    (by linarith) htest horth

/-- The actual clipped Hamiltonian has a unit ground vector, and all
directions orthogonal to it have energy at least `e+g/2`.
AKLV, arXiv:1301.1162v1, Theorem 6.1(a), with explicit cutoff constants.
The gap is therefore at least `g/2`, since its ground energy is at most `e`. -/
theorem exists_ground_gap_twoSidedEnergyTruncation
    {n : Type*} [Fintype n] [DecidableEq n]
    (L N R A : Matrix n n ℂ) (hL : L.PosSemidef) (hN : N.PosSemidef)
    (hR : R.PosSemidef) (hA : A.PosSemidef)
    (hLN : Commute L N) (hLR : Commute L R) (hNR : Commute N R)
    (hAcap : A ≤ (2 : ℂ) • 1) (Ω : EuclideanSpace ℂ n) (hΩ : ‖Ω‖ = 1)
    (e g t : ℝ) (he0 : 0 ≤ e) (he6 : e ≤ 6) (hg : 0 < g) (hg1 : g ≤ 1)
    (ht : 0 < t) (hcut : 1024 * (e + g) ≤ t * g ^ 2)
    (heig : Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ) (L + (N + A) + R) Ω = (e : ℂ) • Ω)
    (hgap : ∀ y : EuclideanSpace ℂ n,
      g * (‖y‖ ^ 2 - ‖⟪Ω, y⟫_ℂ‖ ^ 2) ≤
        (⟪y, Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ) (L + (N + A) + R) y⟫_ℂ).re -
          e * ‖y‖ ^ 2) :
    let ι := Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ)
    let K := Matrix.twoSidedEnergyTruncation L (N + A) R t
    ∃ (e' : ℝ) (φ : EuclideanSpace ℂ n), ‖φ‖ = 1 ∧ ι K φ = (e' : ℂ) • φ ∧
      0 ≤ e' ∧ e' ≤ e ∧
      (∀ x : EuclideanSpace ℂ n,
        (e + g / 2 - e') * (‖x‖ ^ 2 - ‖⟪φ, x⟫_ℂ‖ ^ 2) ≤
          (⟪x, ι K x⟫_ℂ).re - e' * ‖x‖ ^ 2) ∧
      (∀ x : EuclideanSpace ℂ n, ⟪φ, x⟫_ℂ = 0 →
        (e + g / 2) * ‖x‖ ^ 2 ≤ (⟪x, ι K x⟫_ℂ).re) :=
  exists_ground_gap_twoSidedEnergyTruncation_of_orthogonal L N R A hL hN hR hA Ω hΩ e g t hg
    ht.le heig (orthogonal_clipped_energy_ge L N R A hL hN hR hA hLN hLR hNR hAcap
      Ω hΩ e g t he0 he6 hg hg1 ht hcut hgap)

end Matrix
