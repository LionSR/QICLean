/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.LowEnergyBasis.SpectralSplit
import QICLean.ManyBody.Hamiltonian.LowEnergyBasis

/-!
# A uniform ground-space basis

Hastings, arXiv:cond-mat/0508554v3, eq. `oibu` and lines 1695–1708, refines the basis
recursively along spectral splits. With the decay kernel of the low-energy commutators this
gives a basis of the ground space whose summed off-diagonal parts are bounded uniformly in the
system size.

* `recursiveCommutatorCoeff`, `recursiveBasisCoeff`, `exists_orthonormalBasis_uniform_kernel`.
* `exists_groundSpaceBasis_sum_norm_offDiagonalPartFamily_le_of_commutator_le` and
  `exists_groundSpaceBasis_sum_norm_offDiagonalPartFamily_le_uniform`.

Moved from TNLean (`e113e005`): `TNLean/Lattice/LowEnergyBasisRecursive.lean` and
`LowEnergyBasisUniformGeneral.lean`. Changes as in `LowEnergyCommutator`.
-/

noncomputable section

open LowEnergyBasis
open scoped InnerProductSpace

namespace ManyBody

open scoped InnerProductSpace

/-- A uniform upper bound for the commutator coefficient at depth `t` in a spectral
refinement of total dimension at most `N`. Hastings, arXiv:cond-mat/0508554v3,
`proj3new.tex`, lines 1695–1708, with compression cross terms retained. -/
noncomputable def recursiveCommutatorCoeff (N : ℕ) (C : ℝ) (t : ℕ) : ℝ :=
  C * (1 + 2 * (N : ℝ) ^ 3) ^ t

/-- One coefficient dominating all cross-block errors in the recursive basis construction.
Hastings, arXiv:cond-mat/0508554v3, `proj3new.tex`, lines 1695–1708. -/
noncomputable def recursiveBasisCoeff (N : ℕ) (C : ℝ) : ℝ :=
  Real.sqrt ((N : ℝ) ^ 3 * C * (1 + 2 * (N : ℝ) ^ 3) ^ N)

theorem recursiveCommutatorCoeff_nonneg (N t : ℕ) {C : ℝ} (hC : 0 ≤ C) :
    0 ≤ recursiveCommutatorCoeff N C t := by
  unfold recursiveCommutatorCoeff
  positivity

theorem recursiveBasisCoeff_nonneg (N : ℕ) (C : ℝ) : 0 ≤ recursiveBasisCoeff N C :=
  Real.sqrt_nonneg _

/-- The dimension-dependent coefficient bounds the cross-block coefficient at every
allowed depth. Hastings, arXiv:cond-mat/0508554v3, `proj3new.tex`, lines 1695–1708. -/
theorem sqrt_recursiveCommutatorCoeff_le {m N t : ℕ} (hm : m ≤ N) (ht : t ≤ N)
    {C : ℝ} (hC : 0 ≤ C) :
    Real.sqrt ((m : ℝ) ^ 3 * recursiveCommutatorCoeff N C t) ≤ recursiveBasisCoeff N C := by
  apply Real.sqrt_le_sqrt
  unfold recursiveCommutatorCoeff
  have hbase : (1 : ℝ) ≤ 1 + 2 * (N : ℝ) ^ 3 :=
    le_add_of_nonneg_right (by positivity)
  have hpow := pow_le_pow_right₀ hbase ht
  have hmR : (m : ℝ) ≤ N := by exact_mod_cast hm
  have hm3 : (m : ℝ) ^ 3 ≤ (N : ℝ) ^ 3 := pow_le_pow_left₀ (Nat.cast_nonneg _) hmR _
  calc (m : ℝ) ^ 3 * (C * (1 + 2 * (N : ℝ) ^ 3) ^ t)
      = ((m : ℝ) ^ 3 * C) * (1 + 2 * (N : ℝ) ^ 3) ^ t := by ring
    _ ≤ ((N : ℝ) ^ 3 * C) * (1 + 2 * (N : ℝ) ^ 3) ^ N :=
      mul_le_mul (mul_le_mul_of_nonneg_right hm3 hC) hpow (by positivity) (by positivity)
    _ = _ := rfl

/-- Retaining both cross terms advances the commutator coefficient by one depth.
Hastings, arXiv:cond-mat/0508554v3, `proj3new.tex`, lines 1695–1708. -/
theorem recursiveCommutatorCoeff_step {m N t : ℕ} (hm : m ≤ N) {C : ℝ} (hC : 0 ≤ C) :
    recursiveCommutatorCoeff N C t +
      2 * (Real.sqrt ((m : ℝ) ^ 3 * recursiveCommutatorCoeff N C t)) ^ 2 ≤
        recursiveCommutatorCoeff N C (t + 1) := by
  have hCt := recursiveCommutatorCoeff_nonneg N t hC
  rw [Real.sq_sqrt (mul_nonneg (by positivity) hCt)]
  have hmR : (m : ℝ) ≤ N := by exact_mod_cast hm
  have hm3 : (m : ℝ) ^ 3 ≤ (N : ℝ) ^ 3 := pow_le_pow_left₀ (Nat.cast_nonneg _) hmR _
  calc _ = (1 + 2 * (m : ℝ) ^ 3) * recursiveCommutatorCoeff N C t := by ring
    _ ≤ (1 + 2 * (N : ℝ) ^ 3) * recursiveCommutatorCoeff N C t := by gcongr
    _ = _ := by simp only [recursiveCommutatorCoeff, pow_succ]; ring

universe u

set_option backward.isDefEq.respectTransparency false in
/-- The finite-rank induction constructing the basis. The total dimension budget bounds
both the recursion depth and the number of selected original terms. Scalar terminal
subspaces need not have dimension one. Hastings, arXiv:cond-mat/0508554v3,
`proj3new.tex`, lines 1695–1708. -/
theorem exists_orthonormalBasis_uniform_kernel_aux {κ : Type*} [Finite κ]
    (k : κ → κ → ℝ) (hk0 : ∀ i j, 0 ≤ k i j) (hk1 : ∀ i j, k i j ≤ 1)
    (hksymm : ∀ i j, k i j = k j i) (hktri : ∀ i j l, k i j * k j l ≤ k i l)
    (N : ℕ) {C : ℝ} (hC : 0 ≤ C) :
    ∀ (m : ℕ) (E : Type u) [NormedAddCommGroup E] [InnerProductSpace ℂ E]
      [FiniteDimensional ℂ E], Module.finrank ℂ E = m →
      ∀ t : ℕ, t + m ≤ N → ∀ B : κ → E →L[ℂ] E,
        (∀ i, IsSelfAdjoint (B i)) →
        (∀ i j, ‖B i * B j - B j * B i‖ ≤ recursiveCommutatorCoeff N C t * sqrtKernel k t i j) →
        ∃ (b : OrthonormalBasis (Fin m) ℂ E) (s : List κ), s.length ≤ m - 1 ∧
          ∀ i a c, a ≠ c → ‖⟪b a, B i (b c)⟫_ℂ‖ ≤
            recursiveBasisCoeff N C * listKernelSum (sqrtKernel k N) s i := by
  classical
  intro m
  induction m using Nat.strong_induction_on with
  | h m ih =>
    intro E _ _ _ hdim t ht B hB hcomm
    by_cases hm : m ≤ 1
    · let b := (stdOrthonormalBasis ℂ E).reindex (finCongr hdim)
      refine ⟨b, [], by simp, fun i a c hac => ?_⟩
      exact False.elim (hac (Fin.ext (by omega)))
    have hmN : m ≤ N := by omega
    have htN : t ≤ N := by omega
    have hdim' : Module.finrank ℂ E = (m - 1) + 1 := by omega
    have hm' : (m - 1) + 1 = m := by omega
    let Ct := recursiveCommutatorCoeff N C t
    let D := Real.sqrt ((m : ℝ) ^ 3 * Ct)
    have hCt : 0 ≤ Ct := recursiveCommutatorCoeff_nonneg N t hC
    have hD : 0 ≤ D := Real.sqrt_nonneg _
    have hDmax : D ≤ recursiveBasisCoeff N C := sqrt_recursiveCommutatorCoeff_le hmN htN hC
    have hstep : Ct + 2 * D ^ 2 ≤ recursiveCommutatorCoeff N C (t + 1) :=
      recursiveCommutatorCoeff_step hmN hC
    let f := sqrtKernel k t
    have hf0 := sqrtKernel_nonneg hk0 t
    have hf1 := sqrtKernel_le_one hk1 t
    have hfsymm := sqrtKernel_symm hksymm t
    have hftri := sqrtKernel_mul_le hk0 hktri t
    rcases exists_family_spectral_split B hB (by omega : 0 < m - 1) hdim' hCt f hf0
      hfsymm hcomm with hscalar | ⟨P, j, hP, hPn, hQn, hP0, hP1, hcross⟩
    · let b := (stdOrthonormalBasis ℂ E).reindex (finCongr hdim)
      refine ⟨b, [], by simp, fun i a c hac => ?_⟩
      obtain ⟨r, hr⟩ := hscalar i
      simp only [hr, smul_apply, one_apply_eq_self, inner_smul_right,
        b.inner_eq_zero hac, mul_zero, norm_zero, listKernelSum_nil]
      exact le_rfl
    · obtain ⟨K, _, hPK⟩ := isStarProjection_iff_eq_starProjection.mp hP
      subst P
      let : InnerProductSpace ℂ K := K.innerProductSpace
      let : InnerProductSpace ℂ Kᗮ := Kᗮ.innerProductSpace
      let : CompleteSpace K := FiniteDimensional.complete ℂ K
      let : CompleteSpace Kᗮ := FiniteDimensional.complete ℂ Kᗮ
      have hK0 : K ≠ ⊥ := by
        intro h
        exact hP0 (by simp [h])
      have hK1 : K ≠ ⊤ := by
        intro h
        apply hP1
        ext x
        exact K.starProjection_eq_self_iff.mpr (by rw [h]; trivial)
      let p := Module.finrank ℂ K
      let q := Module.finrank ℂ Kᗮ
      have hp : 0 < p := by
        let : Nontrivial K := Submodule.nontrivial_iff_ne_bot.mpr hK0
        exact Module.finrank_pos
      have hq : 0 < q := by
        have hq0 : Kᗮ ≠ ⊥ := fun h => hK1 (K.orthogonal_eq_bot_iff.mp h)
        let : Nontrivial Kᗮ := Submodule.nontrivial_iff_ne_bot.mpr hq0
        exact Module.finrank_pos
      have hpq : p + q = m := K.finrank_add_finrank_orthogonal.trans hdim
      have hpp : p < m := by omega
      have hqq : q < m := by omega
      have hc0 (i : κ) : ‖K.starProjection * B i * (1 - K.starProjection)‖ ≤
          D * Real.sqrt (f i j) := by simpa only [hm'] using (hcross i).1
      have hc1 (i : κ) : ‖(1 - K.starProjection) * B i * K.starProjection‖ ≤
          D * Real.sqrt (f i j) := by simpa only [hm'] using (hcross i).2
      have hPP : K.starProjection * K.starProjection = K.starProjection :=
        hP.isIdempotentElem.eq
      have hQQ : (1 - K.starProjection) * (1 - K.starProjection) = 1 - K.starProjection := by
        noncomm_ring [hPP]
      have hcommL (i l : κ) :
          ‖subspaceCompression K (B i) * subspaceCompression K (B l) -
            subspaceCompression K (B l) * subspaceCompression K (B i)‖ ≤
            recursiveCommutatorCoeff N C (t + 1) * sqrtKernel k (t + 1) i l := by
        rw [norm_subspaceCompression_commutator]
        exact (norm_commutator_compression_le_kernel K.starProjection hPP hPn B hCt hD
          f hf0 hf1 hfsymm hftri j hcomm hc0 hc1 i l).trans
            (mul_le_mul_of_nonneg_right hstep (Real.sqrt_nonneg _))
      have hcommR (i l : κ) :
          ‖subspaceCompression Kᗮ (B i) * subspaceCompression Kᗮ (B l) -
            subspaceCompression Kᗮ (B l) * subspaceCompression Kᗮ (B i)‖ ≤
            recursiveCommutatorCoeff N C (t + 1) * sqrtKernel k (t + 1) i l := by
        rw [norm_subspaceCompression_commutator, K.starProjection_orthogonal']
        have hcQ0 (i : κ) : ‖(1 - K.starProjection) * B i * (1 - (1 - K.starProjection))‖ ≤
            D * Real.sqrt (f i j) := by simpa only [sub_sub_cancel] using hc1 i
        have hcQ1 (i : κ) : ‖(1 - (1 - K.starProjection)) * B i * (1 - K.starProjection)‖ ≤
            D * Real.sqrt (f i j) := by simpa only [sub_sub_cancel] using hc0 i
        exact (norm_commutator_compression_le_kernel (1 - K.starProjection) hQQ hQn B hCt hD
          f hf0 hf1 hfsymm hftri j hcomm hcQ0 hcQ1 i l).trans
            (mul_le_mul_of_nonneg_right hstep (Real.sqrt_nonneg _))
      obtain ⟨u, sL, hsL, hu⟩ := ih p hpp K rfl (t + 1) (by omega)
        (fun i => subspaceCompression K (B i))
        (fun i => isSelfAdjoint_subspaceCompression K (B i) (hB i)) hcommL
      obtain ⟨v, sR, hsR, hv⟩ := ih q hqq Kᗮ rfl (t + 1) (by omega)
        (fun i => subspaceCompression Kᗮ (B i))
        (fun i => isSelfAdjoint_subspaceCompression Kᗮ (B i) (hB i)) hcommR
      obtain ⟨b, hl, hr⟩ := exists_orthonormalBasis_orthogonal_sum K u v
      let e : Fin p ⊕ Fin q ≃ Fin m := Fintype.equivFinOfCardEq (by
        simpa only [Fintype.card_sum, Fintype.card_fin] using hpq)
      refine ⟨b.reindex e, j :: (sL ++ sR), ?_, fun i a c hac => ?_⟩
      · simp only [List.length_cons, List.length_append]
        omega
      · have hnew : ‖K.starProjection * B i * Kᗮ.starProjection‖ ≤
            recursiveBasisCoeff N C * sqrtKernel k N i j := by
          rw [K.starProjection_orthogonal']
          exact (hc0 i).trans (mul_le_mul hDmax
            (sqrtKernel_mono hk0 hk1 i j (by omega : t + 1 ≤ N))
            (Real.sqrt_nonneg _) (recursiveBasisCoeff_nonneg N C))
        have h := norm_inner_le_of_orthogonal_sum K u v b hl hr (B i) (hB i).isSymmetric
          (mul_nonneg (recursiveBasisCoeff_nonneg N C)
            (listKernelSum_nonneg (sqrtKernel_nonneg hk0 N) sL i))
          (mul_nonneg (recursiveBasisCoeff_nonneg N C)
            (listKernelSum_nonneg (sqrtKernel_nonneg hk0 N) sR i))
          (mul_nonneg (recursiveBasisCoeff_nonneg N C) (sqrtKernel_nonneg hk0 N i j))
          (hu i) (hv i) hnew (fun heq => hac (e.symm.injective heq))
        simpa only [OrthonormalBasis.reindex_apply, listKernelSum_cons, listKernelSum_append,
          mul_add, add_comm, add_left_comm, add_assoc] using h

set_option backward.isDefEq.respectTransparency false in
/-- A finite Hermitian family admits an orthonormal basis with uniform
matrix-element decay from at most `n-1` original anchors. The conclusion retains the cross terms
through
successive square roots of the decay kernel. Hastings, arXiv:cond-mat/0508554v3,
`proj3new.tex`, lines 1695–1708. -/
theorem exists_orthonormalBasis_uniform_kernel {κ E : Type*} [Finite κ]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    (B : κ → E →L[ℂ] E) (hB : ∀ i, IsSelfAdjoint (B i)) (k : κ → κ → ℝ)
    (hk0 : ∀ i j, 0 ≤ k i j) (hk1 : ∀ i j, k i j ≤ 1)
    (hksymm : ∀ i j, k i j = k j i) (hktri : ∀ i j l, k i j * k j l ≤ k i l)
    {C : ℝ} (hC : 0 ≤ C) (hcomm : ∀ i j, ‖B i * B j - B j * B i‖ ≤ C * k i j) :
    ∃ (b : OrthonormalBasis (Fin (Module.finrank ℂ E)) ℂ E) (s : List κ),
      s.length ≤ Module.finrank ℂ E - 1 ∧
      ∀ i a c, a ≠ c → ‖⟪b a, B i (b c)⟫_ℂ‖ ≤ recursiveBasisCoeff (Module.finrank ℂ E) C *
        listKernelSum (sqrtKernel k (Module.finrank ℂ E)) s i := by
  exact exists_orthonormalBasis_uniform_kernel_aux k hk0 hk1 hksymm hktri
    (Module.finrank ℂ E) hC (Module.finrank ℂ E) E rfl 0 (by omega) B hB
    (by simpa only [recursiveCommutatorCoeff, pow_zero, mul_one, sqrtKernel_zero] using hcomm)



end ManyBody

namespace ManyBody


section Normalization

variable {E κ : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

omit [CompleteSpace E] in
/-- Normalization by a norm envelope can be undone even for zero terms.
Hastings, arXiv:cond-mat/0508554v3, lines 1698–1708. -/
theorem smul_inv_smul_eq_of_norm_le (B : κ → E →L[ℂ] E) (w : κ → ℝ)
    (hNorm : ∀ i, ‖B i‖ ≤ w i) (i : κ) : w i • ((w i)⁻¹ • B i) = B i := by
  by_cases hi : w i = 0
  · have hBi : B i = 0 := norm_eq_zero.mp
      (((hNorm i).trans_eq hi).antisymm (norm_nonneg _))
    simp [hi, hBi]
  · simp only [smul_smul, mul_inv_cancel₀ hi, one_smul]

omit [CompleteSpace E] in
/-- Weighted commutator decay becomes an unweighted estimate after normalization.
Hastings, arXiv:cond-mat/0508554v3, lines 1698–1708. -/
theorem norm_commutator_inv_smul_le (B : κ → E →L[ℂ] E) (w : κ → ℝ)
    (hw : ∀ i, 0 ≤ w i)
    {C : ℝ} (hC : 0 ≤ C) (f : κ → κ → ℝ) (hf : ∀ i j, 0 ≤ f i j)
    (hcomm : ∀ i j, ‖B i * B j - B j * B i‖ ≤ C * w i * w j * f i j) (i j : κ) :
    ‖((w i)⁻¹ • B i) * ((w j)⁻¹ • B j) -
        ((w j)⁻¹ • B j) * ((w i)⁻¹ • B i)‖ ≤ C * f i j := by
  by_cases hi : w i = 0
  · simp only [hi, inv_zero, zero_smul, zero_mul, mul_zero, sub_self, norm_zero]
    exact mul_nonneg hC (hf i j)
  by_cases hj : w j = 0
  · simp only [hj, inv_zero, zero_smul, zero_mul, mul_zero, sub_self, norm_zero]
    exact mul_nonneg hC (hf i j)
  have hwi : 0 < w i := lt_of_le_of_ne (hw i) (Ne.symm hi)
  have hwj : 0 < w j := lt_of_le_of_ne (hw j) (Ne.symm hj)
  have heq : ((w i)⁻¹ • B i) * ((w j)⁻¹ • B j) -
        ((w j)⁻¹ • B j) * ((w i)⁻¹ • B i) =
      ((w i)⁻¹ * (w j)⁻¹) • (B i * B j - B j * B i) := by
    simp only [smul_mul_assoc, mul_smul_comm, smul_smul,
      mul_comm ((w j)⁻¹) ((w i)⁻¹), smul_sub]
  rw [heq, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (mul_nonneg (inv_nonneg.mpr hwi.le) (inv_nonneg.mpr hwj.le))]
  calc
    _ ≤ ((w i)⁻¹ * (w j)⁻¹) * (C * w i * w j * f i j) :=
      mul_le_mul_of_nonneg_left (hcomm i j) (by positivity)
    _ = _ := by field_simp

/-- Applying the recursive basis theorem after one normalization restores the original
term weights. Hastings, arXiv:cond-mat/0508554v3, lines 1698–1708. -/
theorem exists_orthonormalBasis_uniform_weighted_kernel [FiniteDimensional ℂ E] [Finite κ]
    (B : κ → E →L[ℂ] E) (hB : ∀ i, IsSelfAdjoint (B i))
    (w : κ → ℝ) (hw : ∀ i, 0 ≤ w i) (hNorm : ∀ i, ‖B i‖ ≤ w i)
    (k : κ → κ → ℝ) (hk0 : ∀ i j, 0 ≤ k i j) (hk1 : ∀ i j, k i j ≤ 1)
    (hksymm : ∀ i j, k i j = k j i) (hktri : ∀ i j l, k i j * k j l ≤ k i l)
    {C : ℝ} (hC : 0 ≤ C)
    (hcomm : ∀ i j, ‖B i * B j - B j * B i‖ ≤ C * w i * w j * k i j) :
    ∃ (b : OrthonormalBasis (Fin (Module.finrank ℂ E)) ℂ E) (s : List κ),
      s.length ≤ Module.finrank ℂ E - 1 ∧
      ∀ i a c, a ≠ c → ‖⟪b a, B i (b c)⟫_ℂ‖ ≤
        recursiveBasisCoeff (Module.finrank ℂ E) C * w i *
          listKernelSum (sqrtKernel k (Module.finrank ℂ E)) s i := by
  let _ : Fintype κ := Fintype.ofFinite κ
  let D : κ → E →L[ℂ] E := fun i ↦ (w i)⁻¹ • B i
  have hD (i : κ) : IsSelfAdjoint (D i) := (IsSelfAdjoint.all ((w i)⁻¹)).smul (hB i)
  obtain ⟨b, s, hs, hb⟩ := exists_orthonormalBasis_uniform_kernel D hD k hk0 hk1 hksymm hktri
    hC (norm_commutator_inv_smul_le B w hw hC k hk0 hcomm)
  refine ⟨b, s, hs, fun i a c hac ↦ ?_⟩
  have heq : ‖⟪b a, B i (b c)⟫_ℂ‖ = w i * ‖⟪b a, D i (b c)⟫_ℂ‖ := by
    rw [← smul_inv_smul_eq_of_norm_le B w hNorm i]
    simp only [D, _root_.smul_apply, ← Complex.coe_smul, inner_smul_right, norm_mul,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hw i)]
  rw [heq]
  exact (mul_le_mul_of_nonneg_left (hb i a c hac) (hw i)).trans_eq (by ring)

end Normalization

section AnchorSum

variable {V κ : Type*} [Fintype V] [DecidableEq V] [Fintype κ] {X : V → Type*}
  [∀ v, Fintype (X v)] [∀ v, DecidableEq (X v)]

/-- Each anchor in a finite list contributes one weighted geometric row sum.
Repeated anchors are counted with their multiplicity.
Hastings, arXiv:cond-mat/0508554v3, eq. `oibu`, lines 1689–1708. -/
theorem sum_weight_list_graphDecayKernel_le (G : SimpleGraph V) (a : κ → V)
    (w : κ → ℝ) (hw : ∀ i, 0 ≤ w i) (B : ℝ)
    (hBudget : ∀ x, ∑ i ∈ Finset.univ.filter (fun i ↦ a i = x), w i ≤ B)
    (Kg : ℝ) (kg : ℕ) (hGrowth : ∀ x (r : ℕ),
      ((Finset.univ.filter fun y ↦ G.edist x y = r).card : ℝ) ≤ Kg * ((r : ℝ) + 1) ^ kg)
    {β : ℝ} (hβ : 0 < β) (s : List κ) :
    ∑ i, w i * listKernelSum (fun i j ↦ graphDecayKernel G β (a i) (a j)) s i ≤
      (s.length : ℝ) * (B * (Kg * shellSumConst β kg)) := by
  induction s with
  | nil => simp only [listKernelSum_nil, mul_zero, Finset.sum_const_zero,
      List.length_nil, Nat.cast_zero, zero_mul]; exact le_rfl
  | cons j s ih =>
    have hrow : ∑ i, w i * graphDecayKernel G β (a i) (a j) ≤
        B * (Kg * shellSumConst β kg) := by
      calc
        _ = ∑ i, w i * graphDecayKernel G β (a j) (a i) :=
          Finset.sum_congr rfl fun i _ ↦ by rw [graphDecayKernel_symm]
        _ ≤ _ := sum_weight_mul_exp_neg_edist_le G a w hw B hBudget (a j) Kg kg
          (hGrowth (a j)) hβ
    simp only [listKernelSum_cons, mul_add, Finset.sum_add_distrib, List.length_cons,
      Nat.cast_add, Nat.cast_one]
    exact (add_le_add hrow ih).trans_eq (by ring)

omit [Fintype κ] in
/-- Iterated square roots commute with restriction of a kernel along an anchor map.
Hastings, arXiv:cond-mat/0508554v3, lines 1698–1708. -/
theorem sqrtKernel_comp {α : Type*} (k : α → α → ℝ) (a : κ → α) (n : ℕ) (i j : κ) :
    sqrtKernel (fun i j ↦ k (a i) (a j)) n i j = sqrtKernel k n (a i) (a j) := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [sqrtKernel_succ, ih]

end AnchorSum

noncomputable local instance {ν : Type*} [Fintype ν] [DecidableEq ν]
    (H : Matrix ν ν ℂ) (E₀ : ℝ) : InnerProductSpace ℂ (groundSpace H E₀) :=
  (groundSpace H E₀).innerProductSpace

section Graph

open Matrix
open scoped Matrix.Norms.L2Operator

variable {V : Type*} [Fintype V] [DecidableEq V] {X : V → Type*} [∀ v, Fintype (X v)]
  [∀ v, DecidableEq (X v)] {κ : Type*} [Fintype κ]

set_option backward.isDefEq.respectTransparency false in
/-- **The basis construction from a decaying commutator bound.** Let `M_i` be Hermitian with
`‖M_i‖ ≤ ‖h_i‖`, where the weights `‖h_i‖` obey the support budget `b₀`, and let the ground-space
compressions `B_i = P M_i P` satisfy `‖[B_i, B_j]‖ ≤ C ‖h_i‖ ‖h_j‖ k(a_i, a_j)` for the graph
decay kernel `k` of rate `γ > 0`. Then some orthonormal basis of the ground space bounds the summed
off-diagonal parts of the `P M_i P` by `(n - 1)² c_n(C) |b₀| |K_g| S_{γ/2ⁿ,k}`. This is the
common part of the plain and the truncated basis estimates.
Hastings, arXiv:cond-mat/0508554v3, eq. `oibu` and lines 1698–1708. -/
theorem exists_groundSpaceBasis_sum_norm_offDiagonalPartFamily_le_of_commutator_le
    (G : SimpleGraph V) {T : κ → Finset V} (a : κ → V) (ha : ∀ k, a k ∈ T k)
    (h M : κ → Matrix (Config X) (Config X) ℂ) (hMherm : ∀ k, (M k).IsHermitian)
    (hMnorm : ∀ k, ‖M k‖ ≤ ‖h k‖) (b₀ : ℝ)
    (hBudget : ∀ x, ∑ j ∈ Finset.univ.filter (fun j ↦ x ∈ T j), ‖h j‖ ≤ b₀)
    (Kg : ℝ) (kg : ℕ) (hGrowth : ∀ x (r : ℕ),
      ((Finset.univ.filter fun y ↦ G.edist x y = r).card : ℝ) ≤ Kg * ((r : ℝ) + 1) ^ kg)
    (H : Matrix (Config X) (Config X) ℂ) (E₀ : ℝ) {γ C : ℝ} (hγ : 0 < γ) (hC : 0 ≤ C)
    (hcomm : ∀ i j, ‖groundSpaceCompression H E₀ (M i) * groundSpaceCompression H E₀ (M j) -
        groundSpaceCompression H E₀ (M j) * groundSpaceCompression H E₀ (M i)‖ ≤
      C * ‖h i‖ * ‖h j‖ * graphDecayKernel G γ (a i) (a j))
    [NeZero (Module.finrank ℂ (groundSpace H E₀))] :
    let n := Module.finrank ℂ (groundSpace H E₀)
    ∃ b : OrthonormalBasis (Fin n) ℂ (groundSpace H E₀),
      ∑ i, ‖offDiagonalPartFamily (fun c ↦ (b c : EuclideanSpace ℂ (Config X)))
        (groundCompression H E₀ (M i))‖ ≤
        ((n - 1 : ℕ) : ℝ) ^ 2 * recursiveBasisCoeff n C *
          (|b₀| * (|Kg| * shellSumConst (γ / 2 ^ n) kg)) := by
  classical
  let K := groundSpace H E₀
  let n := Module.finrank ℂ K
  have hGrow : ∀ x (r : ℕ),
      ((Finset.univ.filter fun y ↦ G.edist x y = r).card : ℝ) ≤ |Kg| * ((r : ℝ) + 1) ^ kg :=
    fun x r ↦ (hGrowth x r).trans
      (mul_le_mul_of_nonneg_right (le_abs_self Kg) (by positivity))
  let k := fun i j ↦ graphDecayKernel G γ (a i) (a j)
  have hk0 : ∀ i j, 0 ≤ k i j := fun i j ↦ graphDecayKernel_nonneg G γ (a i) (a j)
  obtain ⟨b, s, hs, hb⟩ := exists_orthonormalBasis_uniform_weighted_kernel
    (fun i ↦ groundSpaceCompression H E₀ (M i))
    (fun i ↦ isSelfAdjoint_groundSpaceCompression _ _ (hMherm i)) (fun i ↦ ‖h i‖)
    (fun i ↦ norm_nonneg _) (fun i ↦ (norm_groundSpaceCompression_le _ _ _).trans (hMnorm i))
    k hk0
    (fun i j ↦ graphDecayKernel_le_one G hγ.le (a i) (a j))
    (fun i j ↦ graphDecayKernel_symm G γ (a i) (a j))
    (fun i j l ↦ graphDecayKernel_mul_le G hγ.le (a i) (a j) (a l)) hC hcomm
  refine ⟨b, ?_⟩
  have hv : Orthonormal ℂ (fun c ↦ (b c : EuclideanSpace ℂ (Config X))) :=
    b.orthonormal.comp_linearIsometry K.subtypeₗᵢ
  have hterm (i : κ) :
      ‖offDiagonalPartFamily (fun c ↦ (b c : EuclideanSpace ℂ (Config X)))
        (groundCompression H E₀ (M i))‖ ≤
      (n - 1 : ℕ) * (recursiveBasisCoeff n C * ‖h i‖ * listKernelSum (sqrtKernel k n) s i) :=
    norm_offDiagonalPartFamily_le hv _
      (mul_nonneg (mul_nonneg (recursiveBasisCoeff_nonneg n C) (norm_nonneg _))
        (listKernelSum_nonneg (sqrtKernel_nonneg hk0 n) s i))
      (fun c e hce ↦ hb i c e hce)
  have hβ : 0 < γ / 2 ^ n := div_pos hγ (pow_pos (by norm_num) n)
  have hBudget' : ∀ x, ∑ i ∈ Finset.univ.filter (fun i ↦ a i = x), ‖h i‖ ≤ |b₀| :=
    fun x ↦ (sum_weight_anchor_le_of_support_budget T a ha
      (fun i ↦ ‖h i‖) (fun i ↦ norm_nonneg _) b₀ hBudget x).trans (le_abs_self b₀)
  have hkpow (i j : κ) : sqrtKernel k n i j =
      graphDecayKernel G (γ / 2 ^ n) (a i) (a j) := by
    rw [show k = (fun i j ↦ graphDecayKernel G γ (a i) (a j)) from rfl,
      sqrtKernel_comp, sqrtKernel_graphDecayKernel]
  have hrow : ∑ i, ‖h i‖ * listKernelSum (sqrtKernel k n) s i ≤
      (s.length : ℝ) * (|b₀| * (|Kg| * shellSumConst (γ / 2 ^ n) kg)) := by
    rw [show sqrtKernel k n = (fun i j ↦ graphDecayKernel G (γ / 2 ^ n) (a i) (a j))
      from funext fun i ↦ funext fun j ↦ hkpow i j]
    exact sum_weight_list_graphDecayKernel_le G a
      (fun i ↦ ‖h i‖) (fun i ↦ norm_nonneg _) |b₀| hBudget' |Kg| kg hGrow hβ s
  have hlen : (s.length : ℝ) ≤ (n - 1 : ℕ) := by exact_mod_cast hs
  have hrow0 : 0 ≤ |b₀| * (|Kg| * shellSumConst (γ / 2 ^ n) kg) :=
    mul_nonneg (abs_nonneg _) (mul_nonneg (abs_nonneg _) (shellSumConst_nonneg hβ kg))
  calc
    _ ≤ ∑ i, (n - 1 : ℕ) *
        (recursiveBasisCoeff n C * ‖h i‖ * listKernelSum (sqrtKernel k n) s i) :=
      Finset.sum_le_sum fun i _ ↦ hterm i
    _ = (n - 1 : ℕ) * recursiveBasisCoeff n C *
        ∑ i, ‖h i‖ * listKernelSum (sqrtKernel k n) s i := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ ≤ (n - 1 : ℕ) * recursiveBasisCoeff n C *
        ((n - 1 : ℕ) * (|b₀| * (|Kg| * shellSumConst (γ / 2 ^ n) kg))) :=
      mul_le_mul_of_nonneg_left (hrow.trans (mul_le_mul_of_nonneg_right hlen hrow0))
        (mul_nonneg (Nat.cast_nonneg _) (recursiveBasisCoeff_nonneg n C))
    _ = _ := by ring

set_option backward.isDefEq.respectTransparency false in
/-- An basis of an arbitrary nonzero finite-dimensional ground space has a
summed off-diagonal bound independent of the number of sites. Its constant depends
only on the ground-space dimension, the local norm budget, interaction geometry and gap.
Hastings, arXiv:cond-mat/0508554v3, eq. `oibu` and lines 1698–1708, with the retained
cross terms and weakened rate recorded in `docs/paper-gaps/hastings05_two_dim_ground_basis.tex`. -/
theorem exists_groundSpaceBasis_sum_norm_offDiagonalPartFamily_le_uniform
    (G : SimpleGraph V) {T : κ → Finset V} (a : κ → V) (ha : ∀ k, a k ∈ T k)
    (Φ : Interaction X T) (hHerm : ∀ k, (Φ.term k).IsHermitian)
    (R : ℕ) (hDiam : ∀ k, ∀ x ∈ T k, ∀ z ∈ T k, G.edist x z ≤ R)
    (vR : ℕ) (hCard : ∀ k, (T k).card ≤ vR) (b₀ : ℝ)
    (hBudget : ∀ x, ∑ j ∈ Finset.univ.filter (fun j ↦ x ∈ T j), ‖Φ.term j‖ ≤ b₀)
    (Kg : ℝ) (kg : ℕ) (hGrowth : ∀ x (r : ℕ),
      ((Finset.univ.filter fun y ↦ G.edist x y = r).card : ℝ) ≤ Kg * ((r : ℝ) + 1) ^ kg)
    {q ΔE : ℝ} (hq : 0 ≤ q) (hΔE : 0 < ΔE) {E₀ : ℝ}
    (hgap : IsGapped Φ.hamiltonian E₀ ΔE)
    [NeZero (Module.finrank ℂ (groundSpace Φ.hamiltonian E₀))] :
    let n := Module.finrank ℂ (groundSpace Φ.hamiltonian E₀)
    let γ := commutatorRate R vR b₀ ΔE
    let C := commutatorConst R vR b₀ |Kg| kg * Real.exp (γ * (2 * R + 1))
    ∃ b : OrthonormalBasis (Fin n) ℂ (groundSpace Φ.hamiltonian E₀),
      ∑ i, ‖offDiagonalPartFamily (fun c ↦ (b c : EuclideanSpace ℂ (Config X)))
        (groundCompression Φ.hamiltonian E₀ (gaussianFilteredTerm q ΔE Φ.hamiltonian (Φ.term i)))‖ ≤
        ((n - 1 : ℕ) : ℝ) ^ 2 * recursiveBasisCoeff n C *
          (|b₀| * (|Kg| * shellSumConst (γ / 2 ^ n) kg)) := by
  have hH : Φ.hamiltonian.IsHermitian := Interaction.isHermitian_hamiltonian hHerm
  have hgapE := ((isGapped_iff_eigenvalues hH).mp hgap).2
  classical
  let γ := commutatorRate R vR b₀ ΔE
  have hγ : 0 < γ := commutatorRate_pos hΔE R vR b₀
  let C := commutatorConst R vR b₀ |Kg| kg * Real.exp (γ * (2 * R + 1))
  have hC : 0 ≤ C := mul_nonneg
    (le_trans (by norm_num) (six_le_commutatorConst R vR b₀ (abs_nonneg Kg) kg))
    (Real.exp_pos _).le
  have hGrow : ∀ x (r : ℕ),
      ((Finset.univ.filter fun y ↦ G.edist x y = r).card : ℝ) ≤ |Kg| * ((r : ℝ) + 1) ^ kg :=
    fun x r ↦ (hGrowth x r).trans
      (mul_le_mul_of_nonneg_right (le_abs_self Kg) (by positivity))
  simp only [groundCompression_gaussianFilteredTerm hq hH]
  exact exists_groundSpaceBasis_sum_norm_offDiagonalPartFamily_le_of_commutator_le G a ha Φ.term
    Φ.term
    hHerm (fun _ ↦ le_rfl) b₀ hBudget Kg kg hGrowth _ E₀ hγ hC fun i j ↦
      (norm_groundSpaceCompression_commutator_le _ _ _ _).trans
        (norm_groundCompression_commutator_le_exp_edist G a ha Φ hHerm R hDiam vR
          hCard b₀ hBudget |Kg| kg hGrow hΔE hgap j i)

end Graph

end ManyBody
