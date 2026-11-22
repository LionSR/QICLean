/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.RCLike.Lemmas
import Mathlib.Analysis.InnerProductSpace.JointEigenspace
import QICLean.Spectral.LowEnergy.Basis.SpectralSplit

/-!
# A recursive basis with decaying matrix elements

Hastings, arXiv:cond-mat/0508554v3, `proj3new.tex`, lines 1695–1708, refines a basis by repeated
spectral splits. For a finite family of self-adjoint operators whose commutators are bounded by
a decay kernel, this gives a basis whose off-diagonal entries are bounded by iterated square
roots of the kernel.

* `sqrtKernel`, `listKernelSum`, `graphDecayKernel`: the kernels and their sums along a list of
  anchors.
* `recursiveCommutatorCoeff`, `recursiveBasisCoeff`, `exists_orthonormalBasis_uniform_kernel`.
* `exists_orthonormalBasis_uniform_weighted_kernel`: the same with weights normalized away.

Moved from TNLean (`e113e005`): `TNLean/Lattice/LowEnergyBasisRecursive.lean`,
`LowEnergyDecayKernel.lean` and the site-free part of `LowEnergyBasisUniformGeneral.lean`.
Changes: namespace `LowEnergyBasis`.
-/

noncomputable section

open scoped InnerProductSpace

namespace LowEnergyBasis

/-- Finite-dimensional complex inner product spaces are complete. -/
local instance completeSpace_of_finiteDimensional {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [FiniteDimensional ℂ E] : CompleteSpace E :=
  FiniteDimensional.complete ℂ E

section DecayKernel

variable {V : Type*}

/-- Successive square roots of a decay kernel. Hastings, arXiv:cond-mat/0508554v3,
`proj3new.tex`, lines 1695–1708, with the cross terms retained. -/
noncomputable def sqrtKernel (k : V → V → ℝ) : ℕ → V → V → ℝ
  | 0 => k
  | n + 1 => fun i j => Real.sqrt (sqrtKernel k n i j)

@[simp]
theorem sqrtKernel_zero (k : V → V → ℝ) (i j : V) : sqrtKernel k 0 i j = k i j := rfl

@[simp]
theorem sqrtKernel_succ (k : V → V → ℝ) (n : ℕ) (i j : V) :
    sqrtKernel k (n + 1) i j = Real.sqrt (sqrtKernel k n i j) := rfl

theorem sqrtKernel_nonneg {k : V → V → ℝ} (hk : ∀ i j, 0 ≤ k i j) :
    ∀ n i j, 0 ≤ sqrtKernel k n i j
  | 0, i, j => hk i j
  | _ + 1, _, _ => Real.sqrt_nonneg _

theorem sqrtKernel_le_one {k : V → V → ℝ} (hk : ∀ i j, k i j ≤ 1) :
    ∀ n i j, sqrtKernel k n i j ≤ 1
  | 0, i, j => hk i j
  | n + 1, i, j => Real.sqrt_le_one.mpr (sqrtKernel_le_one hk n i j)

theorem sqrtKernel_symm {k : V → V → ℝ} (hk : ∀ i j, k i j = k j i) :
    ∀ n i j, sqrtKernel k n i j = sqrtKernel k n j i
  | 0, i, j => hk i j
  | n + 1, i, j => congrArg Real.sqrt (sqrtKernel_symm hk n i j)

theorem sqrtKernel_succ_sq {k : V → V → ℝ} (hk : ∀ i j, 0 ≤ k i j) (n : ℕ) (i j : V) :
    sqrtKernel k (n + 1) i j ^ 2 = sqrtKernel k n i j :=
  Real.sq_sqrt (sqrtKernel_nonneg hk n i j)

theorem sqrtKernel_mono {k : V → V → ℝ} (hk0 : ∀ i j, 0 ≤ k i j)
    (hk1 : ∀ i j, k i j ≤ 1) (i j : V) : Monotone fun n => sqrtKernel k n i j := by
  apply monotone_nat_of_le_succ
  intro n
  rw [sqrtKernel_succ]
  apply Real.le_sqrt_of_sq_le
  have h0 := sqrtKernel_nonneg hk0 n i j
  have h1 := sqrtKernel_le_one hk1 n i j
  nlinarith

/-- The multiplicative triangle inequality persists under taking square roots. Hastings,
arXiv:cond-mat/0508554v3, `proj3new.tex`, lines 1695–1708. -/
theorem sqrtKernel_mul_le {k : V → V → ℝ} (hk0 : ∀ i j, 0 ≤ k i j)
    (hmul : ∀ i j l, k i j * k j l ≤ k i l) :
    ∀ n i j l, sqrtKernel k n i j * sqrtKernel k n j l ≤ sqrtKernel k n i l
  | 0, i, j, l => hmul i j l
  | n + 1, i, j, l => by
      rw [sqrtKernel_succ, sqrtKernel_succ, sqrtKernel_succ,
        ← Real.sqrt_mul (sqrtKernel_nonneg hk0 n i j)]
      exact Real.sqrt_le_sqrt (sqrtKernel_mul_le hk0 hmul n i j l)

/-- The sum of a kernel over a finite list of selected terms, allowing repeated selections
at different spectral splits. Hastings, arXiv:cond-mat/0508554v3, `proj3new.tex`,
lines 1695–1708. -/
def listKernelSum (k : V → V → ℝ) (s : List V) (i : V) : ℝ := (s.map (k i)).sum

@[simp]
theorem listKernelSum_nil (k : V → V → ℝ) (i : V) : listKernelSum k [] i = 0 := rfl

@[simp]
theorem listKernelSum_cons (k : V → V → ℝ) (j : V) (s : List V) (i : V) :
    listKernelSum k (j :: s) i = k i j + listKernelSum k s i := rfl

@[simp]
theorem listKernelSum_append (k : V → V → ℝ) (s t : List V) (i : V) :
    listKernelSum k (s ++ t) i = listKernelSum k s i + listKernelSum k t i := by
  simp only [listKernelSum, List.map_append, List.sum_append]

theorem listKernelSum_nonneg {k : V → V → ℝ} (hk : ∀ i j, 0 ≤ k i j)
    (s : List V) (i : V) : 0 ≤ listKernelSum k s i := by
  induction s with
  | nil => exact le_rfl
  | cons j s hs => exact add_nonneg (hk i j) hs

/-- Exponential graph decay, set to zero between disconnected components. Hastings,
arXiv:cond-mat/0508554v3, `proj3new.tex`, eq. `blecm` and lines 1689–1708. -/
noncomputable def graphDecayKernel (G : SimpleGraph V) (γ : ℝ) (i j : V) : ℝ :=
  if G.edist i j = ⊤ then 0 else Real.exp (-(γ * ((G.edist i j).toNat : ℝ)))

theorem graphDecayKernel_nonneg (G : SimpleGraph V) (γ : ℝ) (i j : V) :
    0 ≤ graphDecayKernel G γ i j := by
  unfold graphDecayKernel
  split_ifs <;> positivity

theorem graphDecayKernel_le_one (G : SimpleGraph V) {γ : ℝ} (hγ : 0 ≤ γ) (i j : V) :
    graphDecayKernel G γ i j ≤ 1 := by
  unfold graphDecayKernel
  split_ifs
  · norm_num
  · exact Real.exp_le_one_iff.mpr
      (neg_nonpos.mpr (mul_nonneg hγ (Nat.cast_nonneg _)))

theorem graphDecayKernel_symm (G : SimpleGraph V) (γ : ℝ) (i j : V) :
    graphDecayKernel G γ i j = graphDecayKernel G γ j i := by
  simp only [graphDecayKernel, G.edist_comm (u := i) (v := j)]

/-- The graph triangle inequality in multiplicative form, including infinite distances.
Hastings, arXiv:cond-mat/0508554v3, `proj3new.tex`, lines 1695–1708. -/
theorem graphDecayKernel_mul_le (G : SimpleGraph V) {γ : ℝ} (hγ : 0 ≤ γ) (i j l : V) :
    graphDecayKernel G γ i j * graphDecayKernel G γ j l ≤ graphDecayKernel G γ i l := by
  classical
  by_cases hij : G.edist i j = ⊤
  · simpa only [graphDecayKernel, hij, ↓reduceIte, zero_mul] using
      graphDecayKernel_nonneg G γ i l
  by_cases hjl : G.edist j l = ⊤
  · simpa only [graphDecayKernel, hjl, ↓reduceIte, mul_zero] using
      graphDecayKernel_nonneg G γ i l
  have hsum : G.edist i j + G.edist j l ≠ ⊤ := by simp [hij, hjl]
  have htri := G.edist_triangle (u := i) (v := j) (w := l)
  have hil : G.edist i l ≠ ⊤ := fun h => hsum (top_le_iff.mp (h ▸ htri))
  have hnat := ENat.toNat_le_toNat htri hsum
  rw [ENat.toNat_add hij hjl] at hnat
  have hreal : ((G.edist i l).toNat : ℝ) ≤
      ((G.edist i j).toNat : ℝ) + ((G.edist j l).toNat : ℝ) := by exact_mod_cast hnat
  simp only [graphDecayKernel, hij, hjl, hil, ↓reduceIte]
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  nlinarith [mul_le_mul_of_nonneg_left hreal hγ]

/-- Taking square roots `n` times divides the graph exponential rate by `2^n`.
Hastings, arXiv:cond-mat/0508554v3, `proj3new.tex`, lines 1695–1708, with the
cross terms of each spectral refinement retained. -/
theorem sqrtKernel_graphDecayKernel (G : SimpleGraph V) (γ : ℝ) (n : ℕ) (i j : V) :
    sqrtKernel (graphDecayKernel G γ) n i j = graphDecayKernel G (γ / 2 ^ n) i j := by
  induction n with
  | zero => simp only [sqrtKernel_zero, pow_zero, div_one]
  | succ n ih =>
    rw [sqrtKernel_succ, ih]
    unfold graphDecayKernel
    split_ifs
    · simp
    · rw [← Real.exp_half]
      congr 1
      rw [pow_succ]
      ring


end DecayKernel

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



section AnchorMap

variable {κ : Type*}

/-- Iterated square roots commute with restriction of a kernel along an anchor map.
Hastings, arXiv:cond-mat/0508554v3, lines 1698–1708. -/
theorem sqrtKernel_comp {α : Type*} (k : α → α → ℝ) (a : κ → α) (n : ℕ) (i j : κ) :
    sqrtKernel (fun i j ↦ k (a i) (a j)) n i j = sqrtKernel k n (a i) (a j) := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [sqrtKernel_succ, ih]


end AnchorMap

end LowEnergyBasis
