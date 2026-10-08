/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Representation.ReplicaTransport.RelativePinBound
import QICLean.Representation.ReplicaEtaForms

/-!
# The skew bound at a split leaf, and the transport estimate

The transport estimate (Proposition 7.4 of the area-law paper, *A two-dimensional area law
from a global spectral gap*, `06-transport.tex`, lines 377–434) uses the skew bound of
Lemma 6.4 (`lem:symbol`, display `replicas:skew-bound`, `05-replicas.tex`, lines 640–660) at a
split leaf: a positive contraction `h` whose designated support `D` meets the middle part `Y`
and exactly one outer part (`06-transport.tex`, lines 735–748). This file proves that
specialization, `TensorPower.ReplicaTransport.SplitSkewBound`, from
`TensorPower.SkewPartition.eventually_re_trace_skewOperator_le_regionalMovementEta` and its
variant with the outer parts exchanged, and hence states Proposition 7.4 without replica
hypotheses.

The comparison has three parts.

* The operator `h` is supported on `D = P₀ ∪ x`, with `P₀ = D ∩ P` and `x = D ∩ Y` for a split
  towards `P`, so it is `lift_{P₀ x} K` with `0 ≤ K ≤ 1`, and `d_h = (dim P₀)(dim x) = dim D`.
* The skew operator of Lemma 6.4 takes its absolute values on `𝒮_k`. For a matrix `Z`
  commuting with the projection `Π` onto `𝒮_k`, `√(Π Z^† Z)` and `√(Z^† Z)` agree after
  multiplication by `Π`, so the two skew operators have the same expectation in every density
  matrix on `𝒮_k`.
* The entropy of Lemma 6.4 in region form, `S_θ(x|P) + S_θ(x|Y \ x)`, is the split entropy
  `I_θ(x:F|P)` (`06-transport.tex`, display `transport:move-eta`).

Lemma 6.4 is stated with an arbitrary `ε > 0` for all large `k`; the remainder `r_k → 0` is
the supremum of the excess over symmetric density matrices, which is finite for each `k`.

The proofs are written from the paper; no Lean source was adapted.

## Main declarations

* `TensorPower.re_coherentIntegral_ofReal` — the complex and real coherent integrals agree.
* `TensorPower.mul_skewOperator_eq_mul_skewSquare` — the two skew operators agree on `𝒮_k`.
* `TensorPower.ReplicaTransport.splitSkewBound` — `SplitSkewBound` holds.
* `TensorPower.ReplicaTransport.transport` — Proposition 7.4.
-/

open scoped Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator Kronecker
open Matrix Set Filter Topology MeasureTheory PermutationRepresentation Entropy

noncomputable section

universe u

namespace TensorPower

section Coherent

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω] {k : ℕ}

/-- For a positive semidefinite `σ` and a real function `f`, the real part of the coherent
integral `∫ f dμ_σ` is the real coherent integral. -/
theorem re_coherentIntegral_ofReal (a : Ω) {σ : Matrix (Fin k → Ω) (Fin k → Ω) ℂ}
    (hσ : σ.PosSemidef) (f : (Ω → ℂ) → ℝ) :
    (coherentIntegral a σ fun θ => (f θ : ℂ)).re = realCoherentIntegral k a σ f := by
  set θ : unitaryGroup Ω ℂ → Ω → ℂ := fun U => (U : Matrix Ω Ω ℂ) *ᵥ Pi.single a 1
  have hreal : ∀ U, (σ * coherentProj k (θ U)).trace =
      (((σ * coherentProj k (θ U)).trace.re : ℝ) : ℂ) := fun U => by
    have h0 : 0 ≤ (σ * coherentProj k (θ U)).trace := by
      rw [coherentProj, mul_vecMulVec, trace_vecMulVec, dotProduct_comm]
      exact hσ.dotProduct_mulVec_nonneg _
    exact Complex.ext rfl (by simp [((Complex.nonneg_iff.mp h0).2).symm])
  have hint : (fun U => (σ * coherentProj k (θ U)).trace * (f (θ U) : ℂ)) =
      fun U => ((f (θ U) * (σ * coherentProj k (θ U)).trace.re : ℝ) : ℂ) := funext fun U => by
    conv_lhs => rw [hreal U]
    push_cast; ring
  unfold coherentIntegral realCoherentIntegral
  change ((symProj (copyPerm Ω k)).trace *
    ∫ U, (σ * coherentProj k (θ U)).trace * (f (θ U) : ℂ) ∂(unitaryHaar Ω)).re = _
  rw [hint, integral_complex_ofReal, trace_symProj, ← Complex.ofReal_natCast,
    ← Complex.ofReal_mul, Complex.ofReal_re]

/-- **The two skew operators agree on `𝒮_k`.** For a positive definite `L` and a matrix `X`,
both commuting with the projection `Π` onto `𝒮_k`, and a Hermitian `ρ = Π ρ`, the skew
operator of the similarity transform `(√L)⁻¹ X √L`, with absolute values taken on `𝒮_k`
(`05-replicas.tex`, line 627), and the skew square of `L^{-1/2} X L^{1/2}`
(`06-transport.tex`, display `transport:skew-square`) agree after multiplication by `ρ`. -/
theorem mul_skewOperator_eq_mul_skewSquare {L X ρ : Matrix (Fin k → Ω) (Fin k → Ω) ℂ}
    (hL : L.PosDef) (hPL : Commute (symProj (copyPerm Ω k)) L)
    (hPX : Commute (symProj (copyPerm Ω k)) X) (hρ : ρ.IsHermitian)
    (hPρ : symProj (copyPerm Ω k) * ρ = ρ) :
    ρ * skewOperator k ((CFC.sqrt L)⁻¹ * X * CFC.sqrt L) =
      ρ * Transport.skewSquare L X := by
  set P := symProj (copyPerm Ω k)
  have hP : P.IsHermitian := isHermitian_symProj
  have hρP : ρ * P = ρ := by
    have := congrArg conjTranspose hPρ
    rwa [conjTranspose_mul, hP.eq, hρ.eq] at this
  rw [← ReplicaTransport.rpow_neg_half_eq_inv_sqrt hL, CFC.sqrt_eq_rpow]
  have hPr : ∀ r : ℝ, Commute P (L ^ r) := fun r => by
    rw [CFC.rpow_def]; exact (Commute.cfc_nnreal hPL.symm _).symm
  set O := L ^ (-(1 / 2) : ℝ) * X * L ^ (1 / 2 : ℝ)
  have hPO : Commute P O := ((hPr _).mul_right hPX).mul_right (hPr _)
  have hPOh : Commute P Oᴴ := by
    have := congrArg conjTranspose hPO.eq
    rw [conjTranspose_mul P O, conjTranspose_mul O P, hP.eq] at this
    exact this.symm
  have key : ∀ Z : Matrix (Fin k → Ω) (Fin k → Ω) ℂ, Z.PosSemidef → Commute P Z →
      ρ * cfc Real.sqrt (P * Z) = ρ * CFC.sqrt Z := fun Z hZ hPZ => by
    have hY : (P * Z).IsHermitian := by
      rw [IsHermitian, conjTranspose_mul, hP.eq, hZ.isHermitian.eq, hPZ.eq]
    have e := mul_cfc_eq_mul_cfc_of_mul_eq hY hZ.isHermitian hPZ
      (by rw [← Matrix.mul_assoc, symProj_mul_symProj]) Real.sqrt
    calc ρ * cfc Real.sqrt (P * Z) = ρ * P * cfc Real.sqrt (P * Z) := by rw [hρP]
      _ = ρ * P * cfc Real.sqrt Z := by rw [Matrix.mul_assoc, e, ← Matrix.mul_assoc]
      _ = ρ * CFC.sqrt Z := by
        rw [hρP, CFC.sqrt_eq_real_sqrt Z hZ.nonneg, cfcₙ_eq_cfc]
  simp only [skewOperator, Transport.skewSquare]
  rw [Matrix.mul_sub, Matrix.mul_sub, Matrix.mul_add,
    key _ (posSemidef_conjTranspose_mul_self O) (hPOh.mul_right hPO),
    key _ (posSemidef_self_mul_conjTranspose O) (hPO.mul_right hPOh), Matrix.mul_sub,
    Matrix.mul_sub, Matrix.mul_add, add_comm (ρ * CFC.sqrt (Oᴴ * O))]

end Coherent

end TensorPower

namespace TensorPower.ReplicaTransport

variable {V : Type*} [Fintype V] [DecidableEq V] {n : V → ℕ}

/-- A positive semidefinite local lift `K ⊗ 1` has a positive semidefinite factor `K`. -/
theorem posSemidef_of_localLift [∀ v, NeZero (n v)] {Q : Finset V}
    {K : Matrix (RegionConfig n Q) (RegionConfig n Q) ℂ} (h : (localLift Q K).PosSemidef) :
    K.PosSemidef := by
  have h1 : (K ⊗ₖ (1 : Matrix ((v : {v // v ∉ Q}) → Fin (n v))
      ((v : {v // v ∉ Q}) → Fin (n v)) ℂ)).PosSemidef := by
    have := h.submatrix (cutEquiv n Q).symm
    simpa [localLift, reindex_apply, submatrix_submatrix] using this
  have e : K = (K ⊗ₖ (1 : Matrix ((v : {v // v ∉ Q}) → Fin (n v))
      ((v : {v // v ∉ Q}) → Fin (n v)) ℂ)).submatrix (fun x => (x, fun _ => 0))
        (fun x => (x, fun _ => 0)) := by
    ext x x'
    simp
  rw [e]
  exact h1.submatrix _

/-- `1 - lift_Q K = lift_Q (1 - K)`. -/
theorem one_sub_localLift {Q : Finset V} (K : Matrix (RegionConfig n Q) (RegionConfig n Q) ℂ) :
    1 - localLift Q K = localLift Q (1 - K) := by
  rw [sub_eq_add_neg, sub_eq_add_neg, localLift_add, ← neg_one_smul ℂ K, localLift_smul,
    localLift_one, neg_one_smul]

omit [Fintype V] in
/-- The cardinality of the configurations of a region is the product of its site
dimensions. -/
theorem card_regionConfig (Q : Finset V) :
    (Fintype.card (RegionConfig n Q) : ℝ) = ∏ v ∈ Q, (n v : ℝ) := by
  rw [Fintype.card_pi]
  push_cast
  simp only [Fintype.card_fin]
  rw [Finset.prod_coe_sort Q fun v => (n v : ℝ)]

omit [Fintype V] in
/-- `log(e (dim A)(dim B)) = log(e dim (A ∪ B))` for disjoint regions. -/
theorem log_exp_mul_card_mul_card {A B : Finset V} (hAB : Disjoint A B) :
    Real.log (Real.exp 1 * (Fintype.card (RegionConfig n A) * Fintype.card (RegionConfig n B))) =
      logDim n (A ∪ B) := by
  rw [card_regionConfig, card_regionConfig, ← Finset.prod_union hAB, logDim]

/-- **Uniform remainders.** If, for every `ε > 0`, eventually `f_k ≤ ε` uniformly, and each
`f_k` is bounded above, then `f_k ≤ r_k` for a sequence `r_k → 0`. -/
theorem exists_tendsto_zero_forall_le {S : ℕ → Type*} (f : ∀ k, S k → ℝ)
    (hb : ∀ k, ∃ B, ∀ s, f k s ≤ B) (h : ∀ ε > 0, ∀ᶠ k in atTop, ∀ s, f k s ≤ ε) :
    ∃ r : ℕ → ℝ, Tendsto r atTop (𝓝 0) ∧ ∀ k s, f k s ≤ r k := by
  refine ⟨fun k => max (⨆ s, f k s) 0, ?_, fun k s => ?_⟩
  · rw [tendsto_order]
    refine ⟨fun a ha => Eventually.of_forall fun k => ha.trans_le (le_max_right _ _),
      fun a ha => ?_⟩
    filter_upwards [h (a / 2) (by linarith)] with k hk
    exact (max_le (Real.iSup_le hk (by linarith)) (by linarith)).trans_lt (by linarith)
  · obtain ⟨B, hB⟩ := hb k
    exact (le_ciSup ⟨B, by rintro _ ⟨s, rfl⟩; exact hB s⟩ s).trans (le_max_left _ _)

theorem skewConst_nonneg : 0 ≤ Entropy.ConditionalSkew.skewConst := by
  unfold Entropy.ConditionalSkew.skewConst
  positivity

/-- The coherent projection onto `𝒮_k` commutes with the copy mean. -/
theorem commute_symProj_copyMean (k : ℕ) (h : Matrix (SiteConfig n) (SiteConfig n) ℂ) :
    Commute (symProj (copyPerm (SiteConfig n) k)) (copyMean n k h) :=
  commute_symProj_of_forall_commute_permOp fun s => commute_copyPerm_copyMean k h s

/-- A matrix fixed by `Π` on the left is fixed by every copy permutation. -/
theorem permOp_mul_of_symProj_mul {k : ℕ}
    {ρ : Matrix (Config k fun v => Fin (n v)) (Config k fun v => Fin (n v)) ℂ}
    (hρ : symProj (copyPerm (SiteConfig n) k) * ρ = ρ) (s : Equiv.Perm (Fin k)) :
    permOp (copyPerm (SiteConfig n) k) s * ρ = ρ := by
  rw [← hρ, ← Matrix.mul_assoc, permOp_mul_symProj]

/-- **One split, for all large `k`** (`06-transport.tex`, lines 735–748, from
`05-replicas.tex`, lines 640–660): the bound of `SplitSkewBound` with an additive `ε`. -/
theorem eventually_re_trace_skewSquare_le [∀ v, NeZero (n v)] {π : PYF V}
    (hπ : π.IsPartition) {D : Finset V} {h : Matrix (SiteConfig n) (SiteConfig n) ℂ}
    (h0 : 0 ≤ h) (h1 : h ≤ 1) (hh : IsSupportedOn h D)
    (hsplit : π.SplitsToP D ∨ π.SplitsToF D) {t : ℝ} (ht0 : 0 < t)
    (hsmall : 2 * t * logDim n D ≤ 1 / 8) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ k in atTop, ∀ ρ : Matrix (Config k fun v => Fin (n v)) (Config k fun v => Fin (n v)) ℂ,
      ρ.PosSemidef → ρ.trace = 1 → symProj (copyPerm (SiteConfig n) k) * ρ = ρ →
      (ρ * Transport.skewSquare (bandMetric n t k π) (copyMean n k h)).trace.re ≤
        2 * Entropy.ConditionalSkew.skewConst * (2 * t) ^ 2 * logDim n D ^ (4 : ℝ) *
          realCoherentIntegral k (TransportData.base n) ρ (fun θ =>
            splitBandEta n π D ((EuclideanSpace.equiv _ ℂ).symm θ) ^ (1 / 8 : ℝ)) + ε := by
  classical
  obtain ⟨hPY, hPF, hYF, hcov⟩ := hπ
  set x := D ∩ π.Y with hxdef
  have hx : x ⊆ π.Y := Finset.inter_subset_right
  have h4 := fourPartition_of_isPartition ⟨hPY, hPF, hYF, hcov⟩ hx
  have hY : x ∪ (π.Y \ x) = π.Y := Finset.union_sdiff_of_subset hx
  have hmem : ∀ v, v ∈ π.P ∨ v ∈ π.Y ∨ v ∈ π.F := fun v => by
    have hv : v ∈ π.P ∪ π.Y ∪ π.F := hcov ▸ Finset.mem_univ v
    simp only [Finset.mem_union] at hv
    tauto
  have ha : (0 : ℝ) < 2 * t := by positivity
  have ht2 : 2 * t / 2 = t := by ring
  have hL : ∀ k, (bandMetric n t k π).PosDef := fun k =>
    posDef_bandMetric ⟨hPY, hPF, hYF, hcov⟩ ht0.le k
  -- the comparison of the two skew operators and of the two coherent integrals
  have hcmp : ∀ (k : ℕ) (ρ : Matrix (Config k fun v => Fin (n v))
      (Config k fun v => Fin (n v)) ℂ), ρ.PosSemidef → symProj (copyPerm (SiteConfig n) k) * ρ = ρ →
      ((ρ * skewOperator k (markedSimilarity n t k π.P π.Y π.F h)).trace).re =
        (ρ * Transport.skewSquare (bandMetric n t k π) (copyMean n k h)).trace.re := by
    intro k ρ hρ hsym
    rw [markedSimilarity, show leafMetric n t k π.P π.Y π.F = bandMetric n t k π from rfl,
      mul_skewOperator_eq_mul_skewSquare (hL k) (commute_symProj_bandMetric t k π)
        (commute_symProj_copyMean k h) hρ.isHermitian hsym]
  rcases hsplit with hsp | hsp
  · -- a split towards `P`
    set P₀ := π.P ∩ D
    set P₁ := π.P \ D
    have hP : P₀ ∪ P₁ = π.P := by rw [Finset.union_comm]; exact Finset.sdiff_union_inter π.P D
    have hsk : SkewPartition P₀ P₁ x (π.Y \ x) π.F :=
      ⟨(Finset.disjoint_sdiff_inter π.P D).symm, Finset.disjoint_sdiff, by rw [hP, hY]; exact hPY,
        by rw [hP]; exact hPF, by rw [hY]; exact hYF, fun v => by rw [hP, hY]; exact hmem v⟩
    have hDsub : D ⊆ P₀ ∪ x := fun v hv => by
      rcases hmem v with h' | h' | h'
      · exact Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨h', hv⟩)
      · exact Finset.mem_union_right _ (Finset.mem_inter.mpr ⟨hv, h'⟩)
      · exact absurd h' (Finset.disjoint_left.mp hsp.2.2 hv)
    have hDeq : P₀ ∪ x = D := Finset.Subset.antisymm
      (Finset.union_subset Finset.inter_subset_right Finset.inter_subset_left) hDsub
    have hP₀x : Disjoint P₀ x :=
      Finset.disjoint_of_subset_left Finset.inter_subset_left (h4.Px)
    obtain ⟨K, rfl⟩ := (hh.mono hDsub).exists_localLift (fun _ => 0)
    have hK0 : 0 ≤ K := Matrix.nonneg_iff_posSemidef.mpr
      (posSemidef_of_localLift (Matrix.nonneg_iff_posSemidef.mp h0))
    have hK1 : K ≤ 1 := by
      rw [Matrix.le_iff] at h1 ⊢
      rw [one_sub_localLift] at h1
      exact posSemidef_of_localLift h1
    have hlog : Real.log (Real.exp 1 * (Fintype.card (RegionConfig n P₀) *
        Fintype.card (RegionConfig n x))) = logDim n D := by
      rw [log_exp_mul_card_mul_card hP₀x, hDeq]
    have hev := hsk.eventually_re_trace_skewOperator_le_regionalMovementEta hK0 hK1 ha
      (by rw [hlog]; exact hsmall) hε
    filter_upwards [hev] with k hk ρ hρ htr hsym
    have hb := hk (TransportData.base n) ρ hρ htr (permOp_mul_of_symProj_mul hsym)
    rw [ht2, hP, hY, hcmp k ρ hρ hsym, hlog, re_coherentIntegral_ofReal _ hρ] at hb
    have hf : (fun θ : SiteConfig n → ℂ =>
        regionalMovementEta π.P x (π.Y \ x) (WithLp.toLp 2 θ) ^ (1 / 8 : ℝ)) =
        fun θ => splitBandEta n π D ((EuclideanSpace.equiv _ ℂ).symm θ) ^ (1 / 8 : ℝ) :=
      funext fun θ => by
        rw [regionalMovementEta_eq_cmi_left h4]
        simp only [splitBandEta, hsp, ↓reduceIte, x]
        rfl
    rw [hf, ← Real.rpow_natCast] at hb
    exact_mod_cast hb
  · -- a split towards `F`: exchange the outer parts
    have hnP : ¬ π.SplitsToP D := fun h' => by
      obtain ⟨v, hv⟩ := hsp.2.1
      exact Finset.disjoint_left.mp h'.2.2 (Finset.mem_inter.mp hv).1 (Finset.mem_inter.mp hv).2
    set P₀ := π.F ∩ D
    set P₁ := π.F \ D
    have hP : P₀ ∪ P₁ = π.F := by rw [Finset.union_comm]; exact Finset.sdiff_union_inter π.F D
    have hsk : SkewPartition P₀ P₁ x (π.Y \ x) π.P :=
      ⟨(Finset.disjoint_sdiff_inter π.F D).symm, Finset.disjoint_sdiff,
        by rw [hP, hY]; exact hYF.symm, by rw [hP]; exact hPF.symm, by rw [hY]; exact hPY.symm,
        fun v => by rw [hP, hY]; rcases hmem v with h' | h' | h' <;> tauto⟩
    have hDsub : D ⊆ P₀ ∪ x := fun v hv => by
      rcases hmem v with h' | h' | h'
      · exact absurd h' (Finset.disjoint_left.mp hsp.2.2 hv)
      · exact Finset.mem_union_right _ (Finset.mem_inter.mpr ⟨hv, h'⟩)
      · exact Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨h', hv⟩)
    have hDeq : P₀ ∪ x = D := Finset.Subset.antisymm
      (Finset.union_subset Finset.inter_subset_right Finset.inter_subset_left) hDsub
    have hP₀x : Disjoint P₀ x :=
      Finset.disjoint_of_subset_left Finset.inter_subset_left (h4.xF.symm)
    obtain ⟨K, rfl⟩ := (hh.mono hDsub).exists_localLift (fun _ => 0)
    have hK0 : 0 ≤ K := Matrix.nonneg_iff_posSemidef.mpr
      (posSemidef_of_localLift (Matrix.nonneg_iff_posSemidef.mp h0))
    have hK1 : K ≤ 1 := by
      rw [Matrix.le_iff] at h1 ⊢
      rw [one_sub_localLift] at h1
      exact posSemidef_of_localLift h1
    have hlog : Real.log (Real.exp 1 * (Fintype.card (RegionConfig n P₀) *
        Fintype.card (RegionConfig n x))) = logDim n D := by
      rw [log_exp_mul_card_mul_card hP₀x, hDeq]
    have hev := hsk.eventually_re_trace_skewOperator_le_swap hK0 hK1 ha
      (by rw [hlog]; exact hsmall) hε
    filter_upwards [hev] with k hk ρ hρ htr hsym
    have hb := hk (TransportData.base n) ρ hρ htr (permOp_mul_of_symProj_mul hsym)
    rw [ht2, hP, hY, hcmp k ρ hρ hsym, hlog, re_coherentIntegral_ofReal _ hρ] at hb
    have hf : (fun θ : SiteConfig n → ℂ =>
        regionalMovementEta π.F x (π.Y \ x) (WithLp.toLp 2 θ) ^ (1 / 8 : ℝ)) =
        fun θ => splitBandEta n π D ((EuclideanSpace.equiv _ ℂ).symm θ) ^ (1 / 8 : ℝ) :=
      funext fun θ => by
        rw [regionalMovementEta_eq_cmi_left h4.swap]
        simp only [splitBandEta, hnP, ↓reduceIte, x]
        rfl
    rw [hf, ← Real.rpow_natCast] at hb
    exact_mod_cast hb

/-- **Lemma 6.4 at a split leaf** (`05-replicas.tex`, display `replicas:skew-bound`,
lines 640–660, in the form used by `06-transport.tex`, lines 735–748): `SplitSkewBound` holds,
with `c = 1/8`, `C = 2 skewConst` and exponent `4`. -/
theorem splitSkewBound : SplitSkewBound.{u} := by
  refine ⟨1 / 8, 2 * Entropy.ConditionalSkew.skewConst, 4, by norm_num, ?_⟩
  intro V _ _ n _ π hπ D h h0 h1 hh hsplit t ht0 _ hsmall
  set M : ∀ k, Matrix (Config k fun v => Fin (n v)) (Config k fun v => Fin (n v)) ℂ :=
    fun k => Transport.skewSquare (bandMetric n t k π) (copyMean n k h)
  set main : ∀ k, Matrix (Config k fun v => Fin (n v)) (Config k fun v => Fin (n v)) ℂ → ℝ :=
    fun k ρ => 2 * Entropy.ConditionalSkew.skewConst * (2 * t) ^ 2 * logDim n D ^ (4 : ℝ) *
      realCoherentIntegral k (TransportData.base n) ρ (fun θ =>
        splitBandEta n π D ((EuclideanSpace.equiv _ ℂ).symm θ) ^ (1 / 8 : ℝ))
  set S : ℕ → Type _ := fun k => {ρ : Matrix (Config k fun v => Fin (n v))
    (Config k fun v => Fin (n v)) ℂ // ρ.PosSemidef ∧ ρ.trace = 1 ∧
      symProj (copyPerm (SiteConfig n) k) * ρ = ρ}
  have hmain : ∀ k (ρ : S k), 0 ≤ main k ρ.1 := fun k ρ => by
    have hD1 := one_le_logDim (n := n) D
    have := realCoherentIntegral_nonneg (k := k) (TransportData.base n) ρ.2.1
      (f := fun θ => splitBandEta n π D ((EuclideanSpace.equiv _ ℂ).symm θ) ^ (1 / 8 : ℝ))
      fun θ => rpow_one_div_eight_nonneg _
    have := skewConst_nonneg
    have : 0 ≤ logDim n D ^ (4 : ℝ) := Real.rpow_nonneg (by linarith) _
    positivity
  obtain ⟨r, hr, hle⟩ := exists_tendsto_zero_forall_le
    (fun k (ρ : S k) => (ρ.1 * M k).trace.re - main k ρ.1)
    (fun k => ⟨‖M k * symProj (copyPerm (SiteConfig n) k)‖, fun ρ => by
      have h1 := (Complex.re_le_norm _).trans (norm_trace_mul_le_of_symmetric ρ.2.1 ρ.2.2.1
        (permOp_mul_of_symProj_mul ρ.2.2.2) (M k))
      linarith [hmain k ρ]⟩)
    (fun ε hε => by
      filter_upwards [eventually_re_trace_skewSquare_le hπ h0 h1 hh hsplit ht0 hsmall hε]
        with k hk ρ
      linarith [hk ρ.1 ρ.2.1 ρ.2.2.1 ρ.2.2.2])
  exact ⟨r, hr, fun k ρ hρ htr hs => by linarith [hle k ⟨ρ, hρ, htr, hs⟩]⟩

/-- **Proposition 7.4, entropy and energy transport** (area-law paper, `prop:transport`,
`06-transport.tex` lines 377--434). Fix a finite one-copy space, history and conditional
choice trees, partitions with cross-band commutation on `𝒮_k`, a positive parameter
`a = 2t`, and positive contractions with designated supports compatible with the terminal
partitions. Let `ℓ ≥ 1` bound `log(e dim x)` for every transferred subsystem and
`log(e dim D_i)` for every term split at some terminal leaf, with `a ℓ` below a universal
threshold. Then for every `k`, every nonzero `pre ∈ 𝒮_k` and every `0 < p < 1`:

* `-∂_p log N(p)² = ∑_h w_h ∫ m_{1/4}(u) Tr(σ_{h,u} log C_h) du`;
* the entropy-gain lower bound with error `C k a K a^{1/4} ℓ^C + β_k`,
  `β_k = O(log(k+1))` independent of `p` and `pre`;
* if `Hbar pre = E₀ pre`, the energy bound
  `⟨v, Hbar v⟩ ≤ 2E₀ + C a² ℓ^C ∑_i W_i(p) ∑_{j∈𝒥_i} π_j ∫ m_{1/4} ∫ η_{i,j}^{1/8} dμ_{σ_{j,u}}
  du + o_k(1)`, with the remainder uniform in `p`, `pre` and the replica state.

The relative coherent pin (Lemma 6.3) and the skew bound (Lemma 6.4) of the source enter
through `relativePinBound` and `splitSkewBound`. -/
theorem transport :
    ∃ c₀ Cent eent Cen een : ℝ, 0 < c₀ ∧
      ∀ {V : Type u} [Fintype V] [DecidableEq V] (n : V → ℕ) [∀ v, NeZero (n v)]
        {K : ℕ} {H : Type*} [Fintype H] [DecidableEq H] {C : H → Type*}
        [∀ h, Fintype (C h)] [∀ h, DecidableEq (C h)] (D : TransportData V K H C)
        {ι : Type*} [Fintype ι] (E : EnergyTerms V n ι),
        D.IsAdmissible → (∀ i, 0 ≤ E.term i) → (∀ i, E.term i ≤ 1) →
        (∀ i, IsSupportedOn (E.term i) (E.support i)) → D.SupportCompatible E →
        ∀ {a ℓ : ℝ}, 0 < a → 1 ≤ ℓ → a * ℓ ≤ c₀ → (∀ k, D.CrossBandCommute n (a / 2) k) →
        (∀ h c g, logDim n (D.move h c g).subsystem ≤ ℓ) →
        (∀ i, (D.splitLeaves E i).Nonempty → logDim n (E.support i) ≤ ℓ) →
        ∃ β r : ℕ → ℝ, (β =O[atTop] fun k : ℕ => Real.log (k + 1)) ∧
          Tendsto r atTop (𝓝 0) ∧
          ∀ (k : ℕ) (pre : Config k (fun v => Fin (n v)) → ℂ),
            pre ∈ symmetricSubspace k (fun v => Fin (n v)) → pre ≠ 0 →
            ∀ p ∈ Ioo (0 : ℝ) 1,
              HasDerivAt
                (fun q => -Real.log (Transport.filteredNormSq (D.rootPath n (a / 2) k q) pre))
                (D.exactDerivative n (a / 2) k pre p) p ∧
              (k : ℝ) * a * D.entropyGain n (a / 2) k pre p -
                  Cent * k * a * K * a ^ (1 / 4 : ℝ) * ℓ ^ eent - β k ≤
                D.exactDerivative n (a / 2) k pre p ∧
              ∀ E₀ : ℝ, E.replicaEnergy k *ᵥ pre = (E₀ : ℂ) • pre →
                let v := Transport.filteredVector (D.rootPath n (a / 2) k p) pre
                (star v ⬝ᵥ (E.replicaEnergy k *ᵥ v)).re ≤
                  2 * E₀ + Cen * a ^ 2 * ℓ ^ een * D.energyError E (a / 2) k pre p + r k :=
  transport_of_splitSkewBound splitSkewBound

end TensorPower.ReplicaTransport
