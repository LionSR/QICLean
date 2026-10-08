/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.Transport.NormDerivative

/-!
# The exact derivative of the filtered norm

For the interpolated tree of one round, with root `M(p)` and a nonzero vector `pre`,
$$-\partial_p\log N(p)^2=\sum_h w_h\int_{\mathbb R}m_{1/4}(u)
  \operatorname{Tr}(\sigma_{h,u}\log C_h)\,du$$
(area-law paper, Proposition 7.4, display `transport:exact-derivative`,
`06-transport.tex` lines 402--408, proof lines 438--494).

The proof is split as in the source:

* the terminal weights of the interpolated tree (lines 275--286);
* the derivative at an interpolating vertex and at the root,
  `M^{-1/2} ∂_p M M^{-1/2} = ∑_h w_h Φ_{(h,old)}(log C_h)` (lines 442--468);
* the derivative of the norm through the Fourier multiplier `g_{1/4}` (lines 470--489);
* passage to the trace adjoint (lines 490--494);
* continuity of `N` on `[0, 1]` and integration over closed subintervals (lines 769--779).

The proofs are written from the paper; no Lean source was adapted.
-/

open scoped Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator unitInterval
open MeasureTheory Set Filter Topology

namespace Matrix

namespace MeanTree

section Bind

variable {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]

/-- The weight of a label after substitution, when only the subtree at `h₀` carries it. -/
theorem weight_bind_of_forall_ne (T : MeanTree ι) {f : ι → MeanTree κ} {h₀ : ι} {j : κ}
    (hf : ∀ h ≠ h₀, (f h).weight j = 0) : (T.bind f).weight j = T.weight h₀ * (f h₀).weight j := by
  induction T with
  | leaf h =>
    by_cases hh : h = h₀
    · subst hh; simp [bind]
    · simp [bind, hf h hh, Pi.single_eq_of_ne' hh]
  | node p l r ihl ihr =>
    simp only [bind, weight_node, ihl, ihr]; ring

omit [DecidableEq ι] in
/-- The weight of a label carried by no substituted subtree is zero. -/
theorem weight_bind_eq_zero (T : MeanTree ι) {f : ι → MeanTree κ} {j : κ}
    (hf : ∀ h, (f h).weight j = 0) : (T.bind f).weight j = 0 := by
  induction T with
  | leaf h => exact hf h
  | node p l r ihl ihr => simp only [bind, weight_node, ihl, ihr]; ring

theorem weight_map_apply (T : MeanTree ι) {g : ι → κ} (hg : Function.Injective g) (c : ι) :
    (T.map g).weight (g c) = T.weight c := by
  rw [map, weight_bind_of_forall_ne T (h₀ := c)]
  · simp
  · intro h hh
    simp [Pi.single_eq_of_ne' (hg.ne hh)]

theorem weight_map_of_forall_ne (T : MeanTree ι) {g : ι → κ} {j : κ} (hj : ∀ c, g c ≠ j) :
    (T.map g).weight j = 0 :=
  weight_bind_eq_zero T fun h => by simp [Pi.single_eq_of_ne' (hj h)]

theorem mem_labels_map (T : MeanTree ι) {g : ι → κ} {j : κ} (hj : j ∈ (T.map g).labels) :
    ∃ c, g c = j := by
  induction T with
  | leaf c =>
    simp only [map, bind, labels_leaf, List.mem_singleton] at hj
    exact ⟨c, hj.symm⟩
  | node p l r ihl ihr =>
    simp only [map, bind, labels_node, List.mem_append] at hj ihl ihr
    rcases hj with hj | hj
    · exact ihl hj
    · exact ihr hj

end Bind

variable {H : Type*} [DecidableEq H] {C : H → Type*} [∀ h, DecidableEq (C h)]

/-- Terminal weight `π_{(h,old)} = (1 - p) w_h` (`06-transport.tex`, display
`transport:terminal-weights`). -/
theorem weight_interpTree_old (T : MeanTree H) (S : ∀ h, MeanTree (C h)) (p : I) (h : H) :
    (interpTree T S p).weight ⟨h, none⟩ = (1 - (p : ℝ)) * T.weight h := by
  rw [interpTree, weight_bind_of_forall_ne T (h₀ := h)]
  · rw [weight_node, weight_map_of_forall_ne _ (by simp)]
    simp; ring
  · intro h' hh'
    rw [weight_node, weight_map_of_forall_ne _ (by simp [hh'])]
    simp [Pi.single_eq_of_ne' (by simp [hh'] : (⟨h', none⟩ : Σ h, Option (C h)) ≠ ⟨h, none⟩)]

/-- Terminal weight `π_{(h,c,new)} = p w_h q_{c|h}` (`06-transport.tex`, display
`transport:terminal-weights`). -/
theorem weight_interpTree_new (T : MeanTree H) (S : ∀ h, MeanTree (C h)) (p : I) (h : H)
    (c : C h) :
    (interpTree T S p).weight ⟨h, some c⟩ = (p : ℝ) * T.weight h * (S h).weight c := by
  rw [interpTree, weight_bind_of_forall_ne T (h₀ := h)]
  · rw [weight_node, weight_map_apply (S h) (g := fun c => (⟨h, some c⟩ : Σ h, Option (C h)))
      (fun a b hab => by simpa using hab)]
    simp; ring
  · intro h' hh'
    rw [weight_node, weight_map_of_forall_ne _ (by simp [hh'])]
    simp [Pi.single_eq_of_ne' (by simp [hh'] : (⟨h', none⟩ : Σ h, Option (C h)) ≠ ⟨h, some c⟩)]

end MeanTree

namespace Transport

open MeanTree

variable {n : Type*} [Fintype n] [DecidableEq n]
  {H : Type*} [Fintype H] [DecidableEq H] {C : H → Type*} [∀ h, Fintype (C h)]
  [∀ h, DecidableEq (C h)]

/-- The interpolation path `q ↦ M(proj q)` on the real line, clamped to `[0, 1]`. -/
noncomputable def interpPath (T : MeanTree H) (S : ∀ h, MeanTree (C h))
    (A : H → Matrix n n ℂ) (A' : ∀ h, C h → Matrix n n ℂ) (q : ℝ) : Matrix n n ℂ :=
  interpRoot T S A A' (projIcc (0 : ℝ) 1 zero_le_one q)

theorem posDef_interpRoot {T : MeanTree H} {S : ∀ h, MeanTree (C h)} {A : H → Matrix n n ℂ}
    {A' : ∀ h, C h → Matrix n n ℂ} (hA : ∀ h, (A h).PosDef) (hA' : ∀ h c, (A' h c).PosDef)
    (p : I) : (interpRoot T S A A' p).PosDef :=
  posDef_eval (fun j => match j with
    | ⟨h, none⟩ => hA h
    | ⟨h, some c⟩ => hA' h c) _

omit [Fintype H] [DecidableEq H] [∀ h, Fintype (C h)] [∀ h, DecidableEq (C h)] in
/-- The relabelled choice tree evaluates to the conditional choice root `B_h`. -/
theorem eval_map_choice (S : ∀ h, MeanTree (C h)) (A : H → Matrix n n ℂ)
    (A' : ∀ h, C h → Matrix n n ℂ) (h : H) :
    ((S h).map fun c => (⟨h, some c⟩ : Σ h, Option (C h))).eval (interpInput A A') =
      choiceRoot S A' h :=
  eval_map _ _ _

omit [∀ h, Fintype (C h)] in
/-- The root derivative along the interpolation parameter, before normalization: for every
subtree `T₀` of the history tree, `∂_q` of the interpolated subtree is the sum over `h` of the
old-child derivatives in the directions `(1 - p)⁻¹ A_h^{1/2} log C_h A_h^{1/2}`
(`06-transport.tex` lines 448--468). -/
theorem hasDerivAt_eval_bind {S : ∀ h, MeanTree (C h)}
    {A : H → Matrix n n ℂ} {A' : ∀ h, C h → Matrix n n ℂ} (hA : ∀ h, (A h).PosDef)
    (hA' : ∀ h c, (A' h c).PosDef) {p : ℝ} (hp : p ∈ Ioo 0 1) (T₀ : MeanTree H) :
    HasDerivAt (fun q => (interpTree T₀ S (projIcc (0 : ℝ) 1 zero_le_one q)).eval
        (interpInput A A'))
      (∑ h, (interpTree T₀ S (projIcc (0 : ℝ) 1 zero_le_one p)).derivLabel (interpInput A A')
        ⟨h, none⟩ ((1 - p)⁻¹ • (A h ^ (1 / 2 : ℝ) * CFC.log (relRatio S A A' h) *
          A h ^ (1 / 2 : ℝ)))) p := by
  have hIn : ∀ j, (interpInput A A' j).PosDef := fun j => match j with
    | ⟨h, none⟩ => hA h
    | ⟨h, some c⟩ => hA' h c
  have hpI : ((projIcc (0 : ℝ) 1 zero_le_one p : I) : ℝ) = p :=
    congrArg Subtype.val (projIcc_of_mem _ (Ioo_subset_Icc_self hp))
  induction T₀ with
  | leaf h₀ =>
    have hB : (choiceRoot S A' h₀).PosDef := posDef_eval (hA' h₀) _
    have hnot : ∀ h, (⟨h, none⟩ : Σ h, Option (C h)) ∉
        ((S h₀).map fun c => (⟨h₀, some c⟩ : Σ h, Option (C h))).labels := by
      intro h hh
      obtain ⟨c, hc⟩ := mem_labels_map _ hh
      obtain ⟨rfl, h2⟩ := Sigma.mk.inj_iff.mp hc
      simp at h2
    have hsum : (∑ h, (interpTree (leaf h₀) S (projIcc (0 : ℝ) 1 zero_le_one p)).derivLabel
        (interpInput A A') ⟨h, none⟩ ((1 - p)⁻¹ • (A h ^ (1 / 2 : ℝ) *
          CFC.log (relRatio S A A' h) * A h ^ (1 / 2 : ℝ)))) =
        geomMeanDerivLeft p (A h₀) (choiceRoot S A' h₀) ((1 - p)⁻¹ • (A h₀ ^ (1 / 2 : ℝ) *
          CFC.log (relRatio S A A' h₀) * A h₀ ^ (1 / 2 : ℝ))) := by
      simp only [interpTree, MeanTree.bind, derivLabel, derivLabel_of_not_mem (hnot _), add_zero,
        ContinuousLinearMap.comp_zero, eval_leaf, eval_map_choice, hpI]
      rw [Finset.sum_eq_single h₀]
      · simp [interpInput]
      · intro h _ hh
        simp [Ne.symm hh]
      · simp
    rw [hsum, ContinuousLinearMap.map_smul_of_tower, relRatio,
      geomMeanDerivLeft_sandwich_log (hA h₀) hB (Ioo_subset_Icc_self hp),
      smul_smul, inv_mul_cancel₀ (by linarith [hp.2] : (1 - p) ≠ 0), one_smul]
    have hev : (fun q => (interpTree (leaf h₀) S (projIcc (0 : ℝ) 1 zero_le_one q)).eval
        (interpInput A A')) =ᶠ[𝓝 p] fun q => geomMean q (A h₀) (choiceRoot S A' h₀) := by
      filter_upwards [Ioo_mem_nhds hp.1 hp.2] with q hq
      simp only [interpTree, MeanTree.bind, eval_node, eval_leaf, eval_map_choice, interpInput]
      rw [projIcc_of_mem _ (Ioo_subset_Icc_self hq)]
    exact (hasDerivAt_geomMean_param (hA h₀) hB p).congr_of_eventuallyEq hev
  | node r l rr ihl ihr =>
    have hL := isHermitian_eval (fun j => (hIn j).isHermitian)
    have h := hasDerivAt_geomMean_of_hasDerivAt r.2 ihl ihr
      (fun q => hL _) (fun q => hL _) (posDef_eval hIn _) (posDef_eval hIn _)
    refine h.congr_deriv ?_
    simp only [interpTree, MeanTree.bind, derivLabel, _root_.add_apply,
      ContinuousLinearMap.comp_apply, map_sum, Finset.sum_add_distrib]

/-- **The derivative at the root** (`06-transport.tex`, displays
`transport:node-p-derivative` and `transport:root-p-derivative`, lines 442--468):
`𝖧 = M^{-1/2} ∂_p M M^{-1/2} = ∑_h w_h Φ_{(h,old)}(log C_h)`. The coefficient is `w_h`,
not the terminal weight `(1 - p) w_h`. -/
theorem exists_hasDerivAt_interpPath {T : MeanTree H} {S : ∀ h, MeanTree (C h)}
    {A : H → Matrix n n ℂ} {A' : ∀ h, C h → Matrix n n ℂ} (hA : ∀ h, (A h).PosDef)
    (hA' : ∀ h c, (A' h c).PosDef) (hT : ∀ h, 0 < T.weight h) {p : ℝ} (hp : p ∈ Ioo 0 1) :
    ∃ D : Matrix n n ℂ, HasDerivAt (interpPath T S A A') D p ∧
      interpPath T S A A' p ^ (-(1 / 2) : ℝ) * D * interpPath T S A A' p ^ (-(1 / 2) : ℝ) =
        ∑ h, T.weight h • (interpTree T S (projIcc (0 : ℝ) 1 zero_le_one p)).leafMap
          (interpInput A A') ⟨h, none⟩ (CFC.log (relRatio S A A' h)) := by
  have hpI : ((projIcc (0 : ℝ) 1 zero_le_one p : I) : ℝ) = p :=
    congrArg Subtype.val (projIcc_of_mem _ (Ioo_subset_Icc_self hp))
  refine ⟨_, hasDerivAt_eval_bind hA hA' hp T, ?_⟩
  rw [Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun h _ => ?_
  have hw : (interpTree T S (projIcc (0 : ℝ) 1 zero_le_one p)).weight ⟨h, none⟩ ≠ 0 := by
    rw [weight_interpTree_old, hpI]
    exact mul_ne_zero (by linarith [hp.2]) (hT h).ne'
  have key : (interpTree T S (projIcc (0 : ℝ) 1 zero_le_one p)).eval (interpInput A A') ^
        (-(1 / 2) : ℝ) * (interpTree T S (projIcc (0 : ℝ) 1 zero_le_one p)).derivLabel
          (interpInput A A') ⟨h, none⟩
          (A h ^ (1 / 2 : ℝ) * CFC.log (relRatio S A A' h) * A h ^ (1 / 2 : ℝ)) *
        (interpTree T S (projIcc (0 : ℝ) 1 zero_le_one p)).eval (interpInput A A') ^
          (-(1 / 2) : ℝ) =
      (interpTree T S (projIcc (0 : ℝ) 1 zero_le_one p)).weight ⟨h, none⟩ •
        (interpTree T S (projIcc (0 : ℝ) 1 zero_le_one p)).leafMap (interpInput A A') ⟨h, none⟩
          (CFC.log (relRatio S A A' h)) :=
    sandwich_derivLabel_eq_smul_leafMap _ hw _
  rw [ContinuousLinearMap.map_smul_of_tower, mul_smul_comm, smul_mul_assoc]
  unfold interpPath interpRoot
  rw [key, weight_interpTree_old, hpI, smul_smul, ← mul_assoc,
    inv_mul_cancel₀ (by linarith [hp.2] : (1 - p) ≠ 0), one_mul]

omit [DecidableEq n] in
/-- Moving a positive map to its trace adjoint: `⟨w, Φ(Z) w⟩ = Tr(Φ^*(|w⟩⟨w|) Z)`
(`06-transport.tex` lines 490--494). -/
theorem star_dotProduct_mulVec_eq_trace_traceAdjointMap
    (Φ : Matrix n n ℂ →ₗ[ℂ] Matrix n n ℂ) (Z : Matrix n n ℂ) (w : n → ℂ) :
    star w ⬝ᵥ (Φ Z *ᵥ w) = (traceAdjointMap Φ (vecMulVec w (star w)) * Z).trace := by
  rw [trace_traceAdjointMap_mul, vecMulVec_mul, trace_vecMulVec, dotProduct_mulVec,
    dotProduct_comm]

/-- **Exact derivative** (area-law paper, Proposition 7.4, display
`transport:exact-derivative`, `06-transport.tex` lines 402--408): for `0 < p < 1` and
nonzero `pre`,
`-∂_p log N(p)² = ∑_h w_h ∫ m_{1/4}(u) Tr(σ_{h,u} log C_h) du`. -/
theorem hasDerivAt_neg_log_filteredNormSq {T : MeanTree H} {S : ∀ h, MeanTree (C h)}
    {A : H → Matrix n n ℂ} {A' : ∀ h, C h → Matrix n n ℂ} (hA : ∀ h, (A h).PosDef)
    (hA' : ∀ h c, (A' h c).PosDef) (hT : ∀ h, 0 < T.weight h) {p : ℝ} (hp : p ∈ Ioo 0 1)
    {pre : n → ℂ} (hpre : pre ≠ 0) :
    HasDerivAt (fun q => -Real.log (filteredNormSq (interpPath T S A A' q) pre))
      (∑ h, T.weight h * ∫ u, fourierWeight u *
        (transportState (interpTree T S (projIcc (0 : ℝ) 1 zero_le_one p)) (interpInput A A')
            (filteredVector (interpPath T S A A' p) pre) ⟨h, none⟩ u *
          CFC.log (relRatio S A A' h)).trace.re) p := by
  obtain ⟨D, hD, hDH⟩ := exists_hasDerivAt_interpPath hA hA' hT hp
  have hM : ∀ q, (interpPath T S A A' q).PosDef := fun q => posDef_interpRoot hA hA' _
  have h1 := hasDerivAt_neg_log_filteredNormSq_of_hasDerivAt hM hD hpre
  convert h1 using 1
  -- Insert `transport:root-p-derivative` and move each leaf map to its trace adjoint.
  rw [hDH]
  set Mp := interpPath T S A A' p
  set v := filteredVector Mp pre
  set T' := interpTree T S (projIcc (0 : ℝ) 1 zero_le_one p)
  have hMh : Mp.IsHermitian := (hM p).isHermitian
  have hint : ∀ h, Integrable fun u : ℝ => fourierWeight u *
      (star (imagPow Mp u *ᵥ v) ⬝ᵥ (T'.leafMap (interpInput A A') ⟨h, none⟩
        (CFC.log (relRatio S A A' h)) *ᵥ (imagPow Mp u *ᵥ v))).re :=
    fun h => integrable_fourierWeight_mul_quadForm hMh _ _
  have htr : ∀ h u, (transportState T' (interpInput A A') v ⟨h, none⟩ u *
      CFC.log (relRatio S A A' h)).trace =
      star (imagPow Mp u *ᵥ v) ⬝ᵥ (T'.leafMap (interpInput A A') ⟨h, none⟩
        (CFC.log (relRatio S A A' h)) *ᵥ (imagPow Mp u *ᵥ v)) := fun h u =>
    (star_dotProduct_mulVec_eq_trace_traceAdjointMap
      (T'.leafMap (interpInput A A') ⟨h, none⟩).toLinearMap _ _).symm
  simp only [htr]
  simp_rw [← integral_const_mul]
  rw [← integral_finsetSum _ fun h _ => (hint h).const_mul (T.weight h)]
  congr 1
  funext u
  rw [sum_mulVec, dotProduct_sum, Complex.re_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun h _ => ?_
  rw [smul_mulVec, dotProduct_smul, Complex.smul_re]
  ring

omit [Fintype H] [DecidableEq H] [∀ h, Fintype (C h)] [∀ h, DecidableEq (C h)] in
/-- `M^{-iu}` is unitary. -/
theorem conjTranspose_imagPow_mul_imagPow (M : Matrix n n ℂ) (u : ℝ) :
    (imagPow M u)ᴴ * imagPow M u = 1 := by
  have hlog : (CFC.log M).IsHermitian := by
    unfold CFC.log; exact cfc_predicate _ _
  exact mul_eq_one_comm.mp (hermitianUnitaryPath_mul_conjTranspose _ hlog _)

/-- The transport states are density matrices (`06-transport.tex` line 491, from
Lemma 7.2): positive semidefinite, with trace `‖v‖²`. -/
theorem posSemidef_transportState {J : Type*} [DecidableEq J] {T' : MeanTree J}
    {A : J → Matrix n n ℂ} (hA : ∀ j, (A j).PosDef) (v : n → ℂ) (j : J) (u : ℝ) :
    (transportState T' A v j u).PosSemidef :=
  posSemidef_traceAdjoint_leafMap hA T' j (posSemidef_vecMulVec_self_star _)

theorem trace_transportState {J : Type*} [DecidableEq J] {T' : MeanTree J}
    {A : J → Matrix n n ℂ} (hA : ∀ j, (A j).PosDef) {j : J} (hw : T'.weight j ≠ 0)
    (v : n → ℂ) (u : ℝ) :
    (transportState T' A v j u).trace = star v ⬝ᵥ v := by
  rw [transportState, trace_traceAdjoint_leafMap hA T' hw, trace_vecMulVec, dotProduct_comm,
    star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, conjTranspose_imagPow_mul_imagPow, one_mulVec]

omit [∀ h, Fintype (C h)] in
/-- The interpolated subtree depends continuously on the interpolation parameter. -/
theorem continuous_eval_interpTree {S : ∀ h, MeanTree (C h)} {A : H → Matrix n n ℂ}
    {A' : ∀ h, C h → Matrix n n ℂ} (hA : ∀ h, (A h).PosDef) (hA' : ∀ h c, (A' h c).PosDef)
    (T₀ : MeanTree H) :
    Continuous fun x : I => (interpTree T₀ S x).eval (interpInput A A') := by
  have hIn : ∀ j, (interpInput A A' j).PosDef := fun j => match j with
    | ⟨h, none⟩ => hA h
    | ⟨h, some c⟩ => hA' h c
  induction T₀ with
  | leaf h₀ =>
    have hB : (choiceRoot S A' h₀).PosDef := posDef_eval (hA' h₀) _
    have hfun : (fun x : I => (interpTree (leaf h₀) S x).eval (interpInput A A')) =
        fun x : I => geomMean x (A h₀) (choiceRoot S A' h₀) := by
      funext x
      simp only [interpTree, MeanTree.bind, eval_node, eval_leaf, eval_map_choice, interpInput]
    rw [hfun]
    exact (continuous_iff_continuousAt.mpr fun q =>
      (hasDerivAt_geomMean_param (hA h₀) hB q).continuousAt).comp continuous_subtype_val
  | node r l rr ihl ihr =>
    refine continuous_iff_continuousAt.mpr fun x => ?_
    rw [← continuousWithinAt_univ]
    have hg := (differentiableWithinAt_geomMean (posDef_eval hIn (interpTree l S x))
      (posDef_eval hIn (interpTree rr S x)) r.2).continuousWithinAt
    exact ContinuousWithinAt.comp (f := fun y : I => ((interpTree l S y).eval (interpInput A A'),
        (interpTree rr S y).eval (interpInput A A'))) hg (ihl.prodMk ihr).continuousWithinAt
      fun y _ => ⟨(posDef_eval hIn (interpTree l S y)).isHermitian,
        (posDef_eval hIn (interpTree rr S y)).isHermitian⟩

omit [∀ h, Fintype (C h)] in
/-- The interpolation path is continuous. -/
theorem continuous_interpPath {T : MeanTree H} {S : ∀ h, MeanTree (C h)}
    {A : H → Matrix n n ℂ} {A' : ∀ h, C h → Matrix n n ℂ} (hA : ∀ h, (A h).PosDef)
    (hA' : ∀ h c, (A' h c).PosDef) : Continuous (interpPath T S A A') :=
  (continuous_eval_interpTree hA hA' T).comp continuous_projIcc

/-- `N²` is positive and continuous on `[0, 1]` (`06-transport.tex` lines 769--771). -/
theorem continuous_filteredNormSq_interpPath {T : MeanTree H} {S : ∀ h, MeanTree (C h)}
    {A : H → Matrix n n ℂ} {A' : ∀ h, C h → Matrix n n ℂ} (hA : ∀ h, (A h).PosDef)
    (hA' : ∀ h c, (A' h c).PosDef) (pre : n → ℂ) :
    Continuous fun q => filteredNormSq (interpPath T S A A' q) pre := by
  have hM : ∀ q, (interpPath T S A A' q).PosDef := fun q => posDef_interpRoot hA hA' _
  simp_rw [filteredNormSq_eq (hM _)]
  have hc : Continuous fun q => interpPath T S A A' q ^ (-(1 / 2) : ℝ) := by
    refine continuous_iff_continuousAt.mpr fun q => ?_
    rw [← continuousWithinAt_univ]
    exact (differentiableWithinAt_rpow_neg_half (hM q)).continuousWithinAt.comp
      (continuous_interpPath hA hA').continuousWithinAt fun y _ => (hM y).isHermitian
  exact Complex.continuous_re.comp (continuous_const.dotProduct
    (hc.matrix_mulVec continuous_const))

/-- **Integration over a closed subinterval** (`06-transport.tex` lines 427--429 and
769--779): the derivative of `-log N²` is interval integrable on `[p₀, p₁] ⊆ [0, 1]`, and
its integral is the difference of the continuous endpoint values. -/
theorem log_filteredNormSq_sub_eq_integral {T : MeanTree H} {S : ∀ h, MeanTree (C h)}
    {A : H → Matrix n n ℂ} {A' : ∀ h, C h → Matrix n n ℂ} (hA : ∀ h, (A h).PosDef)
    (hA' : ∀ h c, (A' h c).PosDef) (hT : ∀ h, 0 < T.weight h) {pre : n → ℂ} (hpre : pre ≠ 0)
    {p₀ p₁ : ℝ} (h0 : 0 ≤ p₀) (h01 : p₀ ≤ p₁) (h1 : p₁ ≤ 1) :
    IntervalIntegrable (fun p => ∑ h, T.weight h * ∫ u, fourierWeight u *
        (transportState (interpTree T S (projIcc (0 : ℝ) 1 zero_le_one p)) (interpInput A A')
            (filteredVector (interpPath T S A A' p) pre) ⟨h, none⟩ u *
          CFC.log (relRatio S A A' h)).trace.re) volume p₀ p₁ ∧
    Real.log (filteredNormSq (interpPath T S A A' p₀) pre) -
        Real.log (filteredNormSq (interpPath T S A A' p₁) pre) =
      ∫ p in p₀..p₁, ∑ h, T.weight h * ∫ u, fourierWeight u *
        (transportState (interpTree T S (projIcc (0 : ℝ) 1 zero_le_one p)) (interpInput A A')
            (filteredVector (interpPath T S A A' p) pre) ⟨h, none⟩ u *
          CFC.log (relRatio S A A' h)).trace.re := by
  sorry

end Transport

end Matrix
