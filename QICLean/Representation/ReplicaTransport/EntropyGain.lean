/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Representation.ReplicaTransport.CoherentLog
import QICLean.Representation.ReplicaTransport.Prerequisites
import QICLean.Representation.ReplicaTransport.States

/-!
# The entropy-gain lower bound of the transport estimate

Area-law paper, Proposition 7.4, display `transport:entropy-gain` (`06-transport.tex`
lines 409--416, proof lines 495--583):
$$-\partial_p\log N(p)^2\ge ka\sum_{h,g}w_h\int m_{1/4}(u)\int\sum_c q_{c|h}
  \eta_{h,c,g}\,d\mu_{\sigma_{h,u}}\,du-CkaKa^{1/4}\ell^C-\beta_k,$$
with `β_k = O(log(k+1))` independent of `p` and `pre`.

Proof outline:

* `cfc_log_relRatio_eq_sum` — band factorization `log C_h = ∑_g log C_{h,g}`
  (display `transport:relative-factorization`, Lemma 7.1);
* `bandRelRatio_eq_eval` — congruence covariance identifies `C_{h,g}` with the
  conditional choice tree of the single-move relative metrics;
* `smul_coherentProj_le_bandRelRatio` — Lemma 6.4 and projection transfer give the
  conditional pin (display `transport:conditional-pin`);
* `coherentIntegral_sub_log_le_re_trace_mul_log` — the logarithmic passage
  (display `transport:log-relative`);
* `exists_entropyGain_le_exactDerivative` — summation over bands and histories, with
  `∑_h w_h = 1` and `∫ m_{1/4} = 1/2`.

The proofs are written from the paper; no Lean source was adapted.
-/

open scoped Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator unitInterval
open Matrix Set Filter PermutationRepresentation Entropy

noncomputable section

namespace TensorPower.ReplicaTransport

variable {V : Type*} [Fintype V] [DecidableEq V] {n : V → ℕ} [∀ v, NeZero (n v)]

section Helpers

variable {m : Type*} [Fintype m] [DecidableEq m]

/-- A matrix commuting with `A` commutes with every real power of `A`. -/
private theorem commute_rpow_of_commute {X A : Matrix m m ℂ} (h : Commute X A) (r : ℝ) :
    Commute X (A ^ r) := by
  rw [CFC.rpow_def]
  exact (Commute.cfc_nnreal h.symm _).symm

/-- An invertible matrix commuting with `A` commutes with `A⁻¹`. -/
private theorem commute_inv_of_commute {X A : Matrix m m ℂ} (h : Commute X A) :
    Commute X A⁻¹ := by
  by_cases hA : IsUnit A.det
  · have h1 : A⁻¹ * A = 1 := nonsing_inv_mul A hA
    have h2 : A * A⁻¹ = 1 := mul_nonsing_inv A hA
    calc X * A⁻¹ = A⁻¹ * (A * X) * A⁻¹ := by
          rw [← Matrix.mul_assoc, h1, Matrix.one_mul]
      _ = A⁻¹ * (X * A) * A⁻¹ := by rw [h.eq]
      _ = A⁻¹ * X := by rw [Matrix.mul_assoc, Matrix.mul_assoc, h2, Matrix.mul_one]
  · rw [nonsing_inv_apply_not_isUnit A hA]
    exact Commute.zero_right X

/-- A matrix commuting with every input commutes with the root of any weighted tree; no
positivity of the inputs is needed. -/
private theorem commute_eval_of_commute {ι : Type*} {A : ι → Matrix m m ℂ} {X : Matrix m m ℂ}
    (hX : ∀ j, Commute X (A j)) (T : Matrix.MeanTree ι) : Commute X (T.eval A) := by
  induction T with
  | leaf j => exact hX j
  | node p l r ihl ihr =>
    rw [Matrix.MeanTree.eval_node, geomMean]
    have ha := fun r : ℝ => commute_rpow_of_commute ihl r
    exact ((ha _).mul_right (commute_rpow_of_commute (((ha _).mul_right ihr).mul_right
      (ha _)) _)).mul_right (ha _)

/-- Whitening a product of commuting bands by the square root of a product of commuting
bands factors band by band. -/
private theorem listProd_whiten {K : ℕ} {A B : Fin K → Matrix m m ℂ} (hA : ∀ g, (A g).PosDef)
    (hB : ∀ g, (B g).PosDef) (hAA : ∀ g g', g ≠ g' → Commute (A g) (A g'))
    (hAB : ∀ g g', g ≠ g' → Commute (A g) (B g')) :
    (List.ofFn A).prod ^ (-(1 / 2) : ℝ) * (List.ofFn B).prod *
        (List.ofFn A).prod ^ (-(1 / 2) : ℝ) =
      (List.ofFn fun g => A g ^ (-(1 / 2) : ℝ) * B g * A g ^ (-(1 / 2) : ℝ)).prod := by
  induction K with
  | zero => simp
  | succ K ih =>
    simp only [List.ofFn_succ, List.prod_cons]
    set PA := (List.ofFn fun g : Fin K => A g.succ).prod
    set PB := (List.ofFn fun g : Fin K => B g.succ).prod
    have hPA : PA.PosDef := Matrix.MeanTree.posDef_listProd_ofFn (fun g => hA _)
      (fun g g' h => hAA _ _ (fun h' => h (Fin.succ_injective _ h')))
    have hA0PA : Commute (A 0) PA := Commute.list_prod_right _ _ fun y hy => by
      obtain ⟨g, rfl⟩ := List.mem_ofFn.mp hy
      exact hAA _ _ (Fin.succ_ne_zero g).symm
    have hA0PB : Commute (A 0) PB := Commute.list_prod_right _ _ fun y hy => by
      obtain ⟨g, rfl⟩ := List.mem_ofFn.mp hy
      exact hAB _ _ (Fin.succ_ne_zero g).symm
    have hPAB0 : Commute PA (B 0) := Commute.list_prod_left _ _ fun y hy => by
      obtain ⟨g, rfl⟩ := List.mem_ofFn.mp hy
      exact hAB _ _ (Fin.succ_ne_zero g)
    rw [(hA 0).mul_rpow_of_commute hPA hA0PA, ← ih (fun g => hA _) (fun g => hB _)
      (fun g g' h => hAA _ _ (fun h' => h (Fin.succ_injective _ h')))
      (fun g g' h => hAB _ _ (fun h' => h (Fin.succ_injective _ h')))]
    set r : ℝ := -(1 / 2)
    have c1 : Commute (PA ^ r) (B 0) := commute_rpow_of_commute hPAB0.symm r |>.symm
    have c2 : Commute PB (A 0 ^ r) := (commute_rpow_of_commute hA0PB.symm r)
    have c3 : Commute (PA ^ r) (A 0 ^ r) := (hPA.commute_rpow (hA 0) hA0PA.symm r r)
    simp only [Matrix.mul_assoc]
    rw [c1.left_comm, c2.left_comm, c3.left_comm]

/-- The logarithm of an ordered product of pairwise commuting positive definite matrices is
the sum of the logarithms. -/
private theorem cfc_log_listProd {K : ℕ} {X : Fin K → Matrix m m ℂ} (hX : ∀ g, (X g).PosDef)
    (hXX : ∀ g g', g ≠ g' → Commute (X g) (X g')) :
    CFC.log (List.ofFn X).prod = ∑ g, CFC.log (X g) := by
  induction K with
  | zero => simp
  | succ K ih =>
    rw [List.ofFn_succ, List.prod_cons, Fin.sum_univ_succ,
      (hX 0).cfc_log_mul (Matrix.MeanTree.posDef_listProd_ofFn (fun g => hX _)
        (fun g g' h => hXX _ _ (fun h' => h (Fin.succ_injective _ h'))))
        (Commute.list_prod_right _ _ fun y hy => by
          obtain ⟨g, rfl⟩ := List.mem_ofFn.mp hy
          exact hXX _ _ (Fin.succ_ne_zero g).symm),
      ih (fun g => hX _) (fun g g' h => hXX _ _ (fun h' => h (Fin.succ_injective _ h')))]

end Helpers

omit [∀ v, NeZero (n v)] in
/-- Band metrics commute with the permutations of entire copies. -/
theorem commute_permOp_bandMetric (t : ℝ) (k : ℕ) (π : PYF V) (s : Equiv.Perm (Fin k)) :
    Commute (permOp (copyPerm (SiteConfig n) k) s) (bandMetric n t k π) := by
  have hW : ∀ Q : Finset V, Commute (permOp (copyPerm (SiteConfig n) k) s)
      (replicaMetric (fun v => Fin (n v)) t k Q) := fun Q =>
    commute_copyPerm_labelObservable k Q _ s
  unfold bandMetric leafMetric leafRoot
  exact ((((commute_inv_of_commute (hW _)).mul_right (commute_inv_of_commute (hW _))).mul_right
    (hW _)).pow_right 2)

omit [Fintype V] [DecidableEq V] in
/-- `log(e dim x) ≥ 1`. -/
theorem one_le_logDim (x : Finset V) : 1 ≤ logDim n x := by
  have hP : 1 ≤ ∏ v ∈ x, (n v : ℝ) := Finset.one_le_prod₀ fun v _ => by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne (n v))
  rw [logDim, Real.log_mul (Real.exp_pos 1).ne' (by linarith), Real.log_exp]
  linarith [Real.log_nonneg hP]

omit [∀ v, NeZero (n v)] in
/-- The entropy of a region of a pure state is continuous in the vector: the reduced matrix is
quadratic in the vector and `ρ ↦ Tr η(ρ)` is continuous on Hermitian matrices. -/
theorem continuous_entropy (R : Finset V) :
    Continuous fun θ : SiteConfig n → ℂ =>
      FiniteProduct.entropy (fun v => Fin (n v)) ((EuclideanSpace.equiv _ ℂ).symm θ) R := by
  have hρ : Continuous fun θ : SiteConfig n → ℂ =>
      FiniteProduct.reducedPure (fun v => Fin (n v)) ((EuclideanSpace.equiv _ ℂ).symm θ) R := by
    refine continuous_pi fun a => continuous_pi fun b => ?_
    simp only [FiniteProduct.reducedPure, FiniteProduct.reducedMatrix_apply, vecMulVec_apply]
    fun_prop
  have heq : ∀ θ : SiteConfig n → ℂ,
      FiniteProduct.entropy (fun v => Fin (n v)) ((EuclideanSpace.equiv _ ℂ).symm θ) R =
        (cfc Real.negMulLog (FiniteProduct.reducedPure (fun v => Fin (n v))
          ((EuclideanSpace.equiv _ ℂ).symm θ) R)).trace.re := fun θ => by
    have hH := (FiniteProduct.reducedPure_posSemidef (fun v => Fin (n v))
      ((EuclideanSpace.equiv _ ℂ).symm θ) R).isHermitian
    rw [FiniteProduct.entropy, _root_.vonNeumannEntropy, hH.cfc_eq, ← RCLike.re_eq_complex_re,
      Matrix.IsHermitian.trace_cfc_eq_sum_re]
  simp_rw [heq]
  refine Complex.continuous_re.comp (continuous_id.matrix_trace.comp ?_)
  exact Continuous.cfc_of_mem_nhdsSet (s := Set.univ) Real.negMulLog Filter.univ_mem hρ
    (fun θ => (FiniteProduct.reducedPure_posSemidef (fun v => Fin (n v))
      ((EuclideanSpace.equiv _ ℂ).symm θ) R).isHermitian.isSelfAdjoint)
    Real.continuous_negMulLog.continuousOn

omit [∀ v, NeZero (n v)] in
/-- The entropy of a move is continuous in the one-copy vector. -/
theorem continuous_moveEta (π : PYF V) (m : Move V) :
    Continuous fun θ : SiteConfig n → ℂ => moveEta n π m ((EuclideanSpace.equiv _ ℂ).symm θ) := by
  cases m with
  | stay => exact continuous_const
  | toP x =>
    simp only [moveEta, FiniteProduct.conditionalMutualInformation]
    exact (((continuous_entropy _).add (continuous_entropy _)).sub (continuous_entropy _)).sub
      (continuous_entropy _)
  | toF x =>
    simp only [moveEta, FiniteProduct.conditionalMutualInformation]
    exact (((continuous_entropy _).add (continuous_entropy _)).sub (continuous_entropy _)).sub
      (continuous_entropy _)

namespace TransportData

variable {K : ℕ} {H : Type*} [Fintype H] [DecidableEq H] {C : H → Type*}
  [∀ h, Fintype (C h)] [∀ h, DecidableEq (C h)] (D : TransportData V K H C)

variable (n) in
/-- The band relative ratio `C_{h,g} = A_{h,g}^{-1/2} B_{h,g} A_{h,g}^{-1/2}`, where `B_{h,g}`
is the conditional choice tree of the new band-`g` metrics (`06-transport.tex`, display
`transport:relative-factorization`). -/
def bandRelRatio (t : ℝ) (k : ℕ) (h : H) (g : Fin K) :
    Matrix (Config k fun v => Fin (n v)) (Config k fun v => Fin (n v)) ℂ :=
  bandMetric n t k (D.old h g) ^ (-(1 / 2) : ℝ) *
    (D.choiceTree h).eval (fun c => bandMetric n t k (D.new h c g)) *
      bandMetric n t k (D.old h g) ^ (-(1 / 2) : ℝ)

omit [Fintype H] [∀ h, Fintype (C h)] in
/-- **Congruence covariance** (`06-transport.tex` lines 510--512): `C_{h,g}` is the
conditional choice tree of the single-move relative metrics
`A_{h,g}^{-1/2} A_{h,c,g} A_{h,g}^{-1/2}`. -/
theorem bandRelRatio_eq_eval (hD : D.IsAdmissible) {t : ℝ} (ht : 0 ≤ t) (k : ℕ) (h : H)
    (g : Fin K) :
    D.bandRelRatio n t k h g = (D.choiceTree h).eval (fun c =>
      bandMetric n t k (D.old h g) ^ (-(1 / 2) : ℝ) * bandMetric n t k (D.new h c g) *
        bandMetric n t k (D.old h g) ^ (-(1 / 2) : ℝ)) := by
  have hA := posDef_bandMetric (n := n) (hD.old_isPartition h g) ht k
  have hB : ∀ c, (bandMetric n t k (D.new h c g)).PosDef := fun c =>
    posDef_bandMetric (Move.isPartition_apply (hD.old_isPartition h g) (hD.move_isValid h c g))
      ht k
  have := Matrix.MeanTree.eval_star_conj hB (hA.rpow (-(1 / 2) : ℝ)).isUnit (D.choiceTree h)
  simp only [hA.star_rpow] at this
  exact this.symm

omit [Fintype H] [∀ h, Fintype (C h)] in
/-- The band relative ratios are positive definite. -/
theorem posDef_bandRelRatio (hD : D.IsAdmissible) {t : ℝ} (ht : 0 ≤ t) (k : ℕ) (h : H)
    (g : Fin K) : (D.bandRelRatio n t k h g).PosDef := by
  have hA := posDef_bandMetric (n := n) (hD.old_isPartition h g) ht k
  have hB : ∀ c, (bandMetric n t k (D.new h c g)).PosDef := fun c =>
    posDef_bandMetric (Move.isPartition_apply (hD.old_isPartition h g) (hD.move_isValid h c g))
      ht k
  rw [D.bandRelRatio_eq_eval hD ht]
  exact Matrix.MeanTree.posDef_eval (fun c => hA.whiten (hB c)) _

omit [∀ v, NeZero (n v)] [Fintype H] [DecidableEq H] [∀ h, Fintype (C h)]
  [∀ h, DecidableEq (C h)] in
/-- The band relative ratios commute with the permutations of entire copies. -/
theorem commute_permOp_bandRelRatio {t : ℝ} (k : ℕ) (h : H) (g : Fin K)
    (s : Equiv.Perm (Fin k)) :
    Commute (permOp (copyPerm (SiteConfig n) k) s) (D.bandRelRatio n t k h g) := by
  unfold bandRelRatio
  have hA := commute_permOp_bandMetric (n := n) t k (D.old h g) s
  exact ((commute_rpow_of_commute hA _).mul_right (commute_eval_of_commute
    (fun c => commute_permOp_bandMetric t k _ s) _)).mul_right (commute_rpow_of_commute hA _)

omit [Fintype H] in
/-- **Conditional pin** (`06-transport.tex`, display `transport:conditional-pin`,
lines 513--531): from per-move pins with common `b > 0` and error `E`, projection transfer
gives `C_{h,g} ≥ b exp(k a [∑_c q_{c|h} η_{h,c,g}(θ) - E]) P_{θ,k}`. -/
theorem smul_coherentProj_le_bandRelRatio (hD : D.IsAdmissible) {t : ℝ} (ht : 0 ≤ t)
    (k : ℕ) (h : H) (g : Fin K) {b Err : ℝ} (hb : 0 < b) (θ : SiteConfig n → ℂ)
    (hpin : ∀ c, (b * Real.exp ((k : ℝ) * (2 * t) *
        (moveEta n (D.old h g) (D.move h c g) ((EuclideanSpace.equiv _ ℂ).symm θ) - Err))) •
          coherentProj k θ ≤
        bandMetric n t k (D.old h g) ^ (-(1 / 2) : ℝ) * bandMetric n t k (D.new h c g) *
          bandMetric n t k (D.old h g) ^ (-(1 / 2) : ℝ)) :
    (b * Real.exp ((k : ℝ) * (2 * t) * (∑ c, (D.choiceTree h).weight c *
        moveEta n (D.old h g) (D.move h c g) ((EuclideanSpace.equiv _ ℂ).symm θ) - Err))) •
          coherentProj k θ ≤ D.bandRelRatio n t k h g := by
  have hA := posDef_bandMetric (n := n) (hD.old_isPartition h g) ht k
  have hB : ∀ c, (bandMetric n t k (D.new h c g)).PosDef := fun c =>
    posDef_bandMetric (Move.isPartition_apply (hD.old_isPartition h g) (hD.move_isValid h c g))
      ht k
  rw [D.bandRelRatio_eq_eval hD ht]
  set x : C h → ℝ := fun c => (k : ℝ) * (2 * t) *
    (moveEta n (D.old h g) (D.move h c g) ((EuclideanSpace.equiv _ ℂ).symm θ) - Err) with hx
  have key := Matrix.MeanTree.smul_le_eval (fun c => hA.whiten (hB c))
    (P := coherentProj k θ)
    (posSemidef_vecMulVec_self_star _) (c := fun c => b * Real.exp (x c))
    (fun c => mul_pos hb (Real.exp_pos _)) hpin (D.choiceTree h)
  convert key using 2
  rw [Finset.prod_congr rfl (fun c _ => Real.mul_rpow hb.le (Real.exp_pos _).le),
    Finset.prod_mul_distrib, ← Real.rpow_sum_of_pos hb, Matrix.MeanTree.sum_weight, Real.rpow_one]
  congr 1
  simp only [← Real.exp_mul, ← Real.exp_sum]
  congr 1
  have hw := (D.choiceTree h).sum_weight
  calc (k : ℝ) * (2 * t) * (∑ c, (D.choiceTree h).weight c *
        moveEta n (D.old h g) (D.move h c g) ((EuclideanSpace.equiv _ ℂ).symm θ) - Err)
      = (k : ℝ) * (2 * t) * (∑ c, (D.choiceTree h).weight c *
        moveEta n (D.old h g) (D.move h c g) ((EuclideanSpace.equiv _ ℂ).symm θ)) -
          (k : ℝ) * (2 * t) * Err * ∑ c, (D.choiceTree h).weight c := by rw [hw]; ring
    _ = ∑ c, x c * (D.choiceTree h).weight c := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun c _ => by simp only [hx]; ring

omit [∀ v, NeZero (n v)] [Fintype H] [∀ h, Fintype (C h)] in
/-- `u ↦ m_{1/4}(u) Re Tr(σ_{j,u} Y)` is integrable: the state is a continuous function of the
unitary `M^{-iu}`, which ranges over the compact unitary group. -/
theorem integrable_fourierWeight_mul_trace_state (t : ℝ) (k : ℕ)
    (pre : Config k (fun v => Fin (n v)) → ℂ) (p : ℝ) (j : Σ h, Option (C h))
    (Y : Matrix (Config k fun v => Fin (n v)) (Config k fun v => Fin (n v)) ℂ) :
    MeasureTheory.Integrable fun u =>
      Matrix.Transport.fourierWeight u * (D.state n t k pre p j u * Y).trace.re := by
  set M := (D.tree (projIcc (0 : ℝ) 1 zero_le_one p)).eval (D.input n t k)
  set v := Matrix.Transport.filteredVector (D.rootPath n t k p) pre
  set Φ := traceAdjointMap ((D.tree (projIcc (0 : ℝ) 1 zero_le_one p)).leafMap
    (D.input n t k) j).toLinearMap
  let G : Matrix (Config k fun v => Fin (n v)) (Config k fun v => Fin (n v)) ℂ → ℝ := fun U =>
    (Φ (vecMulVec (U *ᵥ v) (star (U *ᵥ v))) * Y).trace.re
  have hvec : Continuous fun U : Matrix (Config k fun v => Fin (n v))
      (Config k fun v => Fin (n v)) ℂ => vecMulVec (U *ᵥ v) (star (U *ᵥ v)) := by
    refine continuous_pi fun x => continuous_pi fun y => ?_
    simp only [vecMulVec_apply, mulVec, dotProduct, Pi.star_apply]
    fun_prop
  have hG : Continuous G := Complex.continuous_re.comp
    (((Φ.continuous_of_finiteDimensional.comp hvec).mul continuous_const).matrix_trace)
  have hstate : ∀ u, (D.state n t k pre p j u * Y).trace.re =
      G (hermitianUnitaryPath (CFC.log M) (-u)) := fun u => rfl
  obtain ⟨Cb, hCb⟩ :=
    (isCompact_unitaryGroup (Config k fun v => Fin (n v))).exists_bound_of_continuousOn
      hG.continuousOn
  have hmem : ∀ u, hermitianUnitaryPath (CFC.log M) (-u) ∈
      (unitaryGroup (Config k fun v => Fin (n v)) ℂ : Set _) := fun u =>
    Matrix.mem_unitaryGroup_iff.mpr (hermitianUnitaryPath_mul_conjTranspose _
      (IsSelfAdjoint.log (a := M)) (-u))
  simp_rw [hstate]
  have hint := (Real.integrable_sinhRatioDensity (s := 1 / 4) (by norm_num)).bdd_mul
    (f := fun u => G (hermitianUnitaryPath (CFC.log M) (-u)))
    ((hG.comp ((continuous_hermitianUnitaryPath _).comp continuous_neg)).aestronglyMeasurable)
    (Filter.Eventually.of_forall fun u => hCb _ (hmem u))
  simpa [mul_comm, Matrix.Transport.fourierWeight] using hint

omit [Fintype H] [∀ h, Fintype (C h)] in
/-- **Band factorization** `log C_h = ∑_g log C_{h,g}` (`06-transport.tex`, display
`transport:relative-factorization`, lines 501--509). -/
theorem cfc_log_relRatio_eq_sum (hD : D.IsAdmissible) {t : ℝ} (ht : 0 ≤ t) {k : ℕ}
    (hcomm : D.CrossBandCommute n t k) (h : H) :
    CFC.log (D.relRatio n t k h) = ∑ g, CFC.log (D.bandRelRatio n t k h g) := by
  have hA : ∀ g, (bandMetric n t k (D.old h g)).PosDef := fun g =>
    posDef_bandMetric (hD.old_isPartition h g) ht k
  have hN : ∀ c g, (bandMetric n t k (D.new h c g)).PosDef := fun c g =>
    posDef_bandMetric (Move.isPartition_apply (hD.old_isPartition h g) (hD.move_isValid h c g))
      ht k
  have hNN : ∀ c c' g g', g ≠ g' → Commute (bandMetric n t k (D.new h c g))
      (bandMetric n t k (D.new h c' g')) := fun c c' g g' hg =>
    hcomm ⟨h, some c⟩ ⟨h, some c'⟩ g g' hg
  have hB : ∀ g, ((D.choiceTree h).eval fun c => bandMetric n t k (D.new h c g)).PosDef :=
    fun g => Matrix.MeanTree.posDef_eval (fun c => hN c g) _
  have hAB : ∀ g g', g ≠ g' → Commute (bandMetric n t k (D.old h g))
      ((D.choiceTree h).eval fun c => bandMetric n t k (D.new h c g')) := fun g g' hg =>
    commute_eval_of_commute (fun c => hcomm ⟨h, none⟩ ⟨h, some c⟩ g g' hg) _
  have hAA : ∀ g g', g ≠ g' → Commute (bandMetric n t k (D.old h g))
      (bandMetric n t k (D.old h g')) := fun g g' hg => hcomm ⟨h, none⟩ ⟨h, none⟩ g g' hg
  have hrel : D.relRatio n t k h = (List.ofFn fun g => D.bandRelRatio n t k h g).prod := by
    simp only [relRatio, Matrix.Transport.relRatio, Matrix.Transport.choiceRoot, oldMetric,
      bandRelRatio]
    rw [show D.newMetric n t k h = fun c => (List.ofFn fun g => bandMetric n t k (D.new h c g)).prod
      from rfl, Matrix.MeanTree.eval_listProd_ofFn (fun c g => hN c g) hNN]
    exact listProd_whiten hA hB hAA hAB
  rw [hrel]
  refine cfc_log_listProd (fun g => D.posDef_bandRelRatio hD ht k h g) fun g g' hg => ?_
  have hBB := Matrix.MeanTree.commute_eval_band (fun c g => hN c g) hNN (D.choiceTree h) hg
  have r1 : ∀ r : ℝ, Commute (bandMetric n t k (D.old h g) ^ r)
      (bandMetric n t k (D.old h g') ^ (-(1 / 2) : ℝ)) := fun r =>
    (hA g).commute_rpow (hA g') (hAA g g' hg) r _
  have r2 : ∀ r : ℝ, Commute (bandMetric n t k (D.old h g) ^ r)
      ((D.choiceTree h).eval fun c => bandMetric n t k (D.new h c g')) := fun r =>
    (hA g).commute_rpow_left (hAB g g' hg) r
  have r3 : ∀ r : ℝ, Commute ((D.choiceTree h).eval fun c => bandMetric n t k (D.new h c g))
      (bandMetric n t k (D.old h g') ^ r) := fun r =>
    ((hA g').commute_rpow_left (hAB g' g hg.symm) r).symm
  unfold bandRelRatio
  refine Commute.mul_left (Commute.mul_left ?_ ?_) ?_
  all_goals refine Commute.mul_right (Commute.mul_right ?_ ?_) ?_
  all_goals first | exact r1 _ | exact r2 _ | exact r3 _ | exact hBB

/-- **Entropy-gain lower bound** (area-law paper, Proposition 7.4, display
`transport:entropy-gain`, `06-transport.tex` lines 409--416 and 495--583). The constants
`c₀`, `C`, `e` are universal; `β_k = O(log(k+1))` depends only on the fixed data. -/
theorem exists_entropyGain_le_exactDerivative :
    ∃ c₀ Cent eent : ℝ, 0 < c₀ ∧
      ∀ {V : Type*} [Fintype V] [DecidableEq V] (n : V → ℕ) [∀ v, NeZero (n v)]
        {K : ℕ} {H : Type*} [Fintype H] [DecidableEq H] {C : H → Type*}
        [∀ h, Fintype (C h)] [∀ h, DecidableEq (C h)] (D : TransportData V K H C),
        D.IsAdmissible → ∀ {a ℓ : ℝ}, 0 < a → 1 ≤ ℓ → a * ℓ ≤ c₀ →
        (∀ k, D.CrossBandCommute n (a / 2) k) →
        (∀ h c g, logDim n (D.move h c g).subsystem ≤ ℓ) →
        ∃ β : ℕ → ℝ, (β =O[atTop] fun k : ℕ => Real.log (k + 1)) ∧
          ∀ (k : ℕ) (pre : Config k (fun v => Fin (n v)) → ℂ),
            pre ∈ symmetricSubspace k (fun v => Fin (n v)) → pre ≠ 0 → ∀ p ∈ Ioo (0 : ℝ) 1,
              (k : ℝ) * a * D.entropyGain n (a / 2) k pre p -
                  Cent * k * a * K * a ^ (1 / 4 : ℝ) * ℓ ^ eent - β k ≤
                D.exactDerivative n (a / 2) k pre p := by
  obtain ⟨c₁, Cpin, epin, hc₁, hpinAll⟩ := exists_relativePin
  refine ⟨min c₁ (1 / 4), |Cpin| / 2, max epin 0, lt_min hc₁ (by norm_num), ?_⟩
  intro V _ _ n _ K H _ _ C _ _ D hD a ℓ ha hℓ haℓ hcomm hdim
  have haℓc : a * ℓ ≤ c₁ := haℓ.trans (min_le_left _ _)
  have ha4 : a ≤ 1 / 4 := by
    have : a * 1 ≤ a * ℓ := mul_le_mul_of_nonneg_left hℓ ha.le
    linarith [min_le_right c₁ (1 / 4 : ℝ)]
  have ht0 : (0 : ℝ) < a / 2 := by positivity
  have ht4 : a / 2 < 1 / 4 := by linarith
  have h2t : 2 * (a / 2) = a := by ring
  have hbound : ∀ h (c : C h) g, 2 * (a / 2) * logDim n (D.move h c g).subsystem ≤ c₁ :=
    fun h c g => by
      rw [h2t]
      exact (mul_le_mul_of_nonneg_left (hdim h c g) ha.le).trans haℓc
  choose b hbpos hbO hbpin using fun h (c : C h) g => hpinAll n (D.old h g)
    (hD.old_isPartition h g) (D.move h c g) (hD.move_isValid h c g) ht0 ht4 (hbound h c g)
  -- A common prefactor `b_k = exp(-L_k)`.
  set L : ℕ → ℝ := fun k => ∑ x : (Σ h, C h × Fin K),
    max (-Real.log (b x.1 x.2.1 x.2.2 k)) 0 with hL
  have hLx : ∀ k h (c : C h) g, -Real.log (b h c g k) ≤ L k := fun k h c g =>
    (le_max_left _ _).trans (Finset.single_le_sum (f := fun x : (Σ h, C h × Fin K) =>
      max (-Real.log (b x.1 x.2.1 x.2.2 k)) 0) (fun _ _ => le_max_right _ _)
      (Finset.mem_univ ⟨h, c, g⟩))
  set bmin : ℕ → ℝ := fun k => Real.exp (-L k) with hbmin
  have hbmin_pos : ∀ k, 0 < bmin k := fun k => Real.exp_pos _
  have hbmin_le : ∀ k h (c : C h) g, bmin k ≤ b h c g k := fun k h c g => by
    calc Real.exp (-L k) ≤ Real.exp (Real.log (b h c g k)) :=
          Real.exp_le_exp.mpr (by linarith [hLx k h c g])
      _ = b h c g k := Real.exp_log (hbpos h c g k)
  have hLO : L =O[atTop] fun k : ℕ => Real.log (k + 1) := by
    refine Asymptotics.IsBigO.fun_sum fun x _ => ?_
    refine (Asymptotics.IsBigO.of_bound 1 (Filter.Eventually.of_forall fun k => ?_)).trans
      (hbO x.1 x.2.1 x.2.2)
    simp only [Real.norm_eq_abs, one_mul]
    rw [abs_of_nonneg (le_max_right _ _)]
    exact max_le (le_abs_self _) (abs_nonneg _)
  -- A common error `E = |C| a^{1/4} ℓ^{max(e,0)}`.
  set Err : ℝ := |Cpin| * a ^ (1 / 4 : ℝ) * ℓ ^ (max epin 0) with hErrDef
  have hErr : ∀ h (c : C h) g, Cpin * (2 * (a / 2)) ^ (1 / 4 : ℝ) *
      logDim n (D.move h c g).subsystem ^ epin ≤ Err := by
    intro h c g
    rw [h2t]
    have hx1 := one_le_logDim (n := n) (D.move h c g).subsystem
    have hxℓ := hdim h c g
    have hpow : logDim n (D.move h c g).subsystem ^ epin ≤ ℓ ^ (max epin 0) := by
      rcases le_total 0 epin with he | he
      · rw [max_eq_left he]
        exact Real.rpow_le_rpow (by linarith) hxℓ he
      · rw [max_eq_right he, Real.rpow_zero]
        exact Real.rpow_le_one_of_one_le_of_nonpos hx1 he
    have hA : 0 ≤ a ^ (1 / 4 : ℝ) := Real.rpow_nonneg ha.le _
    have hx0 : 0 ≤ logDim n (D.move h c g).subsystem ^ epin := Real.rpow_nonneg (by linarith) _
    calc Cpin * a ^ (1 / 4 : ℝ) * logDim n (D.move h c g).subsystem ^ epin
        ≤ |Cpin| * a ^ (1 / 4 : ℝ) * logDim n (D.move h c g).subsystem ^ epin :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self _) hA) hx0
      _ ≤ Err := mul_le_mul_of_nonneg_left hpow (mul_nonneg (abs_nonneg _) hA)
  -- Per-move pins with the common prefactor and error.
  have hpinU : ∀ (k : ℕ) h g (θ : SiteConfig n → ℂ), star θ ⬝ᵥ θ = 1 → ∀ c : C h,
      (bmin k * Real.exp ((k : ℝ) * (2 * (a / 2)) *
        (moveEta n (D.old h g) (D.move h c g) ((EuclideanSpace.equiv _ ℂ).symm θ) - Err))) •
          coherentProj k θ ≤
        bandMetric n (a / 2) k (D.old h g) ^ (-(1 / 2) : ℝ) *
          bandMetric n (a / 2) k (D.new h c g) *
            bandMetric n (a / 2) k (D.old h g) ^ (-(1 / 2) : ℝ) := by
    intro k h g θ hθ c
    refine le_trans ?_ (hbpin h c g k θ hθ)
    refine smul_le_smul_of_nonneg_right ?_
      (nonneg_iff_posSemidef.mpr (posSemidef_vecMulVec_self_star _))
    refine mul_le_mul (hbmin_le k h c g) (Real.exp_le_exp.mpr ?_) (Real.exp_pos _).le
      (hbpos h c g k).le
    have hk : 0 ≤ (k : ℝ) * (2 * (a / 2)) := by positivity
    exact mul_le_mul_of_nonneg_left (by linarith [hErr h c g]) hk
  -- The band gain: the conditional pin and the logarithmic passage.
  set F : ∀ h, Fin K → (SiteConfig n → ℂ) → ℝ := fun h g θ => ∑ c, (D.choiceTree h).weight c *
    moveEta n (D.old h g) (D.move h c g) ((EuclideanSpace.equiv _ ℂ).symm θ) with hFdef
  have hFc : ∀ h g, Continuous (F h g) := fun h g =>
    continuous_finsetSum _ fun c _ => continuous_const.mul (continuous_moveEta _ _)
  have hgain : ∀ (k : ℕ) h g (ρ : Matrix (Config k fun v => Fin (n v))
      (Config k fun v => Fin (n v)) ℂ), ρ.PosSemidef → ρ.trace = 1 →
      symProj (copyPerm (SiteConfig n) k) * ρ = ρ →
      Real.log (bmin k) + (k : ℝ) * a * (coherentIntegral k (base n) ρ (F h g) - Err) -
          Real.log (symDim (SiteConfig n) k) ≤
        (ρ * CFC.log (D.bandRelRatio n (a / 2) k h g)).trace.re := by
    intro k h g ρ hρ htr hsym
    have key := coherentIntegral_sub_log_le_re_trace_mul_log (base n)
      (D.posDef_bandRelRatio hD ht0.le k h g)
      (fun s => D.commute_permOp_bandRelRatio (t := a / 2) k h g s)
      (φ := fun θ => (Real.log (bmin k) - (k : ℝ) * a * Err) + ((k : ℝ) * a) * F h g θ)
      (continuous_const.add (continuous_const.mul (hFc h g))) (fun θ hθ => by
        have hc := D.smul_coherentProj_le_bandRelRatio hD ht0.le k h g (hbmin_pos k) θ
          (hpinU k h g θ hθ)
        rw [h2t] at hc
        convert hc using 2
        rw [show Real.log (bmin k) - (k : ℝ) * a * Err + (k : ℝ) * a * F h g θ =
            Real.log (bmin k) + (k : ℝ) * a * (F h g θ - Err) by ring, Real.exp_add,
          Real.exp_log (hbmin_pos k)])
      hρ htr hsym
    rw [coherentIntegral_affine (base n) htr hsym (hFc h g)] at key
    linarith
  -- Summation over bands at fixed history and Fourier time.
  have hsum : ∀ (k : ℕ) (pre : Config k (fun v => Fin (n v)) → ℂ),
      pre ∈ symmetricSubspace k (fun v => Fin (n v)) → pre ≠ 0 → ∀ p ∈ Ioo (0 : ℝ) 1, ∀ h u,
      (k : ℝ) * a * ∑ g, coherentIntegral k (base n) (D.state n (a / 2) k pre p ⟨h, none⟩ u)
          (F h g) - K * ((k : ℝ) * a * Err + Real.log (symDim (SiteConfig n) k) -
            Real.log (bmin k)) ≤
        (D.state n (a / 2) k pre p ⟨h, none⟩ u * CFC.log (D.relRatio n (a / 2) k h)).trace.re := by
    intro k pre hsym hpre p hp h u
    set ρs := D.state n (a / 2) k pre p ⟨h, none⟩ u
    have hσ := D.posSemidef_state hD ht0.le (hcomm k) pre p ⟨h, none⟩ u
    have hσ1 := D.trace_state hD ht0.le (hcomm k) hpre hp ⟨h, none⟩ u
    have hσs := D.symProj_mul_state hD ht0.le (hcomm k) hsym p ⟨h, none⟩ u
    rw [D.cfc_log_relRatio_eq_sum hD ht0.le (hcomm k) h, Matrix.mul_sum, Matrix.trace_sum,
      Complex.re_sum]
    have hle := Finset.sum_le_sum fun g (_ : g ∈ Finset.univ) => hgain k h g ρs hσ hσ1 hσs
    have hcalc : ∑ g : Fin K, (Real.log (bmin k) + (k : ℝ) * a *
        (coherentIntegral k (base n) ρs (F h g) - Err) - Real.log (symDim (SiteConfig n) k)) =
        (k : ℝ) * a * ∑ g, coherentIntegral k (base n) ρs (F h g) - K * ((k : ℝ) * a * Err +
          Real.log (symDim (SiteConfig n) k) - Real.log (bmin k)) := by
      simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.mul_sum, mul_sub,
        Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring
    linarith
  -- Integration in the Fourier time and summation over histories.
  refine ⟨fun k => (K : ℝ) / 2 * (Real.log (symDim (SiteConfig n) k) + L k),
    ((log_symDim_isBigO (Ω := SiteConfig n)).add hLO).const_mul_left _, ?_⟩
  intro k pre hsym hpre p hp
  have hm := Real.integral_sinhRatioDensity (s := 1 / 4) (by norm_num)
  have hmi : MeasureTheory.Integrable Matrix.Transport.fourierWeight :=
    Real.integrable_sinhRatioDensity (s := 1 / 4) (by norm_num)
  have hm' : ∫ u, Matrix.Transport.fourierWeight u = 1 / 2 := by
    change ∫ u, Real.sinhRatioDensity (1 / 4) u = 1 / 2
    rw [hm]; norm_num
  have hEint : ∀ h g, MeasureTheory.Integrable fun u => Matrix.Transport.fourierWeight u *
      coherentIntegral k (base n) (D.state n (a / 2) k pre p ⟨h, none⟩ u) (F h g) := by
    intro h g
    refine (D.integrable_fourierWeight_mul_trace_state (a / 2) k pre p ⟨h, none⟩
      (coherentAverage k (base n) (F h g))).congr (Filter.Eventually.of_forall fun u => ?_)
    simp only [trace_mul_coherentAverage k (base n) (hFc h g)]
  set β' := (K : ℝ) * ((k : ℝ) * a * Err + Real.log (symDim (SiteConfig n) k) -
    Real.log (bmin k))
  have hhist : ∀ h, (k : ℝ) * a * ∑ g, (∫ u, Matrix.Transport.fourierWeight u *
      coherentIntegral k (base n) (D.state n (a / 2) k pre p ⟨h, none⟩ u) (F h g)) - β' / 2 ≤
      ∫ u, Matrix.Transport.fourierWeight u *
        (D.state n (a / 2) k pre p ⟨h, none⟩ u * CFC.log (D.relRatio n (a / 2) k h)).trace.re := by
    intro h
    have e : ∀ u, Matrix.Transport.fourierWeight u * ((k : ℝ) * a * ∑ g,
        coherentIntegral k (base n) (D.state n (a / 2) k pre p ⟨h, none⟩ u) (F h g) - β') =
        (∑ g, (k : ℝ) * a * (Matrix.Transport.fourierWeight u *
          coherentIntegral k (base n) (D.state n (a / 2) k pre p ⟨h, none⟩ u) (F h g))) -
            β' * Matrix.Transport.fourierWeight u := fun u => by
      rw [mul_sub, Finset.mul_sum, Finset.mul_sum]
      congr 1
      · exact Finset.sum_congr rfl fun g _ => by ring
      · ring
    have hsumint : MeasureTheory.Integrable fun u => ∑ g, (k : ℝ) * a *
        (Matrix.Transport.fourierWeight u *
          coherentIntegral k (base n) (D.state n (a / 2) k pre p ⟨h, none⟩ u) (F h g)) :=
      MeasureTheory.integrable_finsetSum _ fun g _ => (hEint h g).const_mul _
    have hlowint : MeasureTheory.Integrable fun u => Matrix.Transport.fourierWeight u *
        ((k : ℝ) * a * ∑ g,
          coherentIntegral k (base n) (D.state n (a / 2) k pre p ⟨h, none⟩ u) (F h g) - β') :=
      (hsumint.sub (hmi.const_mul β')).congr (Filter.Eventually.of_forall fun u => (e u).symm)
    have hlow : ∫ u, Matrix.Transport.fourierWeight u * ((k : ℝ) * a * ∑ g,
        coherentIntegral k (base n) (D.state n (a / 2) k pre p ⟨h, none⟩ u) (F h g) - β') =
        (k : ℝ) * a * ∑ g, (∫ u, Matrix.Transport.fourierWeight u *
          coherentIntegral k (base n) (D.state n (a / 2) k pre p ⟨h, none⟩ u) (F h g)) -
            β' / 2 := by
      rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall e),
        MeasureTheory.integral_sub hsumint (hmi.const_mul _),
        MeasureTheory.integral_finsetSum _ fun g _ => (hEint h g).const_mul _,
        MeasureTheory.integral_const_mul, hm']
      simp only [MeasureTheory.integral_const_mul]
      rw [Finset.mul_sum]
      ring
    rw [← hlow]
    refine MeasureTheory.integral_mono hlowint
      (D.integrable_fourierWeight_mul_trace_state (a / 2) k pre p ⟨h, none⟩ _) fun u => ?_
    exact mul_le_mul_of_nonneg_left (hsum k pre hsym hpre p hp h u)
      (Real.sinhRatioDensity_pos (by norm_num) u).le
  have hw := D.histTree.sum_weight
  calc (k : ℝ) * a * D.entropyGain n (a / 2) k pre p -
        |Cpin| / 2 * k * a * K * a ^ (1 / 4 : ℝ) * ℓ ^ max epin 0 -
          (K : ℝ) / 2 * (Real.log (symDim (SiteConfig n) k) + L k)
      = ∑ h, D.histTree.weight h * ((k : ℝ) * a * ∑ g, (∫ u, Matrix.Transport.fourierWeight u *
          coherentIntegral k (base n) (D.state n (a / 2) k pre p ⟨h, none⟩ u) (F h g)) -
            β' / 2) := by
        have hEG : D.entropyGain n (a / 2) k pre p = ∑ h, D.histTree.weight h * ∑ g,
            ∫ u, Matrix.Transport.fourierWeight u *
              coherentIntegral k (base n) (D.state n (a / 2) k pre p ⟨h, none⟩ u) (F h g) := by
          unfold entropyGain
          simp only [Finset.mul_sum]
          rfl
        have hRHS : ∑ h, D.histTree.weight h * ((k : ℝ) * a * ∑ g,
            (∫ u, Matrix.Transport.fourierWeight u *
              coherentIntegral k (base n) (D.state n (a / 2) k pre p ⟨h, none⟩ u) (F h g)) -
                β' / 2) = (k : ℝ) * a * ∑ h, D.histTree.weight h * ∑ g,
            (∫ u, Matrix.Transport.fourierWeight u *
              coherentIntegral k (base n) (D.state n (a / 2) k pre p ⟨h, none⟩ u) (F h g)) -
                β' / 2 := by
          have e2 : ∀ (h : H) (X : ℝ), D.histTree.weight h * ((k : ℝ) * a * X - β' / 2) =
              (k : ℝ) * a * (D.histTree.weight h * X) - D.histTree.weight h * (β' / 2) :=
            fun h X => by ring
          simp_rw [e2]
          rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.sum_mul, hw, one_mul]
        have hlogb : Real.log (bmin k) = -L k := Real.log_exp _
        have key : ∀ S : ℝ, (k : ℝ) * a * S -
            |Cpin| / 2 * k * a * K * a ^ (1 / 4 : ℝ) * ℓ ^ max epin 0 -
              (K : ℝ) / 2 * (Real.log (symDim (SiteConfig n) k) + L k) =
            (k : ℝ) * a * S - β' / 2 := fun S => by
          simp only [β', hlogb, hErrDef]
          ring
        rw [hEG, hRHS]
        exact key _
    _ ≤ D.exactDerivative n (a / 2) k pre p :=
        Finset.sum_le_sum fun h _ => mul_le_mul_of_nonneg_left (hhist h)
          (hD.histWeight_pos h).le

end TransportData

end TensorPower.ReplicaTransport
