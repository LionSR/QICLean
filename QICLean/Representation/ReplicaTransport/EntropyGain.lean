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

/-- The entropy of a move is continuous in the one-copy vector. -/
theorem continuous_moveEta (π : PYF V) (m : Move V) :
    Continuous fun θ : SiteConfig n → ℂ => moveEta n π m ((EuclideanSpace.equiv _ ℂ).symm θ) := by
  sorry

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
  sorry

end TransportData

end TensorPower.ReplicaTransport
