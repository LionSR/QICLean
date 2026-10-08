/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.Transport.EnergyBlock
import QICLean.Representation.ReplicaTransport.Prerequisites
import QICLean.Representation.ReplicaTransport.States

/-!
# The energy estimate of the transport proposition

Area-law paper, Proposition 7.4, display `transport:energy` (`06-transport.tex`
lines 417--426, proof lines 588--766): if `H̄ pre = E₀ pre`, then
$$\langle v,\bar Hv\rangle\le 2E_0+Ca^2\ell^C\sum_iW_i(p)\sum_{j\in\mathcal J_i}\pi_j
  \int m_{1/4}(u)\int\eta_{i,j}^{1/8}\,d\mu_{\sigma_{j,u}}\,du+o_k(1).$$

Proof outline:

* `commute_input_copyMean_of_not_mem_splitLeaves` — an unsplit leaf metric commutes with
  `h̄_i` (lines 359--364);
* `skewSquare_input_eq_bandMetric` — at a split leaf only the exceptional band fails to
  commute, and the other factors cancel in `O_{i,j}` (lines 732--735);
* `splitEta_eq_splitBandEta` — `η_{i,j}` is the split entropy of the exceptional band;
* `trace_state_skewSquare_le` — Lemma 6.5 at every split term--leaf pair, with one common
  remainder (display `transport:symbol-cost`, lines 736--748);
* `Matrix.Transport.re_star_dotProduct_mulVec_le_energy` (generic block argument) per
  term, then summation over `i` using `M^s v = pre / N` and `H̄ pre = E₀ pre`
  (lines 750--766).

The proofs are written from the paper; no Lean source was adapted.
-/

open scoped Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator unitInterval
open Matrix Set Filter Topology PermutationRepresentation Entropy

noncomputable section

namespace TensorPower.ReplicaTransport

variable {V : Type*} [Fintype V] [DecidableEq V] {n : V → ℕ} [∀ v, NeZero (n v)]

section Helpers

variable {m : Type*} [Fintype m] [DecidableEq m]

/-- The nonsingular inverse of a matrix commutes with everything the matrix commutes with. -/
theorem _root_.Matrix.commute_inv_left {A X : Matrix m m ℂ} (h : Commute A X) :
    Commute A⁻¹ X := by
  by_cases hA : IsUnit A.det
  · have e : A⁻¹ * X * (A * A⁻¹) = A⁻¹ * (A * X) * A⁻¹ := by
      rw [h.eq]; simp only [Matrix.mul_assoc]
    change A⁻¹ * X = X * A⁻¹
    rw [Matrix.mul_nonsing_inv _ hA, Matrix.mul_one, ← Matrix.mul_assoc A⁻¹ A,
      Matrix.nonsing_inv_mul _ hA, Matrix.one_mul] at e
    exact e
  · rw [Matrix.nonsing_inv_apply_not_isUnit _ hA]
    exact Commute.zero_left X

/-- Conjugating by the square root of `A * R` with `R` commuting with `A` and `X` only sees
`A` (`06-transport.tex` lines 732--735). -/
theorem _root_.Matrix.PosDef.rpow_conj_mul_of_commute {A R X : Matrix m m ℂ} (hA : A.PosDef)
    (hR : R.PosDef) (hAR : Commute A R) (hRX : Commute R X) :
    (A * R) ^ (-(1 / 2) : ℝ) * X * (A * R) ^ (1 / 2 : ℝ) =
      A ^ (-(1 / 2) : ℝ) * X * A ^ (1 / 2 : ℝ) := by
  rw [hA.mul_rpow_of_commute hR hAR, hA.mul_rpow_of_commute hR hAR]
  have h1 : Commute (R ^ (-(1 / 2) : ℝ)) X := hR.commute_rpow_left hRX _
  have h2 : Commute (R ^ (-(1 / 2) : ℝ)) (A ^ (1 / 2 : ℝ)) :=
    (hA.commute_rpow hR hAR _ _).symm
  calc A ^ (-(1 / 2) : ℝ) * R ^ (-(1 / 2) : ℝ) * X * (A ^ (1 / 2 : ℝ) * R ^ (1 / 2 : ℝ))
      = A ^ (-(1 / 2) : ℝ) * (R ^ (-(1 / 2) : ℝ) * X) * A ^ (1 / 2 : ℝ) *
          R ^ (1 / 2 : ℝ) := by simp only [Matrix.mul_assoc]
    _ = A ^ (-(1 / 2) : ℝ) * X * (R ^ (-(1 / 2) : ℝ) * A ^ (1 / 2 : ℝ)) *
          R ^ (1 / 2 : ℝ) := by rw [h1.eq]; simp only [Matrix.mul_assoc]
    _ = A ^ (-(1 / 2) : ℝ) * X * A ^ (1 / 2 : ℝ) *
          (R ^ (-(1 / 2) : ℝ) * R ^ (1 / 2 : ℝ)) := by rw [h2.eq]; simp only [Matrix.mul_assoc]
    _ = A ^ (-(1 / 2) : ℝ) * X * A ^ (1 / 2 : ℝ) := by
          rw [hR.rpow_neg_mul_rpow, Matrix.mul_one]

/-- A product of pairwise commuting positive definite matrices is positive definite. -/
theorem _root_.Matrix.posDef_list_ofFn_prod {K : ℕ} (f : Fin K → Matrix m m ℂ)
    (hf : ∀ g, (f g).PosDef) (hcomm : ∀ g g', g ≠ g' → Commute (f g) (f g')) :
    (List.ofFn f).prod.PosDef := by
  induction K with
  | zero => simpa using Matrix.PosDef.one
  | succ K ih =>
    rw [List.ofFn_succ, List.prod_cons]
    refine (hf 0).mul_of_commute (ih _ (fun g => hf _) fun g g' hg => hcomm _ _ ?_) ?_
    · exact fun e => hg (Fin.succ_injective _ e)
    · refine Commute.list_prod_right _ _ fun M hM => ?_
      obtain ⟨g, rfl⟩ := List.mem_ofFn.mp hM
      exact hcomm _ _ (Fin.succ_ne_zero g).symm

/-- **Single-factor reduction.** For pairwise commuting positive definite factors `f g'`, the
similarity transform by the square root of `∏_{g'} f g'` of a matrix commuting with every
factor except `f g` is the similarity transform by the square root of `f g`. -/
theorem _root_.Matrix.list_ofFn_prod_rpow_conj {K : ℕ} (f : Fin K → Matrix m m ℂ)
    (hf : ∀ g, (f g).PosDef) (hcomm : ∀ g g', g ≠ g' → Commute (f g) (f g')) (g : Fin K)
    {X : Matrix m m ℂ} (hX : ∀ g', g' ≠ g → Commute (f g') X) :
    (List.ofFn f).prod ^ (-(1 / 2) : ℝ) * X * (List.ofFn f).prod ^ (1 / 2 : ℝ) =
      f g ^ (-(1 / 2) : ℝ) * X * f g ^ (1 / 2 : ℝ) := by
  induction K with
  | zero => exact g.elim0
  | succ K ih =>
    have htailPD : (List.ofFn fun g' => f g'.succ).prod.PosDef :=
      Matrix.posDef_list_ofFn_prod _ (fun _ => hf _) fun a b hab =>
        hcomm _ _ fun e => hab (Fin.succ_injective _ e)
    have hcomm0 : Commute (f 0) (List.ofFn fun g' => f g'.succ).prod :=
      Commute.list_prod_right _ _ fun M hM => by
        obtain ⟨g', rfl⟩ := List.mem_ofFn.mp hM
        exact hcomm _ _ (Fin.succ_ne_zero g').symm
    rw [List.ofFn_succ, List.prod_cons]
    cases g using Fin.cases with
    | zero =>
      refine (hf 0).rpow_conj_mul_of_commute htailPD hcomm0 ?_
      refine Commute.list_prod_left _ _ fun M hM => ?_
      obtain ⟨g', rfl⟩ := List.mem_ofFn.mp hM
      exact hX _ (Fin.succ_ne_zero g')
    | succ g' =>
      rw [hcomm0.eq, htailPD.rpow_conj_mul_of_commute (hf 0) hcomm0.symm
        (hX 0 (Fin.succ_ne_zero g').symm)]
      exact ih _ (fun _ => hf _) (fun a b hab => hcomm _ _ fun e => hab (Fin.succ_injective _ e))
        g' fun a ha => hX _ fun e => ha (Fin.succ_injective _ e)

end Helpers

omit [∀ v, NeZero (n v)] in
/-- The copy permutations of a subsystem `Q` commute with the copy mean of an operator
supported in `Q`: they differ from permutations of entire copies by permutations of `Qᶜ`,
which act off the support. -/
theorem commute_permOp_subsystemPerm_copyMean_of_subset {k : ℕ} {Q D : Finset V}
    {h : Matrix (SiteConfig n) (SiteConfig n) ℂ} (hh : IsSupportedOn h D) (hDQ : D ⊆ Q)
    (s : Equiv.Perm (Fin k)) :
    Commute (permOp (subsystemPerm k (fun v => Fin (n v)) Q) s) (copyMean n k h) := by
  set P := permOp (subsystemPerm k (fun v => Fin (n v)) Q) s
  set R := permOp (subsystemPerm k (fun v => Fin (n v)) Qᶜ) s
  set R' := permOp (subsystemPerm k (fun v => Fin (n v)) Qᶜ) s⁻¹
  have hRR : R * R' = 1 := by simp only [R, R', ← map_mul, mul_inv_cancel, map_one]
  have hcopy : permOp (copyPerm (SiteConfig n) k) s = P * R :=
    permOp_of_eq_mul _ _ _ (fun g => copyPerm_eq_mul_compl Q g) s
  have hdisj : Disjoint Qᶜ D := disjoint_compl_left.mono_right hDQ
  have hR'c : Commute R' (copyMean n k h) := by
    unfold copyMean
    exact Commute.smul_right (Commute.sum_right _ _ _ fun j _ =>
      commute_permOp_subsystemPerm_siteOp_of_disjoint hh hdisj j s⁻¹) _
  have hX := commute_copyPerm_copyMean k h s
  rw [hcopy] at hX
  change P * copyMean n k h = copyMean n k h * P
  calc P * copyMean n k h = P * R * R' * copyMean n k h := by
        rw [Matrix.mul_assoc P, hRR, Matrix.mul_one]
    _ = P * R * copyMean n k h * R' := by
        rw [Matrix.mul_assoc (P * R), hR'c.eq, ← Matrix.mul_assoc]
    _ = copyMean n k h * (P * R) * R' := by rw [hX.eq]
    _ = copyMean n k h * P := by rw [Matrix.mul_assoc, Matrix.mul_assoc, hRR, Matrix.mul_one]

omit [∀ v, NeZero (n v)] in
/-- A replica metric of a subsystem containing, or disjoint from, the support of `h`
commutes with the copy mean of `h` (`05-replicas.tex` lines 470--473). -/
theorem commute_replicaMetric_copyMean {t : ℝ} {k : ℕ} {Q D : Finset V}
    {h : Matrix (SiteConfig n) (SiteConfig n) ℂ} (hh : IsSupportedOn h D)
    (hQD : D ⊆ Q ∨ Disjoint Q D) :
    Commute (replicaMetric (fun v => Fin (n v)) t k Q) (copyMean n k h) := by
  rcases hQD with hDQ | hQD
  · exact commute_labelObservable_of_forall_commute _
      (fun s => commute_permOp_subsystemPerm_copyMean_of_subset hh hDQ s) _
  · unfold copyMean
    exact Commute.smul_right (Commute.sum_right _ _ _ fun j _ =>
      commute_labelObservable_siteOp_of_disjoint hh hQD j _) _

omit [∀ v, NeZero (n v)] in
/-- A band metric commutes with the copy mean of an operator supported in one of its
parts (`05-replicas.tex` lines 470--473; `06-transport.tex` lines 359--364). -/
theorem commute_bandMetric_copyMean_of_contains {π : PYF V} (hπ : π.IsPartition) {t : ℝ}
    (k : ℕ) {D : Finset V} {h : Matrix (SiteConfig n) (SiteConfig n) ℂ}
    (hh : IsSupportedOn h D) (hD : π.Contains D) :
    Commute (bandMetric n t k π) (copyMean n k h) := by
  obtain ⟨hPY, hPF, hYF, -⟩ := hπ
  have key : (D ⊆ π.P ∨ Disjoint π.P D) ∧ (D ⊆ π.Y ∨ Disjoint π.Y D) ∧
      (D ⊆ π.F ∨ Disjoint π.F D) := by
    rcases hD with hD | hD | hD
    · exact ⟨Or.inl hD, Or.inr (hPY.symm.mono_right hD), Or.inr (hPF.symm.mono_right hD)⟩
    · exact ⟨Or.inr (hPY.mono_right hD), Or.inl hD, Or.inr (hYF.symm.mono_right hD)⟩
    · exact ⟨Or.inr (hPF.mono_right hD), Or.inr (hYF.mono_right hD), Or.inl hD⟩
  obtain ⟨kP, kY, kF⟩ := key
  unfold bandMetric leafMetric leafRoot
  refine Commute.pow_left ?_ 2
  exact ((Matrix.commute_inv_left (commute_replicaMetric_copyMean hh kP)).mul_left
    (Matrix.commute_inv_left (commute_replicaMetric_copyMean hh kF))).mul_left
      (commute_replicaMetric_copyMean hh kY)

/-- `x ^ (1/8) ≥ 0` for every real `x` (for `x < 0` the real power is
`exp(log x / 8) cos(π/8)`). -/
theorem rpow_one_div_eight_nonneg (x : ℝ) : 0 ≤ x ^ (1 / 8 : ℝ) := by
  rcases le_or_gt 0 x with hx | hx
  · exact Real.rpow_nonneg hx _
  · rw [Real.rpow_def_of_neg hx]
    refine mul_nonneg (Real.exp_pos _).le (Real.cos_nonneg_of_mem_Icc ⟨?_, ?_⟩) <;>
      nlinarith [Real.pi_pos]

/-- The coherent integral of a nonnegative function against a positive semidefinite
matrix is nonnegative. -/
theorem coherentIntegral_nonneg {Ω : Type*} [Fintype Ω] [DecidableEq Ω] {k : ℕ} (a : Ω)
    {ρ : Matrix (Fin k → Ω) (Fin k → Ω) ℂ} (hρ : ρ.PosSemidef) {f : (Ω → ℂ) → ℝ}
    (hf : ∀ θ, 0 ≤ f θ) : 0 ≤ coherentIntegral k a ρ f := by
  unfold coherentIntegral
  refine mul_nonneg (Nat.cast_nonneg _) (MeasureTheory.integral_nonneg fun U =>
    mul_nonneg (hf _) ?_)
  rw [coherentProj, Matrix.mul_vecMulVec, Matrix.trace_vecMulVec, dotProduct_comm]
  exact (Complex.nonneg_iff.mp (hρ.dotProduct_mulVec_nonneg _)).1

omit [DecidableEq V] in
/-- `log(e dim x) ≥ 1`. -/
theorem one_le_logDim (x : Finset V) : 1 ≤ logDim n x := by
  unfold logDim
  have h0 : 0 < ∏ v ∈ x, n v := Finset.prod_pos fun v _ => Nat.pos_of_ne_zero (NeZero.ne _)
  have h1 : (1 : ℝ) ≤ ∏ v ∈ x, (n v : ℝ) := by
    rw [← Nat.cast_prod]; exact_mod_cast h0
  rw [Real.log_mul (Real.exp_pos 1).ne' (by positivity), Real.log_exp]
  linarith [Real.log_nonneg h1]

namespace TransportData

variable {K : ℕ} {H : Type*} [Fintype H] [DecidableEq H] {C : H → Type*}
  [∀ h, Fintype (C h)] [∀ h, DecidableEq (C h)] (D : TransportData V K H C)
  {ι : Type*} [Fintype ι] (E : EnergyTerms V n ι)

omit [Fintype H] [DecidableEq H] [∀ h, Fintype (C h)] [∀ h, DecidableEq (C h)] [∀ v, NeZero (n v)] in
/-- A terminal input is the product of the band metrics of its leaf. -/
theorem input_eq_prod (t : ℝ) (k : ℕ) (j : Σ h, Option (C h)) :
    D.input n t k j = (List.ofFn fun g => bandMetric n t k (D.leafPart j g)).prod := by
  rcases j with ⟨h, _ | c⟩ <;> rfl

omit [∀ h, DecidableEq (C h)] [DecidableEq H] in
theorem forall_contains_of_not_mem_splitLeaves {i : ι} {j : Σ h, Option (C h)}
    (hj : j ∉ D.splitLeaves E i) (g : Fin K) : (D.leafPart j g).Contains (E.support i) := by
  classical
  by_contra hg
  exact hj (Finset.mem_filter.mpr ⟨Finset.mem_univ _, g, hg⟩)

/-- **Unsplit leaves commute with the term** (`06-transport.tex` lines 359--364). -/
theorem commute_input_copyMean_of_not_mem_splitLeaves (hD : D.IsAdmissible) {t : ℝ}
    (k : ℕ) (hEsupp : ∀ i, IsSupportedOn (E.term i) (E.support i)) {i : ι}
    {j : Σ h, Option (C h)} (hj : j ∉ D.splitLeaves E i) :
    Commute (D.input n t k j) (copyMean n k (E.term i)) := by
  rw [input_eq_prod]
  refine Commute.list_prod_left _ _ fun M hM => ?_
  obtain ⟨g, rfl⟩ := List.mem_ofFn.mp hM
  exact commute_bandMetric_copyMean_of_contains (D.isPartition_leafPart hD j g) k (hEsupp i)
    (D.forall_contains_of_not_mem_splitLeaves E hj g)

omit [Fintype H] [DecidableEq H] [∀ h, Fintype (C h)] [∀ h, DecidableEq (C h)] [Fintype ι] [∀ v, NeZero (n v)] in
/-- At a split leaf with exceptional band `g`, every other band contains the support. -/
theorem contains_of_ne (hcompat : D.SupportCompatible E) {i : ι} {j : Σ h, Option (C h)}
    {g : Fin K} (hg : ¬ (D.leafPart j g).Contains (E.support i)) {g' : Fin K} (hg' : g' ≠ g) :
    (D.leafPart j g').Contains (E.support i) :=
  ((hcompat j i g).resolve_left hg).2 g' hg'

/-- **Single-band reduction at a split leaf** (`06-transport.tex` lines 732--735): if `g`
is the exceptional band of `D_i` at `j`, the other band factors cancel in
`O_{i,j} = A_j^{-1/2} h̄_i A_j^{1/2}`, so the skew square is that of the band metric. -/
theorem skewSquare_input_eq_bandMetric (hD : D.IsAdmissible) {t : ℝ} (ht : 0 ≤ t) {k : ℕ}
    (hcomm : D.CrossBandCommute n t k) (hEsupp : ∀ i, IsSupportedOn (E.term i) (E.support i))
    (hcompat : D.SupportCompatible E) {i : ι} {j : Σ h, Option (C h)} {g : Fin K}
    (hg : ¬ (D.leafPart j g).Contains (E.support i)) :
    Transport.skewSquare (D.input n t k j) (copyMean n k (E.term i)) =
      Transport.skewSquare (bandMetric n t k (D.leafPart j g)) (copyMean n k (E.term i)) := by
  have key := Matrix.list_ofFn_prod_rpow_conj (fun g => bandMetric n t k (D.leafPart j g))
    (fun g => posDef_bandMetric (D.isPartition_leafPart hD j g) ht k)
    (fun g g' hgg => hcomm j j g g' hgg) g (X := copyMean n k (E.term i)) fun g' hg' =>
      commute_bandMetric_copyMean_of_contains (D.isPartition_leafPart hD j g') k (hEsupp i)
        (D.contains_of_ne E hcompat hg hg')
  rw [← input_eq_prod] at key
  simp only [Transport.skewSquare, key]

omit [Fintype H] [DecidableEq H] [∀ h, Fintype (C h)] [∀ h, DecidableEq (C h)] [Fintype ι] in
/-- `η_{i,j}` is the split entropy of the unique exceptional band. -/
theorem splitEta_eq_splitBandEta (hcompat : D.SupportCompatible E) {i : ι}
    {j : Σ h, Option (C h)} {g : Fin K} (hg : ¬ (D.leafPart j g).Contains (E.support i))
    (θ : EuclideanSpace ℂ (SiteConfig n)) :
    D.splitEta E i j θ = splitBandEta n (D.leafPart j g) (E.support i) θ := by
  classical
  unfold splitEta
  refine Finset.sum_eq_single_of_mem g (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hg⟩)
    fun g' hg' hne => absurd (D.contains_of_ne E hcompat hg hne) ?_
  exact (Finset.mem_filter.mp hg').2

/-- **Symbol cost at the split leaves** (`06-transport.tex`, display
`transport:symbol-cost`, lines 736--748): one remainder `r_k → 0` serves all split
term--leaf pairs, uniformly over density matrices on `𝒮_k`. -/
theorem exists_trace_skewSquare_le :
    ∃ c₀ Csym esym : ℝ, 0 < c₀ ∧
      ∀ {V : Type*} [Fintype V] [DecidableEq V] (n : V → ℕ) [∀ v, NeZero (n v)]
        {K : ℕ} {H : Type*} [Fintype H] [DecidableEq H] {C : H → Type*}
        [∀ h, Fintype (C h)] [∀ h, DecidableEq (C h)] (D : TransportData V K H C)
        {ι : Type*} [Fintype ι] (E : EnergyTerms V n ι),
        D.IsAdmissible → (∀ i, 0 ≤ E.term i) → (∀ i, E.term i ≤ 1) →
        (∀ i, IsSupportedOn (E.term i) (E.support i)) → D.SupportCompatible E →
        ∀ {a ℓ : ℝ}, 0 < a → 1 ≤ ℓ → a * ℓ ≤ c₀ → (∀ k, D.CrossBandCommute n (a / 2) k) →
        (∀ i, (D.splitLeaves E i).Nonempty → logDim n (E.support i) ≤ ℓ) →
        ∃ r : ℕ → ℝ, Tendsto r atTop (𝓝 0) ∧ (∀ k, 0 ≤ r k) ∧
          ∀ (k : ℕ) (i : ι), ∀ j ∈ D.splitLeaves E i,
            ∀ ρ : Matrix (Config k fun v => Fin (n v)) (Config k fun v => Fin (n v)) ℂ,
            ρ.PosSemidef → ρ.trace = 1 → symProj (copyPerm (SiteConfig n) k) * ρ = ρ →
            (ρ * Transport.skewSquare (D.input n (a / 2) k j)
                (copyMean n k (E.term i))).trace.re ≤
              Csym * a ^ 2 * ℓ ^ esym * coherentIntegral k (base n) ρ (fun θ =>
                D.splitEta E i j ((EuclideanSpace.equiv _ ℂ).symm θ) ^ (1 / 8 : ℝ)) + r k := by
  obtain ⟨c, Csym, esym, hc, hsym⟩ := exists_skewSymbol_le_of_split
  refine ⟨min c (1 / 4), max Csym 0, max esym 0, lt_min hc (by norm_num), ?_⟩
  intro V _ _ n _ K H _ _ C _ _ D ι _ E hD h0 h1 hEsupp hcompat a ℓ ha hℓ haℓ hcomm hℓD
  have haℓ' : a ≤ a * ℓ := le_mul_of_one_le_right ha.le hℓ
  have hac : a * ℓ ≤ c := haℓ.trans (min_le_left _ _)
  have ha4 : a * ℓ ≤ 1 / 4 := haℓ.trans (min_le_right _ _)
  have hex : ∀ x : ι × (Σ h, Option (C h)), ∃ r : ℕ → ℝ, Tendsto r atTop (𝓝 0) ∧
      ∀ k, x.2 ∈ D.splitLeaves E x.1 →
        ∀ ρ : Matrix (Config k fun v => Fin (n v)) (Config k fun v => Fin (n v)) ℂ,
          ρ.PosSemidef → ρ.trace = 1 → symProj (copyPerm (SiteConfig n) k) * ρ = ρ →
          (ρ * Transport.skewSquare (D.input n (a / 2) k x.2)
              (copyMean n k (E.term x.1))).trace.re ≤
            max Csym 0 * a ^ 2 * ℓ ^ max esym 0 * coherentIntegral k (base n) ρ (fun θ =>
              D.splitEta E x.1 x.2 ((EuclideanSpace.equiv _ ℂ).symm θ) ^ (1 / 8 : ℝ)) +
              r k := by
    rintro ⟨i, j⟩
    by_cases hj : j ∈ D.splitLeaves E i
    · obtain ⟨g, hg⟩ : ∃ g, ¬ (D.leafPart j g).Contains (E.support i) := by
        simpa [splitLeaves] using hj
      have hsplit := ((hcompat j i g).resolve_left hg).1
      have hlog : logDim n (E.support i) ≤ ℓ := hℓD i ⟨j, hj⟩
      have hL1 := one_le_logDim (n := n) (E.support i)
      have hlogc : 2 * (a / 2) * logDim n (E.support i) ≤ c := by
        rw [show 2 * (a / 2) = a by ring]
        exact (mul_le_mul_of_nonneg_left hlog ha.le).trans hac
      obtain ⟨r, hr, hbound⟩ := hsym n (D.leafPart j g) (D.isPartition_leafPart hD j g)
        (E.support i) (E.term i) (h0 i) (h1 i) (hEsupp i) hsplit (by linarith)
        (by linarith) hlogc
      refine ⟨r, hr, fun k _ ρ hρ htr hsymρ => ?_⟩
      have hb := hbound k ρ hρ htr hsymρ
      have hfun : (fun θ => D.splitEta E i j ((EuclideanSpace.equiv _ ℂ).symm θ) ^ (1 / 8 : ℝ)) =
          fun θ => splitBandEta n (D.leafPart j g) (E.support i)
            ((EuclideanSpace.equiv _ ℂ).symm θ) ^ (1 / 8 : ℝ) :=
        funext fun θ => by rw [D.splitEta_eq_splitBandEta E hcompat hg]
      dsimp only
      rw [D.skewSquare_input_eq_bandMetric E hD (by linarith) (hcomm k) hEsupp hcompat hg, hfun]
      refine hb.trans (add_le_add ?_ le_rfl)
      have hI := coherentIntegral_nonneg (base n) hρ (f := fun θ => splitBandEta n
        (D.leafPart j g) (E.support i) ((EuclideanSpace.equiv _ ℂ).symm θ) ^ (1 / 8 : ℝ))
        fun θ => rpow_one_div_eight_nonneg _
      rw [show 2 * (a / 2) = a by ring]
      have hp1 : logDim n (E.support i) ^ esym ≤ ℓ ^ max esym 0 :=
        (Real.rpow_le_rpow_of_exponent_le hL1 (le_max_left _ _)).trans
          (Real.rpow_le_rpow (by linarith) hlog (le_max_right _ _))
      have hp0 : 0 ≤ logDim n (E.support i) ^ esym := Real.rpow_nonneg (by linarith) _
      gcongr
      exact le_max_left _ _
    · exact ⟨0, tendsto_const_nhds, fun k hk => absurd hk hj⟩
  choose r hr hbound using hex
  refine ⟨fun k => ∑ x, |r x k|, ?_, fun k => Finset.sum_nonneg fun x _ => abs_nonneg _, ?_⟩
  · simpa using tendsto_finsetSum Finset.univ fun x _ => (hr x).abs
  · intro k i j hj ρ hρ htr hs
    refine (hbound (i, j) k hj ρ hρ htr hs).trans (add_le_add le_rfl ?_)
    exact (le_abs_self _).trans (Finset.single_le_sum (f := fun x => |r x k|)
      (fun x _ => abs_nonneg _) (Finset.mem_univ (i, j)))

/-- **Energy estimate** (area-law paper, Proposition 7.4, display `transport:energy`,
`06-transport.tex` lines 417--426 and 588--766). The split weight `W_i(p)` enters twice;
the remainder is uniform in `p`, in `pre` and in the replica state; support dimensions
enter the coefficient only through `ℓ`. -/
theorem exists_energy_le :
    ∃ c₀ Cen een : ℝ, 0 < c₀ ∧
      ∀ {V : Type*} [Fintype V] [DecidableEq V] (n : V → ℕ) [∀ v, NeZero (n v)]
        {K : ℕ} {H : Type*} [Fintype H] [DecidableEq H] {C : H → Type*}
        [∀ h, Fintype (C h)] [∀ h, DecidableEq (C h)] (D : TransportData V K H C)
        {ι : Type*} [Fintype ι] (E : EnergyTerms V n ι),
        D.IsAdmissible → (∀ i, 0 ≤ E.term i) → (∀ i, E.term i ≤ 1) →
        (∀ i, IsSupportedOn (E.term i) (E.support i)) → D.SupportCompatible E →
        ∀ {a ℓ : ℝ}, 0 < a → 1 ≤ ℓ → a * ℓ ≤ c₀ → (∀ k, D.CrossBandCommute n (a / 2) k) →
        (∀ i, (D.splitLeaves E i).Nonempty → logDim n (E.support i) ≤ ℓ) →
        ∃ r : ℕ → ℝ, Tendsto r atTop (𝓝 0) ∧
          ∀ (k : ℕ) (pre : Config k (fun v => Fin (n v)) → ℂ),
            pre ∈ symmetricSubspace k (fun v => Fin (n v)) → pre ≠ 0 → ∀ p ∈ Ioo (0 : ℝ) 1,
            ∀ E₀ : ℝ, E.replicaEnergy k *ᵥ pre = (E₀ : ℂ) • pre →
              let v := Transport.filteredVector (D.rootPath n (a / 2) k p) pre
              (star v ⬝ᵥ (E.replicaEnergy k *ᵥ v)).re ≤
                2 * E₀ + Cen * a ^ 2 * ℓ ^ een * D.energyError E (a / 2) k pre p + r k := by
  sorry

end TransportData

end TensorPower.ReplicaTransport
