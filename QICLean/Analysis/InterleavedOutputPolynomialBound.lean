/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.InterleavedPolynomialCosts
import QICLean.Analysis.InterleavedPolynomialDegree
import QICLean.Analysis.InterleavedPolynomialCoefficient
import QICLean.Analysis.RefinementOutputPolynomialBound

/-!
# A complete polynomial bond with a length-dependent filter count

The count is allowed to vary with length and ground multiplicity, subject to
its derived linear logarithmic estimate. The tree's tiny reference accuracy,
its common-radius ceiling and the final reference/refinement costs are all
retained. The coefficient and natural degree precede length, multiplicity and
requested accuracy. This is a numerical auxiliary to the actual interleaved
ALVV construction, arXiv:1602.08828v2, lines 1797–1817, rather than the printed
sharp parameter profile or a running-time assertion.
-/

namespace Real

private theorem monomial_mixed_power_identity (A B Z : ℝ) (p q n m : ℕ) :
    (A * Z ^ p) ^ n * (B * Z ^ q) ^ m = A ^ n * B ^ m * Z ^ (n * p + m * q) := by
  rw [mul_pow, mul_pow, ← pow_mul Z p n, ← pow_mul Z q m,
    Nat.mul_comm p n, Nat.mul_comm q m, pow_add]
  ring

private theorem monomial_product_identity (A B Z : ℝ) (p q : ℕ) :
    (A * Z ^ p) * (B * Z ^ q) = (A * B) * Z ^ (p + q) := by
  rw [pow_add]
  ring

private theorem interleaved_output_cost_identity
    (Cb CN CM Z : ℝ) (Pb PN PM : ℕ) :
    1000000 * ((Cb * Z ^ Pb) * (CN * Z ^ PN)) ^ 2 * Z * (CM * Z ^ PM) ^ 2 =
      (1000000 * (Cb * CN) ^ 2 * CM ^ 2) * Z ^ ((Pb + PN) * 2 + (1 + PM * 2)) := by
  simp only [pow_add, pow_mul, mul_pow]
  ring

/-- Fixed physical and logarithmic-count parameters control the complete
actual common-radius refinement bond by one uniform polynomial. The count
and sample may vary with length, subject to their honest logarithmic bounds.
Supporting ALVV, arXiv:1602.08828v2, lines 1797–1817. This numerical theorem
does not construct the physical output or assert a running time. -/
theorem exists_interleaved_output_polynomial_bound_with_constants
    (gamma g u Ktree Kref KD : ℝ)
    (hgamma : 0 < gamma) (hg : 0 < g) (hg1 : g ≤ 1) (hu : 0 ≤ u)
    (hKtree : 0 ≤ Ktree) (hKref : 0 ≤ Kref) (hKD : 0 ≤ KD) :
    ∃ C : ℝ, 0 < C ∧
      log (max C 1) ≤ 10000000 * (max Ktree Kref + 1) *
        (u ^ 3 / g + 5 * (1 / g) ^ (1 / 4 : ℝ) * u + 1) *
        (1 + KD + log (1 / g) + log (1 + 1 / gamma)) ∧ ∃ k : ℕ,
      k = interleavedOutputPolynomialDegree g u (max Ktree Kref) KD ∧
      ∀ (L r D s : ℕ) (A eta : ℝ),
      1 ≤ r → 1 ≤ D → 1 ≤ s → gamma ≤ A → A ≤ (L : ℝ) + 1 → 0 < eta →
      let w := 1 + log (r : ℝ) + 2 * log ((L : ℝ) + 1)
      log (D : ℝ) ≤ KD * w →
      (s : ℝ) ≤ 4097 * (r : ℝ) * (log (D : ℝ) + w) →
      let a := 3 / (32 * (D : ℝ) ^ 12 * (s : ℝ) ^ 5)
      let tau := a ^ 2 / 1048576
      let c := gamma / A
      let rho := eta * gamma / (2 * A + eta * gamma)
      let epsilon := c ^ 2 * rho / 32768
      let btree := 16 + log (1 / g) + log (32 * (r : ℝ) * ((L : ℝ) + 1) / tau)
      let bref := 16 + log (1 / g) + log (32 * (r : ℝ) * ((L : ℝ) + 1) / epsilon)
      ∀ Btree B : ℕ, 1 ≤ Btree → 1 ≤ B →
        log (Btree : ℝ) ≤ Ktree *
          (u ^ 3 / g + (1 / g) ^ (1 / 4 : ℝ) * btree ^ (3 / 4 : ℝ) * u) *
          (1 + log btree) →
        log (B : ℝ) ≤ Kref *
          (u ^ 3 / g + (1 / g) ^ (1 / 4 : ℝ) * bref ^ (3 / 4 : ℝ) * u) *
          (1 + log bref) →
      let common := max (r ^ 2 * Btree * Nat.ceil (1 / a)) (r ^ 2 * B)
      let N := Nat.ceil (100 * (D : ℝ) ^ 12 / (c * rho))
      let count := D ^ 6 * s ^ 3
      ((1000000 * (common * N) ^ 2 * (L + 1) * count ^ 2 : ℕ) : ℝ) ≤
        C * (((L : ℝ) + 1) * ((r : ℝ) + 1) * (1 + 1 / eta)) ^ k := by
  let CD := exp KD
  let p := Nat.ceil (2 * KD)
  let Cs := 8194 * (KD + 1)
  let Ct := 1 + 1073741824 * CD ^ 24 * Cs ^ 10
  let CNtree := 1 + 32 * CD ^ 12 * Cs ^ 5
  let Pt := 24 * p + 20
  let Ptree := 12 * p + 10
  let Q := Pt + 1
  let J := 1 + 1 / gamma
  let Kc := 6 * J ^ 2
  let Ke := 196608 * J ^ 3
  let Kcost := max Ct Ke
  let K := max Ktree Kref
  let a0 := u ^ 3 / g
  let a1 := (1 / g) ^ (1 / 4 : ℝ) * u
  let b0 := 16 + log (1 / g) + log (32 * Kcost)
  let p0 := Nat.ceil (K * (a0 + 5 * a1))
  let PB := Q * 5 * p0
  let CB := exp (K * (a0 + 5 * a1) * b0)
  let Ccommon := CB * CNtree
  let Pcommon := PB + 2 + Ptree
  let CN := 1 + 100 * CD ^ 12 * Kc
  let PN := 12 * p + 3
  let CM := CD ^ 6 * Cs ^ 3
  let PM := 6 * p + 6
  let Cpoly := 1 + 1000000 * (Ccommon * CN) ^ 2 * CM ^ 2
  have hCD : 1 ≤ CD := one_le_exp_iff.mpr hKD
  have hCs : 1 ≤ Cs := by dsimp only [Cs]; linarith only [hKD]
  have hCt : 1 ≤ Ct := by
    have hnonneg : 0 ≤ 1073741824 * CD ^ 24 * Cs ^ 10 := by positivity
    dsimp only [Ct]
    linarith only [hnonneg]
  have hCNtree : 1 ≤ CNtree := by
    have hnonneg : 0 ≤ 32 * CD ^ 12 * Cs ^ 5 := by positivity
    dsimp only [CNtree]
    linarith only [hnonneg]
  have hKcost : 1 ≤ Kcost := hCt.trans (le_max_left Ct Ke)
  have hCpoly : 0 < Cpoly := by dsimp only [Cpoly]; positivity
  have hlogPoly := log_interleavedOutputPolynomialCoefficient_le gamma g u K KD
    hgamma hg hg1 hu (hKtree.trans (le_max_left Ktree Kref)) hKD
  change log (max Cpoly 1) ≤ _ at hlogPoly
  refine ⟨Cpoly, hCpoly, ?_, (Pcommon + PN) * 2 + (1 + PM * 2), ?_, ?_⟩
  · exact hlogPoly
  · have hp0 : p0 = Nat.ceil (K * (u ^ 3 / g + 5 * (1 / g) ^ (1 / 4 : ℝ) * u)) := by
      dsimp only [p0, a0, a1]
      congr 1
      ring
    dsimp only [Pcommon, PB, Q, Pt, Ptree, PN, PM, interleavedOutputPolynomialDegree]
    rw [hp0]
    ring
  intro L r D s A eta hr hD hs hgammaA hAL heta w hlogD hsample a tau
    c rho epsilon btree bref Btree B hBtree hB hlogTree hlogRef common N count
  let Z := ((L : ℝ) + 1) * ((r : ℝ) + 1) * (1 + 1 / eta)
  have hA : 0 < A := hgamma.trans_le hgammaA
  have hrR : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hL1 : (1 : ℝ) ≤ (L : ℝ) + 1 := by linarith [(Nat.cast_nonneg L : (0 : ℝ) ≤ L)]
  have hr1 : (1 : ℝ) ≤ (r : ℝ) + 1 := by linarith only [hrR]
  have heta1 : 1 ≤ 1 + 1 / eta := by linarith [one_div_pos.mpr heta]
  have hLR : 1 ≤ ((L : ℝ) + 1) * ((r : ℝ) + 1) :=
    one_le_mul_of_one_le_of_one_le hL1 hr1
  have hZ : 1 ≤ Z := one_le_mul_of_one_le_of_one_le hLR heta1
  have hetaZ : 1 / eta ≤ Z := by
    have he := le_mul_of_one_le_left (by positivity : 0 ≤ 1 + 1 / eta) hLR
    linarith only [he]
  have hrlZ : (r : ℝ) * ((L : ℝ) + 1) ≤ Z := by
    calc
      _ ≤ ((r : ℝ) + 1) * ((L : ℝ) + 1) := by gcongr; linarith
      _ = ((L : ℝ) + 1) * ((r : ℝ) + 1) := mul_comm _ _
      _ ≤ _ := le_mul_of_one_le_right (by positivity) heta1
  obtain ⟨_hZ, hrZ, hLZ, _hw, _hwLog, _hwZ⟩ := interleaved_size_log_bounds hrR hL1 hrlZ
  obtain ⟨hDpoly, hSpoly⟩ := interleaved_count_sample_polynomial_bounds
    KD hKD D s hD r (L + 1) Z hrR hL1 hrlZ hlogD hsample
  change (D : ℝ) ≤ CD * Z ^ p at hDpoly
  change (s : ℝ) ≤ Cs * Z ^ 2 at hSpoly
  obtain ⟨_ha, _ha1, htau, htau1, htauInv, hNtree⟩ :=
    interleaved_inverse_cost_polynomial_bounds D s p hD hs Z CD Cs hZ hCD hCs hDpoly hSpoly
  change 0 < tau at htau
  change tau ≤ 1 at htau1
  change 1 / tau ≤ Ct * Z ^ Pt at htauInv
  change (Nat.ceil (1 / a) : ℝ) ≤ CNtree * Z ^ Ptree at hNtree
  obtain ⟨hcrho, hepsilonInv⟩ := viable_refinement_costs_le_polynomial
    hA hgamma heta hZ (hAL.trans hLZ) hetaZ
  obtain ⟨hc, _hc1, hrho, _hrho1, _hrhoEta, _hpEta,
    hepsilon, hepsilonSmall, _hepsilonBudget, _henergy⟩ :=
    viable_refinement_error_parameters hgamma hgammaA heta
  have hZQ : 1 ≤ Z ^ Q := one_le_pow₀ hZ
  have hZZQ : Z ≤ Z ^ Q := by
    calc
      Z = Z ^ 1 := (pow_one Z).symm
      _ ≤ _ := by gcongr; dsimp only [Q]; omega
  have hTauCost : 1 / tau ≤ Kcost * (Z ^ Q) ^ 4 := by
    apply htauInv.trans
    apply mul_le_mul (le_max_left Ct Ke) ?_
      (pow_nonneg (by linarith only [hZ]) _) (by linarith only [hKcost])
    rw [← pow_mul]
    gcongr
    dsimp only [Q]
    omega
  have hEpsilonCost : 1 / epsilon ≤ Kcost * (Z ^ Q) ^ 4 := by
    apply hepsilonInv.trans
    change Ke * Z ^ 4 ≤ _
    exact mul_le_mul (le_max_right Ct Ke) (pow_le_pow_left₀ (by linarith only [hZ]) hZZQ 4)
      (pow_nonneg (by linarith only [hZ]) _) (by linarith only [hKcost])
  have hTreeProfile := reference_accuracy_log_profile_bounds hg hg1 hKcost hZQ hrR hL1
    (hrlZ.trans hZZQ) htau htau1 hTauCost
  have hRefProfile := reference_accuracy_log_profile_bounds hg hg1 hKcost hZQ hrR hL1
    (hrlZ.trans hZZQ) hepsilon (hepsilonSmall.trans (by norm_num)) hEpsilonCost
  change 1 ≤ btree ∧ btree ≤ b0 + log ((Z ^ Q) ^ 5) at hTreeProfile
  change 1 ≤ bref ∧ bref ≤ b0 + log ((Z ^ Q) ^ 5) at hRefProfile
  have hgInv : 1 ≤ 1 / g := (le_div_iff₀ hg).mpr (by simpa using hg1)
  have hb0 : 1 ≤ b0 := by
    dsimp only [b0]
    linarith [log_nonneg hgInv, log_nonneg (show 1 ≤ 32 * Kcost by linarith only [hKcost])]
  have ha0 : 0 ≤ a0 := by dsimp only [a0]; positivity
  have ha1 : 0 ≤ a1 := by dsimp only [a1]; positivity
  have hX : 1 ≤ (Z ^ Q) ^ 5 := one_le_pow₀ hZQ
  have hlogTree' : log (Btree : ℝ) ≤
      Ktree * (a0 + a1 * btree ^ (3 / 4 : ℝ)) * (1 + log btree) := by
    convert hlogTree using 1
    dsimp only [a0, a1]
    ring
  have hlogRef' : log (B : ℝ) ≤
      Kref * (a0 + a1 * bref ^ (3 / 4 : ℝ)) * (1 + log bref) := by
    convert hlogRef using 1
    dsimp only [a0, a1]
    ring
  have hBt := reference_profile_polynomial_bound hKtree (le_max_left Ktree Kref)
    ha0 ha1 hTreeProfile.1 hb0 (by exact_mod_cast Nat.zero_lt_one.trans_le hBtree)
    hX hTreeProfile.2 hlogTree'
  have hBr := reference_profile_polynomial_bound hKref (le_max_right Ktree Kref)
    ha0 ha1 hRefProfile.1 hb0 (by exact_mod_cast Nat.zero_lt_one.trans_le hB)
    hX hRefProfile.2 hlogRef'
  have hBt' : (Btree : ℝ) ≤ CB * Z ^ PB := by simpa only [PB, ← pow_mul] using hBt
  have hBr' : (B : ℝ) ≤ CB * Z ^ PB := by simpa only [PB, ← pow_mul] using hBr
  have hbound (B' : ℕ) (hB' : (B' : ℝ) ≤ CB * Z ^ PB) :
      ((r ^ 2 * B' : ℕ) : ℝ) ≤ CB * Z ^ (PB + 2) := by
    push_cast
    calc
      _ ≤ Z ^ 2 * (CB * Z ^ PB) := by gcongr
      _ = _ := by
        rw [mul_comm (Z ^ 2) (CB * Z ^ PB)]
        simpa only [one_mul, mul_one] using monomial_product_identity CB 1 Z PB 2
  have hTreeCost : ((r ^ 2 * Btree * Nat.ceil (1 / a) : ℕ) : ℝ) ≤
      Ccommon * Z ^ Pcommon := by
    rw [Nat.cast_mul]
    calc
      _ ≤ (CB * Z ^ (PB + 2)) * (CNtree * Z ^ Ptree) :=
        mul_le_mul (hbound Btree hBt') hNtree (Nat.cast_nonneg _) (by positivity)
      _ = _ := monomial_product_identity CB CNtree Z (PB + 2) Ptree
  have hRefCost : ((r ^ 2 * B : ℕ) : ℝ) ≤ Ccommon * Z ^ Pcommon := by
    calc
      _ ≤ CB * Z ^ (PB + 2) := hbound B hBr'
      _ ≤ (CB * Z ^ (PB + 2)) * (CNtree * Z ^ Ptree) :=
        le_mul_of_one_le_right (by positivity)
          (one_le_mul_of_one_le_of_one_le hCNtree (one_le_pow₀ hZ))
      _ = _ := monomial_product_identity CB CNtree Z (PB + 2) Ptree
  have hcommon : (common : ℝ) ≤ Ccommon * Z ^ Pcommon := by
    dsimp only [common]
    rw [Nat.cast_max]
    exact max_le hTreeCost hRefCost
  have hNcost : 100 * (D : ℝ) ^ 12 / (c * rho) ≤ 100 * CD ^ 12 * Kc * Z ^ PN := by
    calc
      _ = 100 * (D : ℝ) ^ 12 * (1 / (c * rho)) := by ring
      _ ≤ 100 * (CD * Z ^ p) ^ 12 * (Kc * Z ^ 3) := by gcongr
      _ = _ := by
        have hid := monomial_mixed_power_identity CD Kc Z p 3 12 1
        simpa only [PN, pow_one, one_mul, mul_assoc] using
          congrArg (fun x : ℝ ↦ 100 * x) hid
  have hN : (N : ℝ) ≤ CN * Z ^ PN := by
    have hceil := (Nat.ceil_lt_add_one (by positivity : 0 ≤ 100 * (D : ℝ) ^ 12 / (c * rho))).le
    have hpower : (1 : ℝ) ≤ Z ^ PN := one_le_pow₀ hZ
    dsimp only [CN]
    nlinarith only [hceil, hNcost, hpower]
  have hcount : (count : ℝ) ≤ CM * Z ^ PM := by
    change ((D ^ 6 * s ^ 3 : ℕ) : ℝ) ≤ _
    push_cast
    calc
      _ ≤ (CD * Z ^ p) ^ 6 * (Cs * Z ^ 2) ^ 3 := by gcongr
      _ = _ := by
        exact monomial_mixed_power_identity CD Cs Z p 2 6 3
  push_cast
  change (1000000 : ℝ) * ((common : ℝ) * (N : ℝ)) ^ 2 * ((L : ℝ) + 1) * (count : ℝ) ^ 2 ≤ _
  calc
    _ ≤ 1000000 * ((Ccommon * Z ^ Pcommon) * (CN * Z ^ PN)) ^ 2 * Z * (CM * Z ^ PM) ^ 2 := by
      gcongr
    _ = (1000000 * (Ccommon * CN) ^ 2 * CM ^ 2) *
        Z ^ ((Pcommon + PN) * 2 + (1 + PM * 2)) :=
      interleaved_output_cost_identity Ccommon CN CM Z Pcommon PN PM
    _ ≤ Cpoly * Z ^ ((Pcommon + PN) * 2 + (1 + PM * 2)) :=
      mul_le_mul_of_nonneg_right (le_add_of_nonneg_left zero_le_one) (by positivity)

/-- Fixed physical and logarithmic-count parameters control the complete
actual common-radius refinement bond by one uniform polynomial. The count
and sample may vary with length, subject to their honest logarithmic bounds.
Supporting ALVV, arXiv:1602.08828v2, lines 1797–1817. This numerical theorem
does not construct the physical output or assert a running time. -/
theorem exists_interleaved_output_polynomial_bound_with_degree
    (gamma g u Ktree Kref KD : ℝ)
    (hgamma : 0 < gamma) (hg : 0 < g) (hg1 : g ≤ 1) (hu : 0 ≤ u)
    (hKtree : 0 ≤ Ktree) (hKref : 0 ≤ Kref) (hKD : 0 ≤ KD) :
    ∃ C : ℝ, 0 < C ∧ ∃ k : ℕ,
      k = interleavedOutputPolynomialDegree g u (max Ktree Kref) KD ∧
      ∀ (L r D s : ℕ) (A eta : ℝ),
      1 ≤ r → 1 ≤ D → 1 ≤ s → gamma ≤ A → A ≤ (L : ℝ) + 1 → 0 < eta →
      let w := 1 + log (r : ℝ) + 2 * log ((L : ℝ) + 1)
      log (D : ℝ) ≤ KD * w →
      (s : ℝ) ≤ 4097 * (r : ℝ) * (log (D : ℝ) + w) →
      let a := 3 / (32 * (D : ℝ) ^ 12 * (s : ℝ) ^ 5)
      let tau := a ^ 2 / 1048576
      let c := gamma / A
      let rho := eta * gamma / (2 * A + eta * gamma)
      let epsilon := c ^ 2 * rho / 32768
      let btree := 16 + log (1 / g) + log (32 * (r : ℝ) * ((L : ℝ) + 1) / tau)
      let bref := 16 + log (1 / g) + log (32 * (r : ℝ) * ((L : ℝ) + 1) / epsilon)
      ∀ Btree B : ℕ, 1 ≤ Btree → 1 ≤ B →
        log (Btree : ℝ) ≤ Ktree *
          (u ^ 3 / g + (1 / g) ^ (1 / 4 : ℝ) * btree ^ (3 / 4 : ℝ) * u) *
          (1 + log btree) →
        log (B : ℝ) ≤ Kref *
          (u ^ 3 / g + (1 / g) ^ (1 / 4 : ℝ) * bref ^ (3 / 4 : ℝ) * u) *
          (1 + log bref) →
      let common := max (r ^ 2 * Btree * Nat.ceil (1 / a)) (r ^ 2 * B)
      let N := Nat.ceil (100 * (D : ℝ) ^ 12 / (c * rho))
      let count := D ^ 6 * s ^ 3
      ((1000000 * (common * N) ^ 2 * (L + 1) * count ^ 2 : ℕ) : ℝ) ≤
        C * (((L : ℝ) + 1) * ((r : ℝ) + 1) * (1 + 1 / eta)) ^ k := by
  obtain ⟨C, hC, _hlogC, k, hk, hbound⟩ :=
    exists_interleaved_output_polynomial_bound_with_constants
      gamma g u Ktree Kref KD hgamma hg hg1 hu hKtree hKref hKD
  exact ⟨C, hC, k, hk, hbound⟩

/-- Fixed physical and logarithmic-count parameters control the complete
actual common-radius refinement bond by one uniform polynomial. The count
and sample may vary with length, subject to their honest logarithmic bounds.
Supporting ALVV, arXiv:1602.08828v2, lines 1797–1817. This numerical theorem
does not construct the physical output or assert a running time. -/
theorem exists_interleaved_output_polynomial_bound
    (gamma g u Ktree Kref KD : ℝ)
    (hgamma : 0 < gamma) (hg : 0 < g) (hg1 : g ≤ 1) (hu : 0 ≤ u)
    (hKtree : 0 ≤ Ktree) (hKref : 0 ≤ Kref) (hKD : 0 ≤ KD) :
    ∃ C : ℝ, 0 < C ∧ ∃ k : ℕ, ∀ (L r D s : ℕ) (A eta : ℝ),
      1 ≤ r → 1 ≤ D → 1 ≤ s → gamma ≤ A → A ≤ (L : ℝ) + 1 → 0 < eta →
      let w := 1 + log (r : ℝ) + 2 * log ((L : ℝ) + 1)
      log (D : ℝ) ≤ KD * w →
      (s : ℝ) ≤ 4097 * (r : ℝ) * (log (D : ℝ) + w) →
      let a := 3 / (32 * (D : ℝ) ^ 12 * (s : ℝ) ^ 5)
      let tau := a ^ 2 / 1048576
      let c := gamma / A
      let rho := eta * gamma / (2 * A + eta * gamma)
      let epsilon := c ^ 2 * rho / 32768
      let btree := 16 + log (1 / g) + log (32 * (r : ℝ) * ((L : ℝ) + 1) / tau)
      let bref := 16 + log (1 / g) + log (32 * (r : ℝ) * ((L : ℝ) + 1) / epsilon)
      ∀ Btree B : ℕ, 1 ≤ Btree → 1 ≤ B →
        log (Btree : ℝ) ≤ Ktree *
          (u ^ 3 / g + (1 / g) ^ (1 / 4 : ℝ) * btree ^ (3 / 4 : ℝ) * u) *
          (1 + log btree) →
        log (B : ℝ) ≤ Kref *
          (u ^ 3 / g + (1 / g) ^ (1 / 4 : ℝ) * bref ^ (3 / 4 : ℝ) * u) *
          (1 + log bref) →
      let common := max (r ^ 2 * Btree * Nat.ceil (1 / a)) (r ^ 2 * B)
      let N := Nat.ceil (100 * (D : ℝ) ^ 12 / (c * rho))
      let count := D ^ 6 * s ^ 3
      ((1000000 * (common * N) ^ 2 * (L + 1) * count ^ 2 : ℕ) : ℝ) ≤
        C * (((L : ℝ) + 1) * ((r : ℝ) + 1) * (1 + 1 / eta)) ^ k := by
  obtain ⟨C, hC, k, _hk, hbound⟩ := exists_interleaved_output_polynomial_bound_with_degree
    gamma g u Ktree Kref KD hgamma hg hg1 hu hKtree hKref hKD
  exact ⟨C, hC, k, hbound⟩

end Real
