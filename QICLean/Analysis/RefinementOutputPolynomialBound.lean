/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.ReferencePolynomialBound
import QICLean.Analysis.ViableRefinementParameters

/-!
# A polynomial bound for the complete scalar refinement cost

The coefficient and integer exponent depend only on fixed reference-profile and gap
parameters. Length, multiplicity and inverse accuracy enter one common monomial.
These are numerical auxiliaries to ALVV, arXiv:1602.08828v2, `t:alg1`,
lines 1777–1817. No physical output, probability or running time is asserted here.
-/

namespace Real

/-- A polynomial inverse-accuracy budget bounds the actual logarithmic reference
profile above and below. This numerical estimate supports ALVV,
arXiv:1602.08828v2, proof of `t:alg1`, lines 1801–1817. -/
theorem reference_accuracy_log_profile_bounds
    {g K Z r l epsilon : ℝ} (hg : 0 < g) (hg1 : g ≤ 1)
    (hK : 1 ≤ K) (hZ : 1 ≤ Z) (hr : 1 ≤ r) (hl : 1 ≤ l)
    (hrl : r * l ≤ Z) (hepsilon : 0 < epsilon) (hepsilon1 : epsilon ≤ 1)
    (hcost : 1 / epsilon ≤ K * Z ^ 4) :
    let b := 16 + log (1 / g) + log (32 * r * l / epsilon)
    let b0 := 16 + log (1 / g) + log (32 * K)
    1 ≤ b ∧ b ≤ b0 + log (Z ^ 5) := by
  intro b b0
  have hgInv : 1 ≤ 1 / g := (le_div_iff₀ hg).mpr (by simpa using hg1)
  have hrl1 : 1 ≤ r * l := one_le_mul_of_one_le_of_one_le hr hl
  have harg : 1 ≤ 32 * r * l / epsilon := by
    apply (le_div_iff₀ hepsilon).mpr
    nlinarith only [hrl1, hepsilon1]
  have hupper : 32 * r * l / epsilon ≤ 32 * K * Z ^ 5 := by
    calc
      _ = 32 * (r * l) * (1 / epsilon) := by ring
      _ ≤ 32 * Z * (K * Z ^ 4) := by gcongr
      _ = _ := by ring
  have hlog : log (32 * r * l / epsilon) ≤ log (32 * K * Z ^ 5) :=
    log_le_log (by positivity) hupper
  have hsplit : log (32 * K * Z ^ 5) = log (32 * K) + log (Z ^ 5) :=
    log_mul (by positivity) (by positivity)
  refine ⟨?_, ?_⟩
  · dsimp only [b]
    linarith [log_nonneg hgInv, log_nonneg harg]
  · dsimp only [b, b0]
    rw [hsplit] at hlog
    linarith only [hlog]

/-- A monotone logarithmic reference profile gives one explicit natural-power
bound on the reference bond. The coefficient and exponent precede the
accuracy factor. Supporting ALVV, arXiv:1602.08828v2, proof of `t:alg1`,
lines 1801–1817. -/
theorem reference_profile_polynomial_bound
    {K0 K a0 a1 b b0 B X : ℝ} (hK0 : 0 ≤ K0) (hK : K0 ≤ K)
    (ha0 : 0 ≤ a0) (ha1 : 0 ≤ a1) (hb : 1 ≤ b) (hb0 : 1 ≤ b0)
    (hB : 0 < B) (hX : 1 ≤ X) (hbx : b ≤ b0 + log X)
    (hlog : log B ≤ K0 * (a0 + a1 * b ^ (3 / 4 : ℝ)) * (1 + log b)) :
    B ≤ exp (K * (a0 + 5 * a1) * b0) * X ^ Nat.ceil (K * (a0 + 5 * a1)) := by
  have hK' : 0 ≤ K := hK0.trans hK
  apply reference_bound_le_nat_power hK' ha0 ha1 hb0 hB hX
  have hbpos : 0 < b := by linarith only [hb]
  have hpow : b ^ (3 / 4 : ℝ) ≤ (b0 + log X) ^ (3 / 4 : ℝ) :=
    rpow_le_rpow hbpos.le hbx (by norm_num)
  have hlg : log b ≤ log (b0 + log X) := log_le_log hbpos hbx
  have hP : a0 + a1 * b ^ (3 / 4 : ℝ) ≤
      a0 + a1 * (b0 + log X) ^ (3 / 4 : ℝ) :=
    _root_.add_le_add (le_refl a0) (mul_le_mul_of_nonneg_left hpow ha1)
  have hL : 1 + log b ≤ 1 + log (b0 + log X) := _root_.add_le_add (le_refl 1) hlg
  have hP0 : 0 ≤ a0 + a1 * b ^ (3 / 4 : ℝ) := by positivity
  have hL0 : 0 ≤ 1 + log b := by linarith [log_nonneg hb]
  have hPmax0 : 0 ≤ a0 + a1 * (b0 + log X) ^ (3 / 4 : ℝ) := hP0.trans hP
  calc
    _ ≤ K0 * (a0 + a1 * b ^ (3 / 4 : ℝ)) * (1 + log b) := hlog
    _ ≤ K * (a0 + a1 * b ^ (3 / 4 : ℝ)) * (1 + log b) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hK hP0) hL0
    _ ≤ _ := mul_le_mul (mul_le_mul_of_nonneg_left hP hK') hL hL0 (mul_nonneg hK' hPmax0)


private theorem final_cost_identity (Cb CN Ccount Z : ℝ) (P : ℕ) :
    1000000 * ((Cb * Z ^ (P + 2)) * (CN * Z ^ 3)) ^ 2 * Z *
      (Ccount * Z ^ 6) ^ 2 = (1000000 * (Cb * CN) ^ 2 * Ccount ^ 2) *
        Z ^ ((P + 2 + 3) * 2 + (1 + 6 * 2)) := by
  simp only [pow_add, pow_mul, mul_pow]
  ring


/-- The final cost comparison of `exists_refinement_output_polynomial_bound`, stated
without the surrounding local definitions so that it elaborates in a small context. -/
private theorem refinement_cost_tail
    (Z c rho Kc Cb Cs CN Ccount Cpoly : ℝ) (P D L r s Btree B : ℕ)
    (hZ : 1 ≤ Z) (hLZ : (L : ℝ) + 1 ≤ Z) (hrZ : (r : ℝ) ≤ Z) (hrR : (1 : ℝ) ≤ r)
    (hD : 1 ≤ D) (hCb : 0 < Cb) (hc : 0 < c) (hrho : 0 < rho)
    (hcrho : 1 / (c * rho) ≤ Kc * Z ^ 3)
    (hBt : (Btree : ℝ) ≤ Cb * Z ^ P) (hBr : (B : ℝ) ≤ Cb * Z ^ P)
    (hs : (s : ℝ) ≤ 4097 * (r : ℝ) * (1 + log (r : ℝ) + log (D : ℝ) + log 2))
    (hCs : Cs = 4097 * (1 + log (D : ℝ) + log 2))
    (hCN : CN = 100 * (D : ℝ) ^ 12 * Kc + 1)
    (hCcount : Ccount = (D : ℝ) ^ 6 * Cs ^ 3)
    (hCpoly : Cpoly = 1 + 1000000 * (Cb * CN) ^ 2 * Ccount ^ 2) :
    ((1000000 * (max (r ^ 2 * Btree) (r ^ 2 * B) *
        Nat.ceil (100 * (D : ℝ) ^ 12 / (c * rho))) ^ 2 * (L + 1) *
        (D ^ 6 * s ^ 3) ^ 2 : ℕ) : ℝ) ≤
      Cpoly * Z ^ ((P + 2 + 3) * 2 + (1 + 6 * 2)) := by
  subst hCpoly hCcount hCN hCs
  have hbound (B' : ℕ) (hB' : (B' : ℝ) ≤ Cb * Z ^ P) :
      ((r ^ 2 * B' : ℕ) : ℝ) ≤ Cb * Z ^ (P + 2) := by
    push_cast
    calc
      _ ≤ Z ^ 2 * (Cb * Z ^ P) :=
        mul_le_mul (pow_le_pow_left₀ (by positivity) hrZ 2) hB' (by positivity) (by positivity)
      _ = _ := by rw [pow_add]; ring
  have hcommon : ((max (r ^ 2 * Btree) (r ^ 2 * B) : ℕ) : ℝ) ≤ Cb * Z ^ (P + 2) := by
    rw [Nat.cast_max]
    exact max_le (hbound Btree hBt) (hbound B hBr)
  have hNceil : ((Nat.ceil (100 * (D : ℝ) ^ 12 / (c * rho)) : ℕ) : ℝ) ≤
      100 * (D : ℝ) ^ 12 / (c * rho) + 1 :=
    (Nat.ceil_lt_add_one (by positivity : 0 ≤ 100 * (D : ℝ) ^ 12 / (c * rho))).le
  have hNcost : 100 * (D : ℝ) ^ 12 / (c * rho) ≤
      100 * (D : ℝ) ^ 12 * Kc * Z ^ 3 := by
    calc
      _ = 100 * (D : ℝ) ^ 12 * (1 / (c * rho)) := by ring
      _ ≤ 100 * (D : ℝ) ^ 12 * (Kc * Z ^ 3) :=
        mul_le_mul_of_nonneg_left hcrho (by positivity)
      _ = _ := by ring
  have hN : ((Nat.ceil (100 * (D : ℝ) ^ 12 / (c * rho)) : ℕ) : ℝ) ≤
      (100 * (D : ℝ) ^ 12 * Kc + 1) * Z ^ 3 := by
    calc
      _ ≤ 100 * (D : ℝ) ^ 12 / (c * rho) + 1 := hNceil
      _ ≤ 100 * (D : ℝ) ^ 12 * Kc * Z ^ 3 + 1 :=
        _root_.add_le_add hNcost (le_refl 1)
      _ ≤ 100 * (D : ℝ) ^ 12 * Kc * Z ^ 3 + Z ^ 3 :=
        _root_.add_le_add (le_refl _) (one_le_pow₀ hZ)
      _ = _ := by ring
  have hDreal : (1 : ℝ) ≤ D := by exact_mod_cast hD
  have hlogD : 0 ≤ log (D : ℝ) := log_nonneg hDreal
  have hlog2 : 0 ≤ log (2 : ℝ) := log_nonneg (by norm_num)
  have hsample : 1 + log (r : ℝ) + log (D : ℝ) + log 2 ≤
      (1 + log (D : ℝ) + log 2) * (r : ℝ) := by
    have hlogr := log_le_sub_one_of_pos (by linarith only [hrR] : (0 : ℝ) < r)
    have hfix := mul_le_mul_of_nonneg_left hrR (add_nonneg hlogD hlog2)
    nlinarith only [hlogr, hfix]
  have hCs : 0 ≤ 4097 * (1 + log (D : ℝ) + log 2) := by positivity
  have hs2 : (s : ℝ) ≤ 4097 * (1 + log (D : ℝ) + log 2) * (r : ℝ) ^ 2 := by
    calc
      _ ≤ 4097 * (r : ℝ) * (1 + log (r : ℝ) + log (D : ℝ) + log 2) := hs
      _ ≤ 4097 * (r : ℝ) * ((1 + log (D : ℝ) + log 2) * (r : ℝ)) :=
        mul_le_mul_of_nonneg_left hsample (by positivity)
      _ = _ := by ring
  have hsZ : (s : ℝ) ≤ 4097 * (1 + log (D : ℝ) + log 2) * Z ^ 2 :=
    hs2.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hrZ 2) hCs)
  have hcount : ((D ^ 6 * s ^ 3 : ℕ) : ℝ) ≤
      (D : ℝ) ^ 6 * (4097 * (1 + log (D : ℝ) + log 2)) ^ 3 * Z ^ 6 := by
    push_cast
    calc
      _ ≤ (D : ℝ) ^ 6 * (4097 * (1 + log (D : ℝ) + log 2) * Z ^ 2) ^ 3 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hsZ 3) (by positivity)
      _ = _ := by rw [mul_pow, ← pow_mul, mul_assoc]
  push_cast
  calc
    _ ≤ 1000000 * ((Cb * Z ^ (P + 2)) * ((100 * (D : ℝ) ^ 12 * Kc + 1) * Z ^ 3)) ^ 2 * Z *
        ((D : ℝ) ^ 6 * (4097 * (1 + log (D : ℝ) + log 2)) ^ 3 * Z ^ 6) ^ 2 := by
      push_cast at hcommon hN hcount
      gcongr
    _ = (1000000 * (Cb * (100 * (D : ℝ) ^ 12 * Kc + 1)) ^ 2 *
          ((D : ℝ) ^ 6 * (4097 * (1 + log (D : ℝ) + log 2)) ^ 3) ^ 2) *
        Z ^ ((P + 2 + 3) * 2 + (1 + 6 * 2)) := final_cost_identity _ _ _ Z P
    _ ≤ _ := mul_le_mul_of_nonneg_right (le_add_of_nonneg_left zero_le_one) (by positivity)

/-- Fixed scalar reference and gap parameters give a uniform polynomial bound for the
complete recorded refinement cost. Length, multiplicity and inverse requested accuracy are
not used when choosing the coefficient or natural exponent. Numerical auxiliary to ALVV,
arXiv:1602.08828v2, `t:alg1`, lines 1777–1817; the actual physical output is separate. -/
theorem exists_refinement_output_polynomial_bound
    (gamma g u Ktree Kref : ℝ) (D : ℕ)
    (hgamma : 0 < gamma) (hg : 0 < g) (hg1 : g ≤ 1) (hu : 0 ≤ u)
    (hKtree : 0 ≤ Ktree) (hKref : 0 ≤ Kref) (hD : 1 ≤ D) :
    ∃ C : ℝ, 0 < C ∧ ∃ k : ℕ, ∀ (L r : ℕ) (A eta : ℝ),
      1 ≤ r → gamma ≤ A → A ≤ (L : ℝ) + 1 → 0 < eta →
      let c := gamma / A
      let rho := eta * gamma / (2 * A + eta * gamma)
      let epsilon := c ^ 2 * rho / 32768
      let btree := 16 + log (1 / g) + log (32 * (r : ℝ) * ((L : ℝ) + 1) / (1 / 10000))
      let bref := 16 + log (1 / g) + log (32 * (r : ℝ) * ((L : ℝ) + 1) / epsilon)
      ∀ Btree B : ℕ, 1 ≤ Btree → 1 ≤ B →
        log (Btree : ℝ) ≤ Ktree *
          (u ^ 3 / g + (1 / g) ^ (1 / 4 : ℝ) * btree ^ (3 / 4 : ℝ) * u) *
          (1 + log btree) →
        log (B : ℝ) ≤ Kref *
          (u ^ 3 / g + (1 / g) ^ (1 / 4 : ℝ) * bref ^ (3 / 4 : ℝ) * u) *
          (1 + log bref) →
        ∀ s : ℕ, (s : ℝ) ≤
          4097 * (r : ℝ) * (1 + log (r : ℝ) + log (D : ℝ) + log 2) →
        let common := max (r ^ 2 * Btree) (r ^ 2 * B)
        let N := Nat.ceil (100 * (D : ℝ) ^ 12 / (c * rho))
        let count := D ^ 6 * s ^ 3
        ((1000000 * (common * N) ^ 2 * (L + 1) * count ^ 2 : ℕ) : ℝ) ≤
          C * (((L : ℝ) + 1) * ((r : ℝ) + 1) * (1 + 1 / eta)) ^ k := by
  let K := max Ktree Kref
  let a0 := u ^ 3 / g
  let a1 := (1 / g) ^ (1 / 4 : ℝ) * u
  let M := 1 + 1 / gamma
  let Kc := 6 * M ^ 2
  let Ke := 196608 * M ^ 3
  let b0 := 16 + log (1 / g) + log (32 * Ke)
  let p0 := Nat.ceil (K * (a0 + 5 * a1))
  let P := 5 * p0
  let Cb := exp (K * (a0 + 5 * a1) * b0)
  let Cs := 4097 * (1 + log (D : ℝ) + log 2)
  let CN := 100 * (D : ℝ) ^ 12 * Kc + 1
  let Ccount := (D : ℝ) ^ 6 * Cs ^ 3
  let Cpoly := 1 + 1000000 * (Cb * CN) ^ 2 * Ccount ^ 2
  have hCpoly : 0 < Cpoly := by dsimp only [Cpoly]; positivity
  refine ⟨Cpoly, hCpoly, (P + 2 + 3) * 2 + (1 + 6 * 2), ?_⟩
  intro L r A eta hr hgammaA hAL heta c rho epsilon btree bref Btree B
    hBtree hB hlogTree hlogRef s hs common N count
  let Z := ((L : ℝ) + 1) * ((r : ℝ) + 1) * (1 + 1 / eta)
  have hA : 0 < A := hgamma.trans_le hgammaA
  have hrR : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hL1 : (1 : ℝ) ≤ (L : ℝ) + 1 := by linarith [(Nat.cast_nonneg L : (0 : ℝ) ≤ L)]
  have hr1 : (1 : ℝ) ≤ (r : ℝ) + 1 := by linarith [(Nat.cast_nonneg r : (0 : ℝ) ≤ r)]
  have heta1 : 1 ≤ 1 + 1 / eta := by linarith [one_div_pos.mpr heta]
  have hLR : 1 ≤ ((L : ℝ) + 1) * ((r : ℝ) + 1) :=
    one_le_mul_of_one_le_of_one_le hL1 hr1
  have hZ : 1 ≤ Z := one_le_mul_of_one_le_of_one_le hLR heta1
  have hLZ : (L : ℝ) + 1 ≤ Z := by
    calc
      _ ≤ ((L : ℝ) + 1) * ((r : ℝ) + 1) := le_mul_of_one_le_right (by positivity) hr1
      _ ≤ _ := le_mul_of_one_le_right (by positivity) heta1
  have hetaZ : 1 / eta ≤ Z := by
    have hEtaZ : 1 + 1 / eta ≤ Z := le_mul_of_one_le_left (by positivity) hLR
    linarith only [hEtaZ]
  have hrlZ : (r : ℝ) * ((L : ℝ) + 1) ≤ Z := by
    calc
      _ ≤ ((r : ℝ) + 1) * ((L : ℝ) + 1) := by gcongr; linarith
      _ = ((L : ℝ) + 1) * ((r : ℝ) + 1) := mul_comm _ _
      _ ≤ _ := le_mul_of_one_le_right (by positivity) heta1
  obtain ⟨hcrho, hepsilonInv⟩ := viable_refinement_costs_le_polynomial
    hA hgamma heta hZ (hAL.trans hLZ) hetaZ
  obtain ⟨_hc, _hc1, _hrho, _hrho1, _hrhoEta, _hpEta,
    hepsilon, hepsilonSmall, _hepsilonBudget, _henergy⟩ :=
      viable_refinement_error_parameters hgamma hgammaA heta
  have hM : 1 ≤ M := by dsimp only [M]; linarith [one_div_pos.mpr hgamma]
  have hKe : 10000 ≤ Ke := by
    have hpow : (1 : ℝ) ≤ M ^ 3 := one_le_pow₀ hM
    dsimp only [Ke]
    nlinarith only [hpow]
  have hKe1 : 1 ≤ Ke := by linarith only [hKe]
  have hZ4 : (1 : ℝ) ≤ Z ^ 4 := one_le_pow₀ hZ
  have hTreeInv : 1 / (1 / 10000 : ℝ) ≤ Ke * Z ^ 4 := by
    have h := le_mul_of_one_le_right (by linarith only [hKe] : 0 ≤ Ke) hZ4
    norm_num only [one_div_div, div_one] at *
    linarith only [hKe, h]
  have hTreeProfiles := reference_accuracy_log_profile_bounds hg hg1 hKe1 hZ hrR hL1 hrlZ
    (by norm_num : (0 : ℝ) < 1 / 10000) (by norm_num) hTreeInv
  have hRefProfiles := reference_accuracy_log_profile_bounds hg hg1 hKe1 hZ hrR hL1 hrlZ
    hepsilon (hepsilonSmall.trans (by norm_num)) hepsilonInv
  change 1 ≤ btree ∧ btree ≤ b0 + log (Z ^ 5) at hTreeProfiles
  change 1 ≤ bref ∧ bref ≤ b0 + log (Z ^ 5) at hRefProfiles
  have hgInv : 1 ≤ 1 / g := (le_div_iff₀ hg).mpr (by simpa using hg1)
  have hb0 : 1 ≤ b0 := by
    dsimp only [b0]
    linarith [log_nonneg hgInv, log_nonneg (show 1 ≤ 32 * Ke by linarith only [hKe])]
  have ha0 : 0 ≤ a0 := by dsimp only [a0]; positivity
  have ha1 : 0 ≤ a1 := by dsimp only [a1]; positivity
  have hX : (1 : ℝ) ≤ Z ^ 5 := one_le_pow₀ hZ
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
    ha0 ha1 hTreeProfiles.1 hb0
    (by exact_mod_cast Nat.zero_lt_one.trans_le hBtree : (0 : ℝ) < Btree)
    hX hTreeProfiles.2 hlogTree'
  have hBr := reference_profile_polynomial_bound hKref (le_max_right Ktree Kref)
    ha0 ha1 hRefProfiles.1 hb0
    (by exact_mod_cast Nat.zero_lt_one.trans_le hB : (0 : ℝ) < B)
    hX hRefProfiles.2 hlogRef'
  have hBt' : (Btree : ℝ) ≤ Cb * Z ^ P := by simpa only [← pow_mul] using hBt
  have hBr' : (B : ℝ) ≤ Cb * Z ^ P := by simpa only [← pow_mul] using hBr
  have hrZ : (r : ℝ) ≤ Z :=
    (le_mul_of_one_le_right (by positivity) hL1).trans hrlZ
  exact refinement_cost_tail Z c rho Kc Cb Cs CN Ccount Cpoly P D L r s Btree B hZ hLZ hrZ
    hrR hD (exp_pos _) _hc _hrho hcrho hBt' hBr' hs rfl rfl rfl rfl

end Real
