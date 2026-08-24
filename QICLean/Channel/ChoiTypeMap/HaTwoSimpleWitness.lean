/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import Mathlib.RingTheory.RootsOfUnity.Complex
import QICLean.Channel.ChoiTypeMap
import QICLean.Channel.SchmidtNumber

/-!
# Ha's two-simple root-average witness

This module formalizes the first part of the witness construction used by Ha
to prove atomicity of the Choi-type maps. For a dimension `d`, Ha chooses all
`3 ^ d`-th roots of unity, constructs vectors `z_{r,i}` of Schmidt rank at most
two, and defines
\[
  A_r = \frac{1}{3^d}\sum_i |z_{r,i}\rangle\langle z_{r,i}|,
  \qquad
  A_\gamma = \frac1d\sum_r A_r.
\]

The declarations below use zero-based `Fin` indices. Thus source indices
`1, ..., d` become `0, ..., d - 1`; cyclic offsets are still taken in `ZMod d`.
Ha introduces the construction for `γ > 0`, and its witness application assumes
`d ≥ 3` and chooses `0 < γ < 1` so that the final pairing `γ ^ 2 - 1` is negative.
The algebraic definitions and first decomposition below are deliberately total for
every real `γ` and require only `[NeZero d]`: their rank, `V₂`, and PSD proofs use
none of those source inequalities.  This broader input domain does not assert Ha's
later PPT, negative-pairing, or atomicity conclusions outside the source regime.
The block-transpose decomposition on pp. 594--595 is developed separately in
`QICLean.Channel.ChoiTypeMap.HaBlockTranspose`.

## References

* [K.-C. Ha, *Atomic Positive Linear Maps in Matrix Algebras*, Theorem 2.1,
  pp. 593--595][Ha1998AtomicPositiveMaps]
-/

open scoped Matrix ComplexOrder
open Finset

namespace Matrix

variable {d : ℕ} [NeZero d]

/-! ## Ha's roots and two-simple vectors -/

/-- Ha's one-based integer is
\(m_k=\frac32(3^{k-1}-1)\).  With the zero-based Lean index below, this is
\(m_k=\frac32(3^k-1)\).

This is the exponent introduced on Ha 1998, p. 593, immediately before
equation (2.2). -/
def haExponent (k : Fin d) : ℕ :=
  3 * (3 ^ (k : ℕ) - 1) / 2

/-- A sum of two powers of three determines the two exponents up to order.
This is the elementary Sidon property used in Ha's root average. -/
private theorem pow_three_add_pow_three_eq_iff {a b c e : ℕ} :
    3 ^ a + 3 ^ b = 3 ^ c + 3 ^ e ↔
      (a = c ∧ b = e) ∨ (a = e ∧ b = c) := by
  constructor
  · intro h
    have hlog (x y : ℕ) : Nat.log 3 (3 ^ x + 3 ^ y) = max x y := by
      apply Nat.log_eq_of_pow_le_of_lt_pow
      · by_cases hxy : x ≤ y
        · simp [max_eq_right hxy]
        · have hyx : y ≤ x := Nat.le_of_not_ge hxy
          simp [max_eq_left hyx]
      · have hx : 3 ^ x ≤ 3 ^ max x y :=
          Nat.pow_le_pow_right (by norm_num) (Nat.le_max_left x y)
        have hy : 3 ^ y ≤ 3 ^ max x y :=
          Nat.pow_le_pow_right (by norm_num) (Nat.le_max_right x y)
        calc
          3 ^ x + 3 ^ y ≤ 3 ^ max x y + 3 ^ max x y := Nat.add_le_add hx hy
          _ < 3 ^ max x y * 3 := by
            have hp : 0 < 3 ^ max x y := pow_pos (by norm_num) _
            omega
          _ = 3 ^ (max x y + 1) := by rw [pow_succ]
    have hmax : max a b = max c e := by
      rw [← hlog a b, ← hlog c e, h]
    have hordered (x y : ℕ) :
        3 ^ x + 3 ^ y = 3 ^ min x y + 3 ^ max x y := by
      rcases le_total x y with hxy | hyx
      · simp [min_eq_left hxy, max_eq_right hxy]
      · simp [min_eq_right hyx, max_eq_left hyx, add_comm]
    have hmin : min a b = min c e := by
      have hp : 3 ^ min a b = 3 ^ min c e := by
        exact Nat.add_right_cancel (by
          rw [← hordered a b, h, hordered c e, hmax])
      exact (Nat.pow_right_injective (by norm_num : 1 < 3)) hp
    rcases le_total a b with hab | hba <;>
      rcases le_total c e with hce | hec
    · left
      simpa [min_eq_left hab, max_eq_right hab, min_eq_left hce,
        max_eq_right hce] using And.intro hmin hmax
    · right
      simpa [min_eq_left hab, max_eq_right hab, min_eq_right hec,
        max_eq_left hec] using And.intro hmin hmax
    · right
      simpa [min_eq_right hba, max_eq_left hba, min_eq_left hce,
        max_eq_right hce] using And.intro hmax hmin
    · left
      simpa [min_eq_right hba, max_eq_left hba, min_eq_right hec,
        max_eq_left hec] using And.intro hmax hmin
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · rfl
    · ac_rfl

omit [NeZero d] in
/-- Clearing the denominator in Ha's exponent gives its defining odd-power
formula. -/
private theorem two_mul_haExponent (k : Fin d) :
    2 * haExponent k = 3 * (3 ^ (k : ℕ) - 1) := by
  rw [haExponent]
  have hthree : Odd (3 : ℕ) := ⟨1, rfl⟩
  have hodd : Odd (3 ^ (k : ℕ) : ℕ) := hthree.pow
  have heven : Even (3 ^ (k : ℕ) - 1) := Nat.Odd.sub_odd hodd odd_one
  exact Nat.two_mul_div_two_of_even (heven.mul_left 3)

omit [NeZero d] in
/-- Ha's exponents inherit the unordered-pair uniqueness of powers of three. -/
private theorem haExponent_add_eq_iff (a b c e : Fin d) :
    haExponent a + haExponent b = haExponent c + haExponent e ↔
      (a = c ∧ b = e) ∨ (a = e ∧ b = c) := by
  have htwo (k : Fin d) :
      (2 : ℤ) * haExponent k = 3 * ((3 : ℤ) ^ (k : ℕ) - 1) := by
    calc
      (2 : ℤ) * haExponent k = ((2 * haExponent k : ℕ) : ℤ) := by norm_num
      _ = ((3 * (3 ^ (k : ℕ) - 1) : ℕ) : ℤ) := by rw [two_mul_haExponent]
      _ = 3 * ((3 : ℤ) ^ (k : ℕ) - 1) := by
        rw [Nat.cast_mul, Nat.cast_sub (one_le_pow₀ (by norm_num : (1 : ℕ) ≤ 3)),
          Nat.cast_pow]
        norm_num
  constructor
  · intro h
    have hpz :
        (3 : ℤ) ^ (a : ℕ) + (3 : ℤ) ^ (b : ℕ) =
          (3 : ℤ) ^ (c : ℕ) + (3 : ℤ) ^ (e : ℕ) := by
      have hz :
          (2 : ℤ) * (haExponent a + haExponent b) =
            2 * (haExponent c + haExponent e) := by exact_mod_cast congrArg (2 * ·) h
      nlinarith [htwo a, htwo b, htwo c, htwo e]
    have hp :
        3 ^ (a : ℕ) + 3 ^ (b : ℕ) =
          3 ^ (c : ℕ) + 3 ^ (e : ℕ) := by exact_mod_cast hpz
    rcases pow_three_add_pow_three_eq_iff.mp hp with h | h
    · exact Or.inl ⟨Fin.ext h.1, Fin.ext h.2⟩
    · exact Or.inr ⟨Fin.ext h.1, Fin.ext h.2⟩
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · rfl
    · ac_rfl

omit [NeZero d] in
/-- Every pair-sum of Ha exponents lies in the canonical residue interval for
the `3 ^ d`-th roots of unity. -/
private theorem haExponent_add_lt_card (a b : Fin d) :
    haExponent a + haExponent b < 3 ^ d := by
  have hsingle (k : Fin d) : 2 * haExponent k < 3 ^ d := by
    rw [two_mul_haExponent]
    calc
      3 * (3 ^ (k : ℕ) - 1) < 3 * 3 ^ (k : ℕ) := by
        gcongr
        exact Nat.sub_lt (pow_pos (by norm_num) _) (by norm_num)
      _ = 3 ^ ((k : ℕ) + 1) := by rw [pow_succ]; ring
      _ ≤ 3 ^ d := Nat.pow_le_pow_right (by norm_num) k.isLt
  have ha := hsingle a
  have hb := hsingle b
  omega

/-- The canonical primitive `3 ^ d`-th root used to enumerate Ha's complete
family of roots of unity on p. 593. -/
noncomputable def haPrimitiveRoot (d : ℕ) : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I / (3 ^ d : ℂ))

/-- The zero-based enumeration of all `3 ^ d`-th roots of unity used in Ha's
vectors `a_{i,k}`. -/
noncomputable def haRootOfUnity (d : ℕ) (i : Fin (3 ^ d)) : ℂ :=
  haPrimitiveRoot d ^ (i : ℕ)

/-- The chosen generator really is a primitive `3 ^ d`-th root of unity. -/
theorem haPrimitiveRoot_isPrimitive (d : ℕ) :
    IsPrimitiveRoot (haPrimitiveRoot d) (3 ^ d) := by
  simpa [haPrimitiveRoot] using
    Complex.isPrimitiveRoot_exp (3 ^ d) (pow_ne_zero d (by norm_num : 3 ≠ 0))

/-- Every member of Ha's root family is a `3 ^ d`-th root of unity. -/
theorem haRootOfUnity_pow_card (d : ℕ) (i : Fin (3 ^ d)) :
    haRootOfUnity d i ^ (3 ^ d) = 1 := by
  rw [haRootOfUnity, ← pow_mul, Nat.mul_comm, pow_mul,
    (haPrimitiveRoot_isPrimitive d).pow_eq_one, one_pow]

/-- Ha's vector `a_{i,k}` on pp. 593--594.  At zero-based `k = 0` this is
`a_{i,1}` from the paper; the other vectors are its stated phase multiples. -/
noncomputable def haPhaseVector (d : ℕ) [NeZero d]
    (i : Fin (3 ^ d)) (k : Fin d) : Fin d → ℂ :=
  fun p ↦ (haRootOfUnity d i)⁻¹ ^ haExponent k *
    haRootOfUnity d i ^ haExponent p

/-- The coordinates of `a_{i,k}` are a single integer power of Ha's root. -/
private theorem haPhaseVector_eq_zpow (i : Fin (3 ^ d)) (k p : Fin d) :
    haPhaseVector d i k p =
      haRootOfUnity d i ^ ((haExponent p : ℤ) - (haExponent k : ℤ)) := by
  have hn : haRootOfUnity d i ≠ 0 := by
    rw [haRootOfUnity]
    exact pow_ne_zero _ ((haPrimitiveRoot_isPrimitive d).ne_zero
      (pow_ne_zero d (by norm_num)))
  rw [haPhaseVector, zpow_sub₀ hn, zpow_natCast, zpow_natCast]
  simp only [inv_pow]
  ring

/-- Complex conjugation inverts every root in Ha's enumeration. -/
private theorem star_haRootOfUnity (d : ℕ) (i : Fin (3 ^ d)) :
    star (haRootOfUnity d i) = (haRootOfUnity d i)⁻¹ := by
  have hp := haPrimitiveRoot_isPrimitive d
  have hn : 3 ^ d ≠ 0 := pow_ne_zero d (by norm_num)
  have hs : star (haPrimitiveRoot d) = (haPrimitiveRoot d)⁻¹ := by
    simpa [Complex.star_def] using (Complex.inv_eq_conj (hp.norm'_eq_one hn)).symm
  simp [haRootOfUnity, star_pow, hs, inv_pow]

/-- Conjugating a phase coordinate reverses its exponent difference. -/
private theorem star_haPhaseVector (i : Fin (3 ^ d)) (k p : Fin d) :
    star (haPhaseVector d i k p) =
      haRootOfUnity d i ^ ((haExponent k : ℤ) - (haExponent p : ℤ)) := by
  rw [haPhaseVector_eq_zpow, star_zpow₀, star_haRootOfUnity]
  calc
    (haRootOfUnity d i)⁻¹ ^ ((haExponent p : ℤ) - (haExponent k : ℤ)) =
        haRootOfUnity d i ^ (-((haExponent p : ℤ) - (haExponent k : ℤ))) := by
      exact _root_.inv_zpow' _ _
    _ = _ := by
      congr 1
      omega

/-- A phase-product appearing in Ha's projector average is a geometric
progression in the chosen primitive root. -/
private theorem haPhaseVector_mul_star_eq_geom (i : Fin (3 ^ d))
    (a b c e : Fin d) :
    haPhaseVector d i e a * star (haPhaseVector d i b c) =
      ((haPrimitiveRoot d) ^ (haExponent a + haExponent b) *
        ((haPrimitiveRoot d) ^ (haExponent c + haExponent e))⁻¹) ^ (i : ℕ) := by
  have hroot : haRootOfUnity d i ≠ 0 := by
    rw [haRootOfUnity]
    exact pow_ne_zero _ ((haPrimitiveRoot_isPrimitive d).ne_zero
      (pow_ne_zero d (by norm_num)))
  rw [haPhaseVector_eq_zpow, star_haPhaseVector, ← zpow_add₀ hroot,
    show (haExponent a : ℤ) - haExponent e +
        ((haExponent b : ℤ) - haExponent c) =
      (haExponent a + haExponent b : ℕ) - (haExponent c + haExponent e : ℕ) by
      push_cast
      ring,
    zpow_sub₀ hroot, zpow_natCast, zpow_natCast, haRootOfUnity]
  simp only [pow_add, mul_pow, inv_pow]
  ring

/-- Ha's complete root average is one exactly when the two unordered index
pairs agree, and is zero otherwise. -/
private theorem sum_haPhaseVector_mul_star (a b c e : Fin d) :
    ∑ i : Fin (3 ^ d),
        haPhaseVector d i e a * star (haPhaseVector d i b c) =
      if (a = c ∧ b = e) ∨ (a = e ∧ b = c) then (3 ^ d : ℂ) else 0 := by
  classical
  let s := haExponent a + haExponent b
  let t := haExponent c + haExponent e
  let ζ := haPrimitiveRoot d
  let x := ζ ^ s * (ζ ^ t)⁻¹
  simp_rw [haPhaseVector_mul_star_eq_geom]
  change (∑ i : Fin (3 ^ d), x ^ (i : ℕ)) = _
  by_cases hpairs : (a = c ∧ b = e) ∨ (a = e ∧ b = c)
  · have hst : s = t := by
      exact haExponent_add_eq_iff a b c e |>.2 hpairs
    have hζne : ζ ≠ 0 := (haPrimitiveRoot_isPrimitive d).ne_zero
      (pow_ne_zero d (by norm_num))
    have hx : x = 1 := by simp [x, hst, hζne]
    simp [hpairs, hx]
  · have hst : s ≠ t := by
      exact fun h ↦ hpairs (haExponent_add_eq_iff a b c e |>.1 h)
    have hζt : ζ ^ t ≠ 0 :=
      pow_ne_zero _ ((haPrimitiveRoot_isPrimitive d).ne_zero
        (pow_ne_zero d (by norm_num)))
    have hxne : x ≠ 1 := by
      intro hx
      have hpoweq : ζ ^ s = ζ ^ t := (mul_inv_eq_one₀ hζt).mp hx
      exact hst <| (haPrimitiveRoot_isPrimitive d).pow_inj
        (haExponent_add_lt_card a b) (haExponent_add_lt_card c e) hpoweq
    have hxpow : x ^ (3 ^ d) = 1 := by
      change (ζ ^ s * (ζ ^ t)⁻¹) ^ (3 ^ d) = 1
      have hpow (k : ℕ) : (ζ ^ k) ^ (3 ^ d) = 1 := by
        rw [← pow_mul, Nat.mul_comm k, pow_mul,
          (haPrimitiveRoot_isPrimitive d).pow_eq_one, one_pow]
      rw [mul_pow, inv_pow, hpow s, hpow t, inv_one, mul_one]
    simp only [hpairs, ↓reduceIte]
    rw [Fin.sum_univ_eq_sum_range]
    apply mul_left_cancel₀ (sub_ne_zero.mpr hxne)
    rw [mul_geom_sum, hxpow]
    simp

/-- The zero-based phase-vector relation
`a_{i,k} = ω_i ^ (-m_k) • a_{i,0}`, corresponding to Ha's one-based
relation with base vector `a_{i,1}` on p. 593. -/
theorem haPhaseVector_eq_smul_zero (i : Fin (3 ^ d)) (k : Fin d) :
    haPhaseVector d i k =
      (haRootOfUnity d i)⁻¹ ^ haExponent k • haPhaseVector d i 0 := by
  ext p
  simp [haPhaseVector, haExponent]

/-- The coordinates of Ha's base vector
`c₁ = e₁ + γ e₂ + e₃ + ... + e_{d-1} + γ⁻¹ e_d`, written on the cyclic
index set. -/
noncomputable def haBaseWeight (γ : ℝ) (p : ZMod d) : ℂ :=
  if p = 1 then (γ : ℂ) else if p = -1 then (γ : ℂ)⁻¹ else 1

/-- The coordinate of `c_r = S^(r-1) c₁` at `p`, with both source indices
shifted to zero-based `Fin d`. -/
noncomputable def haCyclicWeight (d : ℕ) [NeZero d]
    (γ : ℝ) (r p : Fin d) : ℂ :=
  haBaseWeight γ (ZMod.finEquiv d p - ZMod.finEquiv d r)

/-- The exceptional vector `c_r ∘ a_{i,r}` in Ha's definition of `b_{r,i,j}`. -/
noncomputable def haModifiedPhaseVector (d : ℕ) [NeZero d]
    (γ : ℝ) (r : Fin d) (i : Fin (3 ^ d)) : Fin d → ℂ :=
  fun p ↦ haCyclicWeight d γ r p * haPhaseVector d i r p

/-- Ha's vector `z_{r,i} = Σ_j b_{r,i,j} ⊗ e_j` from p. 594, in coordinates.
The `j = r` column is `c_r ∘ a_{i,r}` and every other column is `a_{i,j}`. -/
noncomputable def haTwoSimpleVector (d : ℕ) [NeZero d]
    (γ : ℝ) (r : Fin d) (i : Fin (3 ^ d)) : Fin d × Fin d → ℂ :=
  fun p ↦ if p.2 = r then haModifiedPhaseVector d γ r i p.1
    else haPhaseVector d i p.2 p.1

/-- The single exceptional column-weight in `z_{r,i}`. -/
noncomputable def haTwoSimpleWeight (d : ℕ) [NeZero d]
    (γ : ℝ) (r : Fin d) (p : Fin d × Fin d) : ℂ :=
  if p.2 = r then haCyclicWeight d γ r p.1 else 1

/-- Separating the root-dependent phase from the exceptional column-weight. -/
private theorem haTwoSimpleVector_eq_weight_mul (γ : ℝ) (r : Fin d)
    (i : Fin (3 ^ d)) (p : Fin d × Fin d) :
    haTwoSimpleVector d γ r i p =
      haTwoSimpleWeight d γ r p * haPhaseVector d i p.2 p.1 := by
  by_cases hp : p.2 = r
  · simp [haTwoSimpleVector, haTwoSimpleWeight, hp, haModifiedPhaseVector]
  · simp [haTwoSimpleVector, haTwoSimpleWeight, hp]

/-- Each `z_{r,i}` is 2-simple in Ha's terminology: its coefficient-matrix
columns lie in the span of the zero-based vectors `a_{i,0}` and
`c_r ∘ a_{i,r}`.

This is the first substantive step of Ha 1998, p. 594. -/
theorem haTwoSimpleVector_hasSchmidtRankLE_two
    (γ : ℝ) (r : Fin d) (i : Fin (3 ^ d)) :
    HasSchmidtRankLE 2 (haTwoSimpleVector d γ r i) := by
  classical
  let a₀ : Fin d → ℂ := haPhaseVector d i 0
  let bᵣ : Fin d → ℂ := haModifiedPhaseVector d γ r i
  rw [HasSchmidtRankLE, schmidtRank, Matrix.rank_eq_finrank_span_cols]
  have hcols :
      Submodule.span ℂ
          (Set.range (fun j : Fin d ↦
            (schmidtCoeffMatrix (haTwoSimpleVector d γ r i)).col j)) ≤
        Submodule.span ℂ ({a₀, bᵣ} : Set (Fin d → ℂ)) := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨j, rfl⟩
    by_cases hj : j = r
    · subst j
      have hcol :
          (schmidtCoeffMatrix (haTwoSimpleVector d γ r i)).col r = bᵣ := by
        ext p
        simp [Matrix.col_apply, schmidtCoeffMatrix, haTwoSimpleVector, bᵣ]
      change (schmidtCoeffMatrix (haTwoSimpleVector d γ r i)).col r ∈
        Submodule.span ℂ ({a₀, bᵣ} : Set (Fin d → ℂ))
      rw [hcol]
      exact Submodule.subset_span (by simp)
    · have hcol :
          (schmidtCoeffMatrix (haTwoSimpleVector d γ r i)).col j =
            (haRootOfUnity d i)⁻¹ ^ haExponent j • a₀ := by
        ext p
        simpa [Matrix.col_apply, schmidtCoeffMatrix, haTwoSimpleVector, hj, a₀] using
          congrFun (haPhaseVector_eq_smul_zero (d := d) i j) p
      change (schmidtCoeffMatrix (haTwoSimpleVector d γ r i)).col j ∈
        Submodule.span ℂ ({a₀, bᵣ} : Set (Fin d → ℂ))
      rw [hcol]
      exact Submodule.smul_mem _ _
        (Submodule.subset_span (by simp : a₀ ∈ ({a₀, bᵣ} : Set (Fin d → ℂ))))
  exact (Submodule.finrank_mono hcols).trans <| by
    calc
      Module.finrank ℂ ↥(Submodule.span ℂ ({a₀, bᵣ} : Set (Fin d → ℂ))) ≤
          ({a₀, bᵣ} : Set (Fin d → ℂ)).toFinset.card :=
        finrank_span_le_card ({a₀, bᵣ} : Set (Fin d → ℂ))
      _ ≤ 2 := by
        rw [Set.toFinset_insert, Set.toFinset_singleton]
        show (insert a₀ {bᵣ} : Finset (Fin d → ℂ)).card ≤ 2
        calc
          (insert a₀ {bᵣ} : Finset (Fin d → ℂ)).card ≤
              ({bᵣ} : Finset (Fin d → ℂ)).card + 1 :=
            Finset.card_insert_le a₀ {bᵣ}
          _ = 2 := by simp

/-! ## The root-average witness -/

/-- Ha's matrix `A_r = 3⁻ᵈ Σ_i z_{r,i} z_{r,i}*` from p. 594. -/
noncomputable def haArGamma (d : ℕ) [NeZero d] (γ : ℝ) (r : Fin d) :
    Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ :=
  ((3 ^ d : ℝ)⁻¹) •
    ∑ i : Fin (3 ^ d),
      vecMulVec (haTwoSimpleVector d γ r i) (star (haTwoSimpleVector d γ r i))

/-- Entrywise evaluation of Ha's root average. -/
theorem haArGamma_apply (γ : ℝ) (r a b c e : Fin d) :
    haArGamma d γ r (a, e) (c, b) =
      haTwoSimpleWeight d γ r (a, e) *
        star (haTwoSimpleWeight d γ r (c, b)) *
          (if (a = c ∧ b = e) ∨ (a = e ∧ b = c) then 1 else 0) := by
  classical
  rw [haArGamma]
  simp only [smul_apply, sum_apply, vecMulVec_apply, Pi.star_apply,
    haTwoSimpleVector_eq_weight_mul, star_mul']
  rw [RCLike.real_smul_eq_coe_smul (K := ℂ) (E := ℂ)]
  simp only [smul_eq_mul]
  rw [show (∑ i : Fin (3 ^ d),
        haTwoSimpleWeight d γ r (a, e) * haPhaseVector d i e a *
          (star (haTwoSimpleWeight d γ r (c, b)) *
            star (haPhaseVector d i b c))) =
      haTwoSimpleWeight d γ r (a, e) *
        star (haTwoSimpleWeight d γ r (c, b)) *
          ∑ i : Fin (3 ^ d),
            haPhaseVector d i e a * star (haPhaseVector d i b c) by
    rw [mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring]
  rw [sum_haPhaseVector_mul_star]
  by_cases hpairs : (a = c ∧ b = e) ∨ (a = e ∧ b = c)
  · simp only [hpairs, ↓reduceIte]
    have hcard : (3 ^ d : ℂ) ≠ 0 := by positivity
    push_cast
    field_simp
  · simp [hpairs]

/-- Ha's `A_γ = d⁻¹ Σ_r A_r` from p. 594. -/
noncomputable def haAGamma (d : ℕ) [NeZero d] (γ : ℝ) :
    Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ :=
  ((d : ℝ)⁻¹) • ∑ r : Fin d, haArGamma d γ r

/-- Each root average `A_r` belongs to Ha's cone `V₂`, expressed in the
repository's Schmidt-number terminology. -/
theorem haArGamma_hasSchmidtNumberLE_two (γ : ℝ) (r : Fin d) :
    HasSchmidtNumberLE 2 (haArGamma d γ r) := by
  rw [haArGamma]
  apply HasSchmidtNumberLE.smul ?_ (by positivity)
  exact hasSchmidtNumberLE_sum Finset.univ fun i _ ↦
    hasSchmidtNumberLE_vecMulVec (haTwoSimpleVector_hasSchmidtRankLE_two γ r i)

/-- **Ha 1998, pp. 594--595, first witness decomposition.**  The matrix
`A_γ` belongs to `V₂`: it is a nonnegative average of projectors onto Ha's
2-simple vectors.

This theorem is the first decomposition. Ha's displayed block-transpose
decomposition is proved in `QICLean.Channel.ChoiTypeMap.HaBlockTranspose`; the
factor shuffle and negative pairing are separate later steps. -/
theorem haAGamma_hasSchmidtNumberLE_two (γ : ℝ) :
    HasSchmidtNumberLE 2 (haAGamma d γ) := by
  rw [haAGamma]
  apply HasSchmidtNumberLE.smul ?_ (by positivity)
  exact hasSchmidtNumberLE_sum Finset.univ fun r _ ↦
    haArGamma_hasSchmidtNumberLE_two γ r

/-- Ha's `A_γ` is positive semidefinite.  This is the PSD half supplied by
its explicit `V₂` decomposition; positivity of its block transpose is a later
displayed decomposition on Ha 1998, p. 595. -/
theorem haAGamma_posSemidef (γ : ℝ) :
    (haAGamma d γ).PosSemidef := by
  exact (haAGamma_hasSchmidtNumberLE_two γ).posSemidef

/-! ## Shared two-term Schmidt-rank bound -/

/-- The elementary tensor `e_i ⊗ e_j`, in the coefficient convention used by
`haTwoSimpleVector`. -/
def haTensorBasis (i j : Fin d) : Fin d × Fin d → ℂ :=
  fun p ↦ (if p.1 = i then 1 else 0) * (if p.2 = j then 1 else 0)

omit [NeZero d] in
/-- A sum of two product vectors has Schmidt rank at most two. -/
private theorem hasSchmidtRankLE_two_product_add
    (u₁ u₂ v₁ v₂ : Fin d → ℂ) :
    HasSchmidtRankLE 2 (fun p : Fin d × Fin d ↦
      u₁ p.1 * v₁ p.2 + u₂ p.1 * v₂ p.2) := by
  classical
  rw [HasSchmidtRankLE, schmidtRank, Matrix.rank_eq_finrank_span_cols]
  have hcols :
      Submodule.span ℂ
          (Set.range (fun j : Fin d ↦
            (schmidtCoeffMatrix (fun p : Fin d × Fin d ↦
              u₁ p.1 * v₁ p.2 + u₂ p.1 * v₂ p.2)).col j)) ≤
        Submodule.span ℂ ({u₁, u₂} : Set (Fin d → ℂ)) := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨j, rfl⟩
    have hcol :
        (schmidtCoeffMatrix (fun p : Fin d × Fin d ↦
          u₁ p.1 * v₁ p.2 + u₂ p.1 * v₂ p.2)).col j =
            v₁ j • u₁ + v₂ j • u₂ := by
      ext i
      simp [Matrix.col_apply, schmidtCoeffMatrix]
      ring
    change
      (schmidtCoeffMatrix (fun p : Fin d × Fin d ↦
        u₁ p.1 * v₁ p.2 + u₂ p.1 * v₂ p.2)).col j ∈
          Submodule.span ℂ ({u₁, u₂} : Set (Fin d → ℂ))
    rw [hcol]
    exact Submodule.add_mem _
      (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
      (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
  exact (Submodule.finrank_mono hcols).trans <| by
    calc
      Module.finrank ℂ ↥(Submodule.span ℂ ({u₁, u₂} : Set (Fin d → ℂ))) ≤
          ({u₁, u₂} : Set (Fin d → ℂ)).toFinset.card :=
        finrank_span_le_card ({u₁, u₂} : Set (Fin d → ℂ))
      _ ≤ 2 := by
        rw [Set.toFinset_insert, Set.toFinset_singleton]
        calc
          (insert u₁ {u₂} : Finset (Fin d → ℂ)).card ≤
              ({u₂} : Finset (Fin d → ℂ)).card + 1 :=
            Finset.card_insert_le u₁ {u₂}
          _ = 2 := by simp

omit [NeZero d] in
/-- A linear combination of two elementary tensors has Schmidt rank at most two. -/
theorem hasSchmidtRankLE_two_tensorBasis_add
    (a b : ℂ) (i j k l : Fin d) :
    HasSchmidtRankLE 2 (fun p : Fin d × Fin d ↦
      a * haTensorBasis i j p + b * haTensorBasis k l p) := by
  have h := hasSchmidtRankLE_two_product_add (d := d)
    (fun x : Fin d ↦ a * if x = i then 1 else 0)
    (fun x : Fin d ↦ b * if x = k then 1 else 0)
    (fun y : Fin d ↦ if y = j then 1 else 0)
    (fun y : Fin d ↦ if y = l then 1 else 0)
  convert h using 1
  funext p
  simp [haTensorBasis]

end Matrix
