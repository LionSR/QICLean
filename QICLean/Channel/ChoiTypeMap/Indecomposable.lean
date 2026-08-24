/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import Mathlib.RingTheory.RootsOfUnity.Complex
import QICLean.Channel.ChoiTypeMap
import QICLean.Channel.PartialTranspose
import QICLean.Channel.SchmidtNumber

/-!
# Ha's two-simple witness for Choi-type maps

This file begins the source-faithful witness construction used by Ha to prove
atomicity of the Choi-type maps.  For a dimension `d`, Ha chooses all
`3 ^ d`-th roots of unity, constructs vectors `z_{r,i}` of Schmidt rank at most
two, and defines
\[
  A_r = \frac{1}{3^d}\sum_i |z_{r,i}\rangle\langle z_{r,i}|,
  \qquad
  A_\gamma = \frac1d\sum_r A_r.
\]

The declarations below use zero-based `Fin` indices.  Thus source indices
`1, ..., d` become `0, ..., d - 1`; cyclic offsets are still taken in `ZMod d`.
Ha introduces the construction for `γ > 0`, and its witness application assumes
`d ≥ 3` and chooses `0 < γ < 1` so that the final pairing `γ ^ 2 - 1` is negative.
The algebraic definitions and first decomposition below are deliberately total for
every real `γ` and require only `[NeZero d]`: their rank, `V₂`, and PSD proofs use
none of those source inequalities.  This broader input domain does not assert Ha's
later PPT, negative-pairing, or atomicity conclusions outside the source regime.
The two results proved here are the exact `V₂` assertions for `A_γ` and for
the partial transpose on Ha's displayed block factor.  The latter is identified
with the repository's right-factor partial transpose and is proved from Ha's
displayed `u_i`, `v_i`, `α_i`, and `β_{i,j}` projector decomposition.  The
Eom--Kye factor shuffle and the negative pairing with the Choi-type map remain
separate steps.

## References

* [K.-C. Ha, *Atomic Positive Linear Maps in Matrix Algebras*, Theorem 2.1,
  pp. 593--595][Ha1998AtomicPositiveMaps]
* [M.-H. Eom and S.-H. Kye, *Duality for Positive Linear Maps in Matrix
  Algebras*, Corollary 3.2 and Theorem 3.3(iii)][EomKye2000Duality]
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
        · simpa [max_eq_right hxy] using Nat.le_add_left (3 ^ y) (3 ^ x)
        · have hyx : y ≤ x := Nat.le_of_not_ge hxy
          simpa [max_eq_left hyx] using Nat.le_add_right (3 ^ x) (3 ^ y)
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

/-- Clearing the denominator in Ha's exponent gives its defining odd-power
formula. -/
private theorem two_mul_haExponent (k : Fin d) :
    2 * haExponent k = 3 * (3 ^ (k : ℕ) - 1) := by
  rw [haExponent]
  have hthree : Odd (3 : ℕ) := ⟨1, rfl⟩
  have hodd : Odd (3 ^ (k : ℕ) : ℕ) := hthree.pow
  have heven : Even (3 ^ (k : ℕ) - 1) := Nat.Odd.sub_odd hodd odd_one
  exact Nat.two_mul_div_two_of_even (heven.mul_left 3)

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
    _ = _ := by congr 1 <;> omega

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
  simp only [pow_add, mul_inv_rev, mul_pow, inv_pow, pow_mul]
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
private noncomputable def haTwoSimpleWeight (d : ℕ) [NeZero d]
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
private theorem haArGamma_apply (γ : ℝ) (r a b c e : Fin d) :
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
  · simp only [hpairs, if_pos]
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

**Scope restriction (first decomposition only):** Ha's subsequent decomposition
of the block transpose, factor shuffle, and negative pairing are not asserted
here.  They are recorded in
`docs/paper-gaps/ha98_choi_type_witness_scope.tex`. -/
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

/-! ## Ha's block-transpose decomposition -/

/-- The elementary tensor `e_i ⊗ e_j`, in the coefficient convention used by
`haTwoSimpleVector`. -/
def haTensorBasis (i j : Fin d) : Fin d × Fin d → ℂ :=
  fun p ↦ (if p.1 = i then 1 else 0) * (if p.2 = j then 1 else 0)

/-- Ha's cyclic successor `i + 1`, with suffixes understood modulo `d`. -/
def haCyclicSucc (i : Fin d) : Fin d :=
  i + 1

/-- The squared exceptional cyclic weight, written in the source's two
oriented neighbouring cases. -/
private theorem haCyclicWeight_mul_star (hd : 3 ≤ d) (γ : ℝ) (a b : Fin d) :
    haCyclicWeight d γ b a * star (haCyclicWeight d γ b a) =
      if a = haCyclicSucc b then (γ : ℂ) ^ 2
      else if b = haCyclicSucc a then ((γ : ℂ)⁻¹) ^ 2 else 1 := by
  have hneg : (-1 : ZMod d) ≠ 1 := by
    intro h
    have h' : ((-1 : ℤ) : ZMod d) = ((1 : ℤ) : ZMod d) := by simpa using h
    have hdvdz : (d : ℤ) ∣ (2 : ℤ) := by
      simpa using
        (ZMod.intCast_eq_intCast_iff_dvd_sub (-1 : ℤ) (1 : ℤ) d).mp h'
    have hdvd : d ∣ 2 := Int.natCast_dvd_natCast.mp hdvdz
    exact (by omega : ¬d ≤ 2) (Nat.le_of_dvd (by norm_num) hdvd)
  have hoff_one {p q : Fin d}
      (h : ZMod.finEquiv d p - ZMod.finEquiv d q = 1) :
      p = haCyclicSucc q := by
    apply (ZMod.finEquiv d).injective
    calc
      ZMod.finEquiv d p =
          (ZMod.finEquiv d p - ZMod.finEquiv d q) + ZMod.finEquiv d q := by ring
      _ = 1 + ZMod.finEquiv d q := by rw [h]
      _ = ZMod.finEquiv d (haCyclicSucc q) := by
        simp [haCyclicSucc, add_comm]
  by_cases hab : a = haCyclicSucc b
  · rw [if_pos hab]
    subst a
    simp [haCyclicWeight, haCyclicSucc, haBaseWeight]
    ring
  · by_cases hba : b = haCyclicSucc a
    · rw [if_neg hab, if_pos hba]
      subst b
      have hw : haCyclicWeight d γ (haCyclicSucc a) a = (γ : ℂ)⁻¹ := by
        simp [haCyclicWeight, haCyclicSucc, haBaseWeight, hneg]
      rw [hw]
      simp
      ring
    · have hone : ZMod.finEquiv d a - ZMod.finEquiv d b ≠ 1 :=
        fun h ↦ hab (hoff_one h)
      have hminus : ZMod.finEquiv d a - ZMod.finEquiv d b ≠ -1 := by
        intro h
        apply hba
        apply hoff_one
        rw [show ZMod.finEquiv d b - ZMod.finEquiv d a =
          -(ZMod.finEquiv d a - ZMod.finEquiv d b) by ring, h]
        simp
      simp [haCyclicWeight, haBaseWeight, hab, hba, hone, hminus]

/-- A diagonal coordinate of `z_{r,i}` has no exceptional weight. -/
private theorem haTwoSimpleWeight_diag (hd : 3 ≤ d) (γ : ℝ)
    (r a : Fin d) : haTwoSimpleWeight d γ r (a, a) = 1 := by
  letI : Fact (1 < d) := ⟨by omega⟩
  by_cases har : a = r
  · subst a
    simp [haTwoSimpleWeight, haCyclicWeight, haBaseWeight]
  · simp [haTwoSimpleWeight, har]

/-- Averaging the exceptional column leaves `d-1` unit weights and one cyclic
weight. -/
private theorem sum_haTwoSimpleWeight_self (hd : 3 ≤ d) (γ : ℝ)
    (a b : Fin d) :
    (∑ r : Fin d,
        haTwoSimpleWeight d γ r (a, b) * star (haTwoSimpleWeight d γ r (a, b))) =
      haCyclicWeight d γ b a * star (haCyclicWeight d γ b a) + (d - 1 : ℕ) := by
  classical
  let f : Fin d → ℂ := fun r ↦
    haTwoSimpleWeight d γ r (a, b) * star (haTwoSimpleWeight d γ r (a, b))
  have hsplit := Finset.sum_erase_add (Finset.univ : Finset (Fin d)) f
    (Finset.mem_univ b)
  rw [← hsplit]
  have herase :
      (∑ r ∈ (Finset.univ : Finset (Fin d)).erase b, f r) =
        ((Finset.univ : Finset (Fin d)).erase b).card := by
    calc
      _ = ∑ _r ∈ (Finset.univ : Finset (Fin d)).erase b, (1 : ℂ) := by
        apply Finset.sum_congr rfl
        intro r hr
        have hrb : b ≠ r := (Finset.mem_erase.mp hr).1.symm
        simp [f, haTwoSimpleWeight, hrb]
      _ = _ := by simp
  rw [herase]
  simp [f, haTwoSimpleWeight, Finset.card_erase_of_mem, Fintype.card_fin, add_comm]

/-- Ha's vector
`u_i = γ / √d (e_{i+1} ⊗ e_i) + 1 / (√d γ) (e_i ⊗ e_{i+1})`
from p. 594, with zero-based cyclic indices. -/
noncomputable def haUVector (d : ℕ) [NeZero d] (γ : ℝ) (i : Fin d) :
    Fin d × Fin d → ℂ :=
  fun p ↦ (γ / Real.sqrt d : ℝ) * haTensorBasis (haCyclicSucc i) i p +
    ((Real.sqrt d * γ)⁻¹ : ℝ) * haTensorBasis i (haCyclicSucc i) p

/-- Ha's vector
`v_i = √((d-1)/d) (e_{i+1} ⊗ e_i + e_i ⊗ e_{i+1})`
from p. 594. -/
noncomputable def haVVector (d : ℕ) [NeZero d] (i : Fin d) :
    Fin d × Fin d → ℂ :=
  fun p ↦ Real.sqrt (((d : ℝ) - 1) / d) *
    (haTensorBasis (haCyclicSucc i) i p + haTensorBasis i (haCyclicSucc i) p)

private theorem haCyclicSucc_ne (hd : 3 ≤ d) (i : Fin d) : haCyclicSucc i ≠ i := by
  intro h
  have hv := congrArg Fin.val h
  by_cases hi : i.val + 1 < d
  · rw [haCyclicSucc, Fin.val_add, Fin.val_one',
      Nat.mod_eq_of_lt (by omega : 1 < d), Nat.mod_eq_of_lt hi] at hv
    omega
  · have hieq : i.val + 1 = d := by omega
    rw [haCyclicSucc, Fin.val_add, Fin.val_one',
      Nat.mod_eq_of_lt (by omega : 1 < d), hieq, Nat.mod_self] at hv
    omega

private theorem haCyclicSucc_injective : Function.Injective (haCyclicSucc : Fin d → Fin d) := by
  intro i j h
  apply (ZMod.finEquiv d).injective
  have hz := congrArg (ZMod.finEquiv d) h
  simpa [haCyclicSucc] using hz

private theorem haCyclicSucc_twice_ne (hd : 3 ≤ d) (i : Fin d) :
    haCyclicSucc (haCyclicSucc i) ≠ i := by
  intro h
  have hz := congrArg (ZMod.finEquiv d) h
  have hz' : (1 : ZMod d) + 1 = 0 := by
    simpa [haCyclicSucc, add_assoc] using
      congrArg (fun z : ZMod d ↦ z - ZMod.finEquiv d i) hz
  have hzcast : ((2 : ℤ) : ZMod d) = 0 := by
    rw [show (2 : ℤ) = 1 + 1 by norm_num, Int.cast_add, Int.cast_one]
    exact hz'
  have hdvdz : (d : ℤ) ∣ (2 : ℤ) :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd (2 : ℤ) d).mp hzcast
  have hdvd : d ∣ 2 := Int.natCast_dvd_natCast.mp hdvdz
  exact (by omega : ¬d ≤ 2) (Nat.le_of_dvd (by norm_num) hdvd)

private theorem haTensorBasis_eq_zero_of_ne (i j : Fin d) (p : Fin d × Fin d)
    (h : p ≠ (i, j)) : haTensorBasis i j p = 0 := by
  rcases p with ⟨a, b⟩
  simp only [haTensorBasis]
  by_cases hai : a = i
  · rw [if_pos hai]
    by_cases hbj : b = j
    · exact (h (Prod.ext hai hbj)).elim
    · simp [hbj]
  · simp [hai]

private theorem haUVector_eq_zero_of_not_support (γ : ℝ) (i : Fin d)
    (p : Fin d × Fin d)
    (h : p ≠ (haCyclicSucc i, i) ∧ p ≠ (i, haCyclicSucc i)) :
    haUVector d γ i p = 0 := by
  rw [haUVector, haTensorBasis_eq_zero_of_ne _ _ _ h.1,
    haTensorBasis_eq_zero_of_ne _ _ _ h.2]
  ring

private theorem haVVector_eq_zero_of_not_support (i : Fin d)
    (p : Fin d × Fin d)
    (h : p ≠ (haCyclicSucc i, i) ∧ p ≠ (i, haCyclicSucc i)) :
    haVVector d i p = 0 := by
  rw [haVVector, haTensorBasis_eq_zero_of_ne _ _ _ h.1,
    haTensorBasis_eq_zero_of_ne _ _ _ h.2]
  ring

/-- Ha's diagonal vector `α_i = e_i ⊗ e_i` from p. 595. -/
def haAlphaVector (i : Fin d) : Fin d × Fin d → ℂ :=
  haTensorBasis i i

/-- Ha's symmetric vector `β_{i,j} = e_j ⊗ e_i + e_i ⊗ e_j` from p. 595. -/
def haBetaVector (i j : Fin d) : Fin d × Fin d → ℂ :=
  fun p ↦ haTensorBasis j i p + haTensorBasis i j p

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

private theorem hasSchmidtRankLE_two_tensorBasis_add
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

private theorem haUVector_hasSchmidtRankLE_two (γ : ℝ) (i : Fin d) :
    HasSchmidtRankLE 2 (haUVector d γ i) := by
  change HasSchmidtRankLE 2 (fun p : Fin d × Fin d ↦
    (γ / Real.sqrt d : ℝ) * haTensorBasis (haCyclicSucc i) i p +
      ((Real.sqrt d * γ)⁻¹ : ℝ) * haTensorBasis i (haCyclicSucc i) p)
  exact hasSchmidtRankLE_two_tensorBasis_add (d := d)
    ((γ / Real.sqrt d : ℝ) : ℂ) ((((Real.sqrt d * γ)⁻¹ : ℝ) : ℂ))
    (haCyclicSucc i) i i (haCyclicSucc i)

private theorem haVVector_hasSchmidtRankLE_two (i : Fin d) :
    HasSchmidtRankLE 2 (haVVector d i) := by
  change HasSchmidtRankLE 2 (fun p : Fin d × Fin d ↦
    Real.sqrt (((d : ℝ) - 1) / d) *
      (haTensorBasis (haCyclicSucc i) i p + haTensorBasis i (haCyclicSucc i) p))
  simpa only [mul_add] using
    (hasSchmidtRankLE_two_tensorBasis_add (d := d)
      ((Real.sqrt (((d : ℝ) - 1) / d) : ℝ) : ℂ)
      ((Real.sqrt (((d : ℝ) - 1) / d) : ℝ) : ℂ)
      (haCyclicSucc i) i i (haCyclicSucc i))

private theorem haAlphaVector_hasSchmidtRankLE_two (i : Fin d) :
    HasSchmidtRankLE 2 (haAlphaVector i) := by
  simpa only [haAlphaVector, one_mul, zero_mul, add_zero] using
    (hasSchmidtRankLE_two_tensorBasis_add (d := d) 1 0 i i i i)

private theorem haBetaVector_hasSchmidtRankLE_two (i j : Fin d) :
    HasSchmidtRankLE 2 (haBetaVector i j) := by
  change HasSchmidtRankLE 2 (fun p : Fin d × Fin d ↦
    haTensorBasis j i p + haTensorBasis i j p)
  simpa only [one_mul] using
    (hasSchmidtRankLE_two_tensorBasis_add (d := d) 1 1 j i i j)

private theorem haBetaVector_ne_zero_iff (i j a b : Fin d) :
    haBetaVector i j (a, b) ≠ 0 ↔ (a = j ∧ b = i) ∨ (a = i ∧ b = j) := by
  simp only [haBetaVector, haTensorBasis]
  split_ifs <;> simp_all

private theorem haBetaVector_eq_zero_of_not_support (i j a b : Fin d)
    (h : ¬((a = j ∧ b = i) ∨ (a = i ∧ b = j))) :
    haBetaVector i j (a, b) = 0 := by
  by_contra hn
  exact h ((haBetaVector_ne_zero_iff i j a b).mp hn)

private theorem haBetaVector_apply_swap (i j a b : Fin d) :
    haBetaVector i j (b, a) = haBetaVector i j (a, b) := by
  simp only [haBetaVector, haTensorBasis]
  split_ifs <;> simp_all <;> ring

/-- The zero-based translation of Ha's two displayed beta ranges:
`3 ≤ j ≤ d-1` when the first source index is `1`, and
`2 ≤ i ≤ d-2`, `i+2 ≤ j ≤ d` otherwise.

Equivalently, these are the naturally ordered non-neighbouring pairs, excluding
the cyclic neighbouring pair `(0, d-1)`. -/
def haBetaPairs (d : ℕ) : Finset (Fin d × Fin d) :=
  Finset.univ.filter fun p ↦
    p.1.1 + 1 < p.2.1 ∧ ¬ (p.1.1 = 0 ∧ p.2.1 + 1 = d)

/-- The beta ranges are exactly the unordered distinct pairs which are not
cyclic neighbours. -/
private theorem mem_haBetaPairs_or_swap_iff (hd : 3 ≤ d) (a b : Fin d)
    (hab : a ≠ b) :
    ((a, b) ∈ haBetaPairs d ∨ (b, a) ∈ haBetaPairs d) ↔
      a ≠ haCyclicSucc b ∧ b ≠ haCyclicSucc a := by
  have hsucc_lt (y : Fin d) (hy : y.val + 1 < d) :
      (haCyclicSucc y).val = y.val + 1 := by
    rw [haCyclicSucc, Fin.val_add, Fin.val_one',
      Nat.mod_eq_of_lt (by omega : 1 < d)]
    exact Nat.mod_eq_of_lt hy
  have hsucc_eq (y : Fin d) (hy : y.val + 1 = d) :
      (haCyclicSucc y).val = 0 := by
    rw [haCyclicSucc, Fin.val_add, Fin.val_one',
      Nat.mod_eq_of_lt (by omega : 1 < d), hy, Nat.mod_self]
  simp only [haBetaPairs, Finset.mem_filter, Finset.mem_univ, true_and]
  have ha := a.isLt
  have hb := b.isLt
  have hne : a.val ≠ b.val := fun h ↦ hab (Fin.ext h)
  constructor
  · rintro (h | h)
    · constructor
      · intro heq
        have hv := congrArg Fin.val heq
        rcases Nat.lt_or_eq_of_le (by omega : b.val + 1 ≤ d) with hblt | hbeq
        · rw [hsucc_lt b hblt] at hv
          omega
        · rw [hsucc_eq b hbeq] at hv
          omega
      · intro heq
        have hv := congrArg Fin.val heq
        have halt : a.val + 1 < d := by omega
        rw [hsucc_lt a halt] at hv
        omega
    · constructor
      · intro heq
        have hv := congrArg Fin.val heq
        have hblt : b.val + 1 < d := by omega
        rw [hsucc_lt b hblt] at hv
        omega
      · intro heq
        have hv := congrArg Fin.val heq
        rcases Nat.lt_or_eq_of_le (by omega : a.val + 1 ≤ d) with halt | haeq
        · rw [hsucc_lt a halt] at hv
          omega
        · rw [hsucc_eq a haeq] at hv
          omega
  · rintro ⟨habn, hban⟩
    by_cases hlt : a.val < b.val
    · left
      constructor
      · have hale : a.val + 1 ≤ b.val := by omega
        exact lt_of_le_of_ne hale fun heq ↦ hban <| by
          apply Fin.ext
          rw [hsucc_lt a (by omega)]
          omega
      · rintro ⟨ha0, hbtop⟩
        apply habn
        apply Fin.ext
        rw [hsucc_eq b hbtop]
        omega
    · right
      have hlt' : b.val < a.val := by omega
      constructor
      · have hble : b.val + 1 ≤ a.val := by omega
        exact lt_of_le_of_ne hble fun heq ↦ habn <| by
          apply Fin.ext
          rw [hsucc_lt b (by omega)]
          omega
      · rintro ⟨hb0, hatop⟩
        apply hban
        apply Fin.ext
        rw [hsucc_eq a hatop]
        omega

/-- A rank-one projector in Ha's displayed decomposition. -/
noncomputable def haVectorProjector (z : Fin d × Fin d → ℂ) :
    Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ :=
  vecMulVec z (star z)

private noncomputable def haCyclicProjectorSum (d : ℕ) [NeZero d] (γ : ℝ) :
    Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ :=
  ∑ i : Fin d,
    (haVectorProjector (haUVector d γ i) + haVectorProjector (haVVector d i))

private theorem haCyclicProjectorSum_apply_eq_single_forward (hd : 3 ≤ d)
    (γ : ℝ) (i : Fin d) (q : Fin d × Fin d) :
    haCyclicProjectorSum d γ (haCyclicSucc i, i) q =
      (haVectorProjector (haUVector d γ i) +
        haVectorProjector (haVVector d i)) (haCyclicSucc i, i) q := by
  classical
  rw [haCyclicProjectorSum, sum_apply, Finset.sum_eq_single i]
  · intro j _ hji
    have hforward : (haCyclicSucc i, i) ≠ (haCyclicSucc j, j) := by
      intro h
      exact hji (congrArg Prod.snd h).symm
    have hreverse : (haCyclicSucc i, i) ≠ (j, haCyclicSucc j) := by
      intro h
      have hj : j = haCyclicSucc i := (congrArg Prod.fst h).symm
      have hi : i = haCyclicSucc j := congrArg Prod.snd h
      apply haCyclicSucc_twice_ne hd i
      rw [← hj, ← hi]
    have hu := haUVector_eq_zero_of_not_support γ j (haCyclicSucc i, i)
      ⟨hforward, hreverse⟩
    have hv := haVVector_eq_zero_of_not_support j (haCyclicSucc i, i)
      ⟨hforward, hreverse⟩
    simp [add_apply, haVectorProjector, vecMulVec_apply, hu, hv]
  · simp

private theorem haCyclicProjectorSum_apply_eq_single_reverse (hd : 3 ≤ d)
    (γ : ℝ) (i : Fin d) (q : Fin d × Fin d) :
    haCyclicProjectorSum d γ (i, haCyclicSucc i) q =
      (haVectorProjector (haUVector d γ i) +
        haVectorProjector (haVVector d i)) (i, haCyclicSucc i) q := by
  classical
  rw [haCyclicProjectorSum, sum_apply, Finset.sum_eq_single i]
  · intro j _ hji
    have hforward : (i, haCyclicSucc i) ≠ (haCyclicSucc j, j) := by
      intro h
      have hi : i = haCyclicSucc j := congrArg Prod.fst h
      have hj : j = haCyclicSucc i := (congrArg Prod.snd h).symm
      apply haCyclicSucc_twice_ne hd i
      rw [← hj, ← hi]
    have hreverse : (i, haCyclicSucc i) ≠ (j, haCyclicSucc j) := by
      intro h
      exact hji (congrArg Prod.fst h).symm
    have hu := haUVector_eq_zero_of_not_support γ j (i, haCyclicSucc i)
      ⟨hforward, hreverse⟩
    have hv := haVVector_eq_zero_of_not_support j (i, haCyclicSucc i)
      ⟨hforward, hreverse⟩
    simp [add_apply, haVectorProjector, vecMulVec_apply, hu, hv]
  · simp

private theorem haCyclicProjectorSum_apply_forward_diag (hd : 3 ≤ d)
    (γ : ℝ) (i : Fin d) :
    haCyclicProjectorSum d γ (haCyclicSucc i, i) (haCyclicSucc i, i) =
      ((d : ℝ)⁻¹ : ℝ) * ((γ : ℂ) ^ 2 + (d - 1 : ℕ)) := by
  rw [haCyclicProjectorSum_apply_eq_single_forward hd]
  have hdr : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have hdpos : 0 < (d : ℝ) := by nlinarith
  have hdm1 : 0 ≤ (d : ℝ) - 1 := by nlinarith
  have hspos : 0 < Real.sqrt d := Real.sqrt_pos.2 hdpos
  have hdsq : (Real.sqrt d) ^ 2 = (d : ℝ) := Real.sq_sqrt hdpos.le
  have hm1sq : (Real.sqrt ((d : ℝ) - 1)) ^ 2 = (d : ℝ) - 1 :=
    Real.sq_sqrt hdm1
  have hne := haCyclicSucc_ne hd i
  simp [add_apply, haVectorProjector, vecMulVec_apply, Pi.star_apply,
    haUVector, haVVector, haTensorBasis, hne]
  apply Complex.ext <;> simp [pow_two]
  rw [Nat.cast_sub (by omega : 1 ≤ d), Nat.cast_one]
  field_simp
  ring_nf at hdsq hm1sq ⊢
  nlinarith

private theorem haCyclicProjectorSum_apply_reverse_diag (hd : 3 ≤ d)
    {γ : ℝ} (hγ : 0 < γ) (i : Fin d) :
    haCyclicProjectorSum d γ (i, haCyclicSucc i) (i, haCyclicSucc i) =
      ((d : ℝ)⁻¹ : ℝ) * (((γ : ℂ)⁻¹) ^ 2 + (d - 1 : ℕ)) := by
  rw [haCyclicProjectorSum_apply_eq_single_reverse hd]
  have hdr : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have hdpos : 0 < (d : ℝ) := by nlinarith
  have hspos : 0 < Real.sqrt d := Real.sqrt_pos.2 hdpos
  have hdsq : (Real.sqrt d) ^ 2 = (d : ℝ) := Real.sq_sqrt hdpos.le
  have hdsq4 : (Real.sqrt d) ^ 4 = (d : ℝ) ^ 2 := by
    rw [show (Real.sqrt d) ^ 4 = ((Real.sqrt d) ^ 2) ^ 2 by ring, hdsq]
  have hm1sq : (Real.sqrt (-1 + (d : ℝ))) ^ 2 = -1 + (d : ℝ) := by
    convert Real.sq_sqrt (show 0 ≤ -1 + (d : ℝ) by nlinarith)
  have hne := haCyclicSucc_ne hd i
  simp [add_apply, haVectorProjector, vecMulVec_apply, Pi.star_apply,
    haUVector, haVVector, haTensorBasis, hne]
  apply Complex.ext <;> simp [pow_two]
  rw [Nat.cast_sub (by omega : 1 ≤ d), Nat.cast_one]
  field_simp
  ring_nf
  rw [hdsq4, hm1sq, hdsq]
  ring

private theorem haCyclicProjectorSum_apply_forward_reverse (hd : 3 ≤ d)
    {γ : ℝ} (hγ : 0 < γ) (i : Fin d) :
    haCyclicProjectorSum d γ (haCyclicSucc i, i) (i, haCyclicSucc i) = 1 := by
  rw [haCyclicProjectorSum_apply_eq_single_forward hd]
  have hdr : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have hdpos : 0 < (d : ℝ) := by nlinarith
  have hdm1 : 0 ≤ (d : ℝ) - 1 := by nlinarith
  have hspos : 0 < Real.sqrt d := Real.sqrt_pos.2 hdpos
  have hdsq : (Real.sqrt d) ^ 2 = (d : ℝ) := Real.sq_sqrt hdpos.le
  have hm1sq : (Real.sqrt ((d : ℝ) - 1)) ^ 2 = (d : ℝ) - 1 :=
    Real.sq_sqrt hdm1
  have hne := haCyclicSucc_ne hd i
  simp [add_apply, haVectorProjector, vecMulVec_apply, Pi.star_apply,
    haUVector, haVVector, haTensorBasis, hne]
  apply Complex.ext <;> simp
  field_simp
  ring_nf at hdsq hm1sq ⊢
  nlinarith

private theorem haCyclicProjectorSum_apply_reverse_forward (hd : 3 ≤ d)
    {γ : ℝ} (hγ : 0 < γ) (i : Fin d) :
    haCyclicProjectorSum d γ (i, haCyclicSucc i) (haCyclicSucc i, i) = 1 := by
  rw [haCyclicProjectorSum_apply_eq_single_reverse hd]
  have hdr : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have hdpos : 0 < (d : ℝ) := by nlinarith
  have hdm1 : 0 ≤ (d : ℝ) - 1 := by nlinarith
  have hspos : 0 < Real.sqrt d := Real.sqrt_pos.2 hdpos
  have hdsq : (Real.sqrt d) ^ 2 = (d : ℝ) := Real.sq_sqrt hdpos.le
  have hm1sq : (Real.sqrt ((d : ℝ) - 1)) ^ 2 = (d : ℝ) - 1 :=
    Real.sq_sqrt hdm1
  have hne := haCyclicSucc_ne hd i
  simp [add_apply, haVectorProjector, vecMulVec_apply, Pi.star_apply,
    haUVector, haVVector, haTensorBasis, hne]
  apply Complex.ext <;> simp
  field_simp
  ring_nf at hdsq hm1sq ⊢
  nlinarith

private theorem haCyclicProjectorSum_apply_eq_zero (γ : ℝ)
    (p q : Fin d × Fin d)
    (h : ∀ i : Fin d, p ≠ (haCyclicSucc i, i) ∧ p ≠ (i, haCyclicSucc i)) :
    haCyclicProjectorSum d γ p q = 0 := by
  classical
  rw [haCyclicProjectorSum, sum_apply]
  apply Finset.sum_eq_zero
  intro i _
  have hu := haUVector_eq_zero_of_not_support γ i p (h i)
  have hv := haVVector_eq_zero_of_not_support i p (h i)
  simp [add_apply, haVectorProjector, vecMulVec_apply, hu, hv]

private theorem haCyclicProjectorSum_apply_forward_eq_zero (hd : 3 ≤ d)
    (γ : ℝ) (i : Fin d) (q : Fin d × Fin d)
    (hq : q ≠ (haCyclicSucc i, i) ∧ q ≠ (i, haCyclicSucc i)) :
    haCyclicProjectorSum d γ (haCyclicSucc i, i) q = 0 := by
  rw [haCyclicProjectorSum_apply_eq_single_forward hd]
  have hu := haUVector_eq_zero_of_not_support γ i q hq
  have hv := haVVector_eq_zero_of_not_support i q hq
  simp [add_apply, haVectorProjector, vecMulVec_apply, hu, hv]

private theorem haCyclicProjectorSum_apply_reverse_eq_zero (hd : 3 ≤ d)
    (γ : ℝ) (i : Fin d) (q : Fin d × Fin d)
    (hq : q ≠ (haCyclicSucc i, i) ∧ q ≠ (i, haCyclicSucc i)) :
    haCyclicProjectorSum d γ (i, haCyclicSucc i) q = 0 := by
  rw [haCyclicProjectorSum_apply_eq_single_reverse hd]
  have hu := haUVector_eq_zero_of_not_support γ i q hq
  have hv := haVVector_eq_zero_of_not_support i q hq
  simp [add_apply, haVectorProjector, vecMulVec_apply, hu, hv]

private noncomputable def haAlphaProjectorSum (d : ℕ) :
    Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ :=
  ∑ i : Fin d, haVectorProjector (haAlphaVector i)

private theorem haAlphaProjectorSum_apply (p q : Fin d × Fin d) :
    haAlphaProjectorSum d p q = if p = q ∧ p.1 = p.2 then 1 else 0 := by
  classical
  rcases p with ⟨a, b⟩
  rcases q with ⟨c, e⟩
  simp [haAlphaProjectorSum, haVectorProjector, haAlphaVector, haTensorBasis,
    sum_apply, vecMulVec_apply, Pi.star_apply]
  aesop

/-- The beta-projector part of Ha's displayed decomposition. -/
private noncomputable def haBetaProjectorSum (d : ℕ) :
    Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ :=
  ∑ p ∈ haBetaPairs d, haVectorProjector (haBetaVector p.1 p.2)

private theorem haBetaProjectorSum_apply_of_mem (a b : Fin d)
    (habmem : (a, b) ∈ haBetaPairs d) (q : Fin d × Fin d)
    (hq : q = (a, b) ∨ q = (b, a)) :
    haBetaProjectorSum d (a, b) q = 1 := by
  classical
  have hm : a.val + 1 < b.val ∧ ¬(a.val = 0 ∧ b.val + 1 = d) := by
    simpa only [haBetaPairs, Finset.mem_filter, Finset.mem_univ, true_and] using habmem
  have habord : a.val < b.val := by omega
  have hab : a ≠ b := by intro h; subst b; omega
  rcases hq with rfl | rfl
  · rw [haBetaProjectorSum, sum_apply, Finset.sum_eq_single (a, b)]
    · simp [haVectorProjector, haBetaVector, haTensorBasis, vecMulVec_apply,
        Pi.star_apply, hab]
    · intro p hp hne
      have hpm : p.1.val + 1 < p.2.val ∧
          ¬(p.1.val = 0 ∧ p.2.val + 1 = d) := by
        simpa only [haBetaPairs, Finset.mem_filter, Finset.mem_univ, true_and] using hp
      have hpord : p.1.val < p.2.val := by omega
      have hnevals : p.1.val ≠ a.val ∨ p.2.val ≠ b.val := by
        by_contra h
        push Not at h
        apply hne
        exact Prod.ext (Fin.ext h.1) (Fin.ext h.2)
      have hv : haBetaVector p.1 p.2 (a, b) = 0 := by
        apply haBetaVector_eq_zero_of_not_support
        rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
        · omega
        · exact hne (Prod.ext rfl rfl)
      simp [haVectorProjector, vecMulVec_apply, hv]
    · exact fun h ↦ (h habmem).elim
  · rw [haBetaProjectorSum, sum_apply, Finset.sum_eq_single (a, b)]
    · simp [haVectorProjector, haBetaVector, haTensorBasis, vecMulVec_apply,
        Pi.star_apply, hab]
    · intro p hp hne
      have hpm : p.1.val + 1 < p.2.val ∧
          ¬(p.1.val = 0 ∧ p.2.val + 1 = d) := by
        simpa only [haBetaPairs, Finset.mem_filter, Finset.mem_univ, true_and] using hp
      have hpord : p.1.val < p.2.val := by omega
      have hnevals : p.1.val ≠ a.val ∨ p.2.val ≠ b.val := by
        by_contra h
        push Not at h
        apply hne
        exact Prod.ext (Fin.ext h.1) (Fin.ext h.2)
      have hv : haBetaVector p.1 p.2 (a, b) = 0 := by
        apply haBetaVector_eq_zero_of_not_support
        rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
        · omega
        · exact hne (Prod.ext rfl rfl)
      simp [haVectorProjector, vecMulVec_apply, hv]
    · exact fun h ↦ (h habmem).elim

private theorem haBetaProjectorSum_apply_eq_zero (a b : Fin d)
    (hnone : (a, b) ∉ haBetaPairs d ∧ (b, a) ∉ haBetaPairs d)
    (q : Fin d × Fin d) : haBetaProjectorSum d (a, b) q = 0 := by
  classical
  rw [haBetaProjectorSum, sum_apply]
  apply Finset.sum_eq_zero
  intro p hp
  have hv : haBetaVector p.1 p.2 (a, b) = 0 := by
    apply haBetaVector_eq_zero_of_not_support
    rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · exact hnone.2 hp
    · exact hnone.1 hp
  simp [haVectorProjector, vecMulVec_apply, hv]

private theorem haBetaProjectorSum_apply_eq_zero_of_right (a b : Fin d)
    (q : Fin d × Fin d) (hq : q ≠ (a, b) ∧ q ≠ (b, a)) :
    haBetaProjectorSum d (a, b) q = 0 := by
  classical
  rw [haBetaProjectorSum, sum_apply]
  apply Finset.sum_eq_zero
  intro p _
  by_cases hpzero : haBetaVector p.1 p.2 (a, b) = 0
  · simp [haVectorProjector, vecMulVec_apply, hpzero]
  · have hp := (haBetaVector_ne_zero_iff p.1 p.2 a b).mp hpzero
    have hqzero : haBetaVector p.1 p.2 q = 0 := by
      rcases q with ⟨c, e⟩
      apply haBetaVector_eq_zero_of_not_support
      intro hqs
      rcases hp with hp | hp <;> rcases hqs with hqs | hqs
      · apply hq.1
        exact Prod.ext (hqs.1.trans hp.1.symm) (hqs.2.trans hp.2.symm)
      · apply hq.2
        exact Prod.ext (hqs.1.trans hp.2.symm) (hqs.2.trans hp.1.symm)
      · apply hq.2
        exact Prod.ext (hqs.1.trans hp.2.symm) (hqs.2.trans hp.1.symm)
      · apply hq.1
        exact Prod.ext (hqs.1.trans hp.1.symm) (hqs.2.trans hp.2.symm)
    simp [haVectorProjector, vecMulVec_apply, hqzero]

private theorem haBetaProjectorSum_apply_swap_left (a b : Fin d)
    (q : Fin d × Fin d) :
    haBetaProjectorSum d (b, a) q = haBetaProjectorSum d (a, b) q := by
  classical
  simp only [haBetaProjectorSum, sum_apply]
  apply Finset.sum_congr rfl
  intro p _
  simp [haVectorProjector, vecMulVec_apply, haBetaVector_apply_swap]

/-- The right-hand side of Ha's displayed identity on p. 595. -/
noncomputable def haBlockTransposeDecomposition (d : ℕ) [NeZero d] (γ : ℝ) :
    Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ :=
  (∑ i : Fin d, (
      haVectorProjector (haUVector d γ i) +
      haVectorProjector (haVVector d i) +
      haVectorProjector (haAlphaVector i))) +
    ∑ p ∈ haBetaPairs d, haVectorProjector (haBetaVector p.1 p.2)

private theorem haBlockTransposeDecomposition_eq_components (γ : ℝ) :
    haBlockTransposeDecomposition d γ =
      haCyclicProjectorSum d γ + haAlphaProjectorSum d + haBetaProjectorSum d := by
  ext p q
  simp only [haBlockTransposeDecomposition, haCyclicProjectorSum, haAlphaProjectorSum,
    haBetaProjectorSum, sum_apply, add_apply]
  rw [← Finset.sum_add_distrib]

/-- The entry formula common to Ha's root average and his displayed projector
decomposition. -/
private noncomputable def haBlockTransposeEntry (d : ℕ) [NeZero d] (γ : ℝ)
    (p q : Fin d × Fin d) : ℂ :=
  if p = q then
    ((d : ℝ)⁻¹ : ℝ) *
      (haCyclicWeight d γ p.2 p.1 * star (haCyclicWeight d γ p.2 p.1) +
        (d - 1 : ℕ))
  else if p.1 = q.2 ∧ p.2 = q.1 then 1 else 0

/-- Entrywise evaluation of the block transpose of Ha's root average. -/
private theorem partialTransposeRight_haAGamma_apply (hd : 3 ≤ d) (γ : ℝ)
    (p q : Fin d × Fin d) :
    partialTransposeRight (haAGamma d γ) p q = haBlockTransposeEntry d γ p q := by
  classical
  rcases p with ⟨a, b⟩
  rcases q with ⟨c, e⟩
  rw [partialTransposeRight_apply, haAGamma]
  simp only [smul_apply, sum_apply]
  rw [RCLike.real_smul_eq_coe_smul (K := ℂ) (E := ℂ)]
  simp only [smul_eq_mul]
  simp_rw [haArGamma_apply]
  by_cases hpq : (a, b) = (c, e)
  · have hac : a = c := congrArg Prod.fst hpq
    have hbe : b = e := congrArg Prod.snd hpq
    subst c
    subst e
    simp only [and_self, true_or, if_pos, mul_one]
    rw [sum_haTwoSimpleWeight_self hd]
    simp [haBlockTransposeEntry]
  · by_cases hswap : a = e ∧ b = c
    · rcases hswap with ⟨rfl, rfl⟩
      have hab : a ≠ b := by
        intro h
        apply hpq
        simpa [h]
      have hdiag (r : Fin d) :
          haTwoSimpleWeight d γ r (a, a) *
              star (haTwoSimpleWeight d γ r (b, b)) = 1 := by
        rw [haTwoSimpleWeight_diag hd, haTwoSimpleWeight_diag hd]
        simp
      simp_rw [hdiag]
      simp [haBlockTransposeEntry, hpq, hab]
    · have hpairs : ¬((a = c ∧ b = e) ∨ (a = e ∧ b = c)) := by
        intro h
        rcases h with h | h
        · apply hpq
          exact Prod.ext h.1 h.2
        · exact hswap h
      simp_rw [if_neg hpairs, mul_zero]
      simp [haBlockTransposeEntry, hpq, hswap]

private theorem haBlockTransposeDecomposition_apply (hd : 3 ≤ d) {γ : ℝ}
    (hγ : 0 < γ) (p q : Fin d × Fin d) :
    haBlockTransposeDecomposition d γ p q = haBlockTransposeEntry d γ p q := by
  classical
  rcases p with ⟨a, b⟩
  rcases q with ⟨c, e⟩
  rw [haBlockTransposeDecomposition_eq_components, add_apply, add_apply]
  by_cases hpq : (a, b) = (c, e)
  · have hac : a = c := congrArg Prod.fst hpq
    have hbe : b = e := congrArg Prod.snd hpq
    subst c
    subst e
    by_cases hab : a = b
    · subst b
      have hcyc : haCyclicProjectorSum d γ (a, a) (a, a) = 0 := by
        apply haCyclicProjectorSum_apply_eq_zero
        intro i
        constructor
        · intro h
          apply haCyclicSucc_ne hd i
          exact (congrArg Prod.fst h).symm.trans (congrArg Prod.snd h)
        · intro h
          apply haCyclicSucc_ne hd i
          exact (congrArg Prod.snd h).symm.trans (congrArg Prod.fst h)
      have hnone : (a, a) ∉ haBetaPairs d ∧ (a, a) ∉ haBetaPairs d := by
        simp [haBetaPairs]
      rw [hcyc, haAlphaProjectorSum_apply,
        haBetaProjectorSum_apply_eq_zero a a hnone]
      have hfix : a ≠ haCyclicSucc a := (haCyclicSucc_ne hd a).symm
      rw [haBlockTransposeEntry, if_pos rfl, haCyclicWeight_mul_star hd γ a a,
        if_neg hfix, if_neg hfix]
      rw [Nat.cast_sub (by omega : 1 ≤ d), Nat.cast_one]
      norm_num
    · by_cases hforward : a = haCyclicSucc b
      · have hnotmem : ¬((a, b) ∈ haBetaPairs d ∨ (b, a) ∈ haBetaPairs d) := by
          intro hm
          exact (mem_haBetaPairs_or_swap_iff hd a b hab).mp hm |>.1 hforward
        have hnone := not_or.mp hnotmem
        rw [show haCyclicProjectorSum d γ (a, b) (a, b) =
            ((d : ℝ)⁻¹ : ℝ) * ((γ : ℂ) ^ 2 + (d - 1 : ℕ)) by
              subst a
              exact haCyclicProjectorSum_apply_forward_diag hd γ b,
          haAlphaProjectorSum_apply,
          haBetaProjectorSum_apply_eq_zero a b hnone]
        rw [haBlockTransposeEntry, if_pos rfl, haCyclicWeight_mul_star hd γ a b]
        simp [hforward, hab, haCyclicSucc_ne hd b]
      · by_cases hreverse : b = haCyclicSucc a
        · have hnotmem :
              ¬((a, b) ∈ haBetaPairs d ∨ (b, a) ∈ haBetaPairs d) := by
            intro hm
            exact (mem_haBetaPairs_or_swap_iff hd a b hab).mp hm |>.2 hreverse
          have hnone := not_or.mp hnotmem
          rw [show haCyclicProjectorSum d γ (a, b) (a, b) =
              ((d : ℝ)⁻¹ : ℝ) *
                (((γ : ℂ)⁻¹) ^ 2 + (d - 1 : ℕ)) by
                subst b
                exact haCyclicProjectorSum_apply_reverse_diag hd hγ a,
            haAlphaProjectorSum_apply,
            haBetaProjectorSum_apply_eq_zero a b hnone]
          rw [haBlockTransposeEntry, if_pos rfl, haCyclicWeight_mul_star hd γ a b]
          have hfix : a ≠ haCyclicSucc a := (haCyclicSucc_ne hd a).symm
          have htwice : a ≠ haCyclicSucc (haCyclicSucc a) :=
            (haCyclicSucc_twice_ne hd a).symm
          simp [hforward, hreverse, hab, hfix, htwice]
        · have hcyc : haCyclicProjectorSum d γ (a, b) (a, b) = 0 := by
            apply haCyclicProjectorSum_apply_eq_zero
            intro i
            constructor
            · intro h
              apply hforward
              exact (congrArg Prod.fst h).trans
                (congrArg haCyclicSucc (congrArg Prod.snd h).symm)
            · intro h
              apply hreverse
              exact (congrArg Prod.snd h).trans
                (congrArg haCyclicSucc (congrArg Prod.fst h).symm)
          have hmem := (mem_haBetaPairs_or_swap_iff hd a b hab).mpr
            ⟨hforward, hreverse⟩
          rcases hmem with habmem | hbamem
          · rw [hcyc, haAlphaProjectorSum_apply,
              haBetaProjectorSum_apply_of_mem a b habmem (a, b) (Or.inl rfl)]
            rw [haBlockTransposeEntry, if_pos rfl, haCyclicWeight_mul_star hd γ a b,
              if_neg hforward, if_neg hreverse]
            rw [Nat.cast_sub (by omega : 1 ≤ d), Nat.cast_one]
            norm_num
            exact hab
          · rw [hcyc, haAlphaProjectorSum_apply,
              haBetaProjectorSum_apply_swap_left b a,
              haBetaProjectorSum_apply_of_mem b a hbamem (a, b) (Or.inr rfl)]
            rw [haBlockTransposeEntry, if_pos rfl, haCyclicWeight_mul_star hd γ a b,
              if_neg hforward, if_neg hreverse]
            rw [Nat.cast_sub (by omega : 1 ≤ d), Nat.cast_one]
            norm_num
            exact hab
  · by_cases hswap : a = e ∧ b = c
    · rcases hswap with ⟨rfl, rfl⟩
      have hab : a ≠ b := by
        intro h
        apply hpq
        simpa [h]
      by_cases hforward : a = haCyclicSucc b
      · have hnotmem : ¬((a, b) ∈ haBetaPairs d ∨ (b, a) ∈ haBetaPairs d) := by
          intro hm
          exact (mem_haBetaPairs_or_swap_iff hd a b hab).mp hm |>.1 hforward
        have hnone := not_or.mp hnotmem
        rw [show haCyclicProjectorSum d γ (a, b) (b, a) = 1 by
              subst a
              exact haCyclicProjectorSum_apply_forward_reverse hd hγ b,
          haAlphaProjectorSum_apply,
          haBetaProjectorSum_apply_eq_zero a b hnone]
        simp [haBlockTransposeEntry, hpq, hab]
      · by_cases hreverse : b = haCyclicSucc a
        · have hnotmem :
              ¬((a, b) ∈ haBetaPairs d ∨ (b, a) ∈ haBetaPairs d) := by
            intro hm
            exact (mem_haBetaPairs_or_swap_iff hd a b hab).mp hm |>.2 hreverse
          have hnone := not_or.mp hnotmem
          rw [show haCyclicProjectorSum d γ (a, b) (b, a) = 1 by
                subst b
                exact haCyclicProjectorSum_apply_reverse_forward hd hγ a,
            haAlphaProjectorSum_apply,
            haBetaProjectorSum_apply_eq_zero a b hnone]
          simp [haBlockTransposeEntry, hpq, hab]
        · have hcyc : haCyclicProjectorSum d γ (a, b) (b, a) = 0 := by
            apply haCyclicProjectorSum_apply_eq_zero
            intro i
            constructor
            · intro h
              apply hforward
              exact (congrArg Prod.fst h).trans
                (congrArg haCyclicSucc (congrArg Prod.snd h).symm)
            · intro h
              apply hreverse
              exact (congrArg Prod.snd h).trans
                (congrArg haCyclicSucc (congrArg Prod.fst h).symm)
          have hmem := (mem_haBetaPairs_or_swap_iff hd a b hab).mpr
            ⟨hforward, hreverse⟩
          rcases hmem with habmem | hbamem
          · rw [hcyc, haAlphaProjectorSum_apply,
              haBetaProjectorSum_apply_of_mem a b habmem (b, a) (Or.inr rfl)]
            simp [haBlockTransposeEntry, hpq, hab]
          · rw [hcyc, haAlphaProjectorSum_apply,
              haBetaProjectorSum_apply_swap_left b a,
              haBetaProjectorSum_apply_of_mem b a hbamem (b, a) (Or.inl rfl)]
            simp [haBlockTransposeEntry, hpq, hab]
    · by_cases hforward : a = haCyclicSucc b
      · have hq : (c, e) ≠ (haCyclicSucc b, b) ∧ (c, e) ≠ (b, haCyclicSucc b) := by
          constructor
          · intro h
            apply hpq
            subst a
            exact h.symm
          · intro h
            apply hswap
            exact ⟨hforward.trans (congrArg Prod.snd h).symm,
              (congrArg Prod.fst h).symm⟩
        rw [show haCyclicProjectorSum d γ (a, b) (c, e) = 0 by
              subst a
              exact haCyclicProjectorSum_apply_forward_eq_zero hd γ b (c, e) hq,
          haAlphaProjectorSum_apply,
          haBetaProjectorSum_apply_eq_zero_of_right a b (c, e) ⟨fun h ↦ hpq h.symm, fun h ↦ hswap
            ⟨(congrArg Prod.snd h).symm, (congrArg Prod.fst h).symm⟩⟩]
        simp [haBlockTransposeEntry, hpq, hswap]
      · by_cases hreverse : b = haCyclicSucc a
        · have hq : (c, e) ≠ (haCyclicSucc a, a) ∧ (c, e) ≠ (a, haCyclicSucc a) := by
            constructor
            · intro h
              apply hswap
              subst b
              exact ⟨(congrArg Prod.snd h).symm, (congrArg Prod.fst h).symm⟩
            · intro h
              apply hpq
              subst b
              exact h.symm
          rw [show haCyclicProjectorSum d γ (a, b) (c, e) = 0 by
                subst b
                exact haCyclicProjectorSum_apply_reverse_eq_zero hd γ a (c, e) hq,
            haAlphaProjectorSum_apply,
            haBetaProjectorSum_apply_eq_zero_of_right a b (c, e) ⟨fun h ↦ hpq h.symm, fun h ↦ hswap
              ⟨(congrArg Prod.snd h).symm, (congrArg Prod.fst h).symm⟩⟩]
          simp [haBlockTransposeEntry, hpq, hswap]
        · have hcyc : haCyclicProjectorSum d γ (a, b) (c, e) = 0 := by
            apply haCyclicProjectorSum_apply_eq_zero
            intro i
            constructor
            · intro h
              apply hforward
              exact (congrArg Prod.fst h).trans
                (congrArg haCyclicSucc (congrArg Prod.snd h).symm)
            · intro h
              apply hreverse
              exact (congrArg Prod.snd h).trans
                (congrArg haCyclicSucc (congrArg Prod.fst h).symm)
          rw [hcyc, haAlphaProjectorSum_apply,
            haBetaProjectorSum_apply_eq_zero_of_right a b (c, e) ⟨fun h ↦ hpq h.symm, fun h ↦ hswap
              ⟨(congrArg Prod.snd h).symm, (congrArg Prod.fst h).symm⟩⟩]
          simp [haBlockTransposeEntry, hpq, hswap]

/-- **Ha 1998, pp. 594--595, displayed block-transpose identity.**

Ha writes `A = Σ A_{p,q} ⊗ e_{p,q}` and transposes the displayed matrix
units `e_{p,q}`.  Thus his `Aᵀ` is the repository's second-factor partial
transpose `partialTransposeRight`, not `partialTransposeLeft`. -/
theorem partialTransposeRight_haAGamma_eq_haBlockTransposeDecomposition
    (hd : 3 ≤ d) {γ : ℝ} (hγ : 0 < γ) :
    partialTransposeRight (haAGamma d γ) = haBlockTransposeDecomposition d γ := by
  ext p q
  rw [partialTransposeRight_haAGamma_apply hd γ p q,
    haBlockTransposeDecomposition_apply hd hγ p q]

/-- Ha's displayed block-transpose sum consists of projectors onto vectors of
Schmidt rank at most two. -/
theorem haBlockTransposeDecomposition_hasSchmidtNumberLE_two (γ : ℝ) :
    HasSchmidtNumberLE 2 (haBlockTransposeDecomposition d γ) := by
  rw [haBlockTransposeDecomposition]
  apply HasSchmidtNumberLE.add
  · exact hasSchmidtNumberLE_sum Finset.univ fun i _ ↦
      ((hasSchmidtNumberLE_vecMulVec (haUVector_hasSchmidtRankLE_two γ i)).add
        (hasSchmidtNumberLE_vecMulVec (haVVector_hasSchmidtRankLE_two i))).add
          (hasSchmidtNumberLE_vecMulVec (haAlphaVector_hasSchmidtRankLE_two i))
  · exact hasSchmidtNumberLE_sum (haBetaPairs d) fun p _ ↦
      hasSchmidtNumberLE_vecMulVec (haBetaVector_hasSchmidtRankLE_two p.1 p.2)

/-- **Ha 1998, pp. 594--595, second `V₂` decomposition.**

The partial transpose on Ha's displayed block factor belongs to `V₂`.  In
the repository's tensor convention this is `partialTransposeRight`, and the
witnessing decomposition is exactly the displayed sum of the vectors `u_i`,
`v_i`, `α_i`, and `β_{i,j}` above.  No negative-pairing or indecomposability
statement is included here. -/
theorem partialTransposeRight_haAGamma_hasSchmidtNumberLE_two
    (hd : 3 ≤ d) {γ : ℝ} (hγ : 0 < γ) :
    HasSchmidtNumberLE 2 (partialTransposeRight (haAGamma d γ)) := by
  rw [partialTransposeRight_haAGamma_eq_haBlockTransposeDecomposition hd hγ]
  exact haBlockTransposeDecomposition_hasSchmidtNumberLE_two γ

end Matrix
