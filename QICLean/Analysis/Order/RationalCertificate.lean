/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Data.Rat.Cast.Order

/-!
# Kernel-checked rational Gram and LDL positivity certificates

A rational matrix `A : Matrix n n ℚ` that admits a weighted Gram factorization
`A = L * Matrix.diagonal d * Lᵀ` with rectangular factor `L : Matrix n k ℚ`
and nonnegative rational weights `d : k → ℚ` (allowing zero pivots `d r = 0`
and arbitrary rectangular shapes `k`) casts to a positive semidefinite matrix
over `ℂ`, over `ℝ`, and over any ordered star ring equipped with a
self-adjoint order-preserving ring homomorphism from `ℚ`.

This file provides:

* Generic algebraic soundness theorems for weighted Gram factorizations,
  positive rational rescaling, and permutation congruence.
* A data-only `RationalGramCertificate` structure together with decidable
  validity predicates and soundness theorems.
* Fast kernel-computable `Bool` checkers (`checkGramBool` and `checkLDLBool`)
  for `Fin`-indexed matrices that verify symmetry and upper-triangular
  reconstruction using `Fin.foldl`, enabling kernel-reduced `decide` proofs
  without `native_decide` or external oracles.
-/

open scoped BigOperators ComplexOrder Matrix

namespace QICLean

section GeneralAlgebra

/-- Entrywise expansion of a weighted Gram product `L * diagonal d * Lᴴ`. -/
theorem Matrix.mul_diagonal_mul_conjTranspose_apply
    {n k R : Type*} [Fintype k] [DecidableEq k] [Ring R] [StarRing R]
    (L : Matrix n k R) (d : k → R) (i j : n) :
    (L * Matrix.diagonal d * Lᴴ) i j = ∑ r : k, L i r * d r * star (L j r) := by
  rw [Matrix.mul_apply]
  simp [Matrix.mul_diagonal, Matrix.conjTranspose_apply]

/-- A weighted Gram product `L * diagonal d * Lᴴ` with nonnegative diagonal weights
is positive semidefinite over any ordered star ring. -/
theorem Matrix.posSemidef_mul_diagonal_mul_conjTranspose
    {n k R : Type*} [Finite n] [Fintype k] [DecidableEq k]
    [Ring R] [PartialOrder R] [StarRing R] [StarOrderedRing R]
    (L : Matrix n k R) (d : k → R) (hd : ∀ r : k, 0 ≤ d r) :
    (L * Matrix.diagonal d * Lᴴ).PosSemidef :=
  (Matrix.PosSemidef.diagonal hd).mul_mul_conjTranspose_same L

/-- Entrywise rational weighted Gram factorization implies positive semidefiniteness
after mapping along any self-adjoint order-preserving ring homomorphism `ℚ →+* R`. -/
theorem Matrix.posSemidef_map_of_ratWeightedGram
    {n k R : Type*} [Finite n] [Fintype k]
    [Ring R] [PartialOrder R] [StarRing R] [StarOrderedRing R]
    (f : ℚ →+* R) (hf_star : ∀ q : ℚ, star (f q) = f q)
    (hf_nonneg : ∀ q : ℚ, 0 ≤ q → 0 ≤ f q)
    {A : Matrix n n ℚ} (L : Matrix n k ℚ) (d : k → ℚ)
    (hd : ∀ r : k, 0 ≤ d r)
    (hfac : ∀ i j : n, A i j = ∑ r : k, L i r * d r * L j r) :
    (A.map f).PosSemidef := by
  classical
  have hEq : A.map f = (L.map f) * Matrix.diagonal (fun r ↦ f (d r)) * (L.map f)ᴴ := by
    ext i j
    rw [Matrix.map_apply, hfac i j, map_sum, Matrix.mul_diagonal_mul_conjTranspose_apply]
    refine Finset.sum_congr rfl fun r _ ↦ ?_
    simp [hf_star]
  rw [hEq]
  exact Matrix.posSemidef_mul_diagonal_mul_conjTranspose (L.map f) (fun r ↦ f (d r))
    (fun r ↦ hf_nonneg (d r) (hd r))

/-- Entrywise rational weighted Gram factorization `A i j = ∑ r, L i r * d r * L j r`
with `d r ≥ 0` certifies that the complex-cast matrix `A.map (Rat.cast : ℚ → ℂ)` is
positive semidefinite. Zero weights and rectangular factors `L : Matrix n k ℚ` are allowed. -/
theorem Matrix.posSemidef_map_ratCast_of_weightedGram
    {n k : Type*} [Finite n] [Fintype k]
    {A : Matrix n n ℚ} (L : Matrix n k ℚ) (d : k → ℚ)
    (hd : ∀ r : k, 0 ≤ d r)
    (hfac : ∀ i j : n, A i j = ∑ r : k, L i r * d r * L j r) :
    (A.map (Rat.cast : ℚ → ℂ)).PosSemidef := by
  have h := Matrix.posSemidef_map_of_ratWeightedGram
    (f := Rat.castHom ℂ)
    (hf_star := fun q ↦ by simp)
    (hf_nonneg := fun q hq ↦ by
      rw [Rat.coe_castHom, ← Complex.ofReal_ratCast, Complex.zero_le_real]
      exact_mod_cast hq)
    L d hd hfac
  simpa using h

/-- Matrix-equation form of rational weighted Gram soundness over `ℂ`:
`A = L * Matrix.diagonal d * Lᵀ` with `d r ≥ 0` implies `(A.map (Rat.cast : ℚ → ℂ)).PosSemidef`. -/
theorem Matrix.posSemidef_map_ratCast_of_eq_mul_diagonal_mul_transpose
    {n k : Type*} [Finite n] [Fintype k] [DecidableEq k]
    {A : Matrix n n ℚ} (L : Matrix n k ℚ) (d : k → ℚ)
    (hd : ∀ r : k, 0 ≤ d r)
    (hfac : A = L * Matrix.diagonal d * Lᵀ) :
    (A.map (Rat.cast : ℚ → ℂ)).PosSemidef := by
  refine Matrix.posSemidef_map_ratCast_of_weightedGram L d hd fun i j ↦ ?_
  rw [hfac, Matrix.mul_apply]
  simp [Matrix.mul_diagonal]

/-- Entrywise rational weighted Gram factorization certifies positive semidefiniteness
of the real-cast matrix `A.map (Rat.cast : ℚ → ℝ)`. -/
theorem Matrix.posSemidef_map_ratCast_real_of_weightedGram
    {n k : Type*} [Finite n] [Fintype k]
    {A : Matrix n n ℚ} (L : Matrix n k ℚ) (d : k → ℚ)
    (hd : ∀ r : k, 0 ≤ d r)
    (hfac : ∀ i j : n, A i j = ∑ r : k, L i r * d r * L j r) :
    (A.map (Rat.cast : ℚ → ℝ)).PosSemidef := by
  have h := Matrix.posSemidef_map_of_ratWeightedGram
    (f := Rat.castHom ℝ)
    (hf_star := fun q ↦ by simp)
    (hf_nonneg := fun q hq ↦ by
      rw [Rat.coe_castHom]
      exact_mod_cast hq)
    L d hd hfac
  simpa using h

/-- Positive rational scaling preserves complex positive semidefiniteness of a
rational-cast matrix. -/
theorem Matrix.posSemidef_map_ratCast_of_smul_pos
    {n : Type*} [Finite n] {A : Matrix n n ℚ} {c : ℚ} (hc : 0 < c)
    (h : ((c • A).map (Rat.cast : ℚ → ℂ)).PosSemidef) :
    (A.map (Rat.cast : ℚ → ℂ)).PosSemidef := by
  have hinv : (0 : ℂ) ≤ ((c⁻¹ : ℚ) : ℂ) := by
    rw [← Complex.ofReal_ratCast, Complex.zero_le_real]
    exact_mod_cast inv_nonneg.mpr hc.le
  have hscaled := h.smul hinv
  have hEq : ((c⁻¹ : ℚ) : ℂ) • ((c • A).map (Rat.cast : ℚ → ℂ)) =
      A.map (Rat.cast : ℚ → ℂ) := by
    ext i j
    simp only [Matrix.smul_apply, Matrix.map_apply, smul_eq_mul]
    norm_cast
    rw [← mul_assoc, inv_mul_cancel₀ hc.ne', one_mul]
  rwa [hEq] at hscaled

/-- Scaled rational weighted Gram soundness over `ℂ`: if `c > 0` and
`c * A i j = ∑ r, L i r * d r * L j r` with `d r ≥ 0`, then
`(A.map (Rat.cast : ℚ → ℂ)).PosSemidef`. -/
theorem Matrix.posSemidef_map_ratCast_of_scaled_weightedGram
    {n k : Type*} [Finite n] [Fintype k]
    {A : Matrix n n ℚ} {c : ℚ} (hc : 0 < c)
    (L : Matrix n k ℚ) (d : k → ℚ)
    (hd : ∀ r : k, 0 ≤ d r)
    (hfac : ∀ i j : n, c * A i j = ∑ r : k, L i r * d r * L j r) :
    (A.map (Rat.cast : ℚ → ℂ)).PosSemidef := by
  refine Matrix.posSemidef_map_ratCast_of_smul_pos hc ?_
  exact Matrix.posSemidef_map_ratCast_of_weightedGram L d hd (fun i j ↦ by
    simpa [Matrix.smul_apply] using hfac i j)

/-- Reindexing a rational matrix by a bijection preserves complex positive semidefiniteness. -/
theorem Matrix.posSemidef_map_ratCast_submatrix_equiv
    {m n : Type*} [Finite m] [Finite n] {A : Matrix n n ℚ} (e : m ≃ n)
    (hA : (A.map (Rat.cast : ℚ → ℂ)).PosSemidef) :
    ((A.submatrix e e).map (Rat.cast : ℚ → ℂ)).PosSemidef := by
  have hEq : (A.submatrix e e).map (Rat.cast : ℚ → ℂ) =
      (A.map (Rat.cast : ℚ → ℂ)).submatrix e e := by
    ext i j
    rfl
  rw [hEq]
  exact hA.submatrix e

end GeneralAlgebra

section CertificateStructure

/-- A data-only rational weighted Gram certificate `(L, d)` representing the
factorization `L * Matrix.diagonal d * Lᵀ`. Zero weights and rectangular
factors (`k ≠ n`) are allowed; no positivity proof is stored as data. -/
structure RationalGramCertificate (n k : Type*) where
  /-- The rectangular rational factor matrix `L`. -/
  factor : Matrix n k ℚ
  /-- The rational diagonal weights `d`. -/
  weights : k → ℚ

namespace RationalGramCertificate

/-- Entrywise rational reconstruction `(L * diagonal d * Lᵀ) i j`. -/
def reconstruct {n k : Type*} [Fintype k]
    (cert : RationalGramCertificate n k) : Matrix n n ℚ :=
  fun i j ↦ ∑ r : k, cert.factor i r * cert.weights r * cert.factor j r

/-- Decidable validity predicate: all diagonal weights are nonnegative and
the reconstructed matrix equals `A` entrywise. -/
def IsValid {n k : Type*} [Fintype k]
    (A : Matrix n n ℚ) (cert : RationalGramCertificate n k) : Prop :=
  (∀ r : k, 0 ≤ cert.weights r) ∧ ∀ i j : n, A i j = cert.reconstruct i j

instance instDecidableIsValid {n k : Type*} [Fintype n] [Fintype k]
    (A : Matrix n n ℚ) (cert : RationalGramCertificate n k) :
    Decidable (cert.IsValid A) := by
  unfold IsValid
  letI : ∀ i : n, Decidable (∀ j : n, A i j = cert.reconstruct i j) :=
    fun _ ↦ Fintype.decidableForallFintype
  exact instDecidableAnd

/-- A valid rational weighted Gram certificate implies complex positive semidefiniteness. -/
theorem IsValid.posSemidef_complex {n k : Type*} [Finite n] [Fintype k]
    {A : Matrix n n ℚ} {cert : RationalGramCertificate n k}
    (h : cert.IsValid A) :
    (A.map (Rat.cast : ℚ → ℂ)).PosSemidef :=
  Matrix.posSemidef_map_ratCast_of_weightedGram cert.factor cert.weights h.1 h.2

/-- A valid rational weighted Gram certificate implies real positive semidefiniteness. -/
theorem IsValid.posSemidef_real {n k : Type*} [Finite n] [Fintype k]
    {A : Matrix n n ℚ} {cert : RationalGramCertificate n k}
    (h : cert.IsValid A) :
    (A.map (Rat.cast : ℚ → ℝ)).PosSemidef :=
  Matrix.posSemidef_map_ratCast_real_of_weightedGram cert.factor cert.weights h.1 h.2

end RationalGramCertificate

end CertificateStructure

section FastFinCheckers

private lemma fin_foldl_add_eq_sum {m : ℕ} (f : Fin m → ℚ) (init : ℚ) :
    Fin.foldl m (fun acc r ↦ acc + f r) init = init + ∑ r : Fin m, f r := by
  induction m generalizing init with
  | zero => simp
  | succ m ih =>
    rw [Fin.foldl_succ, Fin.sum_univ_succ, ih]
    ring

private lemma fin_all_eq_true_iff {m : ℕ} (p : Fin m → Bool) :
    Fin.foldl m (fun acc i ↦ acc && p i) true = true ↔ ∀ i : Fin m, p i = true := by
  suffices ∀ (init : Bool),
      Fin.foldl m (fun acc i ↦ acc && p i) init = true ↔ init = true ∧ ∀ i : Fin m, p i = true by
    simpa using this true
  induction m with
  | zero =>
    intro init
    simp
  | succ m ih =>
    intro init
    rw [Fin.foldl_succ, ih (fun i ↦ p i.succ) (init && p 0)]
    simp only [Bool.and_eq_true, and_assoc, Fin.forall_fin_succ]

/-- Compute `∑ r : Fin k, L i r * d r * L j r` via `Fin.foldl`. -/
def gramEntry {m k : ℕ} (L : Matrix (Fin m) (Fin k) ℚ) (d : Fin k → ℚ)
    (i j : Fin m) : ℚ :=
  Fin.foldl k (fun acc r ↦ acc + L i r * d r * L j r) 0

theorem gramEntry_eq_sum {m k : ℕ} (L : Matrix (Fin m) (Fin k) ℚ) (d : Fin k → ℚ)
    (i j : Fin m) :
    gramEntry L d i j = ∑ r : Fin k, L i r * d r * L j r := by
  unfold gramEntry
  rw [fin_foldl_add_eq_sum, zero_add]

/-- Kernel-computable `Bool` checker for a rectangular rational weighted Gram
certificate on `Fin m`: checks `d r ≥ 0`, symmetry `A j i = A i j` for `i < j`,
and upper-triangular reconstruction `A i j = gramEntry L d i j` for `i ≤ j`. -/
def checkGramBool {m k : ℕ} (A : Matrix (Fin m) (Fin m) ℚ)
    (L : Matrix (Fin m) (Fin k) ℚ) (d : Fin k → ℚ) : Bool :=
  Fin.foldl k (fun acc r ↦ acc && decide (0 ≤ d r)) true &&
  Fin.foldl m (fun acc i ↦
    acc && Fin.foldl m (fun acc' j ↦
      acc' &&
        (if i.val ≤ j.val then
          decide (A i j = gramEntry L d i j) &&
          (if i.val < j.val then decide (A j i = A i j) else true)
        else true)) true) true

/-- Soundness of `checkGramBool`: a passing kernel check proves that
`A.map (Rat.cast : ℚ → ℂ)` is positive semidefinite. -/
theorem posSemidef_complex_of_checkGramBool {m k : ℕ}
    {A : Matrix (Fin m) (Fin m) ℚ} (L : Matrix (Fin m) (Fin k) ℚ) (d : Fin k → ℚ)
    (h : checkGramBool A L d = true) :
    (A.map (Rat.cast : ℚ → ℂ)).PosSemidef := by
  unfold checkGramBool at h
  simp only [Bool.and_eq_true, fin_all_eq_true_iff] at h
  rcases h with ⟨hd_bool, hmat⟩
  have hd : ∀ r : Fin k, 0 ≤ d r := fun r ↦ of_decide_eq_true (hd_bool r)
  refine Matrix.posSemidef_map_ratCast_of_weightedGram L d hd fun i j ↦ ?_
  by_cases hij : i.val ≤ j.val
  · have hcell := hmat i j
    simp only [hij, ↓reduceIte, Bool.and_eq_true] at hcell
    rw [← gramEntry_eq_sum]
    exact of_decide_eq_true hcell.1
  · have hji_lt : j.val < i.val := Nat.lt_of_not_ge hij
    have hji_le : j.val ≤ i.val := hji_lt.le
    have hcell := hmat j i
    simp only [hji_le, hji_lt, ↓reduceIte, Bool.and_eq_true] at hcell
    have hsym : A i j = A j i := of_decide_eq_true hcell.2
    have hrec : A j i = gramEntry L d j i := of_decide_eq_true hcell.1
    rw [hsym, hrec, gramEntry_eq_sum]
    refine Finset.sum_congr rfl fun r _ ↦ ?_
    ring

/-- The lower-triangular truncation of a square rational matrix: entries strictly
above the diagonal (`i < r`) are set to zero. -/
def lowerFactor {m : ℕ} (L : Matrix (Fin m) (Fin m) ℚ) : Matrix (Fin m) (Fin m) ℚ :=
  fun i r ↦ if r.val ≤ i.val then L i r else 0

/-- Compute `∑ r ≤ i, L i r * d r * L j r` via `Fin.foldl` over `Fin (i.val + 1)`. -/
def ldlEntry {m : ℕ} (L : Matrix (Fin m) (Fin m) ℚ) (d : Fin m → ℚ)
    (i j : Fin m) : ℚ :=
  Fin.foldl (i.val + 1) (fun acc r ↦
    let idx : Fin m := ⟨r.val, Nat.lt_of_lt_of_le r.isLt i.isLt⟩
    acc + L i idx * d idx * L j idx) 0

theorem ldlEntry_eq_lowerFactor_sum {m : ℕ}
    (L : Matrix (Fin m) (Fin m) ℚ) (d : Fin m → ℚ)
    {i j : Fin m} (hij : i.val ≤ j.val) :
    ldlEntry L d i j = ∑ r : Fin m, lowerFactor L i r * d r * lowerFactor L j r := by
  unfold ldlEntry
  rw [fin_foldl_add_eq_sum, zero_add]
  symm
  rw [← Finset.sum_filter_add_sum_filter_not
    (s := Finset.univ) (p := fun r : Fin m ↦ r.val ≤ i.val)]
  have hzero : ∑ r ∈ Finset.univ.filter (fun r : Fin m ↦ ¬ r.val ≤ i.val),
      lowerFactor L i r * d r * lowerFactor L j r = 0 := by
    refine Finset.sum_eq_zero fun r hr ↦ ?_
    have hnot : ¬ r.val ≤ i.val := (Finset.mem_filter.mp hr).2
    simp [lowerFactor, hnot]
  rw [hzero, add_zero]
  refine Finset.sum_bij'
    (fun (r : Fin m) (hr : r ∈ Finset.univ.filter (fun r : Fin m ↦ r.val ≤ i.val)) ↦
      (⟨r.val, Nat.lt_succ_of_le (Finset.mem_filter.mp hr).2⟩ : Fin (i.val + 1)))
    (fun (r : Fin (i.val + 1)) _ ↦
      (⟨r.val, Nat.lt_of_lt_of_le r.isLt i.isLt⟩ : Fin m))
    (fun _ _ ↦ Finset.mem_univ _)
    (fun r _ ↦ Finset.mem_filter.mpr ⟨Finset.mem_univ _, Nat.le_of_lt_succ r.isLt⟩)
    (fun _ _ ↦ rfl)
    (fun _ _ ↦ rfl)
    (fun r hr ↦ ?_)
  have hri : r.val ≤ i.val := (Finset.mem_filter.mp hr).2
  have hrj : r.val ≤ j.val := le_trans hri hij
  simp [lowerFactor, hri, hrj]

/-- Kernel-computable `Bool` checker for a rational LDL factorization `A = L * diag(d) * Lᵀ`
on `Fin m`, where `L` is interpreted as lower-triangular via `lowerFactor L`.
Only sums `r = 0 .. i` for upper-triangular entries `i ≤ j`, reducing kernel work
by roughly 4×–5× compared to dense Gram multiplication. -/
def checkLDLBool {m : ℕ} (A : Matrix (Fin m) (Fin m) ℚ)
    (L : Matrix (Fin m) (Fin m) ℚ) (d : Fin m → ℚ) : Bool :=
  Fin.foldl m (fun acc r ↦ acc && decide (0 ≤ d r)) true &&
  Fin.foldl m (fun acc i ↦
    acc && Fin.foldl m (fun acc' j ↦
      acc' &&
        (if i.val ≤ j.val then
          decide (A i j = ldlEntry L d i j) &&
          (if i.val < j.val then decide (A j i = A i j) else true)
        else true)) true) true

/-- Soundness of `checkLDLBool`: a passing kernel check proves that
`A.map (Rat.cast : ℚ → ℂ)` is positive semidefinite. -/
theorem posSemidef_complex_of_checkLDLBool {m : ℕ}
    {A : Matrix (Fin m) (Fin m) ℚ} (L : Matrix (Fin m) (Fin m) ℚ) (d : Fin m → ℚ)
    (h : checkLDLBool A L d = true) :
    (A.map (Rat.cast : ℚ → ℂ)).PosSemidef := by
  unfold checkLDLBool at h
  simp only [Bool.and_eq_true, fin_all_eq_true_iff] at h
  rcases h with ⟨hd_bool, hmat⟩
  have hd : ∀ r : Fin m, 0 ≤ d r := fun r ↦ of_decide_eq_true (hd_bool r)
  refine Matrix.posSemidef_map_ratCast_of_weightedGram (lowerFactor L) d hd fun i j ↦ ?_
  by_cases hij : i.val ≤ j.val
  · have hcell := hmat i j
    simp only [hij, ↓reduceIte, Bool.and_eq_true] at hcell
    rw [← ldlEntry_eq_lowerFactor_sum L d hij]
    exact of_decide_eq_true hcell.1
  · have hji_lt : j.val < i.val := Nat.lt_of_not_ge hij
    have hji_le : j.val ≤ i.val := hji_lt.le
    have hcell := hmat j i
    simp only [hji_le, hji_lt, ↓reduceIte, Bool.and_eq_true] at hcell
    have hsym : A i j = A j i := of_decide_eq_true hcell.2
    have hrec : A j i = ldlEntry L d j i := of_decide_eq_true hcell.1
    rw [hsym, hrec, ldlEntry_eq_lowerFactor_sum L d hji_le]
    refine Finset.sum_congr rfl fun r _ ↦ ?_
    ring

end FastFinCheckers

section FastPairCheckers

/-- An unnormalized rational pair `(num, den)` representing `(num : ℚ) / (den : ℚ)`.
Arithmetic on `QPair` avoids `Nat.gcd` normalization, so `decide` reduces
exact rational identities using only primitive `Int` and `Nat` kernel operations. -/
structure QPair where
  /-- Numerator. -/
  num : ℤ
  /-- Denominator (checked to be positive by the certificate verifier). -/
  den : ℕ
  deriving DecidableEq, Repr

namespace QPair

/-- Interpret a `QPair` as a rational number `(num : ℚ) / (den : ℚ)`. -/
def toRat (q : QPair) : ℚ := (q.num : ℚ) / (q.den : ℚ)

/-- Construct an integer as a `QPair` with denominator `1`. -/
def ofInt (z : ℤ) : QPair := ⟨z, 1⟩

@[simp] theorem toRat_ofInt (z : ℤ) : (ofInt z).toRat = (z : ℚ) := by
  simp [ofInt, toRat]

/-- Zero-short-circuiting addition on `QPair`. -/
def add (a b : QPair) : QPair :=
  if a.num == 0 then b
  else if b.num == 0 then a
  else ⟨a.num * (b.den : ℤ) + b.num * (a.den : ℤ), a.den * b.den⟩

/-- Zero-short-circuiting multiplication on `QPair`. -/
def mul (a b : QPair) : QPair :=
  if a.num == 0 || b.num == 0 then ⟨0, 1⟩
  else ⟨a.num * b.num, a.den * b.den⟩

/-- Exact rational equality check `a.toRat = b.toRat` via cross-multiplication. -/
def ratEq (a b : QPair) : Bool :=
  decide (a.num * (b.den : ℤ) = b.num * (a.den : ℤ))

theorem den_pos_add {a b : QPair} (ha : 0 < a.den) (hb : 0 < b.den) :
    0 < (a.add b).den := by
  unfold add
  split_ifs
  · exact hb
  · exact ha
  · exact Nat.mul_pos ha hb

theorem den_pos_mul {a b : QPair} (ha : 0 < a.den) (hb : 0 < b.den) :
    0 < (a.mul b).den := by
  unfold mul
  split_ifs
  · exact Nat.one_pos
  · exact Nat.mul_pos ha hb

theorem toRat_add {a b : QPair} (ha : 0 < a.den) (hb : 0 < b.den) :
    (a.add b).toRat = a.toRat + b.toRat := by
  unfold add
  by_cases h1 : a.num == 0
  · have ha0 : a.num = 0 := by simpa using h1
    simp [toRat, ha0]
  · by_cases h2 : b.num == 0
    · have hb0 : b.num = 0 := by simpa using h2
      simp [h1, toRat, hb0]
    · simp only [h1, h2, toRat, Bool.false_eq_true, ↓reduceIte]
      have ha' : (a.den : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr ha.ne'
      have hb' : (b.den : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hb.ne'
      push_cast
      field_simp [ha', hb']

theorem toRat_mul {a b : QPair} (ha : 0 < a.den) (hb : 0 < b.den) :
    (a.mul b).toRat = a.toRat * b.toRat := by
  unfold mul
  by_cases h : (a.num == 0 || b.num == 0) = true
  · simp only [h, ↓reduceIte, toRat, Int.cast_zero, Nat.cast_one, div_one]
    simp only [Bool.or_eq_true, beq_iff_eq] at h
    rcases h with ha0 | hb0
    · simp [ha0]
    · simp [hb0]
  · simp only [h, toRat, Bool.false_eq_true, ↓reduceIte]
    have ha' : (a.den : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr ha.ne'
    have hb' : (b.den : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hb.ne'
    push_cast
    field_simp [ha', hb']

theorem toRat_eq_of_ratEq {a b : QPair} (ha : 0 < a.den) (hb : 0 < b.den)
    (h : a.ratEq b = true) : a.toRat = b.toRat := by
  unfold ratEq at h
  have hmul : a.num * (b.den : ℤ) = b.num * (a.den : ℤ) := of_decide_eq_true h
  have ha' : (a.den : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr ha.ne'
  have hb' : (b.den : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hb.ne'
  unfold toRat
  rw [div_eq_div_iff ha' hb']
  exact_mod_cast hmul

theorem toRat_nonneg {a : QPair} (ha : 0 < a.den) (hnum : 0 ≤ a.num) :
    0 ≤ a.toRat := by
  unfold toRat
  exact div_nonneg (by exact_mod_cast hnum) (by exact_mod_cast ha.le)

end QPair

private lemma fin_foldl_qpair_add {m : ℕ} (f : Fin m → QPair)
    (hf : ∀ r : Fin m, 0 < (f r).den) (init : QPair) (hinit : 0 < init.den) :
    0 < (Fin.foldl m (fun acc r ↦ acc.add (f r)) init).den ∧
    (Fin.foldl m (fun acc r ↦ acc.add (f r)) init).toRat =
      init.toRat + ∑ r : Fin m, (f r).toRat := by
  induction m generalizing init with
  | zero =>
    simp [hinit]
  | succ m ih =>
    rw [Fin.foldl_succ, Fin.sum_univ_succ]
    have hstep_pos : 0 < (init.add (f 0)).den := QPair.den_pos_add hinit (hf 0)
    have hstep_rat : (init.add (f 0)).toRat = init.toRat + (f 0).toRat :=
      QPair.toRat_add hinit (hf 0)
    obtain ⟨hden, hrat⟩ := ih (fun r ↦ f r.succ) (fun r ↦ hf r.succ) (init.add (f 0)) hstep_pos
    refine ⟨hden, ?_⟩
    rw [hrat, hstep_rat]
    ring

/-- Compute `∑ r : Fin k, L i r * d r * L j r` using `QPair` arithmetic. -/
def gramPairEntry {m k : ℕ} (L : Matrix (Fin m) (Fin k) QPair) (d : Fin k → QPair)
    (i j : Fin m) : QPair :=
  Fin.foldl k (fun acc r ↦ acc.add (((L i r).mul (d r)).mul (L j r))) (QPair.ofInt 0)

theorem gramPairEntry_spec {m k : ℕ} (L : Matrix (Fin m) (Fin k) QPair) (d : Fin k → QPair)
    (hL : ∀ i r, 0 < (L i r).den) (hd : ∀ r, 0 < (d r).den) (i j : Fin m) :
    0 < (gramPairEntry L d i j).den ∧
    (gramPairEntry L d i j).toRat =
      ∑ r : Fin k, (L i r).toRat * (d r).toRat * (L j r).toRat := by
  unfold gramPairEntry
  have hterm_pos : ∀ r : Fin k, 0 < (((L i r).mul (d r)).mul (L j r)).den :=
    fun r ↦ QPair.den_pos_mul (QPair.den_pos_mul (hL i r) (hd r)) (hL j r)
  obtain ⟨hden, hrat⟩ := fin_foldl_qpair_add
    (fun r ↦ ((L i r).mul (d r)).mul (L j r)) hterm_pos (QPair.ofInt 0) Nat.one_pos
  refine ⟨hden, ?_⟩
  rw [hrat, QPair.toRat_ofInt, Int.cast_zero, zero_add]
  refine Finset.sum_congr rfl fun r _ ↦ ?_
  rw [QPair.toRat_mul (QPair.den_pos_mul (hL i r) (hd r)) (hL j r),
    QPair.toRat_mul (hL i r) (hd r)]

/-- Fast `decide`-compatible `Bool` checker for a rectangular rational weighted Gram
certificate represented with `QPair` entries. -/
def checkGramPairBool {m k : ℕ} (A : Matrix (Fin m) (Fin m) QPair)
    (L : Matrix (Fin m) (Fin k) QPair) (d : Fin k → QPair) : Bool :=
  Fin.foldl k (fun acc r ↦ acc && (decide (0 < (d r).den) && decide (0 ≤ (d r).num))) true &&
  Fin.foldl m (fun acc i ↦
    acc && Fin.foldl k (fun acc' r ↦ acc' && decide (0 < (L i r).den)) true) true &&
  Fin.foldl m (fun acc i ↦
    acc && Fin.foldl m (fun acc' j ↦
      acc' && (decide (0 < (A i j).den) &&
        (if i.val ≤ j.val then
          (A i j).ratEq (gramPairEntry L d i j) &&
          (if i.val < j.val then (A j i).ratEq (A i j) else true)
        else true))) true) true

/-- Soundness of `checkGramPairBool`: a passing `decide` check certifies that
`(A.map QPair.toRat).map (Rat.cast : ℚ → ℂ)` is positive semidefinite. -/
theorem posSemidef_complex_of_checkGramPairBool {m k : ℕ}
    {A : Matrix (Fin m) (Fin m) QPair} (L : Matrix (Fin m) (Fin k) QPair) (d : Fin k → QPair)
    (h : checkGramPairBool A L d = true) :
    ((A.map QPair.toRat).map (Rat.cast : ℚ → ℂ)).PosSemidef := by
  unfold checkGramPairBool at h
  simp only [Bool.and_eq_true, fin_all_eq_true_iff] at h
  rcases h with ⟨⟨hd_chk, hL_chk⟩, hA_chk⟩
  have hd_pos : ∀ r : Fin k, 0 < (d r).den := fun r ↦ of_decide_eq_true (hd_chk r).1
  have hd_nonneg : ∀ r : Fin k, 0 ≤ (d r).toRat :=
    fun r ↦ QPair.toRat_nonneg (hd_pos r) (of_decide_eq_true (hd_chk r).2)
  have hL_pos : ∀ i r, 0 < (L i r).den := fun i r ↦ of_decide_eq_true (hL_chk i r)
  have hA_pos : ∀ i j, 0 < (A i j).den := fun i j ↦ of_decide_eq_true (hA_chk i j).1
  refine Matrix.posSemidef_map_ratCast_of_weightedGram
    (L.map QPair.toRat) (fun r ↦ (d r).toRat) hd_nonneg fun i j ↦ ?_
  by_cases hij : i.val ≤ j.val
  · have hcell := (hA_chk i j).2
    simp only [hij, ↓reduceIte, Bool.and_eq_true] at hcell
    obtain ⟨hden, hrat⟩ := gramPairEntry_spec L d hL_pos hd_pos i j
    have heq := QPair.toRat_eq_of_ratEq (hA_pos i j) hden hcell.1
    simpa [Matrix.map_apply] using heq.trans hrat
  · have hji_lt : j.val < i.val := Nat.lt_of_not_ge hij
    have hji_le : j.val ≤ i.val := hji_lt.le
    have hcell := (hA_chk j i).2
    simp only [hji_le, hji_lt, ↓reduceIte, Bool.and_eq_true] at hcell
    obtain ⟨hden, hrat⟩ := gramPairEntry_spec L d hL_pos hd_pos j i
    have hsym := QPair.toRat_eq_of_ratEq (hA_pos i j) (hA_pos j i) hcell.2
    have hrec := QPair.toRat_eq_of_ratEq (hA_pos j i) hden hcell.1
    rw [Matrix.map_apply, hsym, hrec, hrat]
    refine Finset.sum_congr rfl fun r _ ↦ ?_
    simp only [Matrix.map_apply]
    ring

/-- Compute `∑ r ≤ i, L i r * d r * L j r` using `QPair` arithmetic. -/
def ldlPairEntry {m : ℕ} (L : Matrix (Fin m) (Fin m) QPair) (d : Fin m → QPair)
    (i j : Fin m) : QPair :=
  Fin.foldl (i.val + 1) (fun acc r ↦
    let idx : Fin m := ⟨r.val, Nat.lt_of_lt_of_le r.isLt i.isLt⟩
    acc.add (((L i idx).mul (d idx)).mul (L j idx))) (QPair.ofInt 0)

theorem ldlPairEntry_spec {m : ℕ} (L : Matrix (Fin m) (Fin m) QPair) (d : Fin m → QPair)
    (hL : ∀ i r, r.val ≤ i.val → 0 < (L i r).den) (hd : ∀ r, 0 < (d r).den)
    {i j : Fin m} (hij : i.val ≤ j.val) :
    0 < (ldlPairEntry L d i j).den ∧
    (ldlPairEntry L d i j).toRat =
      ∑ r : Fin m, lowerFactor (L.map QPair.toRat) i r * (d r).toRat *
        lowerFactor (L.map QPair.toRat) j r := by
  unfold ldlPairEntry
  have hterm_pos : ∀ r : Fin (i.val + 1),
      0 < (((L i ⟨r.val, Nat.lt_of_lt_of_le r.isLt i.isLt⟩).mul
        (d ⟨r.val, Nat.lt_of_lt_of_le r.isLt i.isLt⟩)).mul
        (L j ⟨r.val, Nat.lt_of_lt_of_le r.isLt i.isLt⟩)).den := by
    intro r
    have hri : r.val ≤ i.val := Nat.le_of_lt_succ r.isLt
    have hrj : r.val ≤ j.val := le_trans hri hij
    exact QPair.den_pos_mul
      (QPair.den_pos_mul (hL i _ hri) (hd _)) (hL j _ hrj)
  obtain ⟨hden, hrat⟩ := fin_foldl_qpair_add
    (fun r : Fin (i.val + 1) ↦
      let idx : Fin m := ⟨r.val, Nat.lt_of_lt_of_le r.isLt i.isLt⟩
      ((L i idx).mul (d idx)).mul (L j idx))
    hterm_pos (QPair.ofInt 0) Nat.one_pos
  refine ⟨hden, ?_⟩
  rw [hrat, QPair.toRat_ofInt, Int.cast_zero, zero_add]
  have hsum : (∑ r : Fin (i.val + 1),
      (((L i ⟨r.val, Nat.lt_of_lt_of_le r.isLt i.isLt⟩).mul
        (d ⟨r.val, Nat.lt_of_lt_of_le r.isLt i.isLt⟩)).mul
        (L j ⟨r.val, Nat.lt_of_lt_of_le r.isLt i.isLt⟩)).toRat) =
      ldlEntry (L.map QPair.toRat) (fun r ↦ (d r).toRat) i j := by
    unfold ldlEntry
    rw [fin_foldl_add_eq_sum, zero_add]
    refine Finset.sum_congr rfl fun r _ ↦ ?_
    have hri : r.val ≤ i.val := Nat.le_of_lt_succ r.isLt
    have hrj : r.val ≤ j.val := le_trans hri hij
    rw [QPair.toRat_mul (QPair.den_pos_mul (hL i _ hri) (hd _)) (hL j _ hrj),
      QPair.toRat_mul (hL i _ hri) (hd _)]
    rfl
  rw [hsum, ldlEntry_eq_lowerFactor_sum (L.map QPair.toRat) (fun r ↦ (d r).toRat) hij]

/-- Fast `decide`-compatible `Bool` checker for a rational LDL factorization of an
integer-entry matrix `A : Matrix (Fin m) (Fin m) ℤ`, with lower-triangular factor
`L : Matrix (Fin m) (Fin m) QPair` and diagonal weights `d : Fin m → QPair`. -/
def checkLDLPairIntBool {m : ℕ} (A : Matrix (Fin m) (Fin m) ℤ)
    (L : Matrix (Fin m) (Fin m) QPair) (d : Fin m → QPair) : Bool :=
  Fin.foldl m (fun acc r ↦ acc && (decide (0 < (d r).den) && decide (0 ≤ (d r).num))) true &&
  Fin.foldl m (fun acc i ↦
    acc && Fin.foldl m (fun acc' r ↦
      acc' && (if r.val ≤ i.val then decide (0 < (L i r).den) else true)) true) true &&
  Fin.foldl m (fun acc i ↦
    acc && Fin.foldl m (fun acc' j ↦
      acc' &&
        (if i.val ≤ j.val then
          (QPair.ofInt (A i j)).ratEq (ldlPairEntry L d i j) &&
          (if i.val < j.val then decide (A j i = A i j) else true)
        else true)) true) true

/-- Soundness of `checkLDLPairIntBool`: a passing `decide` check proves that
`A.map (Int.cast : ℤ → ℂ)` is positive semidefinite (no `native_decide`). -/
theorem posSemidef_complex_of_checkLDLPairIntBool {m : ℕ}
    {A : Matrix (Fin m) (Fin m) ℤ} (L : Matrix (Fin m) (Fin m) QPair) (d : Fin m → QPair)
    (h : checkLDLPairIntBool A L d = true) :
    (A.map (Int.cast : ℤ → ℂ)).PosSemidef := by
  unfold checkLDLPairIntBool at h
  simp only [Bool.and_eq_true, fin_all_eq_true_iff] at h
  rcases h with ⟨⟨hd_chk, hL_chk⟩, hA_chk⟩
  have hd_pos : ∀ r : Fin m, 0 < (d r).den := fun r ↦ of_decide_eq_true (hd_chk r).1
  have hd_nonneg : ∀ r : Fin m, 0 ≤ (d r).toRat :=
    fun r ↦ QPair.toRat_nonneg (hd_pos r) (of_decide_eq_true (hd_chk r).2)
  have hL_pos : ∀ i r : Fin m, r.val ≤ i.val → 0 < (L i r).den := by
    intro i r hri
    have hr := hL_chk i r
    simp only [hri, ↓reduceIte] at hr
    exact of_decide_eq_true hr
  have hrat : ((A.map (Int.cast : ℤ → ℚ)).map (Rat.cast : ℚ → ℂ)).PosSemidef := by
    refine Matrix.posSemidef_map_ratCast_of_weightedGram
      (lowerFactor (L.map QPair.toRat)) (fun r ↦ (d r).toRat) hd_nonneg fun i j ↦ ?_
    by_cases hij : i.val ≤ j.val
    · have hcell := hA_chk i j
      simp only [hij, ↓reduceIte, Bool.and_eq_true] at hcell
      obtain ⟨hden, hsum⟩ := ldlPairEntry_spec L d hL_pos hd_pos hij
      have heq := QPair.toRat_eq_of_ratEq Nat.one_pos hden hcell.1
      simpa [Matrix.map_apply] using heq.trans hsum
    · have hji_lt : j.val < i.val := Nat.lt_of_not_ge hij
      have hji_le : j.val ≤ i.val := hji_lt.le
      have hcell := hA_chk j i
      simp only [hji_le, hji_lt, ↓reduceIte, Bool.and_eq_true] at hcell
      obtain ⟨hden, hsum⟩ := ldlPairEntry_spec L d hL_pos hd_pos hji_le
      have hsym : A i j = A j i := of_decide_eq_true hcell.2
      have hrec := QPair.toRat_eq_of_ratEq Nat.one_pos hden hcell.1
      rw [Matrix.map_apply, hsym, ← QPair.toRat_ofInt (A j i), hrec, hsum]
      refine Finset.sum_congr rfl fun r _ ↦ ?_
      ring
  have hcast : (A.map (Int.cast : ℤ → ℚ)).map (Rat.cast : ℚ → ℂ) =
      A.map (Int.cast : ℤ → ℂ) := by
    ext i j
    simp
  rwa [hcast] at hrat

end FastPairCheckers

end QICLean
