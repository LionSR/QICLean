/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Algebra.MatrixSpectralDecomp
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.FieldSimp

/-!
# Kraus coupling without a faithful input

A Hermitian prepared matrix and positive output and effect matrices with
compatible positive total mass admit a rectangular Kraus family whose
cardinality is at most the larger of the output and effect ranks.
Cyclic matchings combine weighted matrix units coherently. No inverse of
the prepared matrix is used.

## Main result

* `Matrix.exists_kraus_state_effect_coupling_max_rank` constructs a Kraus
  family with the prescribed prepared-state output and trace effect.

## Implementation notes

The compact spectral indexing is adapted from `LionSR/TNLean`,
`TNLean/Algebra/KrausMarginalCoupling.lean`, commit
`6c340a425319a5438853fca437da18cd0a22450a`, with an isometric matrix
factorization in place of individual unit-vector identities.

## References

* Wolf, *Quantum Channels & Operations: Guided Tour*, Section 2.1,
  for the Kraus representation used in this coupling construction.
-/
open scoped Matrix BigOperators ComplexOrder

namespace Matrix

/-- Injective labels in a finite additive group group the weighted matrix
units into one Kraus operator per group element. Their effect is scalar,
and on diagonal inputs their sum is trace preparation. The weights need
not be normalized. This is the algebraic matching construction for the
Kraus representation in Wolf, Section 2.1. -/
private theorem exists_matching_kraus_diagonal_identities
    {G α β : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    (row : α → G) (col : β → G)
    (hrow : Function.Injective row) (hcol : Function.Injective col)
    (w : α → ℂ) :
    ∃ K : G → Matrix α β ℂ,
      (∀ k i j, K k i j = if row i - col j = k then w i else 0) ∧
      (∑ k, (K k)ᴴ * K k) = (∑ i, star (w i) * w i) • (1 : Matrix β β ℂ) ∧
      (∀ d : β → ℂ,
        (∑ k, K k * Matrix.diagonal d * (K k)ᴴ) =
          (∑ j, d j) • Matrix.diagonal (fun i => w i * star (w i))) := by
  let K : G → Matrix α β ℂ :=
    fun k i j => if row i - col j = k then w i else 0
  have hEffectEntry (k : G) (j l : β) :
      ((K k)ᴴ * K k) j l = ∑ i, star (K k i j) * K k i l := rfl
  have hPreparedEntry (k : G) (d : β → ℂ) (i l : α) :
      (K k * Matrix.diagonal d * (K k)ᴴ) i l =
        ∑ j, (K k i j * d j) * star (K k l j) := by
    rw [Matrix.mul_apply]
    simp only [Matrix.mul_diagonal, Matrix.conjTranspose_apply]
  refine ⟨K, fun _ _ _ => rfl, ?_, ?_⟩
  · ext j l : 2
    simp only [Matrix.sum_apply, hEffectEntry, Matrix.smul_apply, Matrix.one_apply,
      smul_eq_mul]
    by_cases hjl : j = l
    · subst l
      simp only [ite_true, mul_one]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      simp [K, mul_ite]
    · have hZero : (∑ k, ∑ i, star (K k i j) * K k i l) = 0 := by
        apply Finset.sum_eq_zero
        intro k _
        apply Finset.sum_eq_zero
        intro i _
        by_cases hFirst : row i - col j = k
        · have hSecond : row i - col l ≠ k := by
            intro h
            apply hjl
            apply hcol
            have h' := congrArg (fun x => row i - x) (hFirst.trans h.symm)
            simpa using h'
          simp [K, hFirst, hSecond]
        · simp [K, hFirst]
      simpa [hjl] using hZero
  · intro d
    ext i l : 2
    simp only [Matrix.sum_apply, hPreparedEntry, Matrix.smul_apply, Matrix.diagonal_apply,
      smul_eq_mul]
    by_cases hil : i = l
    · subst l
      simp only [ite_true]
      rw [Finset.sum_comm, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro j _
      calc
        (∑ k, (K k i j * d j) * star (K k i j)) =
            (w i * d j) * star (w i) := by
          simp [K, ite_mul]
        _ = d j * (w i * star (w i)) := by ring
    · have hZero : (∑ k, ∑ j, (K k i j * d j) * star (K k l j)) = 0 := by
        apply Finset.sum_eq_zero
        intro k _
        apply Finset.sum_eq_zero
        intro j _
        by_cases hFirst : row i - col j = k
        · have hSecond : row l - col j ≠ k := by
            intro h
            apply hil
            apply hrow
            have h' := congrArg (fun x => x + col j) (hFirst.trans h.symm)
            simpa using h'
          simp [K, hFirst, hSecond]
        · simp [K, hFirst]
      simpa [hil] using hZero

/-- A Hermitian prepared matrix and positive output and effect matrices
with the same positive total mass admit a rectangular Kraus family with
at most the larger of the output and effect ranks. No positivity,
normalization or faithfulness assumption is imposed on the prepared
matrix. The construction uses the Kraus representation of Wolf,
Section 2.1. -/
theorem exists_kraus_state_effect_coupling_max_rank {m n : Type*}
    [Fintype m] [Fintype n]
    {ρ B : Matrix m m ℂ} {A : Matrix n n ℂ}
    (hρ : ρ.IsHermitian) (hA : A.PosSemidef) (hB : B.PosSemidef)
    (hTrace : A.trace = (B * ρ).trace) (hPos : 0 < A.trace.re) :
    ∃ K : Fin (max A.rank B.rank) → Matrix n m ℂ,
      (∑ k, K k * ρ * (K k)ᴴ) = A ∧ (∑ k, (K k)ᴴ * K k) = B := by
  classical
  obtain ⟨a, U, ha, hU, hAeq⟩ := hA.exists_compact_spectral_isometry
  obtain ⟨b, Z, hb, _hZ, hBeq⟩ := hB.exists_compact_spectral_isometry
  let T : ℝ := ∑ i, a i
  have hATrace : A.trace = (T : ℂ) :=
    (congrArg Matrix.trace hAeq).trans (trace_eq_sum_spectral_weights U hU a)
  have hT : 0 < T := by simpa only [hATrace, Complex.ofReal_re] using hPos
  let d : Fin B.rank → ℂ := fun j => (Real.sqrt (b j) : ℂ)
  have hD : Matrix.diagonal d * (Matrix.diagonal d)ᴴ =
      Matrix.diagonal (fun j => (b j : ℂ)) := by
    rw [Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal]
    congr 1
    funext j
    have hr : Real.sqrt (b j) * Real.sqrt (b j) = b j := by
      simpa only [pow_two] using Real.sq_sqrt (hb j).le
    simpa [d] using congrArg Complex.ofReal hr
  let S : Matrix m (Fin B.rank) ℂ := Z * Matrix.diagonal d
  have hSS : S * Sᴴ = B := by
    calc
      S * Sᴴ = Z * (Matrix.diagonal d * (Matrix.diagonal d)ᴴ) * Zᴴ := by
        simp only [S, Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = B := by rw [hD, ← hBeq]
  let σ := Sᴴ * ρ * S
  have hσ : σ.IsHermitian := Matrix.isHermitian_conjTranspose_mul_mul S hρ
  let V := hσ.eigenvectorUnitary
  let Vm : Matrix (Fin B.rank) (Fin B.rank) ℂ := V
  let eigen : Fin B.rank → ℂ := RCLike.ofReal ∘ hσ.eigenvalues
  have hVL : Vmᴴ * Vm = 1 := by
    simpa only [Vm, Matrix.star_eq_conjTranspose] using Unitary.coe_star_mul_self V
  have hVR : Vm * Vmᴴ = 1 := by
    simpa only [Vm, Unitary.coe_star, Matrix.star_eq_conjTranspose] using
      Unitary.coe_mul_star_self V
  have hσeq : σ = Vm * Matrix.diagonal eigen * Vmᴴ := by
    simpa only [Vm, V, eigen, Unitary.conjStarAlgAut_apply,
      Matrix.star_eq_conjTranspose, Function.comp_def] using hσ.spectral_theorem
  let W : Matrix m (Fin B.rank) ℂ := S * Vm
  have hWW : W * Wᴴ = B := by
    calc
      W * Wᴴ = S * (Vm * Vmᴴ) * Sᴴ := by
        simp only [W, Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = B := by rw [hVR, Matrix.mul_one, hSS]
  have hPrepared : Wᴴ * ρ * W = Matrix.diagonal eigen := by
    calc
      Wᴴ * ρ * W = Vmᴴ * σ * Vm := by
        simp only [W, σ, Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = Matrix.diagonal eigen := by
        rw [hσeq]
        calc
          _ = Vmᴴ * Vm * Matrix.diagonal eigen * (Vmᴴ * Vm) := by
            simp only [Matrix.mul_assoc]
          _ = Matrix.diagonal eigen := by rw [hVL, Matrix.one_mul, Matrix.mul_one]
  have hMass : ∑ j, eigen j = (T : ℂ) := by
    have h := congrArg Matrix.trace hPrepared
    rw [Matrix.trace_mul_cycle, hWW, Matrix.trace_diagonal] at h
    exact h.symm.trans (hTrace.symm.trans hATrace)
  let w : Fin A.rank → ℂ := fun i => (Real.sqrt (a i / T) : ℂ)
  have hw (i : Fin A.rank) : star (w i) * w i = ((a i / T : ℝ) : ℂ) := by
    have hr : Real.sqrt (a i / T) * Real.sqrt (a i / T) = a i / T := by
      simpa only [pow_two] using Real.sq_sqrt (div_nonneg (ha i).le hT.le)
    simpa [w] using congrArg Complex.ofReal hr
  have hw' (i : Fin A.rank) : w i * star (w i) = ((a i / T : ℝ) : ℂ) := by
    rw [mul_comm]
    exact hw i
  have hNorm : ∑ i, star (w i) * w i = 1 := by
    simp_rw [hw]
    have hr : ∑ i, a i / T = 1 := by
      simp_rw [div_eq_mul_inv]
      rw [← Finset.sum_mul]
      change T * T⁻¹ = 1
      exact mul_inv_cancel₀ hT.ne'
    simpa only [Complex.ofReal_sum, Complex.ofReal_one] using congrArg Complex.ofReal hr
  have hDiag : (T : ℂ) • Matrix.diagonal (fun i => w i * star (w i)) =
      Matrix.diagonal (fun i => (a i : ℂ)) := by
    ext i j : 2
    by_cases hij : i = j
    · subst j
      simp only [Matrix.smul_apply, Matrix.diagonal_apply, ite_true, smul_eq_mul, hw']
      have hr : T * (a i / T) = a i := by field_simp [hT.ne']
      exact_mod_cast hr
    · simp [hij]
  let N := max A.rank B.rank
  have hNA : Nonempty (Fin A.rank) := by
    by_contra h
    let : IsEmpty (Fin A.rank) := not_nonempty_iff.mp h
    have hZero : T = 0 := by simp [T]
    exact hT.ne' hZero
  obtain ⟨i₀⟩ := hNA
  have hN : 0 < N :=
    (lt_of_le_of_lt (Nat.zero_le i₀.val) i₀.isLt).trans_le (Nat.le_max_left _ _)
  let : NeZero N := ⟨hN.ne'⟩
  let e := (ZMod.finEquiv N).toEquiv
  let row : Fin A.rank → ZMod N := fun i => e (Fin.castLE (Nat.le_max_left _ _) i)
  let col : Fin B.rank → ZMod N := fun j => e (Fin.castLE (Nat.le_max_right _ _) j)
  have hrow : Function.Injective row := by
    intro i j h
    apply Fin.ext
    exact congrArg (fun k : Fin N => k.val) (e.injective h)
  have hcol : Function.Injective col := by
    intro i j h
    apply Fin.ext
    exact congrArg (fun k : Fin N => k.val) (e.injective h)
  obtain ⟨R, _, hEffect, hState⟩ :=
    exists_matching_kraus_diagonal_identities row col hrow hcol w
  let K : ZMod N → Matrix n m ℂ := fun k => U * R k * Wᴴ
  have hKState (k : ZMod N) : K k * ρ * (K k)ᴴ =
      U * (R k * Matrix.diagonal eigen * (R k)ᴴ) * Uᴴ := by
    simp only [K, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
    calc
      _ = U * (R k * (Wᴴ * ρ * W) * (R k)ᴴ) * Uᴴ := by
        simp only [Matrix.mul_assoc]
      _ = _ := by rw [hPrepared]
  have hKEffect (k : ZMod N) : (K k)ᴴ * K k = W * ((R k)ᴴ * R k) * Wᴴ := by
    simp only [K, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
    calc
      _ = W * ((R k)ᴴ * (Uᴴ * U) * R k) * Wᴴ := by
        simp only [Matrix.mul_assoc]
      _ = _ := by rw [hU, Matrix.mul_one]
  have hSumState : (∑ k, K k * ρ * (K k)ᴴ) = A := by
    simp_rw [hKState]
    calc
      _ = U * (∑ k, R k * Matrix.diagonal eigen * (R k)ᴴ) * Uᴴ := by
        rw [Matrix.mul_sum, Matrix.sum_mul]
      _ = A := by rw [hState eigen, hMass, hDiag, ← hAeq]
  have hSumEffect : (∑ k, (K k)ᴴ * K k) = B := by
    simp_rw [hKEffect]
    calc
      _ = W * (∑ k, (R k)ᴴ * R k) * Wᴴ := by rw [Matrix.mul_sum, Matrix.sum_mul]
      _ = B := by rw [hEffect, hNorm, one_smul, Matrix.mul_one, hWW]
  refine ⟨fun k => K (e k), ?_, ?_⟩
  · exact (Fintype.sum_equiv e _ _ (fun k => rfl)).trans hSumState
  · exact (Fintype.sum_equiv e _ _ (fun k => rfl)).trans hSumEffect

end Matrix
