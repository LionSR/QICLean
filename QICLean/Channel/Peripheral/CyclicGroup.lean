/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Channel.Peripheral.Spectrum
import Mathlib.RingTheory.RootsOfUnity.Complex

/-!
# Cyclicity from multiplicative closure of peripheral eigenvalues

The finite-set argument in Wolf Theorem 6.6 is independent of positivity.
Multiplication by a peripheral eigenvalue injects the peripheral set into itself,
hence permutes it. Comparing products proves that every peripheral eigenvalue
is an `m`-th root of unity, where `m` is the cardinality of that set. Distinct
eigenvalues have independent eigenvectors, giving the dimension bound.
-/

open scoped BigOperators

section

variable {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]

/-- The number of peripheral eigenvalues is bounded by the ambient complex
dimension. This is the order estimate used in Wolf Theorem 6.6(1). -/
theorem peripheralEigenvalues_card_le_finrank (T : V →ₗ[ℂ] V) :
    (peripheralEigenvalues_finite T).toFinset.card ≤ Module.finrank ℂ V := by
  classical
  let S := (peripheralEigenvalues_finite T).toFinset
  choose X hX using fun μ : S =>
    ((peripheralEigenvalues_finite T).mem_toFinset.mp μ.property).1.exists_hasEigenvector
  have hli := Module.End.eigenvectors_linearIndependent' T
    (fun μ : S => (μ : ℂ)) Subtype.val_injective X hX
  simpa [S] using hli.fintype_card_le_finrank

/-- A nonempty multiplicatively closed peripheral spectrum is exactly the set
of powers of the canonical primitive root `exp (2πi/m)`, where `m` is its
cardinality. This is the finite-group step in Wolf Theorem 6.6(1). -/
theorem peripheralEigenvalues_eq_range_exp_of_mul_mem
    (T : V →ₗ[ℂ] V) (hOne : (1 : ℂ) ∈ peripheralEigenvalues T)
    (hMul : ∀ μ ν : ℂ, μ ∈ peripheralEigenvalues T →
      ν ∈ peripheralEigenvalues T → μ * ν ∈ peripheralEigenvalues T) :
    let m := (peripheralEigenvalues_finite T).toFinset.card
    let γ := Complex.exp (2 * ↑Real.pi * Complex.I / ↑m)
    0 < m ∧ m ≤ Module.finrank ℂ V ∧ IsPrimitiveRoot γ m ∧
      peripheralEigenvalues T = Set.range (fun j : Fin m => γ ^ (j : ℕ)) := by
  classical
  let hfin := peripheralEigenvalues_finite T
  let S := hfin.toFinset
  let m := S.card
  let γ := Complex.exp (2 * ↑Real.pi * Complex.I / ↑m)
  have hm : 0 < m := Finset.card_pos.mpr ⟨1, hfin.mem_toFinset.mpr hOne⟩
  have hne (μ : ℂ) (hμ : μ ∈ S) : μ ≠ 0 :=
    Complex.ne_zero_of_norm_eq_one (hfin.mem_toFinset.mp hμ).2
  have hmul (μ ν : ℂ) (hμ : μ ∈ S) (hν : ν ∈ S) : μ * ν ∈ S :=
    hfin.mem_toFinset.mpr (hMul μ ν (hfin.mem_toFinset.mp hμ) (hfin.mem_toFinset.mp hν))
  have hroot (μ : ℂ) (hμ : μ ∈ S) : μ ^ m = 1 := by
    have himage : S.image (μ * ·) = S := by
      apply Finset.eq_of_subset_of_card_le
      · intro ν hν
        obtain ⟨η, hη, rfl⟩ := Finset.mem_image.mp hν
        exact hmul μ η hμ hη
      · rw [Finset.card_image_of_injective S (fun _ _ h => mul_left_cancel₀ (hne μ hμ) h)]
    have hperm : ∏ ν ∈ S, (μ * ν) = ∏ ν ∈ S, ν := by
      calc
        ∏ ν ∈ S, (μ * ν) = ∏ ν ∈ S.image (μ * ·), ν :=
          (Finset.prod_image (f := fun ν : ℂ => ν)
            (fun _ _ _ _ h => mul_left_cancel₀ (hne μ hμ) h)).symm
        _ = ∏ ν ∈ S, ν := by rw [himage]
    rw [Finset.prod_mul_distrib, Finset.prod_const] at hperm
    exact mul_right_cancel₀ (Finset.prod_ne_zero_iff.mpr hne) (by simpa using hperm)
  have : NeZero m := ⟨hm.ne'⟩
  have hγ : IsPrimitiveRoot γ m := Complex.isPrimitiveRoot_exp m hm.ne'
  have hSsub : S ⊆ Polynomial.nthRootsFinset m (1 : ℂ) := by
    intro μ hμ
    exact (Polynomial.mem_nthRootsFinset hm (1 : ℂ)).mpr (hroot μ hμ)
  have hSeq : S = Polynomial.nthRootsFinset m (1 : ℂ) :=
    Finset.eq_of_subset_of_card_le hSsub (by rw [hγ.card_nthRootsFinset])
  refine ⟨hm, peripheralEigenvalues_card_le_finrank T, hγ, ?_⟩
  change peripheralEigenvalues T = Set.range (fun j : Fin m => γ ^ (j : ℕ))
  ext μ
  constructor
  · intro hμ
    obtain ⟨j, hj, heq⟩ := hγ.eq_pow_of_pow_eq_one (hroot μ (hfin.mem_toFinset.mpr hμ))
    exact ⟨⟨j, hj⟩, heq⟩
  · rintro ⟨j, rfl⟩
    apply hfin.mem_toFinset.mp
    change γ ^ (j : ℕ) ∈ S
    rw [hSeq]
    exact (Polynomial.mem_nthRootsFinset hm (1 : ℂ)).mpr (by
      rw [← pow_mul, Nat.mul_comm, pow_mul, hγ.pow_eq_one, one_pow])

end
