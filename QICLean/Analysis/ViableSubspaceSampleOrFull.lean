/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.ViableSubspaceBootstrap

/-!
# Sampling a viable space or retaining its whole dimension

The actual Haar-subspace construction is used with sample dimension equal
to the minimum of the prescribed size and the input dimension. When the
whole input fits within the prescribed size, its full coordinate sample is
exactly the input space and no probability estimate is needed. These facts
support ALVV, arXiv:1602.08828v2, Lemma `l:rs`, lines 530–558, and the
merge construction, lines 1662–1677.

**Local fix (complex sphere net count):** The conditional existence estimate
retains the corrected real dimension `2 * dim(T)` and the associated net
scale. See `docs/paper-gaps/alvv16_random_sampling_net_count.tex`.
-/

open scoped TensorProduct
open Module

namespace Submodule

variable {M F : Type*}
  [NormedAddCommGroup M] [InnerProductSpace ℂ M] [FiniteDimensional ℂ M]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F]

/-- A full-dimensional coordinate sample is the actual input subspace.
Supporting ALVV, arXiv:1602.08828v2, Lemma `l:rs`, lines 530–558. -/
lemma randomSubspace_eq_of_card_eq {W : Submodule ℂ M} {q : ℕ}
    (b : OrthonormalBasis (Fin q) ℂ W) (A : Finset (Fin q))
    (hA : A.card = q) (U : Matrix.unitaryGroup (Fin q) ℂ) :
    randomSubspace b A U = W := by
  apply Submodule.eq_of_le_of_finrank_eq (randomSubspace_le b A U)
  rw [finrank_randomSubspace, hA, finrank_eq_card_basis b.toBasis, Fintype.card_fin]

/-- Retaining the whole actual input satisfies the weakened sampling
viability bound for every unitary. Supporting ALVV,
arXiv:1602.08828v2, Lemma `l:rs`, lines 530–558. -/
lemma IsViable.randomSubspace_min_of_le {W : Submodule ℂ M} {q : ℕ}
    (b : OrthonormalBasis (Fin q) ℂ W) (s : ℕ) {delta : ℝ}
    {T : Submodule ℂ (M ⊗[ℂ] F)} (hT : IsViable delta W T) (hdelta : delta ≤ 1)
    (hfull : q ≤ s) (U : Matrix.unitaryGroup (Fin q) ℂ) :
    let A := Finset.univ.map (Fin.castLEEmb (Nat.min_le_right s q))
    IsViable (1 - (1 - delta) * (min s q : ℕ) / (8 * q)) (randomSubspace b A U) T := by
  intro A
  have hA : A.card = q := by simp [A, Nat.min_eq_right hfull]
  rw [randomSubspace_eq_of_card_eq b A hA U]
  apply hT.of_le
  rw [Nat.min_eq_right hfull]
  by_cases hq : q = 0
  · simpa only [hq, Nat.cast_zero, mul_zero, div_zero, sub_zero] using hdelta
  · have hqR : (q : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hq
    field_simp
    linarith

/-- A prescribed sample size is truncated to the actual input dimension.
The full-dimensional branch retains the original space and does not assume
an unnecessary failure-probability estimate. The other branch is the actual
Haar sample of ALVV, arXiv:1602.08828v2, Lemma `l:rs`, lines 530–558. -/
lemma exists_isViable_randomSubspace_min {W : Submodule ℂ M} {q : ℕ}
    (b : OrthonormalBasis (Fin q) ℂ W) (s : ℕ) {delta : ℝ}
    {T : Submodule ℂ (M ⊗[ℂ] F)} (hT : IsViable delta W T) (hdelta : delta ≤ 1)
    (hfailure : s < q →
      (1 + 2 / Real.sqrt ((1 - delta) * (s : ℝ) / (8 * q))) ^
        (2 * Module.finrank ℂ T) * q * Real.exp (-(s / 16 : ℝ)) < 1) :
    let A := Finset.univ.map (Fin.castLEEmb (Nat.min_le_right s q))
    ∃ U : Matrix.unitaryGroup (Fin q) ℂ,
      IsViable (1 - (1 - delta) * (min s q : ℕ) / (8 * q))
        (randomSubspace b A U) T := by
  intro A
  have hcard : A.card = min s q := by simp [A]
  by_cases hfull : q ≤ s
  · exact ⟨1, hT.randomSubspace_min_of_le b s hdelta hfull 1⟩
  · have hsq : s < q := lt_of_not_ge hfull
    have hfailure' :
        (1 + 2 / Real.sqrt ((1 - delta) * (A.card : ℝ) / (8 * Fintype.card (Fin q)))) ^
          (2 * Module.finrank ℂ T) * Fintype.card (Fin q) *
            Real.exp (-(A.card / 16 : ℝ)) < 1 := by
      simpa only [hcard, Nat.min_eq_left hsq.le, Fintype.card_fin] using hfailure hsq
    simpa only [hcard, Fintype.card_fin] using
      exists_isViable_randomSubspace b A hT hfailure'

end Submodule
