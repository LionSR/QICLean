/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Algebra.HermitianHelpers
import QICLean.Analysis.LowEnergyPerturbation

/-!
# The decreasing order of a Hermitian spectrum

For a Hermitian matrix on a nonempty finite index set, the last eigenvalue in decreasing
order is the minimum eigenvalue, and the closed spectral span below an energy is the same for
the eigenbasis indexed by the index set and for the one indexed in decreasing order of the
eigenvalues.

Moved from TNLean, `TNLean/Lattice/HardTruncation.lean` at commit `e41c3b63`, with the
statements unchanged.

## Main results

* `Matrix.IsHermitian.eigenvalues₀_last_eq_minEigenvalue`
* `Matrix.IsHermitian.spectralSpanLE_eigenvectorBasis_eq`
-/

open Matrix
open scoped InnerProductSpace

namespace Matrix.IsHermitian

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The last eigenvalue in decreasing order is the minimum eigenvalue: for a Hermitian `M` on
`n` coordinates with eigenvalues `λ₀ ≥ ⋯ ≥ λ_{n-1}`, `λ_{n-1} = min_i λ_i`. An auxiliary identity
for the ground energy of an ordered spectrum. -/
theorem eigenvalues₀_last_eq_minEigenvalue [Nonempty n] {M : Matrix n n ℂ}
    (hM : M.IsHermitian) :
    hM.eigenvalues₀ ⟨Fintype.card n - 1, Nat.sub_lt Fintype.card_pos (by decide)⟩ =
      minEigenvalue hM := by
  classical
  let e : Fin (Fintype.card n) ≃ n := Fintype.equivOfCardEq (Fintype.card_fin _)
  apply le_antisymm
  · obtain ⟨i, hi⟩ := minEigenvalue_achieved hM
    have hle : e.symm i ≤ ⟨Fintype.card n - 1, Nat.sub_lt Fintype.card_pos (by decide)⟩ := by
      change (e.symm i).val ≤ Fintype.card n - 1
      omega
    have h := hM.eigenvalues₀_antitone hle
    change hM.eigenvalues₀ (e.symm i) = minEigenvalue hM at hi
    exact h.trans_eq hi
  · simpa only [IsHermitian.eigenvalues, e, Equiv.symm_apply_apply] using
      minEigenvalue_le hM (e ⟨Fintype.card n - 1, Nat.sub_lt Fintype.card_pos (by decide)⟩)

/-- The two canonical eigenvector bases of a Hermitian `M`, one indexed by the coordinates and
one in decreasing order of the eigenvalues, span the same space below every threshold `c`:
`span{vᵢ : λᵢ ≤ c} = span{w_j : μ_j ≤ c}`. An auxiliary identity relating the two
enumerations of the spectrum. -/
theorem spectralSpanLE_eigenvectorBasis_eq {M : Matrix n n ℂ} (hM : M.IsHermitian) (c : ℝ) :
    Submodule.spectralSpanLE hM.eigenvectorBasis hM.eigenvalues c =
      Submodule.spectralSpanLE
        ((isSymmetric_toEuclideanLin_iff.mpr hM).eigenvectorBasis finrank_euclideanSpace)
        hM.eigenvalues₀ c := by
  let e : Fin (Fintype.card n) ≃ n := Fintype.equivOfCardEq (Fintype.card_fin _)
  unfold Submodule.spectralSpanLE
  congr 1
  ext x
  constructor
  · rintro ⟨i, hi, rfl⟩
    refine ⟨e.symm i, hi, ?_⟩
    simp only [IsHermitian.eigenvectorBasis, OrthonormalBasis.reindex_apply, e]
  · rintro ⟨i, hi, rfl⟩
    refine ⟨e i, ?_, ?_⟩
    · have hi' : hM.eigenvalues₀ i ≤ c := hi
      simpa [IsHermitian.eigenvalues, e] using hi'
    · simp only [IsHermitian.eigenvectorBasis, OrthonormalBasis.reindex_apply,
        e, Equiv.symm_apply_apply]

end Matrix.IsHermitian
