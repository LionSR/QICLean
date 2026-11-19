/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.InnerProductSpace.Projection.Basic

/-!
# Off-diagonal parts in an eigenbasis

Hastings, *Solving gapped Hamiltonians locally*, arXiv:cond-mat/0508554v3, lines 476–491 and
1678–1693, chooses a basis of a ground space that diagonalizes the compression of one
approximate term. This file works on an arbitrary inner product space.

* `abs_sub_mul_norm_inner_le_norm_commutator`, `norm_inner_le_norm_commutator_div`: between
  eigenvectors of a self-adjoint `A` with eigenvalues `r ≠ s`, `|⟨v, B w⟩| ≤ ‖[A, B]‖ / |r - s|`.
* `offDiagonalPart`, `norm_offDiagonalPart_le_norm_commutator_div`: the off-diagonal part of an
  operator in an orthonormal pair, bounded by the commutator over the eigenvalue difference.
* `offDiagonalPartFamily`, `sum_norm_offDiagonalPartFamily_le`: the same in an orthonormal
  family of eigenvectors with pairwise separated eigenvalues, summed over a finite family.
* `norm_apply_sub_inner_smul_le_add_offDiagonalPart(Family)`: eq. `low` up to the off-diagonal
  part.

Moved from TNLean (`e113e005`): `TNLean/Lattice/LowEnergyBasis.lean`,
`LowEnergyBasisSimpleSpectrum.lean`, and the off-diagonal section of
`LowEnergyCommutator.lean`. Changes: namespace `LowEnergyBasis`.
-/

noncomputable section

open scoped InnerProductSpace

namespace LowEnergyBasis

section Commutator

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [CompleteSpace E]

/-- **Matrix elements between eigenvectors from a commutator.** If `A` is self-adjoint with
`A v = r v` and `A w = s w`, then `|r - s| ‖⟪v, B w⟫‖ ≤ ‖[A, B]‖ ‖v‖ ‖w‖` for every `B`, since
`⟪v, [A, B] w⟫ = (r - s) ⟪v, B w⟫`. Hastings, arXiv:cond-mat/0508554v3, lines 1678–1690. -/
theorem abs_sub_mul_norm_inner_le_norm_commutator {A : E →L[𝕜] E} (hA : IsSelfAdjoint A)
    (B : E →L[𝕜] E) {v w : E} {r s : ℝ} (hv : A v = (r : 𝕜) • v) (hw : A w = (s : 𝕜) • w) :
    |r - s| * ‖⟪v, B w⟫_𝕜‖ ≤ ‖A * B - B * A‖ * ‖v‖ * ‖w‖ := by
  have hkey : ⟪v, (A * B - B * A) w⟫_𝕜 = ((r - s : ℝ) : 𝕜) * ⟪v, B w⟫_𝕜 := by
    have hsymm : ⟪v, A (B w)⟫_𝕜 = ⟪A v, B w⟫_𝕜 := (hA.isSymmetric v (B w)).symm
    simp only [_root_.sub_apply, mul_apply_eq_comp, inner_sub_right,
      hsymm, hv, hw, map_smul, inner_smul_left, inner_smul_right, RCLike.conj_ofReal]
    push_cast
    ring
  calc |r - s| * ‖⟪v, B w⟫_𝕜‖ = ‖⟪v, (A * B - B * A) w⟫_𝕜‖ := by
        rw [hkey, norm_mul, RCLike.norm_ofReal]
    _ ≤ ‖v‖ * ‖(A * B - B * A) w‖ := norm_inner_le_norm _ _
    _ ≤ ‖v‖ * (‖A * B - B * A‖ * ‖w‖) := by gcongr; exact (A * B - B * A).le_opNorm w
    _ = _ := by ring

/-- **Off-diagonal elements in an eigenbasis.** If `A` is self-adjoint with `A v = r v`,
`A w = s w` and `r ≠ s`, then `‖⟪v, B w⟫‖ ≤ ‖[A, B]‖ ‖v‖ ‖w‖ / |r - s|` for every `B`. With
`A = P M_j P`, `B = P M_i P` and unit ground vectors `v`, `w`, this is Hastings' bound
`o(i) ≤ ‖[P M_i P, P M_j P]‖ / δλ_j` on the off-diagonal elements of `M_i` in a basis of the
ground space diagonalizing `M_j`, arXiv:cond-mat/0508554v3, lines 1678–1690. -/
theorem norm_inner_le_norm_commutator_div {A : E →L[𝕜] E} (hA : IsSelfAdjoint A)
    (B : E →L[𝕜] E) {v w : E} {r s : ℝ} (hv : A v = (r : 𝕜) • v) (hw : A w = (s : 𝕜) • w)
    (hrs : r ≠ s) :
    ‖⟪v, B w⟫_𝕜‖ ≤ ‖A * B - B * A‖ * ‖v‖ * ‖w‖ / |r - s| := by
  rw [le_div_iff₀ (abs_pos.mpr (sub_ne_zero.mpr hrs)), mul_comm]
  exact abs_sub_mul_norm_inner_le_norm_commutator hA B hv hw

end Commutator

end LowEnergyBasis

section TwoLevel

open scoped InnerProductSpace

namespace LowEnergyBasis

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [CompleteSpace E]

/-- The off-diagonal part `⟨v, B w⟩ |v⟩⟨w| + ⟨w, B v⟩ |w⟩⟨v|` of `B` in the pair `v`, `w`.
Hastings, arXiv:cond-mat/0508554v3, `proj3new.tex`, lines 476–480. -/
noncomputable def offDiagonalPart (v w : E) (B : E →L[𝕜] E) : E →L[𝕜] E :=
  ⟪v, B w⟫_𝕜 • InnerProductSpace.rankOne 𝕜 v w + ⟪w, B v⟫_𝕜 • InnerProductSpace.rankOne 𝕜 w v

omit [CompleteSpace E] in
theorem offDiagonalPart_apply (v w : E) (B : E →L[𝕜] E) (x : E) :
    offDiagonalPart v w B x =
      (⟪v, B w⟫_𝕜 * ⟪w, x⟫_𝕜) • v + (⟪w, B v⟫_𝕜 * ⟪v, x⟫_𝕜) • w := by
  simp [offDiagonalPart, InnerProductSpace.rankOne_apply, smul_smul]

omit [CompleteSpace E] in
/-- **The norm of the off-diagonal part.** For an orthonormal pair `v`, `w`, the off-diagonal
part of `B` has norm at most the larger of `‖⟨v, B w⟩‖` and `‖⟨w, B v⟩‖`. -/
theorem norm_offDiagonalPart_le {v w : E} (hv : ‖v‖ = 1) (hw : ‖w‖ = 1) (hvw : ⟪v, w⟫_𝕜 = 0)
    (B : E →L[𝕜] E) :
    ‖offDiagonalPart v w B‖ ≤ max ‖⟪v, B w⟫_𝕜‖ ‖⟪w, B v⟫_𝕜‖ := by
  set m := max ‖⟪v, B w⟫_𝕜‖ ‖⟪w, B v⟫_𝕜‖
  have hm : 0 ≤ m := le_max_of_le_left (norm_nonneg _)
  have hon : Orthonormal 𝕜 ![v, w] := by
    rw [orthonormal_iff_ite]
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [hvw, inner_self_eq_norm_sq_to_K, hv, hw, inner_eq_zero_symm.mp hvw]
  refine ContinuousLinearMap.opNorm_le_bound _ hm fun x => ?_
  have hbessel := hon.sum_inner_products_le (s := Finset.univ) x
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one] at hbessel
  have horth : ⟪(⟪v, B w⟫_𝕜 * ⟪w, x⟫_𝕜) • v, (⟪w, B v⟫_𝕜 * ⟪v, x⟫_𝕜) • w⟫_𝕜 = 0 := by
    rw [inner_smul_left, inner_smul_right, hvw, mul_zero, mul_zero]
  have hsq : ‖offDiagonalPart v w B x‖ ^ 2 =
      (‖⟪v, B w⟫_𝕜‖ * ‖⟪w, x⟫_𝕜‖) ^ 2 + (‖⟪w, B v⟫_𝕜‖ * ‖⟪v, x⟫_𝕜‖) ^ 2 := by
    rw [offDiagonalPart_apply, sq, norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _ horth,
      norm_smul, norm_smul, hv, hw, norm_mul, norm_mul]
    ring
  have h1 : (‖⟪v, B w⟫_𝕜‖ * ‖⟪w, x⟫_𝕜‖) ^ 2 ≤ (m * ‖⟪w, x⟫_𝕜‖) ^ 2 := by
    gcongr
    exact le_max_left _ _
  have h2 : (‖⟪w, B v⟫_𝕜‖ * ‖⟪v, x⟫_𝕜‖) ^ 2 ≤ (m * ‖⟪v, x⟫_𝕜‖) ^ 2 := by
    gcongr
    exact le_max_right _ _
  have h3 : ‖offDiagonalPart v w B x‖ ^ 2 ≤ (m * ‖x‖) ^ 2 := by
    rw [hsq]
    nlinarith [sq_nonneg m]
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp h3

/-- **The off-diagonal part in an eigenbasis, `o(i) ≤ ‖[P M_i P, P M_j P]‖ / δλ_j`.** Let `A` be
self-adjoint with `A v = r v`, `A w = s w`, `r ≠ s`, for an orthonormal pair `v`, `w`. Then the
off-diagonal part of any `B` in this pair has norm at most `‖[A, B]‖ / |r - s|`. With
`A = P M_j P` and `B = P M_i P` this is Hastings, arXiv:cond-mat/0508554v3, `proj3new.tex`,
lines 1683–1690. -/
theorem norm_offDiagonalPart_le_norm_commutator_div {A : E →L[𝕜] E} (hA : IsSelfAdjoint A)
    (B : E →L[𝕜] E) {v w : E} (hv : ‖v‖ = 1) (hw : ‖w‖ = 1) (hvw : ⟪v, w⟫_𝕜 = 0) {r s : ℝ}
    (hAv : A v = (r : 𝕜) • v) (hAw : A w = (s : 𝕜) • w) (hrs : r ≠ s) :
    ‖offDiagonalPart v w B‖ ≤ ‖A * B - B * A‖ / |r - s| := by
  refine (norm_offDiagonalPart_le hv hw hvw B).trans (max_le ?_ ?_)
  · simpa [hv, hw] using norm_inner_le_norm_commutator_div hA B hAv hAw hrs
  · simpa [hv, hw, abs_sub_comm] using norm_inner_le_norm_commutator_div hA B hAw hAv hrs.symm

/-- **The sum of the off-diagonal parts.** In an eigenbasis of `A` with eigenvalue difference
`δλ = |r - s| > 0`, `∑ᵢ o(i) ≤ (∑ᵢ ‖[A, Bᵢ]‖) / δλ` for any finite family `Bᵢ`. With
`A = P M_j P`, `Bᵢ = P M_i P` and the decay of the low-energy commutators in `d(i, j)`
(`norm_groundCompression_commutator_le_graphNeighborhood`), this is the step from the bound on
each `o(i)` to eq. `oibu`, Hastings, arXiv:cond-mat/0508554v3, `proj3new.tex`, lines 1689–1694. -/
theorem sum_norm_offDiagonalPart_le {ι : Type*} (t : Finset ι) {A : E →L[𝕜] E}
    (hA : IsSelfAdjoint A) (B : ι → E →L[𝕜] E) {v w : E} (hv : ‖v‖ = 1) (hw : ‖w‖ = 1)
    (hvw : ⟪v, w⟫_𝕜 = 0) {r s : ℝ} (hAv : A v = (r : 𝕜) • v) (hAw : A w = (s : 𝕜) • w)
    (hrs : r ≠ s) :
    ∑ i ∈ t, ‖offDiagonalPart v w (B i)‖ ≤ (∑ i ∈ t, ‖A * B i - B i * A‖) / |r - s| := by
  rw [Finset.sum_div]
  exact Finset.sum_le_sum fun i _ =>
    norm_offDiagonalPart_le_norm_commutator_div hA (B i) hv hw hvw hAv hAw hrs

omit [CompleteSpace E] in
/-- **Eq. `low` up to `o(i)`.** Let `P` be the orthogonal projection onto a closed subspace `K`
with `v ∈ K` a unit vector, `⟨v, w⟩ = 0`, and every vector `u` of `K` equal to
`⟨v, u⟩ v + ⟨w, u⟩ w`, as when `v`, `w` is an orthonormal pair spanning `K`. Then for every `M`,
`‖M v - ⟨v, M v⟩ v‖ ≤ ‖(1 - P) M v‖ + ‖o‖`, where `o` is the off-diagonal part of `P M P` in the
pair. Hastings, arXiv:cond-mat/0508554v3, `proj3new.tex`, lines 476–491; the first term is the
one bounded by eq. `facld` (`norm_sub_starProjection_apply_le_of_gaussianFilteredTerm`). -/
theorem norm_apply_sub_inner_smul_le_add_offDiagonalPart (K : Submodule 𝕜 E)
    [K.HasOrthogonalProjection] {v w : E} (hv : ‖v‖ = 1) (hvw : ⟪v, w⟫_𝕜 = 0)
    (hvK : v ∈ K) (hspan : ∀ u ∈ K, u = ⟪v, u⟫_𝕜 • v + ⟪w, u⟫_𝕜 • w) (M : E →L[𝕜] E) :
    ‖M v - ⟪v, M v⟫_𝕜 • v‖ ≤
      ‖M v - K.starProjection (M v)‖ +
        ‖offDiagonalPart v w (K.starProjection * M * K.starProjection)‖ := by
  set P := K.starProjection
  have hPv : P v = v := K.starProjection_eq_self_iff.mpr hvK
  have hsa : ∀ x y, ⟪x, P y⟫_𝕜 = ⟪P x, y⟫_𝕜 := fun x y =>
    (K.starProjection_isSymmetric x y).symm
  have hdecomp := hspan (P (M v)) (K.starProjection_apply_mem _)
  have hvv : ⟪v, P (M v)⟫_𝕜 = ⟪v, M v⟫_𝕜 := by rw [hsa, hPv]
  have hoff : offDiagonalPart v w (P * M * P) v = ⟪w, P (M v)⟫_𝕜 • w := by
    rw [offDiagonalPart_apply, inner_eq_zero_symm.mp hvw, inner_self_eq_norm_sq_to_K, hv]
    simp [hPv]
  have hP : P (M v) - ⟪v, M v⟫_𝕜 • v = ⟪w, P (M v)⟫_𝕜 • w := by
    nth_rw 1 [hdecomp]
    rw [hvv]
    abel
  have hsplit : M v - ⟪v, M v⟫_𝕜 • v =
      (M v - P (M v)) + offDiagonalPart v w (P * M * P) v := by
    rw [hoff, ← hP]
    abel
  rw [hsplit]
  refine (norm_add_le _ _).trans (add_le_add le_rfl ?_)
  simpa [hv] using (offDiagonalPart v w (P * M * P)).le_opNorm v

end LowEnergyBasis

end TwoLevel

section SimpleSpectrum

open scoped InnerProductSpace

namespace LowEnergyBasis

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  {n : ℕ} [NeZero n]

/-- The cyclic shift by `k` of the off-diagonal part of `B` in the family `v`:
`∑_a ⟨v_a, B v_{a+k}⟩ |v_a⟩⟨v_{a+k}|`. -/
noncomputable def shiftPart (v : Fin n → E) (B : E →L[𝕜] E) (k : Fin n) : E →L[𝕜] E :=
  ∑ a, ⟪v a, B (v (a + k))⟫_𝕜 • InnerProductSpace.rankOne 𝕜 (v a) (v (a + k))

omit [NeZero n] in
theorem shiftPart_apply (v : Fin n → E) (B : E →L[𝕜] E) (k : Fin n) (x : E) :
    shiftPart v B k x = ∑ a, (⟪v a, B (v (a + k))⟫_𝕜 * ⟪v (a + k), x⟫_𝕜) • v a := by
  simp [shiftPart, InnerProductSpace.rankOne_apply, smul_smul]

/-- **The norm of a cyclic shift.** For an orthonormal family `v`, if every element
`⟨v_a, B v_{a+k}⟩` has norm at most `m`, then the shift by `k` has norm at most `m`. -/
theorem norm_shiftPart_le {v : Fin n → E} (hv : Orthonormal 𝕜 v) (B : E →L[𝕜] E) (k : Fin n)
    {m : ℝ} (hm : 0 ≤ m) (hB : ∀ a, ‖⟪v a, B (v (a + k))⟫_𝕜‖ ≤ m) :
    ‖shiftPart v B k‖ ≤ m := by
  refine ContinuousLinearMap.opNorm_le_bound _ hm fun x => ?_
  set l : Fin n → 𝕜 := fun a => ⟪v a, B (v (a + k))⟫_𝕜 * ⟪v (a + k), x⟫_𝕜
  have hsq : ‖shiftPart v B k x‖ ^ 2 = ∑ a, ‖l a‖ ^ 2 := by
    rw [shiftPart_apply, ← inner_self_eq_norm_sq (𝕜 := 𝕜), hv.inner_sum l l Finset.univ]
    simp only [RCLike.conj_mul, map_sum]
    norm_cast
  have hle : ∑ a, ‖l a‖ ^ 2 ≤ m ^ 2 * ∑ a, ‖⟪v (a + k), x⟫_𝕜‖ ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun a _ => ?_
    simp only [l, norm_mul, mul_pow]
    gcongr
    exact hB a
  have hshift : ∑ a, ‖⟪v (a + k), x⟫_𝕜‖ ^ 2 = ∑ b, ‖⟪v b, x⟫_𝕜‖ ^ 2 :=
    Fintype.sum_equiv (Equiv.addRight k) _ _ fun _ => rfl
  have hbessel := hv.sum_inner_products_le (s := Finset.univ) (x := x)
  have h : ‖shiftPart v B k x‖ ^ 2 ≤ (m * ‖x‖) ^ 2 := by
    rw [hsq, mul_pow]
    calc ∑ a, ‖l a‖ ^ 2 ≤ m ^ 2 * ∑ b, ‖⟪v b, x⟫_𝕜‖ ^ 2 := hshift ▸ hle
      _ ≤ m ^ 2 * ‖x‖ ^ 2 := by gcongr
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp h

/-- The off-diagonal part of `B` in the family `v`, the sum of the cyclic shifts by `k ≠ 0`:
the operator with the same off-diagonal elements `⟨v_a, B v_b⟩`, `a ≠ b`, as `B` and zeros on the
diagonal. Hastings, arXiv:cond-mat/0508554v3, `proj3new.tex`, lines 476–480. -/
noncomputable def offDiagonalPartFamily (v : Fin n → E) (B : E →L[𝕜] E) : E →L[𝕜] E :=
  ∑ k ∈ Finset.univ.erase 0, shiftPart v B k

/-- **The norm of the off-diagonal part.** For an orthonormal family `v : Fin n → E`, if every
off-diagonal element `⟨v_a, B v_b⟩`, `a ≠ b`, has norm at most `m`, then the off-diagonal part
of `B` has norm at most `(n - 1) m`. -/
theorem norm_offDiagonalPartFamily_le {v : Fin n → E} (hv : Orthonormal 𝕜 v) (B : E →L[𝕜] E)
    {m : ℝ} (hm : 0 ≤ m) (hB : ∀ a b, a ≠ b → ‖⟪v a, B (v b)⟫_𝕜‖ ≤ m) :
    ‖offDiagonalPartFamily v B‖ ≤ (n - 1 : ℕ) * m := by
  refine (norm_sum_le _ _).trans ?_
  have hcard : (Finset.univ.erase (0 : Fin n)).card = n - 1 := by simp
  calc ∑ k ∈ Finset.univ.erase 0, ‖shiftPart v B k‖
      ≤ ∑ _k ∈ Finset.univ.erase (0 : Fin n), m := by
        refine Finset.sum_le_sum fun k hk => norm_shiftPart_le hv B k hm fun a => hB _ _ ?_
        intro h
        exact (Finset.ne_of_mem_erase hk) (by simpa using h)
    _ = (n - 1 : ℕ) * m := by rw [Finset.sum_const, hcard, nsmul_eq_mul]

/-- **The off-diagonal part in an eigenbasis with simple spectrum, `o ≤ (n - 1) ‖[A, B]‖ / δ`.**
Let `A` be self-adjoint with `A v_a = r_a v_a` for an orthonormal family `v : Fin n → E`, with
eigenvalues pairwise at least `δ > 0` apart. Then the off-diagonal part of any `B` in this family
has norm at most `(n - 1) ‖[A, B]‖ / δ`. With `A = P M_j P` and `B = P M_i P` this is the bound on
`o(i)` of Hastings, arXiv:cond-mat/0508554v3, `proj3new.tex`, lines 1683–1705, for a compression
`P M_j P` with simple spectrum on the ground space. -/
theorem norm_offDiagonalPartFamily_le_norm_commutator_div [CompleteSpace E] {A : E →L[𝕜] E}
    (hA : IsSelfAdjoint A) (B : E →L[𝕜] E) {v : Fin n → E} (hv : Orthonormal 𝕜 v) {r : Fin n → ℝ}
    (hAv : ∀ a, A (v a) = (r a : 𝕜) • v a) {δ : ℝ} (hδ : 0 < δ)
    (hgap : ∀ a b, a ≠ b → δ ≤ |r a - r b|) :
    ‖offDiagonalPartFamily v B‖ ≤ (n - 1 : ℕ) * (‖A * B - B * A‖ / δ) := by
  refine norm_offDiagonalPartFamily_le hv B (by positivity) fun a b hab => ?_
  have hrs : r a ≠ r b := fun h => by
    have := hgap a b hab
    rw [h, sub_self, abs_zero] at this
    linarith
  have h := norm_inner_le_norm_commutator_div hA B (hAv a) (hAv b) hrs
  rw [(hv.1 a), (hv.1 b), mul_one, mul_one] at h
  exact h.trans (div_le_div_of_nonneg_left (norm_nonneg _) hδ (hgap a b hab))

/-- **The sum of the off-diagonal parts.** In an eigenbasis of `A` with eigenvalue spacing at
least `δ > 0`, `∑ᵢ o(i) ≤ (n - 1) (∑ᵢ ‖[A, Bᵢ]‖) / δ` for any finite family `Bᵢ`. With
`A = P M_j P` and `Bᵢ = P M_i P`, this is the step from the bound on each `o(i)` to eq. `oibu`,
Hastings, arXiv:cond-mat/0508554v3, `proj3new.tex`, lines 1689–1705. -/
theorem sum_norm_offDiagonalPartFamily_le [CompleteSpace E] {ι : Type*} (t : Finset ι)
    {A : E →L[𝕜] E} (hA : IsSelfAdjoint A) (B : ι → E →L[𝕜] E) {v : Fin n → E}
    (hv : Orthonormal 𝕜 v)
    {r : Fin n → ℝ} (hAv : ∀ a, A (v a) = (r a : 𝕜) • v a) {δ : ℝ} (hδ : 0 < δ)
    (hgap : ∀ a b, a ≠ b → δ ≤ |r a - r b|) :
    ∑ i ∈ t, ‖offDiagonalPartFamily v (B i)‖ ≤
      (n - 1 : ℕ) * ((∑ i ∈ t, ‖A * B i - B i * A‖) / δ) := by
  rw [Finset.sum_div, Finset.mul_sum]
  exact Finset.sum_le_sum fun i _ =>
    norm_offDiagonalPartFamily_le_norm_commutator_div hA (B i) hv hAv hδ hgap

/-- The off-diagonal part applied to a basis vector: `o v_a = ∑_{b ≠ a} ⟨v_b, B v_a⟩ v_b`. -/
theorem offDiagonalPartFamily_apply_self {v : Fin n → E} (hv : Orthonormal 𝕜 v)
    (B : E →L[𝕜] E) (a : Fin n) :
    offDiagonalPartFamily v B (v a) = ∑ b ∈ Finset.univ.erase a, ⟪v b, B (v a)⟫_𝕜 • v b := by
  have hshift (k : Fin n) : shiftPart v B k (v a) = ⟪v (a - k), B (v a)⟫_𝕜 • v (a - k) := by
    rw [shiftPart_apply]
    have hterm (b : Fin n) : (⟪v b, B (v (b + k))⟫_𝕜 * ⟪v (b + k), v a⟫_𝕜) • v b =
        if b = a - k then ⟪v (a - k), B (v a)⟫_𝕜 • v (a - k) else 0 := by
      rw [orthonormal_iff_ite.mp hv]
      by_cases hb : b = a - k
      · subst hb
        simp
      · have : b + k ≠ a := fun h => hb (eq_sub_of_add_eq h)
        simp [this, hb]
    simp_rw [hterm]
    simp
  rw [offDiagonalPartFamily, sum_apply]
  simp_rw [hshift]
  refine Finset.sum_nbij' (fun k => a - k) (fun b => a - b) ?_ ?_ ?_ ?_ ?_
  · intro k hk
    simp only [Finset.mem_erase, Finset.mem_univ, and_true] at hk ⊢
    intro h
    exact hk (by simpa using (sub_eq_self.mp h))
  · intro b hb
    simp only [Finset.mem_erase, Finset.mem_univ, and_true] at hb ⊢
    intro h
    exact hb (sub_eq_zero.mp h).symm
  · intro k _
    simp
  · intro b _
    simp
  · intro k _
    rfl

/-- **Eq. `low` up to `o` for every basis vector.** Let `P` be the orthogonal projection onto a
closed subspace `K` with orthonormal basis `v : Fin n → E`, so that every `u ∈ K` equals
`∑_b ⟨v_b, u⟩ v_b`. Then for every `M` and every `a`,
`‖M v_a - ⟨v_a, M v_a⟩ v_a‖ ≤ ‖(1 - P) M v_a‖ + ‖o‖`, where `o` is the off-diagonal part of
`P M P` in the basis. Hastings, arXiv:cond-mat/0508554v3, `proj3new.tex`, lines 476–491; the
first term is the one bounded by eq. `facld`
(`norm_sub_starProjection_apply_le_of_gaussianFilteredTerm`). -/
theorem norm_apply_sub_inner_smul_le_add_offDiagonalPartFamily [CompleteSpace E]
    (K : Submodule 𝕜 E) [K.HasOrthogonalProjection] {v : Fin n → E} (hv : Orthonormal 𝕜 v)
    (hvK : ∀ b, v b ∈ K) (hspan : ∀ u ∈ K, u = ∑ b, ⟪v b, u⟫_𝕜 • v b) (M : E →L[𝕜] E)
    (a : Fin n) :
    ‖M (v a) - ⟪v a, M (v a)⟫_𝕜 • v a‖ ≤
      ‖M (v a) - K.starProjection (M (v a))‖ +
        ‖offDiagonalPartFamily v (K.starProjection * M * K.starProjection)‖ := by
  set P := K.starProjection
  have hPv : P (v a) = v a := K.starProjection_eq_self_iff.mpr (hvK a)
  have hsym : ∀ x y, ⟪x, P y⟫_𝕜 = ⟪P x, y⟫_𝕜 := fun x y =>
    (K.starProjection_isSymmetric x y).symm
  have hsa (b : Fin n) : ⟪v b, P (M (v a))⟫_𝕜 = ⟪v b, M (v a)⟫_𝕜 := by
    have hPb : P (v b) = v b := K.starProjection_eq_self_iff.mpr (hvK b)
    rw [hsym, hPb]
  have hdecomp := hspan (P (M (v a))) (K.starProjection_apply_mem _)
  have hoff : offDiagonalPartFamily v (P * M * P) (v a) =
      P (M (v a)) - ⟪v a, M (v a)⟫_𝕜 • v a := by
    rw [offDiagonalPartFamily_apply_self hv]
    have hPMP (b : Fin n) : ⟪v b, (P * M * P) (v a)⟫_𝕜 = ⟪v b, P (M (v a))⟫_𝕜 := by
      simp [hPv]
    simp_rw [hPMP]
    conv_rhs => rw [hdecomp, ← Finset.add_sum_erase _ _ (Finset.mem_univ a), hsa a]
    abel
  have hsplit : M (v a) - ⟪v a, M (v a)⟫_𝕜 • v a =
      (M (v a) - P (M (v a))) + offDiagonalPartFamily v (P * M * P) (v a) := by
    rw [hoff]
    abel
  rw [hsplit]
  refine (norm_add_le _ _).trans (add_le_add le_rfl ?_)
  simpa [hv.1 a] using (offDiagonalPartFamily v (P * M * P)).le_opNorm (v a)

end LowEnergyBasis

end SimpleSpectrum
