/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import Mathlib.RingTheory.RootsOfUnity.Complex
import QICLean.Channel.ChoiTypeMap
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
The main result of this first slice is the exact `V₂` assertion: `A_γ` has
Schmidt number at most two and is therefore positive semidefinite.  Ha's later
rank-one decomposition of the block transpose, the Eom--Kye factor shuffle,
and the negative pairing with the Choi-type map remain separate steps.

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

/-- Ha's integer
\(m_k=\frac32(3^{k-1}-1)\), in zero-based indexing.

This is the exponent introduced on Ha 1998, p. 593, immediately before
equation (2.2). -/
def haExponent (k : Fin d) : ℕ :=
  3 * (3 ^ (k : ℕ) - 1) / 2

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

/-- The phase-vector relation `a_{i,k} = ω_i ^ (-m_k) • a_{i,1}` from
Ha 1998, p. 593. -/
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

/-- Each `z_{r,i}` is 2-simple in Ha's terminology: its coefficient-matrix
columns lie in the span of `a_{i,1}` and `c_r ∘ a_{i,r}`.

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

end Matrix
