/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Algebra.OperatorSchmidt
import QICLean.Channel.SchmidtRank

/-!
# Schmidt rank after application of an operator

Applying a finite bipartite operator increases a vector's Schmidt rank by at
most the operator-Schmidt rank. The proof uses a minimal product decomposition
of the operator and a rank factorization of the vector's coefficient matrix.
Both tensor factors may be empty, and the zero vector is included. No
normalization, positivity, spectral or independence assumption is required.
Iterating an operator of operator-Schmidt rank at most `D` gives the bound
`schmidtRank (K ^ r *ᵥ ψ) ≤ D ^ r * schmidtRank ψ`.

This is the algebraic rank-growth implication used with AKLV,
arXiv:1301.1162v1, Definition def:AGSP, lines 296–314, and LVV,
arXiv:1307.5143v1, Claim c:errorreduction, equation e:decomp, lines 579–588.
The spectral and entropy estimates in approximate ground-space projection
arguments are separate results.
-/

open scoped BigOperators Kronecker Matrix

namespace Matrix

/-- The coefficient matrix uses the original product-index order. The right
factor acts by ordinary transpose, not conjugate transpose. -/
private theorem schmidtCoeffMatrix_kronecker_mulVec
    {m n : Type*} [Fintype m] [Fintype n]
    (A : Matrix m m ℂ) (B : Matrix n n ℂ) (ψ : m × n → ℂ) :
    schmidtCoeffMatrix ((A ⊗ₖ B) *ᵥ ψ) =
      A * schmidtCoeffMatrix ψ * Bᵀ := by
  rw [Matrix.mul_assoc]
  ext i j
  simp only [schmidtCoeffMatrix_apply, Matrix.mulVec, dotProduct,
    Fintype.sum_prod_type, Matrix.kroneckerMap_apply, Matrix.mul_apply,
    Matrix.transpose_apply, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  ac_rfl

/-- A finite sum of products factors through the product of the summand index
and the common inner matrix index. Empty index types are included. -/
private theorem sum_mul_factor_through_product
    {m n ι κ : Type*} [Fintype m] [Fintype n] [Fintype ι] [Fintype κ]
    (A : ι → Matrix m m ℂ) (B : ι → Matrix n n ℂ)
    (P : Matrix m κ ℂ) (Q : Matrix κ n ℂ) :
    (∑ t, A t * P * (Q * (B t)ᵀ)) =
      (Matrix.of (fun i (z : ι × κ) ↦ (A z.1 * P) i z.2) : Matrix m (ι × κ) ℂ) *
        (Matrix.of (fun (z : ι × κ) j ↦ (Q * (B z.1)ᵀ) z.2 j) : Matrix (ι × κ) n ℂ) := by
  ext i j
  simp only [Matrix.sum_apply, Matrix.mul_apply, Fintype.sum_prod_type, Matrix.of_apply]

/-- Applying a bipartite operator increases a vector's Schmidt rank by at most
its operator-Schmidt rank. AKLV, arXiv:1301.1162v1, Definition def:AGSP,
lines 296–314; LVV, arXiv:1307.5143v1, equation e:decomp, lines 584–588.
Empty tensor factors and the zero vector are included. -/
theorem schmidtRank_mulVec_le
    {m n : Type*} [Fintype m] [Fintype n]
    (K : Matrix (m × n) (m × n) ℂ) (ψ : m × n → ℂ) :
    schmidtRank (K *ᵥ ψ) ≤ operatorSchmidtRank K * schmidtRank ψ := by
  classical
  obtain ⟨A, B, hK⟩ := hasOperatorSchmidtDecomposition_operatorSchmidtRank K
  obtain ⟨P, Q, hPQ⟩ := exists_mul_eq_of_rank_le
    (k := schmidtRank ψ) (schmidtCoeffMatrix ψ) (le_refl _)
  let L : Matrix m (Fin (operatorSchmidtRank K) × Fin (schmidtRank ψ)) ℂ :=
    Matrix.of fun i z ↦ (A z.1 * P) i z.2
  let R : Matrix (Fin (operatorSchmidtRank K) × Fin (schmidtRank ψ)) n ℂ :=
    Matrix.of fun z j ↦ (Q * (B z.1)ᵀ) z.2 j
  have hcoeff : schmidtCoeffMatrix (K *ᵥ ψ) =
      ∑ t, A t * schmidtCoeffMatrix ψ * (B t)ᵀ := by
    conv_lhs => rw [hK]
    rw [Matrix.sum_mulVec]
    ext i j
    simp only [schmidtCoeffMatrix_apply, Finset.sum_apply, Matrix.sum_apply]
    apply Finset.sum_congr rfl
    intro t _
    exact congrFun (congrFun
      (schmidtCoeffMatrix_kronecker_mulVec (A t) (B t) ψ) i) j
  have hfactor : schmidtCoeffMatrix (K *ᵥ ψ) = L * R := by
    calc
      schmidtCoeffMatrix (K *ᵥ ψ) =
          ∑ t, A t * schmidtCoeffMatrix ψ * (B t)ᵀ := hcoeff
      _ = ∑ t, A t * P * (Q * (B t)ᵀ) := by
        apply Finset.sum_congr rfl
        intro t _
        rw [← hPQ]
        simp only [Matrix.mul_assoc]
      _ = L * R := by
        simpa only [L, R] using sum_mul_factor_through_product A B P Q
  change (schmidtCoeffMatrix (K *ᵥ ψ)).rank ≤
    operatorSchmidtRank K * schmidtRank ψ
  rw [hfactor]
  refine (Matrix.rank_mul_le_left L R).trans ?_
  simpa only [Fintype.card_prod, Fintype.card_fin] using
    Matrix.rank_le_card_width L

open Classical in
/-- Powers of one bipartite operator give multiplicative Schmidt-rank growth.
AKLV, arXiv:1301.1162v1, Definition 2.1 (`def:AGSP`) and Corollary 2.4
(`col:half`); the rank-tail entropy argument is at lines 1059–1075.
Empty factors, zero powers and the zero input are included. -/
theorem schmidtRank_pow_mulVec_le
    {m n : Type*} [Fintype m] [Fintype n]
    (K : Matrix (m × n) (m × n) ℂ) (ψ : m × n → ℂ)
    {D : ℕ} (hD : operatorSchmidtRank K ≤ D) (r : ℕ) :
    schmidtRank ((K ^ r) *ᵥ ψ) ≤ D ^ r * schmidtRank ψ := by
  induction r with
  | zero => simp
  | succ r ih =>
    simpa only [pow_succ', ← mulVec_mulVec, Nat.mul_assoc] using
      (schmidtRank_mulVec_le K ((K ^ r) *ᵥ ψ)).trans (Nat.mul_le_mul hD ih)

end Matrix
