/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Algebra.Matrix.InvariantBlocks
import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.Order.Star.Rat
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-!
# Tests and axiom guard for `QICLean.Algebra.Matrix.InvariantBlocks`

Verifies:
1. Multi-block non-contiguous fiber transport over `ℚ` (5×5 matrix with 3 fibers of
   sizes 1, 2, 2 transported onto 2 canonical representatives of sizes 1 and 2,
   including nontrivial permutation transport).
2. Global symmetry orbit transport (`posSemidef_of_global_orbit_transport`) over `ℂ`.
3. Congruence block-diagonal reduction (`posSemidef_of_mul_blockDiagonal'_conjTranspose`)
   splitting an `S_2`-invariant 3×3 matrix into 2×2 trivial and 1×1 antisymmetric sectors.
4. Strict axiom guard allowing only `propext`, `Classical.choice`, and `Quot.sound`.
-/

open scoped Matrix ComplexOrder

namespace InvariantBlocksTest

/-! ## 1. Nontrivial 5×5 multi-block transport over ℚ -/

/-- Three non-contiguous fibers in `Fin 5`: `{0}`, `{1, 3}`, `{2, 4}`. -/
def testKey : Fin 5 → Fin 3
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 1
  | 4 => 2

/-- Two orbit types: fiber 0 maps to type 0 (size 1); fibers 1 and 2 both map to type 1 (size 2). -/
abbrev testRepIdx : Fin 3 → Fin 2
  | 0 => 0
  | 1 => 1
  | 2 => 1

abbrev testRepDim : Fin 2 → Type
  | 0 => Fin 1
  | 1 => Fin 2

/-- Representative 0 is `[5]`; representative 1 is `[[2, 1], [1, 2]]`. -/
def testRep : ∀ t : Fin 2, Matrix (testRepDim t) (testRepDim t) ℚ
  | 0 => !![5]
  | 1 => !![2, 1; 1, 2]

/-- Explicit 5×5 matrix supported on the three fibers, with fiber 2 reversed relative to fiber 1. -/
def testMat : Matrix (Fin 5) (Fin 5) ℚ :=
  !![5, 0, 0, 0, 0;
     0, 2, 0, 1, 0;
     0, 0, 2, 0, 1;
     0, 1, 0, 2, 0;
     0, 0, 1, 0, 2]

/-- Explicit fiber-to-representative equivalences, reversing fiber 2 (`2 ↦ 1, 4 ↦ 0`). -/
def testTransport : ∀ k : Fin 3, {i : Fin 5 // testKey i = k} ≃ testRepDim (testRepIdx k)
  | 0 =>
    { toFun := fun _ ↦ 0
      invFun := fun _ ↦ ⟨0, rfl⟩
      left_inv := fun ⟨i, hi⟩ ↦ by
        fin_cases i <;> first | rfl | exact absurd hi (by decide)
      right_inv := fun j ↦ by fin_cases j; rfl }
  | 1 =>
    { toFun := fun ⟨i, _⟩ ↦ if i = 1 then 0 else 1
      invFun := fun j ↦ if j = 0 then ⟨1, rfl⟩ else ⟨3, rfl⟩
      left_inv := fun ⟨i, hi⟩ ↦ by
        fin_cases i <;> first | rfl | exact absurd hi (by decide)
      right_inv := fun j ↦ by fin_cases j <;> rfl }
  | 2 =>
    { toFun := fun ⟨i, _⟩ ↦ if i = 4 then 0 else 1
      invFun := fun j ↦ if j = 0 then ⟨4, rfl⟩ else ⟨2, rfl⟩
      left_inv := fun ⟨i, hi⟩ ↦ by
        fin_cases i <;> first | rfl | exact absurd hi (by decide)
      right_inv := fun j ↦ by fin_cases j <;> rfl }

theorem testRep_posSemidef : ∀ t : Fin 2, (testRep t).PosSemidef := by
  intro t
  match t with
  | 0 =>
    refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ ?_
    · ext i j
      fin_cases i; fin_cases j
      simp [testRep]
    · intro x
      have h : star x ⬝ᵥ (testRep 0).mulVec x = 5 * (x 0) ^ 2 := by
        simp [testRep, dotProduct, Matrix.mulVec]
        ring
      rw [h]
      positivity
  | 1 =>
    refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ ?_
    · ext i j
      fin_cases i <;> fin_cases j <;> simp [testRep]
    · intro x
      have h : star x ⬝ᵥ (testRep 1).mulVec x =
          (x 0 + x 1) ^ 2 + (x 0) ^ 2 + (x 1) ^ 2 := by
        simp [testRep, dotProduct, Matrix.mulVec, Fin.sum_univ_two]
        ring
      rw [h]
      positivity

theorem testMat_posSemidef : testMat.PosSemidef := by
  refine Matrix.posSemidef_of_fiber_transport testKey testMat ?_ testRepIdx testRepDim
    testRep testTransport ?_ testRep_posSemidef
  · intro i j hij
    fin_cases i <;> fin_cases j <;> first | rfl | exact absurd rfl hij
  · intro k ⟨i, hi⟩ ⟨j, hj⟩
    match k with
    | 0 =>
      fin_cases i <;> fin_cases j <;>
        first | exact absurd hi (by decide) | exact absurd hj (by decide) | rfl
    | 1 =>
      fin_cases i <;> fin_cases j <;>
        first | exact absurd hi (by decide) | exact absurd hj (by decide) | rfl
    | 2 =>
      fin_cases i <;> fin_cases j <;>
        first | exact absurd hi (by decide) | exact absurd hj (by decide) | rfl

/-! ## 2. Global orbit symmetry transport over ℂ -/

/-- A 4×4 complex matrix on `Fin 2 × Fin 2` whose two fibers under `Prod.fst` are swapped
by the global involution `(a, b) ↦ (1 - a, 1 - b)`. -/
def symKey : Fin 2 × Fin 2 → Fin 2 := Prod.fst

def symMat : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  fun x y ↦
    if x.1 = y.1 then
      if x.2 = y.2 then (2 : ℂ) else (1 : ℂ)
    else 0

def flipGlobal : Fin 2 → (Fin 2 × Fin 2 ≃ Fin 2 × Fin 2)
  | 0 => Equiv.refl _
  | 1 => (Equiv.swap (0 : Fin 2) 1).prodCongr (Equiv.swap (0 : Fin 2) 1)

theorem symMat_posSemidef : symMat.PosSemidef := by
  refine Matrix.posSemidef_of_global_orbit_transport symKey symMat
    (fun i j hij ↦ by simp only [symMat, symKey] at hij ⊢; simp [hij])
    (fun _ ↦ (0 : Fin 1)) (fun _ ↦ (0 : Fin 2)) flipGlobal ?_ ?_ ?_
  · intro k ⟨a, b⟩
    fin_cases k <;> fin_cases a <;> fin_cases b <;> simp [symKey, flipGlobal]
  · intro k ⟨a1, b1⟩ ⟨a2, b2⟩ h1 h2
    fin_cases k <;> fin_cases a1 <;> fin_cases b1 <;> fin_cases a2 <;> fin_cases b2 <;>
      simp_all [symKey, symMat, flipGlobal]
  · intro t
    fin_cases t
    refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ ?_
    · ext ⟨⟨a1, b1⟩, h1⟩ ⟨⟨a2, b2⟩, h2⟩
      fin_cases a1 <;> fin_cases b1 <;> fin_cases a2 <;> fin_cases b2 <;>
        simp_all [symKey, symMat, Matrix.fiberBlock]
    · intro x
      let v0 : ℂ := x ⟨(0, 0), rfl⟩
      let v1 : ℂ := x ⟨(0, 1), rfl⟩
      have h : star x ⬝ᵥ (Matrix.fiberBlock symKey symMat 0).mulVec x =
          star (v0 + v1) * (v0 + v1) + star v0 * v0 + star v1 * v1 := by
        let e : {i : Fin 2 × Fin 2 // symKey i = 0} ≃ Fin 2 :=
          { toFun := fun ⟨p, _⟩ ↦ p.2
            invFun := fun b ↦ ⟨(0, b), rfl⟩
            left_inv := fun ⟨⟨a, b⟩, h⟩ ↦ by fin_cases a; rfl; simp [symKey] at h
            right_inv := fun _ ↦ rfl }
        simp only [dotProduct, Matrix.mulVec, Pi.star_apply, Matrix.fiberBlock_apply]
        rw [Fintype.sum_equiv e _ (fun b ↦ star (x ⟨(0, b), rfl⟩) *
            ∑ j : Fin 2, symMat (0, b) (0, j) * x ⟨(0, j), rfl⟩) (fun p ↦ by
              rcases p with ⟨⟨a, b⟩, ha⟩
              have ha0 : a = 0 := ha
              subst ha0
              rfl)]
        simp only [Fin.sum_univ_two, symMat, ↓reduceIte, zero_ne_one, one_ne_zero, v0, v1, star_add]
        ring
      rw [h]
      exact add_nonneg (add_nonneg (star_mul_self_nonneg _) (star_mul_self_nonneg _))
        (star_mul_self_nonneg _)

/-! ## 3. Stabilizer congruence block-diagonalization over ℚ -/

/-- An `S_2`-invariant 3×3 matrix (swapping indices 1 and 2) that is not block diagonal
in the standard basis, factored as `V * blockDiagonal' B * Vᴴ` with 2×2 and 1×1 blocks. -/
def stabMat : Matrix (Fin 3) (Fin 3) ℚ :=
  !![4, 2, 2;
     2, 3, 1;
     2, 1, 3]

abbrev stabDim : Fin 2 → Type
  | 0 => Fin 2
  | 1 => Fin 1

instance (k : Fin 2) : Fintype (stabDim k) := by
  match k with
  | 0 => infer_instance
  | 1 => infer_instance

def stabBlocks : ∀ k : Fin 2, Matrix (stabDim k) (stabDim k) ℚ
  | 0 => !![4, 2; 2, 2]
  | 1 => !![1]

def stabV : Matrix (Fin 3) (Σ k : Fin 2, stabDim k) ℚ
  | 0, ⟨0, 0⟩ => 1
  | 1, ⟨0, 1⟩ => 1
  | 2, ⟨0, 1⟩ => 1
  | 1, ⟨1, 0⟩ => 1
  | 2, ⟨1, 0⟩ => -1
  | _, _ => 0

theorem stabMat_eq_conj :
    stabMat = stabV * Matrix.blockDiagonal' stabBlocks * stabVᴴ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [stabMat, stabV, stabBlocks, Matrix.mul_apply, Fintype.sum_sigma,
      Fin.sum_univ_two, Matrix.blockDiagonal'_apply] <;>
    norm_num

theorem stabMat_posSemidef : stabMat.PosSemidef := by
  rw [stabMat_eq_conj]
  refine Matrix.posSemidef_of_mul_blockDiagonal'_conjTranspose stabBlocks stabV ?_
  intro k
  match k with
  | 0 =>
    refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ ?_
    · ext i j; fin_cases i <;> fin_cases j <;> simp [stabBlocks]
    · intro x
      have h : star x ⬝ᵥ (stabBlocks 0).mulVec x =
          2 * (x 0 + x 1) ^ 2 + 2 * (x 0) ^ 2 := by
        simp [stabBlocks, dotProduct, Matrix.mulVec, Fin.sum_univ_two]
        ring
      rw [h]
      positivity
  | 1 =>
    refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ ?_
    · ext i j; fin_cases i; fin_cases j; simp [stabBlocks]
    · intro x
      have h : star x ⬝ᵥ (stabBlocks 1).mulVec x = (x 0) ^ 2 := by
        simp [stabBlocks, dotProduct, Matrix.mulVec]
        ring
      rw [h]
      positivity

/-! ## 4. Strict axiom guard -/

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let decls := #[
    ``Matrix.posSemidef_reindex_iff,
    ``Matrix.isHermitian_blockDiagonal'_iff',
    ``Matrix.dotProduct_mulVec_blockDiagonal',
    ``Matrix.posSemidef_blockDiagonal'_iff,
    ``Matrix.posSemidef_blockDiagonal_iff,
    ``Matrix.fiberBlock,
    ``Matrix.fiberBlock_apply,
    ``Matrix.submatrix_sigmaFiberEquiv_eq_blockDiagonal',
    ``Matrix.reindex_sigmaFiberEquiv_symm_eq_blockDiagonal',
    ``Matrix.posSemidef_iff_forall_fiberBlock,
    ``Matrix.posSemidef_iff_forall_fiber_transport,
    ``Matrix.posSemidef_of_fiber_transport,
    ``Matrix.fiberEquivOfGlobalEquiv,
    ``Matrix.fiberEquivOfGlobalEquiv_apply,
    ``Matrix.posSemidef_of_global_orbit_transport,
    ``Matrix.posSemidef_of_mul_blockDiagonal'_conjTranspose,
    ``InvariantBlocksTest.testMat_posSemidef,
    ``InvariantBlocksTest.symMat_posSemidef,
    ``InvariantBlocksTest.stabMat_posSemidef
  ]
  for decl in decls do
    unless (← Lean.getEnv).contains decl do
      throwError "Missing declaration {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"

end InvariantBlocksTest
