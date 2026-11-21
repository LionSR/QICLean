/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Algebra.BigOperators.Group.List.Defs
import Mathlib.Data.List.OfFn
import Mathlib.Data.Matrix.Mul

/-!
# Successive matrix actions

Applying the continuous linear maps of a matrix list from left to right gives
the product of the reversed list. The matrices need not commute or be invertible,
and both the list and the finite coordinate type may be empty.

The ascending application convention occurs in `output` in `openai/math`,
commit `adc7f1241b42e322a6451854ab7e4b4c146bf78a`,
`lean/OAI/MathematicalPhysics/PEPSFilters/Basic.lean`, lines 166–169.
This proof is independently written; no upstream Lean proof text is reused.
-/

namespace Matrix

variable {ι 𝕜 : Type*} [Fintype ι] [DecidableEq ι] [RCLike 𝕜]

/-- Successive applications in list order equal the action of the reverse
matrix product, including the empty list and an empty coordinate type. -/
theorem foldl_toEuclideanCLM_eq_reverse_prod (l : List (Matrix ι ι 𝕜))
    (Ω : EuclideanSpace 𝕜 ι) :
    (l.map (fun A ↦ toEuclideanCLM (n := ι) (𝕜 := 𝕜) A)).foldl (fun ψ T ↦ T ψ) Ω =
      toEuclideanLin l.reverse.prod Ω := by
  rw [List.foldl_map]
  change l.foldl (fun ψ A ↦ toEuclideanLin A ψ) Ω = _
  induction l generalizing Ω with
  | nil => simp [toEuclideanLin]
  | cons A l ih =>
    simp [List.reverse_cons, List.prod_append, ih, toEuclideanLin, toLpLin_mul_same]

end Matrix

section MatrixProductIntertwine

/-!
# Ordered products through a rectangular intertwiner

A common rectangular intertwiner for two ordered families also intertwines
their products. The matrices need not be Hermitian or invertible, and the
intertwiner need not be an isometry. Empty products are included.

Auxiliary to the ordered band products in OpenAI's area-law manuscript,
`06-transport.tex`, lines 57--61 and 120--128, and `07-comparators.tex`,
lines 80--110 and 370--381, revision
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

namespace Matrix

/-- A common rectangular intertwiner preserves an ordered finite product.
Auxiliary to the ordered band-product identities in the area-law manuscript,
`06-transport.tex`, lines 57--61 and 120--128, and `07-comparators.tex`,
lines 80--110 and 370--381. -/
theorem listProd_ofFn_intertwine
    {α m n : Type*} [Semiring α]
    [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    {K : ℕ} {A : Fin K → Matrix m m α} {B : Fin K → Matrix n n α}
    (Z : Matrix m n α) (h : ∀ g, A g * Z = Z * B g) :
    (List.ofFn A).prod * Z = Z * (List.ofFn B).prod := by
  have hprod := List.prod_hom_rel (List.ofFn (id : Fin K → Fin K))
    (r := fun L R ↦ L * Z = Z * R) (f := A) (g := B)
    (by simp only [Matrix.one_mul, Matrix.mul_one]) (by
      intro g L R hLR
      rw [Matrix.mul_assoc, hLR, ← Matrix.mul_assoc, h g, Matrix.mul_assoc])
  simpa only [List.map_ofFn, Function.comp_id] using hprod

end Matrix

end MatrixProductIntertwine
