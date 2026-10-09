/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import Mathlib.Analysis.CStarAlgebra.Matrix

/-!
# Operator norms in arbitrary orthonormal coordinates

Changing the input and output coordinates by orthonormal bases conjugates a
continuous linear map by linear isometric equivalences. Its matrix therefore
has exactly the same Euclidean operator norm. No relation between the input and
output dimensions is required.
-/

noncomputable section
open scoped Matrix.Norms.L2Operator
open ContinuousLinearMap

namespace ContinuousLinearMap

variable {𝕜 E F m n : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
  [Fintype m] [Fintype n] [DecidableEq n]

/-- Passing to arbitrary finite orthonormal coordinates preserves the operator norm. -/
theorem norm_toMatrix_orthonormal (T : E →L[𝕜] F)
    (bIn : OrthonormalBasis n 𝕜 E) (bOut : OrthonormalBasis m 𝕜 F) :
    ‖LinearMap.toMatrix bIn.toBasis bOut.toBasis T.toLinearMap‖ = ‖T‖ := by
  classical
  let C : EuclideanSpace 𝕜 n →L[𝕜] EuclideanSpace 𝕜 m :=
    (bOut.repr : F →L[𝕜] EuclideanSpace 𝕜 m) ∘L T ∘L
      (bIn.repr.symm : EuclideanSpace 𝕜 n →L[𝕜] E)
  have hM : LinearMap.toMatrix bIn.toBasis bOut.toBasis T.toLinearMap =
      Matrix.toEuclideanLin.symm C.toLinearMap := by
    rw [Matrix.toEuclideanLin_eq_toLin_orthonormal]
    ext i j
    simp [LinearMap.toMatrix_apply, C]
  rw [hM, Matrix.l2_opNorm_def, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply]
  change ‖C‖ = ‖T‖
  dsimp only [C]
  rw [opNorm_linearIsometryEquiv_comp, opNorm_comp_linearIsometryEquiv]

end ContinuousLinearMap
