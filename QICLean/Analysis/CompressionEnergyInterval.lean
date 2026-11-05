/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.CompressionEnergyBounds
import QICLean.Analysis.TensorEnergyMinimum

/-!
# Two-sided intervals for actual compressed minima

A positive scalar lower bound and a nonzero tensor Rayleigh bound determine
an interval containing the least ordered eigenvalue of the actual native
orthogonal compression. This combines the existing lower and upper
variational estimates without any extra nonempty-space hypothesis.
Supporting ALVV, arXiv:1602.08828v2, the energy-estimation argument,
lines 1793–1807.
-/

open scoped TensorProduct InnerProductSpace ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace Matrix

variable {σ F : Type*} [Fintype σ] [DecidableEq σ]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F]

/-- The actual compressed minimum lies between the supplied scalar lower
bound and the tensor Rayleigh upper bound. The nonzero tensor vector
constructs the compression dimension witness. Supporting ALVV,
arXiv:1602.08828v2, Figure `fig:algo1`, line 1631, and lines 1793–1807. -/
theorem IsHermitian.exists_compression_min_between_of_tensor_energy
    {K : Matrix σ σ ℂ} (hK : K.IsHermitian)
    (S : Submodule ℂ (EuclideanSpace ℂ σ)) (lo hi : ℝ)
    (hlow : (K - (lo : ℂ) • 1).PosSemidef)
    {w : EuclideanSpace ℂ σ ⊗[ℂ] F}
    (hw : w ∈ S.tensorProd (⊤ : Submodule ℂ F)) (hwne : w ≠ 0)
    (henergy : (inner ℂ (TensorProduct.mapL
      (toEuclideanCLM (𝕜 := ℂ) (n := σ) K) (1 : F →L[ℂ] F) w) w).re ≤ hi * ‖w‖ ^ 2) :
    ∃ (n : ℕ) (hn : Module.finrank ℂ S = n + 1),
      lo ≤ (S.orthogonalCompression_isSymmetric
        (isSymmetric_toEuclideanLin_iff.mpr hK)).eigenvalues hn (Fin.last n) ∧
      (S.orthogonalCompression_isSymmetric
        (isSymmetric_toEuclideanLin_iff.mpr hK)).eigenvalues hn (Fin.last n) ≤ hi := by
  obtain ⟨n, hn, hupper⟩ := S.exists_compression_min_eigenvalue_le_of_tensor_energy
    (toEuclideanCLM (𝕜 := ℂ) (n := σ) K)
    (isSymmetric_toEuclideanLin_iff.mpr hK) hw hwne henergy
  exact ⟨n, hn, hK.orthogonalCompression_eigenvalue_ge lo hlow S hn (Fin.last n), hupper⟩

end Matrix
