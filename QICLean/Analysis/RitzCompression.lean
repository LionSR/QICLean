/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.RitzSubspace

/-!
# Rayleigh–Ritz extraction from an actual candidate space

The original symmetric operator is compressed by the actual orthogonal
projection onto the candidate space. Its ordered eigenvectors construct
the selected low space. No compressed operator, spectral basis or output
energy bound is supplied as data. The trial-space energy bound remains
an explicit hypothesis of this variational auxiliary to ALVV,
arXiv:1602.08828v2, Figure `fig:algo1`, lines 1620–1643, and the last
step of `t:alg1`, lines 1811–1817.
-/

open scoped InnerProductSpace

namespace Submodule

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E]

/-- Compress the given operator by the actual orthogonal projection onto
W. This is the restriction used for the final spectral selection in
ALVV, arXiv:1602.08828v2, Figure `fig:algo1`, lines 1641–1643. -/
noncomputable def orthogonalCompression (W : Submodule ℂ E) (H : E →ₗ[ℂ] E) :
    W →ₗ[ℂ] W :=
  W.orthogonalProjectionOnto.toLinearMap.comp (H.comp W.subtype)

/-- The actual compression preserves quadratic and mixed forms on W.
This supports the variational restriction in ALVV, arXiv:1602.08828v2,
Figure `fig:algo1`, lines 1641–1643. -/
theorem inner_orthogonalCompression (W : Submodule ℂ E) (H : E →ₗ[ℂ] E) (x y : W) :
    inner ℂ x (W.orthogonalCompression H y) = inner ℂ (x : E) (H (y : E)) := by
  change inner ℂ (x : E) (W.starProjection (H (y : E))) = _
  rw [← W.inner_starProjection_left_eq_right,
    W.starProjection_eq_self_iff.mpr x.property]

/-- Symmetry of the original operator gives symmetry of its actual
compression. Auxiliary to ALVV, arXiv:1602.08828v2, Figure `fig:algo1`,
lines 1641–1643. -/
theorem orthogonalCompression_isSymmetric (W : Submodule ℂ E)
    {H : E →ₗ[ℂ] E} (hH : H.IsSymmetric) :
    (W.orthogonalCompression H).IsSymmetric := by
  intro x y
  change inner ℂ (W.starProjection (H (x : E))) (y : E) =
    inner ℂ (x : E) (W.starProjection (H (y : E)))
  rw [W.inner_starProjection_left_eq_right, W.starProjection_eq_self_iff.mpr y.property,
    ← W.inner_starProjection_left_eq_right, W.starProjection_eq_self_iff.mpr x.property]
  exact hH (x : E) (y : E)

/-- The actual lowest r eigenvectors of the orthogonal compression, mapped
back into W. This is the output space in ALVV, arXiv:1602.08828v2,
Figure `fig:algo1`, lines 1641–1643. -/
noncomputable def ritzSubspace (W : Submodule ℂ E) {H : E →ₗ[ℂ] E}
    (hH : H.IsSymmetric) (r : ℕ) : Submodule ℂ E :=
  ((W.orthogonalCompression_isSymmetric hH).ritzSubspace r).map W.subtype

/-- The actual Ritz space lies in the candidate space. Supporting ALVV,
arXiv:1602.08828v2, Figure `fig:algo1`, lines 1641–1643. -/
theorem ritzSubspace_le (W : Submodule ℂ E) {H : E →ₗ[ℂ] E}
    (hH : H.IsSymmetric) (r : ℕ) : W.ritzSubspace hH r ≤ W := by
  rintro _ ⟨x, _hx, rfl⟩
  exact x.property

/-- The selected actual Ritz space has the requested dimension whenever
that many independent candidate vectors are available. Supporting ALVV,
arXiv:1602.08828v2, Figure `fig:algo1`, lines 1641–1643. -/
theorem finrank_ritzSubspace (W : Submodule ℂ E) {H : E →ₗ[ℂ] E}
    (hH : H.IsSymmetric) (r : ℕ) (hr : r ≤ Module.finrank ℂ W) :
    Module.finrank ℂ (W.ritzSubspace hH r) = r := by
  rw [ritzSubspace, finrank_map_subtype_eq]
  exact (W.orthogonalCompression_isSymmetric hH).finrank_ritzSubspace r hr

/-- A trial-space bound for the original operator controls every vector
in the actual selected Ritz space. The compression and its eigenvectors
are constructed, not supplied. This is the min–max extraction in ALVV,
arXiv:1602.08828v2, `t:alg1`, lines 1811–1817. -/
theorem re_inner_apply_le_of_mem_ritzSubspace (W : Submodule ℂ E)
    {H : E →ₗ[ℂ] E} (hH : H.IsSymmetric) (V : Submodule ℂ W) (e : ℝ)
    (hV : ∀ x ∈ V, (inner ℂ (x : E) (H (x : E))).re ≤ e * ‖(x : E)‖ ^ 2)
    {x : E} (hx : x ∈ W.ritzSubspace hH (Module.finrank ℂ V)) :
    (inner ℂ x (H x)).re ≤ e * ‖x‖ ^ 2 := by
  have htrial : ∀ x ∈ V,
      (inner ℂ x (W.orthogonalCompression H x)).re ≤ e * ‖x‖ ^ 2 := by
    intro y hy
    rw [inner_orthogonalCompression]
    simpa only [Submodule.norm_coe] using hV y hy
  obtain ⟨y, hy, rfl⟩ := hx
  change (inner ℂ (y : E) (H (y : E))).re ≤ e * ‖(y : E)‖ ^ 2
  have hbound := LinearMap.IsSymmetric.re_inner_apply_le_of_mem_ritzSubspace
    (W.orthogonalCompression_isSymmetric hH) V e htrial hy
  rw [inner_orthogonalCompression] at hbound
  simpa only [Submodule.norm_coe] using hbound

end Submodule
