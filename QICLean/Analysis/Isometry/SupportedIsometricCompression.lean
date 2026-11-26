/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Algebra.Unitary.MatrixUnitaryBetween
import QICLean.Analysis.Projection.PosSemidefSupport
import Mathlib.Analysis.Normed.Ring.Units

/-!
# Comparing isometric frames of supported matrices

An isometric frame identifies a matrix with its compression when its support
lies in the frame range. Individual matrices can then be extended by
the identity on the complementary space for purposes of commutation, and
restricted again to a smaller supported frame. These algebraic extensions do
not assert a projective representation on the complementary space.

The identities support the restriction argument in
arXiv:1010.3732, Appendix C, lines 2653–2717.

Moved from TNLean, `TNLean/Algebra/SupportedIsometricCompression.lean` at commit
`49b78ed821` (Apache-2.0).

Moved from TNLean, `TNLean/MPS/Symmetry/ContinuousFamily/LocalInvariantCompression.lean` at commit
`021ba0bd19` (Apache-2.0).
-/

open scoped Matrix ComplexOrder

namespace Matrix

/-- Extend a matrix from an isometrically included subspace by the identity
on its orthogonal complement. No projective multiplication law on the
ambient space is asserted. Auxiliary context: arXiv:1010.3732,
Appendix C, lines 2712–2717. -/
def isometryExtendByIdentity {m D : ℕ}
    (K : Matrix (Fin m) (Fin D) ℂ) (X : Matrix (Fin D) (Fin D) ℂ) :
    Matrix (Fin m) (Fin m) ℂ := K * X * Kᴴ + (1 - K * Kᴴ)

/-- The individual extension intertwines with its isometric inclusion.
Source context: arXiv:1010.3732, Appendix C, lines 2712–2717. -/
theorem isometryExtendByIdentity_mul_isometry {m D : ℕ}
    (K : Matrix (Fin m) (Fin D) ℂ) (hK : K.IsIsometry)
    (X : Matrix (Fin D) (Fin D) ℂ) :
    isometryExtendByIdentity K X * K = K * X := by
  simp only [isometryExtendByIdentity, Matrix.add_mul, Matrix.sub_mul,
    Matrix.mul_assoc, show Kᴴ * K = 1 from hK, Matrix.mul_one, Matrix.one_mul,
    sub_self, add_zero]

/-- The adjoint inclusion intertwines with the individual extension.
Source context: arXiv:1010.3732, Appendix C, lines 2712–2717. -/
theorem isometry_conjTranspose_mul_isometryExtendByIdentity {m D : ℕ}
    (K : Matrix (Fin m) (Fin D) ℂ) (hK : K.IsIsometry)
    (X : Matrix (Fin D) (Fin D) ℂ) :
    Kᴴ * isometryExtendByIdentity K X = X * Kᴴ := by
  simp only [isometryExtendByIdentity, Matrix.mul_add, Matrix.mul_sub,
    ← Matrix.mul_assoc, show Kᴴ * K = 1 from hK, Matrix.mul_one, Matrix.one_mul,
    sub_self, add_zero]

/-- A supported density is reconstructed from its isometric compression.
Source context: arXiv:1010.3732, Appendix C, lines 2653–2717. -/
theorem isometry_reconstruct_of_supportProj {m D : ℕ}
    (K : Matrix (Fin m) (Fin D) ℂ) (σ : Matrix (Fin m) (Fin m) ℂ)
    (hσ : σ.PosSemidef) (hsupport : K * Kᴴ = hσ.supportProj) :
    K * (Kᴴ * σ * K) * Kᴴ = σ := by
  calc
    K * (Kᴴ * σ * K) * Kᴴ = (K * Kᴴ) * σ * (K * Kᴴ) := by
      simp only [Matrix.mul_assoc]
    _ = σ := by
      rw [hsupport, hσ.supportProj_mul_self, hσ.mul_supportProj_self]

/-- Commutation with the compressed density gives commutation of the
individual extension with the ambient density. Source context:
arXiv:1010.3732, Appendix C, lines 2653–2717. -/
theorem commute_isometryExtendByIdentity_of_commute_compression {m D : ℕ}
    (K : Matrix (Fin m) (Fin D) ℂ) (hK : K.IsIsometry)
    (σ : Matrix (Fin m) (Fin m) ℂ) (hσ : σ.PosSemidef)
    (hsupport : K * Kᴴ = hσ.supportProj)
    (X : Matrix (Fin D) (Fin D) ℂ) (hComm : Commute X (Kᴴ * σ * K)) :
    Commute (isometryExtendByIdentity K X) σ := by
  have hrec := isometry_reconstruct_of_supportProj K σ hσ hsupport
  change isometryExtendByIdentity K X * σ = σ * isometryExtendByIdentity K X
  calc
    isometryExtendByIdentity K X * σ =
        isometryExtendByIdentity K X * (K * (Kᴴ * σ * K) * Kᴴ) := by rw [hrec]
    _ = K * (X * (Kᴴ * σ * K)) * Kᴴ := by
      simp only [← Matrix.mul_assoc, isometryExtendByIdentity_mul_isometry K hK X]
    _ = K * ((Kᴴ * σ * K) * X) * Kᴴ := by rw [hComm.eq]
    _ = K * (Kᴴ * σ * K) * (Kᴴ * isometryExtendByIdentity K X) := by
      rw [isometry_conjTranspose_mul_isometryExtendByIdentity K hK X]
      simp only [Matrix.mul_assoc]
    _ = σ * isometryExtendByIdentity K X := by
      rw [← Matrix.mul_assoc, hrec]

/-- Absorption of an isometric frame projection implies absorption of the
frame itself. Source context: arXiv:1010.3732, Appendix C, lines 2712–2717. -/
theorem isometry_absorption_of_projector_absorption {m r : ℕ}
    (J : Matrix (Fin m) (Fin r) ℂ) (hJ : J.IsIsometry)
    (S : Matrix (Fin m) (Fin m) ℂ) (hSP : S * (J * Jᴴ) = J * Jᴴ) :
    S * J = J := by
  simpa only [Matrix.mul_assoc, show Jᴴ * J = 1 from hJ, Matrix.mul_one]
    using congrArg (fun X => X * J) hSP

/-- A frame lying in the range of another isometric frame remains isometric
when read in the latter coordinates. Source context: arXiv:1010.3732,
Appendix C, lines 2712–2717. -/
theorem isIsometry_conjTranspose_mul_of_absorption {m D r : ℕ}
    (K : Matrix (Fin m) (Fin D) ℂ) (J : Matrix (Fin m) (Fin r) ℂ)
    (hJ : J.IsIsometry) (hsub : (K * Kᴴ) * J = J) :
    (Kᴴ * J).IsIsometry := by
  change (Kᴴ * J)ᴴ * (Kᴴ * J) = 1
  calc
    (Kᴴ * J)ᴴ * (Kᴴ * J) = Jᴴ * ((K * Kᴴ) * J) := by
      simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
        Matrix.mul_assoc]
    _ = 1 := by
      simpa only [hsub] using (show Jᴴ * J = 1 from hJ)

/-- Nested compression agrees with direct compression on a supported frame.
Source context: arXiv:1010.3732, Appendix C, lines 2712–2717. -/
theorem isometry_double_compression_eq_of_absorption {m D r : ℕ}
    (K : Matrix (Fin m) (Fin D) ℂ) (J : Matrix (Fin m) (Fin r) ℂ)
    (M : Matrix (Fin m) (Fin m) ℂ) (hsub : (K * Kᴴ) * J = J) :
    (Kᴴ * J)ᴴ * (Kᴴ * M * K) * (Kᴴ * J) = Jᴴ * M * J := by
  have hAdj : Jᴴ * (K * Kᴴ) = Jᴴ := by
    simpa only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
      using congrArg Matrix.conjTranspose hsub
  calc
    (Kᴴ * J)ᴴ * (Kᴴ * M * K) * (Kᴴ * J) =
        (Jᴴ * (K * Kᴴ)) * M * ((K * Kᴴ) * J) := by
      simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
    _ = Jᴴ * M * J := by
      rw [hsub, hAdj]

/-- Commutation of an individual extension descends to the original
isometric coordinates. Source context: arXiv:1010.3732, Appendix C,
lines 2712–2717. -/
theorem commute_compression_of_commute_isometryExtendByIdentity {m D : ℕ}
    (K : Matrix (Fin m) (Fin D) ℂ) (hK : K.IsIsometry)
    (X : Matrix (Fin D) (Fin D) ℂ) (P : Matrix (Fin m) (Fin m) ℂ)
    (hComm : Commute (isometryExtendByIdentity K X) P) :
    Commute X (Kᴴ * P * K) := by
  have hEq := congrArg (fun Y => Kᴴ * Y * K) hComm.eq
  simp only [← Matrix.mul_assoc] at hEq
  rw [isometry_conjTranspose_mul_isometryExtendByIdentity K hK X,
    Matrix.mul_assoc (Kᴴ * P), isometryExtendByIdentity_mul_isometry K hK X] at hEq
  simpa only [Commute, SemiconjBy, Matrix.mul_assoc] using hEq

/-- A support frame of a trace-one positive density has positive dimension.
Source context: arXiv:1010.3732, Appendix C, nonzero support. -/
theorem supportFrame_dimension_pos_of_trace_one {m D : ℕ}
    (K : Matrix (Fin m) (Fin D) ℂ) (σ : Matrix (Fin m) (Fin m) ℂ)
    (hσ : σ.PosSemidef) (hsupport : K * Kᴴ = hσ.supportProj)
    (htrace : σ.trace = 1) : 0 < D := by
  by_contra h
  have hD : D = 0 := by omega
  subst D
  have hzero : K * Kᴴ = 0 := by
    ext i j
    simp [Matrix.mul_apply]
  have hσzero : σ = 0 := by
    simpa only [← hsupport, hzero, Matrix.zero_mul] using hσ.supportProj_mul_self.symm
  simp only [hσzero, Matrix.trace_zero, zero_ne_one] at htrace

end Matrix

section PointwiseInvariantCompression

open scoped Matrix


namespace Matrix

/-- Conjugation descends through an invariant isometric corner without
requiring the tensor letters themselves to preserve that corner.
Source context: arXiv:1010.3732, Appendix C, lines 2712–2717. -/
theorem isometry_compression_conj_of_commute {D r : ℕ}
    (J : Matrix (Fin D) (Fin r) ℂ) (hJ : J.IsIsometry)
    (X M : Matrix (Fin D) (Fin D) ℂ) (hX : Commute X (J * Jᴴ)) :
    Jᴴ * (X * M * Xᴴ) * J =
      (Jᴴ * X * J) * (Jᴴ * M * J) * (Jᴴ * X * J)ᴴ := by
  have hleft := congrArg (fun Y => Jᴴ * Y) hX.eq
  have hL : Jᴴ * X = (Jᴴ * X * J) * Jᴴ := by
    simpa only [← Matrix.mul_assoc, show Jᴴ * J = 1 from hJ, Matrix.one_mul]
      using hleft.symm
  have hR : Xᴴ * J = J * (Jᴴ * X * J)ᴴ := by
    simpa only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
      using congrArg Matrix.conjTranspose hL
  calc
    Jᴴ * (X * M * Xᴴ) * J = (Jᴴ * X) * M * (Xᴴ * J) := by
      simp only [Matrix.mul_assoc]
    _ = (Jᴴ * X * J) * (Jᴴ * M * J) * (Jᴴ * X * J)ᴴ := by
      rw [hL, hR]
      simp only [Matrix.mul_assoc, show Jᴴ * J = 1 from hJ, Matrix.mul_one]

end Matrix

end PointwiseInvariantCompression

section LocalInvariantCompression

section

open scoped Matrix Matrix.Norms.L2Operator ComplexOrder

open Filter Topology


namespace Set.Icc

/-- A property holding near a point of the unit interval holds along every
sufficiently short affine subinterval issuing from that point. -/
theorem eventually_forall_convexComb {p : unitInterval → Prop}
    (t₀ : unitInterval) (hp : ∀ᶠ t in 𝓝 t₀, p t) :
    ∀ᶠ t in 𝓝 t₀, ∀ s : unitInterval, p (Set.Icc.convexComb t₀ t s) := by
  obtain ⟨ε, hε, hpε⟩ := Metric.eventually_nhds_iff.mp hp
  filter_upwards [Metric.ball_mem_nhds t₀ hε] with t ht
  intro s
  apply hpε
  have hdist : dist (Set.Icc.convexComb t₀ t s) t₀ ≤ dist t t₀ := by
    change |(1 - (s : ℝ)) * (t₀ : ℝ) + s * t - t₀| ≤ |(t : ℝ) - t₀|
    rw [show (1 - (s : ℝ)) * (t₀ : ℝ) + s * t - t₀ =
      (s : ℝ) * (t - t₀) by ring, abs_mul, abs_of_nonneg s.2.1]
    exact mul_le_of_le_one_left (abs_nonneg _) s.2.2
  exact hdist.trans_lt ht

end Set.Icc

end

end LocalInvariantCompression
