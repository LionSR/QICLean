/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.RootChannel

/-!
# Root-channel products evaluated on a common annihilated vector

For a positive contraction k annihilating a vector Ω, put
G = sqrt(1 - k) and K = sqrt(k). The channel B ↦ G B G + K B K
acts on Ω as the single vector action G(B Ω). Iterating this identity
in the original order of a list gives the corresponding chronological
product of the G factors. The input matrix and the vector are
arbitrary apart from the annihilation equations.

## References

* OpenAI, *A two-dimensional area law from a global spectral gap*, September
  24, 2026, `09-amplification.tex`, eq:amplification-channel-vector,
  lines 75–88, revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.

These identities are auxiliary to the coupled omission argument.
-/

open scoped Matrix MatrixOrder ComplexOrder

namespace Matrix

variable {n ι : Type*} [Fintype n] [DecidableEq n]

/-- A root channel evaluated on a vector annihilated by its positive deficit
equals the square-root contraction acting on the matrix-applied vector.
Source: `09-amplification.tex`, eq:amplification-channel-vector, lines 75–88. -/
theorem rootChannel_sqrt_mulVec_eq
    {k : Matrix n n ℂ} (hk₀ : 0 ≤ k) (hk₁ : k ≤ 1)
    {Ω : n → ℂ} (hΩ : k *ᵥ Ω = 0) (B : Matrix n n ℂ) :
    rootChannel (CFC.sqrt (1 - k)) (CFC.sqrt k) B *ᵥ Ω =
      CFC.sqrt (1 - k) *ᵥ (B *ᵥ Ω) := by
  have hK : CFC.sqrt k *ᵥ Ω = 0 := sqrt_mulVec_eq_zero hk₀ hΩ
  have hG : CFC.sqrt (1 - k) *ᵥ Ω = Ω := sqrt_one_sub_mulVec_eq_self hk₁ hΩ
  simp only [rootChannel, add_mulVec, ← mulVec_mulVec, hG, hK, mulVec_zero, add_zero]

/-- The actual chronological channel action on an arbitrary matrix, evaluated
on a common annihilated vector, equals the chronological square-root vector
action. The same original list is used on both sides, including repeated
letters and the empty list.
Source: `09-amplification.tex`, eq:amplification-channel-vector, lines 75–88. -/
theorem rootChannel_foldl_mulVec_eq
    (k : ι → Matrix n n ℂ) (hk₀ : ∀ i, 0 ≤ k i) (hk₁ : ∀ i, k i ≤ 1)
    {Ω : n → ℂ} (hΩ : ∀ i, k i *ᵥ Ω = 0)
    (w : List ι) (B : Matrix n n ℂ) :
    (w.foldl (fun C i ↦ rootChannel (CFC.sqrt (1 - k i)) (CFC.sqrt (k i)) C) B)
        *ᵥ Ω =
      w.foldl (fun v i ↦ CFC.sqrt (1 - k i) *ᵥ v) (B *ᵥ Ω) := by
  exact (List.foldl_hom (fun C : Matrix n n ℂ ↦ C *ᵥ Ω) (l := w) (init := B)
    (fun C i ↦ (rootChannel_sqrt_mulVec_eq (hk₀ i) (hk₁ i) (hΩ i) C).symm)).symm

end Matrix
