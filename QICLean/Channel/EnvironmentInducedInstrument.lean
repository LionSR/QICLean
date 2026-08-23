/-
Copyright (c) 2026 Sirui Lu and QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sirui Lu
-/
import QICLean.Channel.ChoiRectangular
import QICLean.Channel.KrausRectangular
import QICLean.Channel.POVM
import QICLean.Channel.QuantumSteering

/-!
# Environment-induced instruments

This file formalizes Wolf's proposition "Environment induced instruments"
(`Notes/WolfNoteTexSource/ch02_representations.tex`, lines 447--475).

For a rectangular channel `T : M_d(ℂ) → M_d'(ℂ)` with a supplied
Stinespring/open-system matrix `V`, every finite decomposition `T = ∑ᵢ Tᵢ`
into completely positive maps is realized by inserting a POVM effect on the
same environment before taking the partial trace. Moreover, the Choi (Kraus)
rank of each summand is at most the rank of its effect.

The proof follows Wolf's route: the supplied dilation purifies the rectangular
Choi operator, and unnormalized quantum steering produces the POVM. The direct
Choi identity for effect insertion then transports the steering identities
back to maps.
-/

open scoped Matrix ComplexOrder MatrixOrder BigOperators
open Matrix Finset

namespace Channel

variable {d d' r n : ℕ}

/-- The coefficient matrix of the Choi purification obtained from a rectangular
Stinespring matrix `V : ℂ^d → ℂ^{d'} ⊗ ℂ^r`:
`C_(a,i),e = d⁻¹ᐟ² V_(a,e),i`.

This is Wolf's vector `(𝟙_d ⊗ V)|Ω⟩`, with factors reindexed so that the Choi
system `ℂ^{d'} ⊗ ℂ^d` comes first and the environment `ℂ^r` comes last. -/
noncomputable def choiPurificationCoeff
    (V : Matrix (Fin d' × Fin r) (Fin d) ℂ) :
    Matrix (Fin d' × Fin d) (Fin r) ℂ :=
  fun ai e => ((1 : ℂ) / ((d : ℝ).sqrt : ℂ)) * V (ai.1, e) ai.2

/-- Embed an input vector `x ∈ ℂ^d` as `x ⊗ φ`, where Wolf's fixed
initial environment vector has type `φ ∈ ℂ^{d'} ⊗ ℂ^{d'}`. The ambient input
space therefore has exact dimension `d * (d')^2`. -/
noncomputable def openSystemInputEmbedding
    (φ : Fin d' × Fin d' → ℂ) :
    Matrix (Fin d × (Fin d' × Fin d')) (Fin d) ℂ :=
  fun p i => if p.1 = i then φ p.2 else 0

/-- Wolf's fixed-state input `ρ ⊗ |φ⟩⟨φ|` from Equation (2.14), indexed as
`ℂ^d ⊗ (ℂ^{d'} ⊗ ℂ^{d'})`. -/
noncomputable def openSystemInput
    (φ : Fin d' × Fin d' → ℂ) (ρ : Matrix (Fin d) (Fin d) ℂ) :
    Matrix (Fin d × (Fin d' × Fin d')) (Fin d × (Fin d' × Fin d')) ℂ :=
  Matrix.kroneckerMap (· * ·) ρ (Matrix.vecMulVec φ (star φ))

/-- The fixed-state input is the compression through
`openSystemInputEmbedding`: `(𝟙_d ⊗ |φ⟩) ρ (𝟙_d ⊗ ⟨φ|)`. -/
theorem openSystemInput_eq_embedding
    (φ : Fin d' × Fin d' → ℂ) (ρ : Matrix (Fin d) (Fin d) ℂ) :
    openSystemInput φ ρ =
      openSystemInputEmbedding φ * ρ * (openSystemInputEmbedding φ)ᴴ := by
  classical
  ext ⟨i, s⟩ ⟨j, t⟩
  simp only [openSystemInput, Matrix.kroneckerMap_apply, Matrix.vecMulVec_apply,
    Pi.star_apply, RCLike.star_def, Matrix.mul_apply, openSystemInputEmbedding, ite_mul,
    zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte, Matrix.conjTranspose_apply]
  rw [Finset.sum_eq_single j]
  · simp
    ring
  · intro x _ hx
    have hjx : j ≠ x := fun h => hx h.symm
    simp [hjx]
  · simp

/-- Reindex the output of Wolf's supplied open-system operator from
`environment ⊗ output` to the output-first convention `output ⊗ environment`
used by `stinespringV` and `environmentEffectMap`. -/
noncomputable def openSystemStinespringV
    (U : Matrix (Fin (d * d') × Fin d')
      (Fin d × (Fin d' × Fin d')) ℂ)
    (φ : Fin d' × Fin d' → ℂ) :
    Matrix (Fin d' × Fin (d * d')) (Fin d) ℂ :=
  fun ae i => ∑ p : Fin d × (Fin d' × Fin d'),
    U (ae.2, ae.1) p * openSystemInputEmbedding φ p i

/-- The rectangular map obtained by inserting an environment effect `P` into
`V X Vᴴ` and then tracing out the environment. This is the reduced supplied-
Stinespring form of Wolf Equation (2.15). -/
noncomputable def environmentEffectMap
    (V : Matrix (Fin d' × Fin r) (Fin d) ℂ)
    (P : Matrix (Fin r) (Fin r) ℂ) :
    Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d') (Fin d') ℂ where
  toFun X a b := ∑ e : Fin r, ∑ f : Fin r, P e f *
    ∑ i : Fin d, ∑ j : Fin d, V (a, f) i * X i j * star (V (b, e) j)
  map_add' X Y := by
    ext a b
    change (∑ e : Fin r, ∑ f : Fin r, P e f *
        ∑ i : Fin d, ∑ j : Fin d,
          V (a, f) i * (X + Y) i j * star (V (b, e) j)) =
      (∑ e : Fin r, ∑ f : Fin r, P e f *
        ∑ i : Fin d, ∑ j : Fin d,
          V (a, f) i * X i j * star (V (b, e) j)) +
      ∑ e : Fin r, ∑ f : Fin r, P e f *
        ∑ i : Fin d, ∑ j : Fin d,
          V (a, f) i * Y i j * star (V (b, e) j)
    simp only [Matrix.add_apply, mul_add, add_mul, Finset.sum_add_distrib]
  map_smul' c X := by
    ext a b
    change (∑ e : Fin r, ∑ f : Fin r, P e f *
        ∑ i : Fin d, ∑ j : Fin d,
          V (a, f) i * (c • X) i j * star (V (b, e) j)) =
      c * ∑ e : Fin r, ∑ f : Fin r, P e f *
        ∑ i : Fin d, ∑ j : Fin d,
          V (a, f) i * X i j * star (V (b, e) j)
    simp only [Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun e _ => Finset.sum_congr rfl fun f _ =>
      Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring

@[simp]
theorem environmentEffectMap_apply
    (V : Matrix (Fin d' × Fin r) (Fin d) ℂ)
    (P : Matrix (Fin r) (Fin r) ℂ) (X : Matrix (Fin d) (Fin d) ℂ)
    (a b : Fin d') :
    environmentEffectMap V P X a b = ∑ e : Fin r, ∑ f : Fin r, P e f *
      ∑ i : Fin d, ∑ j : Fin d, V (a, f) i * X i j * star (V (b, e) j) :=
  rfl

/-- `environmentEffectMap` is literally environment-effect insertion followed
by the partial trace, in the output-first tensor ordering used by the local
rectangular Stinespring API. -/
theorem environmentEffectMap_eq_traceRight
    (V : Matrix (Fin d' × Fin r) (Fin d) ℂ)
    (P : Matrix (Fin r) (Fin r) ℂ) (X : Matrix (Fin d) (Fin d) ℂ) :
    environmentEffectMap V P X =
      Matrix.traceRight
        (Matrix.kroneckerMap (· * ·) (1 : Matrix (Fin d') (Fin d') ℂ) P *
          (V * X * Vᴴ)) := by
  classical
  ext a b
  simp only [environmentEffectMap_apply, Matrix.traceRight_apply, Matrix.mul_apply,
    Matrix.kroneckerMap_apply, Matrix.one_apply, Matrix.conjTranspose_apply]
  simp_rw [Fintype.sum_prod_type]
  simp only [ite_mul, one_mul, zero_mul]
  change (∑ e : Fin r, ∑ f : Fin r, P e f *
      ∑ i : Fin d, ∑ j : Fin d, V (a, f) i * X i j * star (V (b, e) j)) =
    ∑ e : Fin r, ∑ y : Fin d', ∑ f : Fin r,
      if a = y then P e f *
        ∑ j : Fin d, (∑ i : Fin d, V (y, f) i * X i j) * star (V (b, e) j)
      else 0
  have hcollapse (e f : Fin r) :
      (∑ y : Fin d', if a = y then P e f *
        ∑ j : Fin d, (∑ i : Fin d, V (y, f) i * X i j) * star (V (b, e) j)
      else 0) =
        P e f * ∑ j : Fin d,
          (∑ i : Fin d, V (a, f) i * X i j) * star (V (b, e) j) := by
    rw [Finset.sum_eq_single a]
    · simp
    · intro y _ hya
      have hay : a ≠ y := fun h => hya h.symm
      simp [hay]
    · simp
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [Finset.sum_comm]
  calc
    ∑ f : Fin r, P e f *
        ∑ i : Fin d, ∑ j : Fin d, V (a, f) i * X i j * star (V (b, e) j) =
      ∑ f : Fin r, P e f * ∑ j : Fin d,
        (∑ i : Fin d, V (a, f) i * X i j) * star (V (b, e) j) := by
          refine Finset.sum_congr rfl fun f _ => congrArg (P e f * ·) ?_
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun j _ => (Finset.sum_mul _ _ _).symm
    _ = ∑ f : Fin r, ∑ y : Fin d', if a = y then P e f *
        ∑ j : Fin d, (∑ i : Fin d, V (y, f) i * X i j) * star (V (b, e) j)
      else 0 := Finset.sum_congr rfl fun f _ => (hcollapse e f).symm

/-- The Choi operator of environment-effect insertion is the corresponding
sandwich of the Choi-purification coefficient matrix. -/
theorem choiMatrix_environmentEffectMap [NeZero d]
    (V : Matrix (Fin d' × Fin r) (Fin d) ℂ)
    (P : Matrix (Fin r) (Fin r) ℂ) :
    ChoiRectangular.choiMatrix (environmentEffectMap V P) =
      choiPurificationCoeff V * Pᵀ * (choiPurificationCoeff V)ᴴ := by
  classical
  have hd : 0 < d := NeZero.pos d
  let c : ℂ := (1 : ℂ) / ((d : ℝ).sqrt : ℂ)
  have hcc : c * star c = 1 / (d : ℂ) := by
    simpa [c] using ChoiJamiolkowski.omegaCoeff_eq_inv (D := d) hd
  ext ⟨a, i⟩ ⟨b, j⟩
  rw [ChoiRectangular.choiMatrix_apply,
    MaximallyEntangled.omegaSlice_eq_single (d := d) i j]
  simp only [MaximallyEntangled.omegaCoeff_eq_inv hd, environmentEffectMap_apply,
    Matrix.mul_apply, Matrix.transpose_apply, Matrix.conjTranspose_apply,
    choiPurificationCoeff]
  change (∑ e : Fin r, ∑ f : Fin r, P e f *
      ∑ x : Fin d, ∑ y : Fin d,
        V (a, f) x * Matrix.single i j (1 / (d : ℂ)) x y * star (V (b, e) y)) =
    ∑ f : Fin r, (∑ e : Fin r, (c * V (a, e) i) * P f e) *
      star (c * V (b, f) j)
  have hsingle : ∀ e f : Fin r,
      (∑ x : Fin d, ∑ y : Fin d,
        V (a, f) x * Matrix.single i j (1 / (d : ℂ)) x y * star (V (b, e) y)) =
      V (a, f) i * (1 / (d : ℂ)) * star (V (b, e) j) := by
    intro e f
    simp only [Matrix.single, Matrix.of_apply]
    rw [Finset.sum_eq_single i]
    · rw [Finset.sum_eq_single j]
      · simp
      · intro y _ hy
        have hjy : j ≠ y := fun h => hy h.symm
        simp [hjy]
      · simp
    · intro x _ hx
      have hix : i ≠ x := fun h => hx h.symm
      simp [hix]
    · simp
  simp_rw [hsingle]
  have hterm (e f : Fin r) :
      P e f * (V (a, f) i * (1 / (d : ℂ)) * star (V (b, e) j)) =
        (c * V (a, f) i) * P e f * star (c * V (b, e) j) := by
    rw [star_mul, ← hcc]
    ring
  calc
    (∑ e : Fin r, ∑ f : Fin r,
        P e f * (V (a, f) i * (1 / (d : ℂ)) * star (V (b, e) j))) =
      ∑ e : Fin r, ∑ f : Fin r,
        (c * V (a, f) i) * P e f * star (c * V (b, e) j) := by
          exact Finset.sum_congr rfl fun e _ =>
            Finset.sum_congr rfl fun f _ => hterm e f
    _ = ∑ f : Fin r, ∑ e : Fin r,
        (c * V (a, e) i) * P f e * star (c * V (b, f) j) := by
          rw [Finset.sum_comm]
    _ = ∑ f : Fin r, (∑ e : Fin r, (c * V (a, e) i) * P f e) *
        star (c * V (b, f) j) := by
          exact Finset.sum_congr rfl fun f _ => (Finset.sum_mul _ _ _).symm

/-- Inserting the identity effect recovers the ordinary reduced Stinespring
map. -/
theorem environmentEffectMap_one
    (V : Matrix (Fin d' × Fin r) (Fin d) ℂ) (X : Matrix (Fin d) (Fin d) ℂ) :
    environmentEffectMap V (1 : Matrix (Fin r) (Fin r) ℂ) X =
      Matrix.traceRight (V * X * Vᴴ) := by
  rw [environmentEffectMap_eq_traceRight]
  ext a b
  simp [Matrix.traceRight_apply, Matrix.mul_apply]

/-- Swap the row factors of a joint matrix from `environment ⊗ output`
to `output ⊗ environment`. -/
noncomputable def swapOutputEnvironment
    (W : Matrix (Fin r × Fin d') (Fin d) ℂ) :
    Matrix (Fin d' × Fin r) (Fin d) ℂ :=
  fun ae i => W (ae.2, ae.1) i

@[simp]
theorem swapOutputEnvironment_apply
    (W : Matrix (Fin r × Fin d') (Fin d) ℂ) (a : Fin d') (e : Fin r) (i : Fin d) :
    swapOutputEnvironment W (a, e) i = W (e, a) i :=
  rfl

/-- Swapping an `environment ⊗ output` joint matrix to the local
`output ⊗ environment` convention transports left partial trace with
`P ⊗ 𝟙` to `environmentEffectMap`. -/
theorem environmentEffectMap_swap
    (W : Matrix (Fin r × Fin d') (Fin d) ℂ)
    (P : Matrix (Fin r) (Fin r) ℂ) (X : Matrix (Fin d) (Fin d) ℂ) :
    environmentEffectMap (swapOutputEnvironment W) P X =
      Matrix.partialTraceLeft
        (Matrix.kroneckerMap (· * ·) P
          (1 : Matrix (Fin d') (Fin d') ℂ) * (W * X * Wᴴ)) := by
  classical
  ext a b
  simp only [environmentEffectMap_apply, swapOutputEnvironment_apply,
    Matrix.partialTraceLeft_apply,
    Matrix.mul_apply, Matrix.kroneckerMap_apply, Matrix.one_apply,
    Matrix.conjTranspose_apply]
  let F : Fin r → (Fin r × Fin d') → ℂ := fun e p =>
    (P e p.1 * if a = p.2 then 1 else 0) *
      ∑ j : Fin d, (∑ i : Fin d, W p i * X i j) * star (W (e, b) j)
  change (∑ e : Fin r, ∑ f : Fin r, P e f *
      ∑ i : Fin d, ∑ j : Fin d, W (f, a) i * X i j * star (W (e, b) j)) =
    ∑ e : Fin r, ∑ p : Fin r × Fin d', F e p
  rw [show (∑ e : Fin r, ∑ p : Fin r × Fin d', F e p) =
      ∑ e : Fin r, ∑ f : Fin r, ∑ y : Fin d', F e (f, y) by
    exact Finset.sum_congr rfl fun e _ => Fintype.sum_prod_type _]
  dsimp only [F]
  simp only [mul_ite, mul_one, mul_zero]
  simp only [ite_mul, zero_mul]
  change (∑ e : Fin r, ∑ f : Fin r, P e f *
      ∑ i : Fin d, ∑ j : Fin d, W (f, a) i * X i j * star (W (e, b) j)) =
    ∑ e : Fin r, ∑ f : Fin r, ∑ y : Fin d',
      if a = y then P e f *
        ∑ j : Fin d, (∑ i : Fin d, W (f, y) i * X i j) * star (W (e, b) j)
      else 0
  have hcollapse (e f : Fin r) :
      (∑ y : Fin d', if a = y then P e f *
        ∑ j : Fin d, (∑ i : Fin d, W (f, y) i * X i j) * star (W (e, b) j)
      else 0) =
        P e f * ∑ j : Fin d,
          (∑ i : Fin d, W (f, a) i * X i j) * star (W (e, b) j) := by
    rw [Finset.sum_eq_single a]
    · simp
    · intro y _ hya
      have hay : a ≠ y := fun h => hya h.symm
      simp [hay]
    · simp
  refine Finset.sum_congr rfl fun e _ => ?_
  calc
    ∑ f : Fin r, P e f *
        ∑ i : Fin d, ∑ j : Fin d, W (f, a) i * X i j * star (W (e, b) j) =
      ∑ f : Fin r, P e f * ∑ j : Fin d,
        (∑ i : Fin d, W (f, a) i * X i j) * star (W (e, b) j) := by
          refine Finset.sum_congr rfl fun f _ => congrArg (P e f * ·) ?_
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun j _ => (Finset.sum_mul _ _ _).symm
    _ = ∑ f : Fin r, ∑ y : Fin d', if a = y then P e f *
        ∑ j : Fin d, (∑ i : Fin d, W (f, y) i * X i j) * star (W (e, b) j)
      else 0 := Finset.sum_congr rfl fun f _ => (hcollapse e f).symm

/-- Effect insertion for the reindexed Stinespring matrix is exactly Wolf's
system-plus-environment expression. The left partial trace discards the
`d * d'`-dimensional environment and retains the `d'`-dimensional output. -/
theorem environmentEffectMap_openSystem
    (U : Matrix (Fin (d * d') × Fin d')
      (Fin d × (Fin d' × Fin d')) ℂ)
    (φ : Fin d' × Fin d' → ℂ)
    (P : Matrix (Fin (d * d')) (Fin (d * d')) ℂ)
    (X : Matrix (Fin d) (Fin d) ℂ) :
    environmentEffectMap (openSystemStinespringV U φ) P X =
      Matrix.partialTraceLeft
        ((Matrix.kroneckerMap (· * ·) P
            (1 : Matrix (Fin d') (Fin d') ℂ) * U) *
          openSystemInput φ X * Uᴴ) := by
  classical
  let W : Matrix (Fin (d * d') × Fin d') (Fin d) ℂ :=
    U * openSystemInputEmbedding φ
  have hV : openSystemStinespringV U φ = swapOutputEnvironment W := by
    ext ae i
    rcases ae with ⟨a, e⟩
    simp only [openSystemStinespringV, swapOutputEnvironment_apply, W,
      Matrix.mul_apply]
  rw [hV, environmentEffectMap_swap W]
  congr 1
  rw [openSystemInput_eq_embedding]
  simp only [W, Matrix.conjTranspose_mul, Matrix.mul_assoc]

/-- **Environment induced instruments** (Wolf, Chapter 2, Proposition and
Equation (2.15), `Notes/WolfNoteTexSource/ch02_representations.tex`, lines
447--475), in reduced supplied-Stinespring form.

Let `T : M_d(ℂ) → M_d'(ℂ)` be completely positive and trace preserving, and
suppose the supplied rectangular matrix `V : ℂ^d → ℂ^{d'} ⊗ ℂ^r` realizes
`T(X) = tr_r(V X Vᴴ)`. For every nonempty finite decomposition `T = ∑ᵢ Tᵢ`
into completely positive maps, there is a POVM `P` on that same environment
such that

`Tᵢ(X) = tr_r[(𝟙_{d'} ⊗ Pᵢ) V X Vᴴ]`

for every `i` and `X`, and
`Channel.choiRank (Tᵢ i) ≤ (P.ops i).rank`.

The explicit trace-preservation hypothesis records Wolf's channel assumption;
the steering argument itself only uses complete positivity, the decomposition,
and the supplied representation. -/
theorem exists_environment_povm_of_sum_eq_stinespring [NeZero d]
    (T : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d') (Fin d') ℂ)
    (Tᵢ : Fin n →
      Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d') (Fin d') ℂ)
    (hT : IsKrausCP T)
    (_hTP : ∀ X : Matrix (Fin d) (Fin d) ℂ, (T X).trace = X.trace)
    (hTᵢ : ∀ i, IsKrausCP (Tᵢ i))
    (hsum : ∑ i, Tᵢ i = T)
    (V : Matrix (Fin d' × Fin r) (Fin d) ℂ)
    (hV : ∀ X, T X = Matrix.traceRight (V * X * Vᴴ)) :
    ∃ P : POVM r n,
      (∀ i X, Tᵢ i X = environmentEffectMap V (P.ops i) X) ∧
      (∀ i, Channel.choiRank (Tᵢ i) ≤ (P.ops i).rank) := by
  classical
  let _ : NeZero n := ⟨by
    intro hn
    subst n
    have hTzero : T = 0 := by simpa using hsum.symm
    have htrace := _hTP (1 : Matrix (Fin d) (Fin d) ℂ)
    rw [hTzero] at htrace
    have hd : (d : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne d)
    exact hd (by simpa using htrace.symm)⟩
  let C := choiPurificationCoeff V
  have hTchoi : (ChoiRectangular.choiMatrix T).PosSemidef :=
    (ChoiRectangular.isKrausCP_iff_choiMatrix_posSemidef T).mp hT
  have hTᵢchoi : ∀ i, (ChoiRectangular.choiMatrix (Tᵢ i)).PosSemidef := fun i =>
    (ChoiRectangular.isKrausCP_iff_choiMatrix_posSemidef (Tᵢ i)).mp (hTᵢ i)
  have hC : C * Cᴴ = ChoiRectangular.choiMatrix T := by
    calc
      C * Cᴴ = C * (1 : Matrix (Fin r) (Fin r) ℂ)ᵀ * Cᴴ := by simp
      _ = ChoiRectangular.choiMatrix
          (environmentEffectMap V (1 : Matrix (Fin r) (Fin r) ℂ)) := by
            simpa [C] using
              (choiMatrix_environmentEffectMap V
                (1 : Matrix (Fin r) (Fin r) ℂ)).symm
      _ = ChoiRectangular.choiMatrix T := by
            congr 1
            ext X
            rw [environmentEffectMap_one, ← hV X]
  have hchoiSum : ∑ i, ChoiRectangular.choiMatrix (Tᵢ i) =
      ChoiRectangular.choiMatrix T := by
    rw [← ChoiRectangular.choiMatrix_sum Finset.univ Tᵢ]
    simpa using congrArg ChoiRectangular.choiMatrix hsum
  obtain ⟨P, hP⟩ := Matrix.exists_povm_of_sum_posSemidef
    (ρ := ChoiRectangular.choiMatrix T) hTchoi (C := C) hC
    (fun i => ChoiRectangular.choiMatrix (Tᵢ i)) hTᵢchoi hchoiSum
  refine ⟨P, ?_, ?_⟩
  · intro i X
    have hmaps : Tᵢ i = environmentEffectMap V (P.ops i) :=
      ChoiRectangular.choiMatrix_injective <| by
        rw [choiMatrix_environmentEffectMap]
        exact hP i
    exact LinearMap.congr_fun hmaps X
  · intro i
    rw [Channel.choiRank, hP i]
    simpa only [Matrix.mul_assoc] using
      (Matrix.rank_mul_le_right C ((P.ops i)ᵀ * Cᴴ)).trans
        ((Matrix.rank_mul_le_left (P.ops i)ᵀ Cᴴ).trans_eq
          (Matrix.rank_transpose (P.ops i)))

/-- **Wolf Proposition (Environment induced instruments), literal
system-plus-environment form** (Chapter 2, Equation (2.15),
`Notes/WolfNoteTexSource/ch02_representations.tex`, lines 447--475).

The supplied operator `U` has Wolf's exact dimensions. Its input is
`ℂ^d ⊗ ℂ^{d'} ⊗ ℂ^{d'}`, of total dimension `d * (d')^2`; its output is
`ℂ^{d d'} ⊗ ℂ^{d'}`, with environment dimension `d d'` and retained system
dimension `d'`. The fixed normalized vector is
`φ ∈ ℂ^{d'} ⊗ ℂ^{d'}`. For every CP decomposition `T = ∑ᵢ Tᵢ`, the returned
POVM on `ℂ^{d d'}` realizes the literal insertion formula

`Tᵢ(ρ) = tr_E[(Pᵢ ⊗ 𝟙_{d'}) U (ρ ⊗ |φ⟩⟨φ|) Uᴴ]`

and satisfies `choiRank (Tᵢ i) ≤ rank(Pᵢ)`.

The two Gram identities state that the supplied heterogeneous matrix `U` is
unitary after identifying its equal-cardinality input and output index types.
They and the normalization hypothesis record all data of Wolf Equation (2.14);
the proof uses the supplied representation itself to pass to the reduced
Stinespring theorem above. -/
theorem exists_environment_povm_of_sum_eq_openSystem [NeZero d]
    (T : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d') (Fin d') ℂ)
    (Tᵢ : Fin n →
      Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d') (Fin d') ℂ)
    (hT : IsKrausCP T)
    (hTP : ∀ X : Matrix (Fin d) (Fin d) ℂ, (T X).trace = X.trace)
    (hTᵢ : ∀ i, IsKrausCP (Tᵢ i))
    (hsum : ∑ i, Tᵢ i = T)
    (U : Matrix (Fin (d * d') × Fin d')
      (Fin d × (Fin d' × Fin d')) ℂ)
    (_hU : Uᴴ * U = 1 ∧ U * Uᴴ = 1)
    (φ : Fin d' × Fin d' → ℂ)
    (_hφ : ∑ x, star (φ x) * φ x = 1)
    (hopen : ∀ ρ : Matrix (Fin d) (Fin d) ℂ,
      T ρ = Matrix.partialTraceLeft (U * openSystemInput φ ρ * Uᴴ)) :
    ∃ P : POVM (d * d') n,
      (∀ i ρ, Tᵢ i ρ =
        Matrix.partialTraceLeft
          ((Matrix.kroneckerMap (· * ·) (P.ops i)
              (1 : Matrix (Fin d') (Fin d') ℂ) * U) *
            openSystemInput φ ρ * Uᴴ)) ∧
      (∀ i, Channel.choiRank (Tᵢ i) ≤ (P.ops i).rank) := by
  classical
  let V := openSystemStinespringV U φ
  have hV : ∀ ρ : Matrix (Fin d) (Fin d) ℂ,
      T ρ = Matrix.traceRight (V * ρ * Vᴴ) := by
    intro ρ
    calc
      T ρ = Matrix.partialTraceLeft (U * openSystemInput φ ρ * Uᴴ) := hopen ρ
      _ = environmentEffectMap V (1 : Matrix (Fin (d * d')) (Fin (d * d')) ℂ) ρ := by
        rw [environmentEffectMap_openSystem]
        simp
      _ = Matrix.traceRight (V * ρ * Vᴴ) := environmentEffectMap_one V ρ
  obtain ⟨P, hrealize, hrank⟩ :=
    exists_environment_povm_of_sum_eq_stinespring T Tᵢ hT hTP hTᵢ hsum V hV
  refine ⟨P, ?_, hrank⟩
  intro i ρ
  rw [hrealize i ρ]
  exact environmentEffectMap_openSystem U φ (P.ops i) ρ

end Channel
