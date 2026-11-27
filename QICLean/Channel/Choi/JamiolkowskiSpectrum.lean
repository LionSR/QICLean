/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Spectral.Radius.SubperipheralSpectrum
import QICLean.Analysis.TraceNorm.Variational
import QICLean.Analysis.TraceNorm.TraceNormContractivity
import QICLean.Channel.Choi.Rectangular

/-!
# Channel spectrum versus Jamiołkowski spectrum

For a completely positive trace-preserving map $T : M_d(\mathbb C) \to M_d(\mathbb C)$
with Jamiołkowski state $\tau$, the largest modulus $\mu$ of an eigenvalue of
$T$ strictly inside the unit disc satisfies
$$\mu \le 1 - d^2 \lambda_{\min}(\tau).$$
This is Wolf's Corollary "Channel spectrum vs. Jamiolkowski spectrum",
Eq. (8.87).

The proof follows Wolf's route through the Choi-dominated Doeblin criterion
with $Y = \mathbf 1 / d$. Every lower bound $c\mathbf 1 \le \tau$ makes
$S = T - c d \operatorname{tr}[\,\cdot\,]\mathbf 1$ completely positive with trace
scaling $1 - d^2 c$, so $T$ contracts traceless Hermitian matrices in trace
norm by $1 - d^2 c$, and so does every power $T^n$ by the factor
$(1 - d^2 c)^n$. Wolf concludes by citing the asymptotic lower bound of
Prop. 8.6 and Thm. 8.23. Here the conclusion is drawn directly from an
eigenvector $X$ for a subperipheral eigenvalue $z$: $X$ is traceless, its
Hermitian and anti-Hermitian parts are traceless Hermitian, and
$|z|^n \|X\|_1 = \|T^n(X)\|_1$ is bounded by a constant times
$(1 - d^2 c)^n$, which forces $|z| \le 1 - d^2 c$.

## Main results

* `Matrix.traceNorm_map_le_of_smul_one_le_choiMatrix` — the one-step
  trace-norm contraction of traceless Hermitian matrices.
* `Matrix.subperipheralModulus_le_of_smul_one_le_choiMatrix` — Eq. (8.87)
  for every lower bound $c\mathbf 1 \le \tau$.
* `Matrix.subperipheralModulus_le_one_sub_sq_mul_min_eigenvalue` — Eq. (8.87)
  with the smallest eigenvalue of $\tau$.
* `Matrix.choiMatrix_tracePrepareMap`, `Matrix.traceNorm_map_sub_map_le_of_choi_domination`:
  choi-dominated Doeblin contraction.

## References

Michael M. Wolf, *Quantum Channels & Operations: Guided Tour* (July 5, 2012),
Chapter 8, Corollary "Channel spectrum vs. Jamiolkowski spectrum", Eq. (8.87);
`Notes/WolfNoteTexSource/ch08_distance_measures.tex`, lines 978–992.
-/

open scoped Matrix ComplexOrder MatrixOrder

section Doeblin

/-!
## Choi-dominated Doeblin contraction

If the rectangular Choi matrix of a trace-preserving, Hermiticity-preserving
linear map $T : M_D(\mathbb{C}) \to M_{D'}(\mathbb{C})$ dominates
$(\varepsilon/D)(Y \otimes \mathbf{1})$ for some $\varepsilon \ge 0$ and Hermitian $Y$
with $\mathrm{tr}[Y] = 1$, then $T$ satisfies the Doeblin trace-norm contraction
$\|T(\rho_1) - T(\rho_2)\|_1 \le (1 - \varepsilon)\|\rho_1 - \rho_2\|_1$ for all
density matrices.

The proof constructs the trace-prepare map $T'(X) = \mathrm{tr}[X]Y$, computes its
rectangular Choi matrix as $(1/D)(Y \otimes \mathbf{1})$, uses the rectangular CP/PSD
equivalence to derive positivity of $T - \varepsilon T'$, and applies the quantum
Doeblin theorem (`Matrix.traceNorm_map_sub_map_le_of_doeblin`).

### Main results

* `Matrix.choiMatrix_tracePrepareMap` — the rectangular Choi matrix
  of the trace-prepare map is $(1/d)(Y \otimes \mathbf{1})$.
* `Matrix.traceNorm_map_sub_map_le_of_choi_domination` — Wolf Eq. (8.86):
  Choi-dominated Doeblin contraction.

### References

Michael M. Wolf, *Quantum Channels & Operations: Guided Tour* (July 5, 2012),
Chapter 8, Eq. (8.86);
Notes/WolfNoteTexSource/ch08_distance_measures.tex, lines 971–979.
-/

noncomputable section

namespace Matrix

/-! ### Choi-dominated Doeblin contraction -/

/-- **Choi matrix of the trace-prepare map** (auxiliary lemma for Eq. (8.86)).

For an arbitrary matrix $Y$ on the output space, the trace-prepare
map $T'(X) = \mathrm{tr}[X]Y$ has Choi matrix
$(1/d)(Y \otimes \mathbf{1})$ in the output-factor-first tensor order of
`ChoiRectangular.choiMatrix`.

`Notes/WolfNoteTexSource/ch08_distance_measures.tex`, line 973. -/
lemma choiMatrix_tracePrepareMap (d d' : ℕ)
    (Y : Matrix (Fin d') (Fin d') ℂ) :
    ChoiRectangular.choiMatrix (tracePrepareMap (α := Fin d) Y) =
      (1 / (d : ℂ)) • (kroneckerMap (· * ·) Y (1 : Matrix (Fin d) (Fin d) ℂ)) := by
  by_cases hd : d = 0
  · subst hd
    ext ⟨a, i⟩ ⟨b, j⟩
    exact Fin.elim0 i
  · have : NeZero d := ⟨hd⟩
    have hdpos : 0 < d := Nat.pos_of_ne_zero hd
    ext ⟨a, i⟩ ⟨b, j⟩
    calc
      ChoiRectangular.choiMatrix (tracePrepareMap (α := Fin d) Y) (a, i) (b, j)
          = (tracePrepareMap (α := Fin d) Y
              (Matrix.bipartiteSlice (Matrix.omegaProj d) i j)) a b := by
        rw [ChoiRectangular.choiMatrix_apply]
      _ = (Matrix.trace (Matrix.bipartiteSlice (Matrix.omegaProj d) i j) • Y) a b := by
        rw [tracePrepareMap_apply]
      _ = Matrix.trace (Matrix.bipartiteSlice (Matrix.omegaProj d) i j) * Y a b := by
        rw [Matrix.smul_apply, smul_eq_mul]
      _ = Matrix.trace ((1 / (d : ℂ)) • Matrix.single i j (1 : ℂ)) * Y a b := by
        have h := ChoiJamiolkowski.omegaSlice_eq_single (D := d) i j
        rw [h, ChoiJamiolkowski.omegaCoeff_eq_inv hdpos]
        simp [Matrix.smul_single]
      _ = ((1 / (d : ℂ)) * Matrix.trace (Matrix.single i j (1 : ℂ))) * Y a b := by
        rw [Matrix.trace_smul, smul_eq_mul]
      _ = (1 / (d : ℂ)) * (kroneckerMap (· * ·) Y (1 : Matrix (Fin d) (Fin d) ℂ))
            (a, i) (b, j) := by
        by_cases hij : i = j
        · subst hij
          simp [kroneckerMap_apply]
        · simp [kroneckerMap_apply, hij]
      _ = ((1 / (d : ℂ)) • (kroneckerMap (· * ·) Y (1 : Matrix (Fin d) (Fin d) ℂ)))
            (a, i) (b, j) := by
        rw [Matrix.smul_apply, smul_eq_mul]

/-- **Choi-dominated Doeblin contraction.**

Let $T : M_D(\mathbb{C}) \to M_{D'}(\mathbb{C})$ be a trace-preserving, Hermiticity-preserving
linear map.  For $\varepsilon \ge 0$ and a Hermitian $Y$ with trace one, if
the (rectangular, output-factor-first) Choi matrix satisfies
```
τ = choi(T) ≥ (ε/D)(Y ⊗ 𝟙),
```
then for all density operators $\rho_1, \rho_2 \in M_D$,
```
‖T(ρ₁) - T(ρ₂)‖₁ ≤ (1 - ε) ‖ρ₁ - ρ₂‖₁.
```

The proof constructs $T'(X) = \mathrm{tr}[X]Y$ (the trace-prepare map) and applies
`Matrix.traceNorm_map_sub_map_le_of_doeblin` (Wolf Theorem 8.17, Eq. (8.82)).
The Choi domination guarantees, via the rectangular CP/PSD equivalence
(`ChoiRectangular.isKrausCP_iff_choiMatrix_posSemidef`), that $T - \varepsilon T'$ is
positive, satisfying the hypothesis of Theorem 8.17.

`Notes/WolfNoteTexSource/ch08_distance_measures.tex`, lines 971–979. -/
theorem traceNorm_map_sub_map_le_of_choi_domination
    {D D' : ℕ}
    {ε : ℝ}
    {T : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D') (Fin D') ℂ}
    {Y : Matrix (Fin D') (Fin D') ℂ}
    (htrT : ∀ X : Matrix (Fin D) (Fin D) ℂ, (T X).trace = X.trace)
    (hhermT : ∀ X : Matrix (Fin D) (Fin D) ℂ, X.IsHermitian → (T X).IsHermitian)
    (hYherm : Y.IsHermitian)
    (hYtr : Y.trace = 1)
    (hε_nonneg : 0 ≤ ε)
    (hchoi : ChoiRectangular.choiMatrix T ≥
      ((ε : ℂ) / (D : ℂ)) • (kroneckerMap (· * ·) Y (1 : Matrix (Fin D) (Fin D) ℂ)))
    {ρ₁ ρ₂ : Matrix (Fin D) (Fin D) ℂ} (h₁ : ρ₁.PosSemidef)
    (h₂ : ρ₂.PosSemidef) (h₁tr : ρ₁.trace = 1) (h₂tr : ρ₂.trace = 1) :
    traceNorm (T ρ₁ - T ρ₂) ≤ (1 - ε) * traceNorm (ρ₁ - ρ₂) := by
  by_cases hD : D = 0
  · subst hD
    have hzero : (ρ₁ : Matrix (Fin 0) (Fin 0) ℂ).trace = (0 : ℂ) := by simp
    rw [hzero] at h₁tr
    norm_num at h₁tr
  · have : NeZero D := ⟨hD⟩
    -- Step 1: construct T' = tracePrepareMap Y
    set T' := tracePrepareMap (α := Fin D) Y with hT'_def
    -- T' is trace-preserving (since tr Y = 1)
    have htrT' : ∀ X : Matrix (Fin D) (Fin D) ℂ, (T' X).trace = X.trace := by
      intro X
      rw [hT'_def, tracePrepareMap_trace, hYtr, mul_one]
    -- T' is Hermiticity-preserving
    have hhermT' : ∀ X : Matrix (Fin D) (Fin D) ℂ, X.IsHermitian → (T' X).IsHermitian := by
      intro X hX
      have htr_star : star (X.trace) = X.trace := by
        calc
          star (X.trace) = (Xᴴ).trace := by rw [Matrix.trace_conjTranspose]
          _ = X.trace := by rw [hX]
      rw [hT'_def, tracePrepareMap_apply]
      calc
        (X.trace • Y)ᴴ = star (X.trace) • Yᴴ := by simp [Matrix.conjTranspose_smul]
        _ = star (X.trace) • Y := by rw [hYherm.eq]
        _ = X.trace • Y := by rw [htr_star]
    -- T' has the special form T'(X) = tr[X]·Y
    have hT'_form : ∃ Y' : Matrix (Fin D') (Fin D') ℂ,
        ∀ X : Matrix (Fin D) (Fin D) ℂ, T' X = (X.trace) • Y' := by
      refine ⟨Y, ?_⟩
      intro X
      rw [hT'_def, tracePrepareMap_apply]
    -- Step 2: key identity choiMatrix(T') = (1/D)(Y ⊗ 𝟙)
    have hchoi_T' : ChoiRectangular.choiMatrix T' =
        (1 / (D : ℂ)) • (kroneckerMap (· * ·) Y (1 : Matrix (Fin D) (Fin D) ℂ)) :=
      choiMatrix_tracePrepareMap D D' Y
    -- Step 3: choi(T - ε·T') ≥ 0 via linearity and Choi domination
    have hchoi_diff_pos : (ChoiRectangular.choiMatrix (T - (ε : ℂ) • T')).PosSemidef := by
      have hsub : ChoiRectangular.choiMatrix (T - (ε : ℂ) • T') =
          ChoiRectangular.choiMatrix T - ChoiRectangular.choiMatrix ((ε : ℂ) • T') :=
        (ChoiRectangular.choiMatrixLinearMap (d := D) (d' := D')).map_sub T ((ε : ℂ) • T')
      rw [hsub, ChoiRectangular.choiMatrix_smul, hchoi_T']
      -- Now:  choi(T) - (ε:ℂ) • ((1/D)(Y⊗1)) = choi(T) - ((ε:ℂ)/D)(Y⊗1)
      have hsmul : (ε : ℂ) • ((1 / (D : ℂ)) •
          (kroneckerMap (· * ·) Y (1 : Matrix (Fin D) (Fin D) ℂ))) =
          ((ε : ℂ) / (D : ℂ)) •
          (kroneckerMap (· * ·) Y (1 : Matrix (Fin D) (Fin D) ℂ)) := by
        rw [smul_smul]
        congr
        ring
      rw [hsmul]
      -- hchoi says choi(T) ≥ ((ε:ℂ)/D)(Y⊗1), so the difference is PSD
      exact (Matrix.le_iff.mp hchoi)
    -- Step 4: by rectangular CP/PSD equivalence, T - ε·T' is completely positive
    have hCP_diff : IsKrausCP (T - (ε : ℂ) • T') :=
      (ChoiRectangular.isKrausCP_iff_choiMatrix_posSemidef (T - (ε : ℂ) • T')).mpr hchoi_diff_pos
    -- Hence T - ε·T' preserves PSD (positive map)
    have hpos_diff : ∀ ρ : Matrix (Fin D) (Fin D) ℂ, ρ.PosSemidef →
        ((T - (ε : ℂ) • T') ρ).PosSemidef :=
      fun ρ hρ => hCP_diff.map_posSemidef hρ
    -- Step 5: apply the quantum Doeblin theorem
    exact traceNorm_map_sub_map_le_of_doeblin htrT htrT' hhermT hhermT' hT'_form
      hε_nonneg hpos_diff h₁ h₂ h₁tr h₂tr

end Matrix

end

end Doeblin

section JamiolkowskiSpectrum

open Filter Topology

noncomputable section

namespace Matrix

variable {D : ℕ}

/-- A map with a Kraus representation commutes with the conjugate transpose. -/
lemma isKrausCP_map_conjTranspose
    {T : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ}
    (hT : IsKrausCP T) (X : Matrix (Fin D) (Fin D) ℂ) : T Xᴴ = (T X)ᴴ := by
  obtain ⟨r, A, hA⟩ := hT
  simp [hA, Matrix.conjTranspose_sum, Matrix.conjTranspose_mul, Matrix.mul_assoc]

/-- **One-step contraction from a scalar Choi lower bound** (Wolf Eq. (8.86)
with $Y = \mathbf 1 / d$).

Let $T : M_D(\mathbb C) \to M_D(\mathbb C)$ be trace preserving and suppose
$c \mathbf 1 \le \tau$ for the Choi matrix $\tau$ of $T$. Then
$0 \le 1 - D^2 c$ and every traceless Hermitian $H$ satisfies
$\|T(H)\|_1 \le (1 - D^2 c)\|H\|_1$.

`Notes/WolfNoteTexSource/ch08_distance_measures.tex`, lines 971–979 and 988. -/
theorem traceNorm_map_le_of_smul_one_le_choiMatrix [NeZero D]
    {T : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ}
    (htr : ∀ X : Matrix (Fin D) (Fin D) ℂ, (T X).trace = X.trace) {c : ℝ}
    (hc : c • (1 : Matrix (Fin D × Fin D) (Fin D × Fin D) ℂ) ≤
      ChoiRectangular.choiMatrix T) :
    0 ≤ 1 - (D : ℝ) ^ 2 * c ∧
      ∀ H : Matrix (Fin D) (Fin D) ℂ, H.IsHermitian → H.trace = 0 →
        traceNorm (T H) ≤ (1 - (D : ℝ) ^ 2 * c) * traceNorm H := by
  have hD : (D : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne D)
  set Y : Matrix (Fin D) (Fin D) ℂ := ((c * D : ℝ) : ℂ) • 1 with hY
  set S := T - tracePrepareMap (α := Fin D) Y with hS
  -- The Choi matrix of `S` is `τ - c 𝟙`.
  have hchoiS : ChoiRectangular.choiMatrix S =
      ChoiRectangular.choiMatrix T - c • (1 : Matrix (Fin D × Fin D) (Fin D × Fin D) ℂ) := by
    have hsub : ChoiRectangular.choiMatrix S =
        ChoiRectangular.choiMatrix T -
          ChoiRectangular.choiMatrix (tracePrepareMap (α := Fin D) Y) :=
      (ChoiRectangular.choiMatrixLinearMap (d := D) (d' := D)).map_sub T _
    rw [hsub, choiMatrix_tracePrepareMap]
    congr 1
    ext ⟨a, i⟩ ⟨b, j⟩
    by_cases hab : a = b <;> by_cases hij : i = j <;>
      simp [hY, kroneckerMap_apply, hab, hij, Complex.real_smul, mul_left_comm _ (c : ℂ), hD]
  have hCP : IsKrausCP S := by
    rw [ChoiRectangular.isKrausCP_iff_choiMatrix_posSemidef, hchoiS]
    exact Matrix.le_iff.mp hc
  have hpos : ∀ ρ : Matrix (Fin D) (Fin D) ℂ, ρ.PosSemidef → (S ρ).PosSemidef :=
    fun ρ hρ => hCP.map_posSemidef hρ
  have hscale : ∀ ρ : Matrix (Fin D) (Fin D) ℂ,
      (S ρ).trace = ((1 - (D : ℝ) ^ 2 * c : ℝ) : ℂ) * ρ.trace := by
    intro ρ
    rw [hS, LinearMap.sub_apply, Matrix.trace_sub, htr, tracePrepareMap_trace, hY,
      Matrix.trace_smul, Matrix.trace_one]
    simp only [Fintype.card_fin, smul_eq_mul]
    push_cast
    ring
  have hnonneg : 0 ≤ 1 - (D : ℝ) ^ 2 * c := by
    have h1 := (hpos 1 Matrix.PosSemidef.one).trace_nonneg
    rw [hscale, Matrix.trace_one, Fintype.card_fin] at h1
    have h2 : (0 : ℝ) ≤ (1 - (D : ℝ) ^ 2 * c) * D := by
      rwa [← Complex.ofReal_natCast, ← Complex.ofReal_mul, Complex.zero_le_real] at h1
    have hDpos : (0 : ℝ) < D := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne D))
    exact nonneg_of_mul_nonneg_left h2 hDpos
  refine ⟨hnonneg, fun H hH hH0 => ?_⟩
  have hSH : S H = T H := by
    rw [hS, LinearMap.sub_apply, tracePrepareMap_apply, hH0, zero_smul, sub_zero]
  rw [← hSH]
  exact traceNorm_map_le_of_positive_of_scaledTrace hpos hscale hnonneg hH

/-- **Wolf Eq. (8.87) for an arbitrary scalar lower bound on the Choi matrix.**

Let $T : M_D(\mathbb C) \to M_D(\mathbb C)$ be completely positive and trace
preserving, and suppose $c \mathbf 1 \le \tau$ for its Jamiołkowski state
$\tau$. Then the largest modulus $\mu$ of an eigenvalue of $T$ in the open
unit disc satisfies $\mu \le 1 - D^2 c$.

`Notes/WolfNoteTexSource/ch08_distance_measures.tex`, lines 980–992. -/
theorem subperipheralModulus_le_of_smul_one_le_choiMatrix
    {T : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ}
    (hCP : IsKrausCP T)
    (htr : ∀ X : Matrix (Fin D) (Fin D) ℂ, (T X).trace = X.trace) {c : ℝ}
    (hc : c • (1 : Matrix (Fin D × Fin D) (Fin D × Fin D) ℂ) ≤
      ChoiRectangular.choiMatrix T) :
    Module.End.subperipheralModulus T ≤ 1 - (D : ℝ) ^ 2 * c := by
  rcases Nat.eq_zero_or_pos D with hD0 | hDpos
  · subst hD0
    simpa using Module.End.subperipheralModulus_le_one T
  have : NeZero D := ⟨hDpos.ne'⟩
  obtain ⟨hq, hcontr⟩ := traceNorm_map_le_of_smul_one_le_choiMatrix htr hc
  set q : ℝ := 1 - (D : ℝ) ^ 2 * c
  -- Powers of `T` preserve Hermiticity and tracelessness.
  have hherm_pow : ∀ (n : ℕ) (H : Matrix (Fin D) (Fin D) ℂ), H.IsHermitian →
      ((T ^ n) H).IsHermitian := by
    intro n H hH
    induction n with
    | zero => simpa using hH
    | succ m ihm =>
      rw [pow_succ', Module.End.mul_apply]
      unfold Matrix.IsHermitian
      rw [← isKrausCP_map_conjTranspose hCP, ihm.eq]
  have htr_pow : ∀ (n : ℕ) (H : Matrix (Fin D) (Fin D) ℂ), H.trace = 0 →
      ((T ^ n) H).trace = 0 := by
    intro n H hH0
    induction n with
    | zero => simpa using hH0
    | succ m ihm => rw [pow_succ', Module.End.mul_apply, htr, ihm]
  -- Powers of `T` contract traceless Hermitian matrices by `q ^ n`.
  have hpow : ∀ (n : ℕ) (H : Matrix (Fin D) (Fin D) ℂ), H.IsHermitian → H.trace = 0 →
      traceNorm ((T ^ n) H) ≤ q ^ n * traceNorm H := by
    intro n
    induction n with
    | zero => intro H _ _; simp
    | succ n ih =>
      intro H hH hH0
      rw [pow_succ', Module.End.mul_apply]
      calc traceNorm (T ((T ^ n) H))
          ≤ q * traceNorm ((T ^ n) H) := hcontr _ (hherm_pow n H hH) (htr_pow n H hH0)
        _ ≤ q * (q ^ n * traceNorm H) := mul_le_mul_of_nonneg_left (ih H hH hH0) hq
        _ = q ^ (n + 1) * traceNorm H := by ring
  -- Every subperipheral eigenvalue has modulus at most `q`.
  have hzle : ∀ z ∈ Module.End.subperipheralSpectrum T, ‖z‖ ≤ q := by
    intro z hz
    obtain ⟨X, hX⟩ := hz.1.exists_hasEigenvector
    have hTX : T X = z • X := hX.apply_eq_smul
    have hX0 : X ≠ 0 := hX.2
    have hz1 : z ≠ 1 := by
      rintro rfl
      have h := hz.2
      rw [norm_one] at h
      exact lt_irrefl _ h
    have htrX : X.trace = 0 := by
      have h := htr X
      rw [hTX, Matrix.trace_smul, smul_eq_mul] at h
      have : (z - 1) * X.trace = 0 := by rw [sub_mul, h, one_mul, sub_self]
      exact (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr hz1)
    set H : Matrix (Fin D) (Fin D) ℂ := (1 / 2 : ℂ) • (X + Xᴴ) with hH_def
    set K : Matrix (Fin D) (Fin D) ℂ := (-Complex.I / 2) • (X - Xᴴ) with hK_def
    have hHherm : H.IsHermitian := by
      unfold Matrix.IsHermitian
      rw [hH_def, conjTranspose_smul, conjTranspose_add, conjTranspose_conjTranspose,
        add_comm]
      congr 1
      simp
    have hKherm : K.IsHermitian := by
      unfold Matrix.IsHermitian
      rw [hK_def, conjTranspose_smul, conjTranspose_sub, conjTranspose_conjTranspose]
      ext i j
      simp only [smul_apply, sub_apply, smul_eq_mul]
      have : star (-Complex.I / 2) = Complex.I / 2 := by
        simp [Complex.conj_I, div_eq_mul_inv]
      rw [this]
      ring
    have htrH : H.trace = 0 := by
      rw [hH_def, Matrix.trace_smul, Matrix.trace_add, Matrix.trace_conjTranspose, htrX]
      simp
    have htrK : K.trace = 0 := by
      rw [hK_def, Matrix.trace_smul, Matrix.trace_sub, Matrix.trace_conjTranspose, htrX]
      simp
    have hXHK : X = H + Complex.I • K := by
      ext i j
      simp only [hH_def, hK_def, add_apply, smul_apply, sub_apply, smul_eq_mul]
      ring_nf
      rw [Complex.I_sq]
      ring
    set C : ℝ := traceNorm H + traceNorm K with hC
    have hbound : ∀ n : ℕ, ‖z‖ ^ n * traceNorm X ≤ q ^ n * C := by
      intro n
      have hTnX : (T ^ n) X = z ^ n • X := hX.pow_apply n
      calc ‖z‖ ^ n * traceNorm X = traceNorm ((T ^ n) X) := by
            rw [hTnX, traceNorm_smul, norm_pow]
        _ = traceNorm ((T ^ n) H + Complex.I • (T ^ n) K) := by
            congr 1
            rw [← map_smul, ← map_add, ← hXHK]
        _ ≤ traceNorm ((T ^ n) H) + traceNorm (Complex.I • (T ^ n) K) :=
            traceNorm_add_le _ _
        _ = traceNorm ((T ^ n) H) + traceNorm ((T ^ n) K) := by
            rw [traceNorm_smul, Complex.norm_I, one_mul]
        _ ≤ q ^ n * traceNorm H + q ^ n * traceNorm K :=
            add_le_add (hpow n H hHherm htrH) (hpow n K hKherm htrK)
        _ = q ^ n * C := by rw [hC]; ring
    by_contra hlt
    replace hlt := not_le.mp hlt
    have hzpos : 0 < ‖z‖ := lt_of_le_of_lt hq hlt
    have hr0 : 0 ≤ q / ‖z‖ := div_nonneg hq hzpos.le
    have hr1 : q / ‖z‖ < 1 := (div_lt_one hzpos).mpr hlt
    have hle : ∀ n : ℕ, traceNorm X ≤ (q / ‖z‖) ^ n * C := by
      intro n
      have hzn : 0 < ‖z‖ ^ n := pow_pos hzpos n
      rw [div_pow, div_mul_eq_mul_div, le_div_iff₀ hzn, mul_comm]
      exact hbound n
    have htend : Tendsto (fun n : ℕ => (q / ‖z‖) ^ n * C) atTop (𝓝 0) := by
      simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr1).mul_const C
    have hX_le : traceNorm X ≤ 0 := ge_of_tendsto' htend hle
    exact hX0 ((traceNorm_eq_zero_iff X).mp (le_antisymm hX_le (traceNorm_nonneg X)))
  by_cases hne : (Module.End.subperipheralSpectrum T).Nonempty
  · obtain ⟨z, hz, hnorm⟩ := Module.End.exists_norm_eq_subperipheralModulus T hne
    rw [← hnorm]
    exact hzle z hz
  · rw [Module.End.subperipheralModulus_eq_zero_of_empty T
      (Set.not_nonempty_iff_eq_empty.mp hne)]
    exact hq

/-- The Choi matrix of a map with a Kraus representation is positive
semidefinite, in every input dimension. -/
lemma isKrausCP_choiMatrix_posSemidef
    {T : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ}
    (hT : IsKrausCP T) : (ChoiRectangular.choiMatrix T).PosSemidef := by
  obtain ⟨r, A, hA⟩ := hT
  exact ChoiRectangular.choiMatrix_of_kraus_posSemidef A T hA

/-- A Hermitian matrix dominates its smallest eigenvalue times the identity. -/
lemma IsHermitian.iInf_eigenvalues_smul_one_le {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℂ} (hA : A.IsHermitian) :
    (⨅ i, hA.eigenvalues i) • (1 : Matrix n n ℂ) ≤ A := by
  rw [← Algebra.algebraMap_eq_smul_one, algebraMap_le_iff_le_spectrum (a := A) hA.isSelfAdjoint]
  intro x hx
  rw [hA.spectrum_real_eq_range_eigenvalues] at hx
  obtain ⟨i, rfl⟩ := hx
  exact ciInf_le (Set.finite_range _).bddBelow i

/-- **Wolf Corollary "Channel spectrum vs. Jamiolkowski spectrum"**, Eq. (8.87).

Let $T : M_d(\mathbb C) \to M_d(\mathbb C)$ be completely positive and trace
preserving with Jamiołkowski state $\tau$ (the Choi matrix of $T$ against the
normalized maximally entangled state). If $\mu$ is the largest modulus of an
eigenvalue of $T$ strictly inside the unit disc and $\lambda_{\min}(\tau)$ is
the smallest eigenvalue of $\tau$, then
$$\mu \le 1 - d^2 \lambda_{\min}(\tau).$$

The value $\mu = 0$ is used when no eigenvalue lies in the open unit disc
(`Module.End.subperipheralModulus`). For $d = 0$ the empty infimum is $0$ and
the statement reads $\mu \le 1$.

`Notes/WolfNoteTexSource/ch08_distance_measures.tex`, lines 980–992. -/
theorem subperipheralModulus_le_one_sub_sq_mul_min_eigenvalue
    {T : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ}
    (hCP : IsKrausCP T)
    (htr : ∀ X : Matrix (Fin D) (Fin D) ℂ, (T X).trace = X.trace) :
    Module.End.subperipheralModulus T ≤
      1 - (D : ℝ) ^ 2 *
        ⨅ i, (isKrausCP_choiMatrix_posSemidef hCP).isHermitian.eigenvalues i :=
  subperipheralModulus_le_of_smul_one_le_choiMatrix hCP htr
    (IsHermitian.iInf_eigenvalues_smul_one_le _)

end Matrix

end

end JamiolkowskiSpectrum
