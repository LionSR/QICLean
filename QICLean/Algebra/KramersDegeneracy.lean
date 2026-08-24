/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.Normed.Operator.LinearIsometry
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.Eigenspace.Matrix
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.LinearAlgebra.Matrix.DotProduct

/-!
# Kramers degeneracy

Wolf, *Quantum Channels & Operations*, Chapter 3, proves Kramers' theorem: a Hermitian
operator $H$ commuting with an antiunitary $T$ of square $-1$ has every eigenvalue at
least two-fold degenerate (Wolf Thm 3.1,
`Notes/WolfNoteTexSource/ch03_positive_not_completely.tex`, lines 498–521).  Wolf
reduces the statement to matrices: writing $T = \Gamma V$ with $\Gamma$ complex
conjugation and $V$ unitary, the commutation $[H, T] = 0$ becomes
$H V^\dagger = V^\dagger H^T$ and the condition $T^2 = -1$ becomes antisymmetry
$V^T = -V$ (lines 500–501).

The subsequent "Kramers' theorem II" (Wolf Thm 3.2, lines 527–530) relaxes the
unitary to a general antisymmetric intertwiner $A \neq 0$ with $H A = A H^T$ and
claims the same global degeneracy.  As printed that claim is false: with
$H = \operatorname{diag}(0, 1, 1)$ and $A$ the standard antisymmetric unit
$[[0,1],[-1,0]]$ of the $1$-eigenspace one has $H A = A H^T$ and $A^T = -A \neq 0$,
yet the eigenvalue $0$ is simple, because the partner vector $A \overline\psi$ of
the $0$-eigenvector vanishes.
The correct statement is conditional: $A \overline\psi$ is always an eigenvector of $H$
for the same eigenvalue and is always orthogonal to $\psi$, so the eigenvalue is
degenerate *whenever the partner is nonzero*; a global conclusion follows when $A$ is
injective, e.g. invertible.  The counterexample and the corrected statements are
recorded in `docs/paper-gaps/wolf_ch3_kramers_theorem_ii.tex`.

Degeneracy is expressed as `2 ≤ Module.finrank ℂ (Module.End.eigenspace H.toLin' μ)`.
Wolf's proof exhibits two orthogonal eigenvectors for the same eigenvalue, so the
eigenspace dimension is the invariant his argument bounds; the geometric multiplicity
of a Hermitian matrix also agrees with the algebraic one, so nothing is lost against
the phrase "two-fold degenerate".

## Main results

* `Matrix.dotProduct_mulVec_self_eq_zero_of_transpose_eq_neg`: the quadratic form of an
  antisymmetric complex matrix vanishes identically.
* `Matrix.two_le_finrank_eigenspace_of_linearIndependent_pair`: two independent
  eigenvectors for one eigenvalue bound the eigenspace dimension below by two.
* `Matrix.IsHermitian.transpose_mulVec_star_of_mulVec_eq_smul`: the conjugate of a
  `μ`-eigenvector of a Hermitian matrix is a `μ`-eigenvector of its transpose.
* `Matrix.IsHermitian.mulVec_star_intertwiner_of_mul_eq_mul_transpose`: eigenvector
  transport across an antisymmetric intertwiner — the partner `A *ᵥ star ψ` is again a
  `μ`-eigenvector.
* `Matrix.IsHermitian.two_le_finrank_eigenspace_of_intertwiner_mulVec_star_ne_zero`:
  the corrected conditional Kramers theorem II.
* `Matrix.IsHermitian.two_le_finrank_eigenspace_of_antisymmetric_isUnit`: the
  invertible-`A` global corollary.
* `Matrix.IsHermitian.two_le_finrank_eigenspace_of_antisymmetric_unitary`: the
  matrix form of Kramers' theorem, recovered as the unitary case of the corrected
  intertwiner theorem.
* `Matrix.IsHermitian.two_le_finrank_eigenspace_of_antiunitary`: Kramers' theorem with
  Wolf's printed antiunitary hypotheses.

## References

* Wolf, *Quantum Channels & Operations*, Chapter 3, Theorem 3.1 (Kramers' theorem)
  and Theorem 3.2 (Kramers' theorem II),
  `Notes/WolfNoteTexSource/ch03_positive_not_completely.tex`, lines 498–530.
-/

open scoped ComplexOrder Matrix

namespace Matrix

variable {n : Type*} [Fintype n]

/-- The quadratic form of an antisymmetric complex matrix vanishes: if `Mᵀ = -M`, then
`x ⬝ᵥ M *ᵥ x = 0` for every vector `x`.  This is the mechanism behind the orthogonality
step of Kramers' theorem (Wolf ch03, equations (3.29)–(3.30), lines 512–520 of
`Notes/WolfNoteTexSource/ch03_positive_not_completely.tex`). -/
theorem dotProduct_mulVec_self_eq_zero_of_transpose_eq_neg {M : Matrix n n ℂ}
    (hM : Mᵀ = -M) (x : n → ℂ) : x ⬝ᵥ M *ᵥ x = 0 := by
  have hself : x ⬝ᵥ M *ᵥ x = -(x ⬝ᵥ M *ᵥ x) := by
    calc x ⬝ᵥ M *ᵥ x = x ᵥ* M ⬝ᵥ x := Matrix.dotProduct_mulVec x M x
      _ = Mᵀ *ᵥ x ⬝ᵥ x := by rw [Matrix.mulVec_transpose]
      _ = (-M) *ᵥ x ⬝ᵥ x := by rw [hM]
      _ = -(M *ᵥ x ⬝ᵥ x) := by rw [Matrix.neg_mulVec, neg_dotProduct]
      _ = -(x ⬝ᵥ M *ᵥ x) := by rw [dotProduct_comm]
  have htwo : (2 : ℂ) * (x ⬝ᵥ M *ᵥ x) = 0 := by linear_combination hself
  simpa using htwo

omit [Fintype n] in
/-- The conjugate transpose of an antisymmetric complex matrix is again antisymmetric:
`Vᴴᵀ = -Vᴴ` whenever `Vᵀ = -V`. -/
theorem transpose_conjTranspose_eq_neg_of_transpose_eq_neg {V : Matrix n n ℂ}
    (hV : Vᵀ = -V) : Vᴴᵀ = -Vᴴ := by
  rw [← Matrix.conjTranspose_transpose_eq_transpose_conjTranspose, hV,
    Matrix.conjTranspose_neg]

/-- Two nonzero orthogonal vectors are linearly independent. -/
private theorem linearIndependent_pair_of_dotProduct_star_eq_zero {u v : n → ℂ} (hu : u ≠ 0)
    (hv : v ≠ 0) (huv : star u ⬝ᵥ v = 0) : LinearIndependent ℂ ![u, v] := by
  rw [LinearIndependent.pair_iff' hu]
  intro a hav
  refine hv ?_
  have hself : star u ⬝ᵥ u ≠ 0 := fun h => hu (dotProduct_star_self_eq_zero.mp h)
  have ha : a * (star u ⬝ᵥ u) = 0 := by
    have h : star u ⬝ᵥ (a • u) = 0 := by rw [hav]; exact huv
    rwa [dotProduct_smul, smul_eq_mul] at h
  rw [← hav, (mul_eq_zero.mp ha).resolve_right hself, zero_smul]

/-- The partner vector `A *ᵥ star ψ` of an antisymmetric intertwiner is orthogonal to
`ψ`: `star ψ ⬝ᵥ (A *ᵥ star ψ) = 0`.  This is Wolf's orthogonality calculation
(equations (3.29)–(3.30), ch03 lines 512–520) with `A` in place of `V†`. -/
theorem dotProduct_star_mulVec_star_eq_zero_of_transpose_eq_neg {A : Matrix n n ℂ}
    (hA : Aᵀ = -A) (ψ : n → ℂ) : star ψ ⬝ᵥ A *ᵥ star ψ = 0 :=
  dotProduct_mulVec_self_eq_zero_of_transpose_eq_neg hA (star ψ)

variable [DecidableEq n]

/-- Two linearly independent eigenvectors of `A` for the same eigenvalue `μ` force the
eigenspace of `μ` to have dimension at least two. -/
theorem two_le_finrank_eigenspace_of_linearIndependent_pair {A : Matrix n n ℂ} {μ : ℂ}
    {u v : n → ℂ} (hu : A *ᵥ u = μ • u) (hv : A *ᵥ v = μ • v)
    (hLI : LinearIndependent ℂ ![u, v]) :
    2 ≤ Module.finrank ℂ (Module.End.eigenspace (Matrix.toLin' A) μ) := by
  have hmem : ∀ i : Fin 2, ![u, v] i ∈ Module.End.eigenspace (Matrix.toLin' A) μ := by
    intro i
    fin_cases i <;> rw [Module.End.mem_eigenspace_iff, Matrix.toLin'_apply] <;>
      simpa using ‹_›
  have hLIsub : LinearIndependent ℂ fun i : Fin 2 => (⟨![u, v] i, hmem i⟩ :
      Module.End.eigenspace (Matrix.toLin' A) μ) :=
    LinearIndependent.of_comp (Module.End.eigenspace (Matrix.toLin' A) μ).subtype hLI
  simpa using hLIsub.fintype_card_le_finrank

end Matrix

namespace Matrix.IsHermitian

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Every eigenvalue of a Hermitian matrix is fixed by complex conjugation. -/
private theorem conj_eq_self_of_hasEigenvalue {H : Matrix n n ℂ} (hH : H.IsHermitian) {μ : ℂ}
    (hμ : Module.End.HasEigenvalue (Matrix.toLin' H) μ) : (starRingEnd ℂ) μ = μ := by
  have hspec : μ ∈ spectrum ℂ H := by
    rw [← Matrix.spectrum_toLin']
    exact Module.End.hasEigenvalue_iff_mem_spectrum.mp hμ
  rw [hH.spectrum_eq_image_range] at hspec
  obtain ⟨r, -, rfl⟩ := hspec
  simp

omit [DecidableEq n] in
/-- The entrywise conjugate of a `μ`-eigenvector of a Hermitian matrix `H` is a
`μ`-eigenvector of the transpose `Hᵀ`, provided `μ` is real (which Hermiticity of `H`
forces, see `Matrix.IsHermitian.conj_eq_self_of_hasEigenvalue`).  This is the middle
step of Wolf's ch03-line-509 calculation
`H *ᵥ (Vᴴ *ᵥ star ψ) = Vᴴ *ᵥ (Hᵀ *ᵥ star ψ) = λ • (Vᴴ *ᵥ star ψ)`, factored out so it
can be reused with a general intertwiner. -/
theorem transpose_mulVec_star_of_mulVec_eq_smul {H : Matrix n n ℂ} (hH : H.IsHermitian)
    {μ : ℂ} {ψ : n → ℂ} (hψ : H *ᵥ ψ = μ • ψ) (hμ : (starRingEnd ℂ) μ = μ) :
    Hᵀ *ᵥ star ψ = μ • star ψ := by
  rw [Matrix.mulVec_transpose, ← hH.eq, ← Matrix.star_mulVec, hψ]
  ext i
  simp [Pi.star_apply, hμ]

omit [DecidableEq n] in
/-- **Eigenvector transport across an antisymmetric intertwiner** (Wolf ch03 line 509
with `A` in place of `V†`): if `H` is Hermitian, `H * A = A * Hᵀ`, and `ψ` is a
`μ`-eigenvector of `H` with `μ` real, then the partner `A *ᵥ star ψ` is again a
`μ`-eigenvector: `H *ᵥ (A *ᵥ star ψ) = μ • (A *ᵥ star ψ)`. -/
theorem mulVec_star_intertwiner_of_mul_eq_mul_transpose {H A : Matrix n n ℂ}
    (hH : H.IsHermitian) (hHA : H * A = A * Hᵀ) {μ : ℂ} {ψ : n → ℂ}
    (hψ : H *ᵥ ψ = μ • ψ) (hμ : (starRingEnd ℂ) μ = μ) :
    H *ᵥ (A *ᵥ star ψ) = μ • (A *ᵥ star ψ) := by
  rw [Matrix.mulVec_mulVec, hHA, ← Matrix.mulVec_mulVec,
    hH.transpose_mulVec_star_of_mulVec_eq_smul hψ hμ, Matrix.mulVec_smul]

/-- **Kramers' theorem II, corrected conditional form** (Wolf Thm 3.2, ch03 lines
527–530).

Let `H` be Hermitian and let `A` be an antisymmetric intertwiner, `Aᵀ = -A` with
`H * A = A * Hᵀ`.  If `ψ` is a `μ`-eigenvector of `H` whose partner `A *ᵥ star ψ` is
nonzero, then the eigenspace of `μ` is at least two-dimensional: `ψ` and its partner
are orthogonal eigenvectors for the same eigenvalue.

Wolf's printed Theorem 3.2 assumes only `A ≠ 0` and concludes that *every* eigenvalue of
`H` is at least two-fold degenerate.  That global form is false, because the partner
`A *ᵥ star ψ` of a particular eigenvector can vanish; the nonvanishing hypothesis below
is exactly what Wolf's calculation needs and cannot be dropped (the eigenvalue `0` of
`H = diag (0, 1, 1)` with `A` the antisymmetric unit of the `1`-eigenspace is simple —
see the paper-gap note).

**Local fix (Wolf ch03, lines 527–530):** the nonvanishing hypothesis
`A *ᵥ star ψ ≠ 0` is added to the printed statement.  Counterexample and corrected
statement: `docs/paper-gaps/wolf_ch3_kramers_theorem_ii.tex`. -/
theorem two_le_finrank_eigenspace_of_intertwiner_mulVec_star_ne_zero {H A : Matrix n n ℂ}
    (hH : H.IsHermitian) (hHA : H * A = A * Hᵀ) (hAanti : Aᵀ = -A)
    {μ : ℂ} {ψ : n → ℂ} (hψ : H *ᵥ ψ = μ • ψ) (hψne : ψ ≠ 0)
    (hAψ : A *ᵥ star ψ ≠ 0) :
    2 ≤ Module.finrank ℂ (Module.End.eigenspace (Matrix.toLin' H) μ) := by
  have hμev : Module.End.HasEigenvalue (Matrix.toLin' H) μ :=
    Module.End.hasEigenvalue_of_hasEigenvector <| Module.End.hasEigenvector_iff.mpr
      ⟨Module.End.mem_eigenspace_iff.mpr (by rw [Matrix.toLin'_apply]; exact hψ), hψne⟩
  have hconj : (starRingEnd ℂ) μ = μ := conj_eq_self_of_hasEigenvalue hH hμev
  have hφ : H *ᵥ (A *ᵥ star ψ) = μ • (A *ᵥ star ψ) :=
    hH.mulVec_star_intertwiner_of_mul_eq_mul_transpose hHA hψ hconj
  have horth : star ψ ⬝ᵥ A *ᵥ star ψ = 0 :=
    Matrix.dotProduct_star_mulVec_star_eq_zero_of_transpose_eq_neg hAanti ψ
  exact Matrix.two_le_finrank_eigenspace_of_linearIndependent_pair hψ hφ
    (Matrix.linearIndependent_pair_of_dotProduct_star_eq_zero hψne hAψ horth)

/-- **Kramers' theorem II for an invertible antisymmetric intertwiner** (corrected
global form of Wolf Thm 3.2, ch03 lines 527–530): if `H` is Hermitian and `A` is an
invertible antisymmetric matrix with `H * A = A * Hᵀ`, then every eigenvalue of `H`
is at least two-fold degenerate.

Invertibility makes the partner `A *ᵥ star ψ` of every eigenvector nonzero, so the
corrected conditional theorem applies to every eigenvalue.  Over `ℂ` an antisymmetric
matrix can be invertible only in even dimension (`Aᵀ = -A` gives
`det A = (-1)^n det A`), matching Wolf's remark (lines 523–525) that antisymmetric
unitaries exist only in even dimensions.

**Local fix (Wolf ch03, lines 527–530):** the printed hypothesis `A ≠ 0` is
strengthened to invertibility of `A`, a convenient uniform hypothesis under which
Wolf's calculation closes for every eigenvalue at once.  Documented in
`docs/paper-gaps/wolf_ch3_kramers_theorem_ii.tex`. -/
theorem two_le_finrank_eigenspace_of_antisymmetric_isUnit {H A : Matrix n n ℂ}
    (hH : H.IsHermitian) (hAunit : IsUnit A) (hHA : H * A = A * Hᵀ) (hAanti : Aᵀ = -A)
    {μ : ℂ} (hμ : Module.End.HasEigenvalue (Matrix.toLin' H) μ) :
    2 ≤ Module.finrank ℂ (Module.End.eigenspace (Matrix.toLin' H) μ) := by
  obtain ⟨ψ, hψmem, hψne⟩ := hμ.exists_hasEigenvector
  have hψ : H *ᵥ ψ = μ • ψ := by
    have h := Module.End.mem_eigenspace_iff.mp hψmem
    rwa [Matrix.toLin'_apply] at h
  have hAψ : A *ᵥ star ψ ≠ 0 := by
    intro hzero
    obtain ⟨u, hu⟩ := hAunit
    have hid : (↑u⁻¹ : Matrix n n ℂ) * A = 1 := by rw [← hu, Units.inv_mul]
    have hstarψ : star ψ = 0 := by
      have h := congrArg (fun w : n → ℂ => (↑u⁻¹ : Matrix n n ℂ) *ᵥ w) hzero
      rwa [Matrix.mulVec_zero, Matrix.mulVec_mulVec, hid, Matrix.one_mulVec] at h
    exact hψne (by simpa using congrArg star hstarψ)
  exact hH.two_le_finrank_eigenspace_of_intertwiner_mulVec_star_ne_zero hHA hAanti
    hψ hψne hAψ

/-- **Kramers' theorem** (Wolf, *Quantum Channels & Operations*, Thm 3.1, ch03
lines 503–506), in Wolf's own matrix reduction of the antiunitary statement.

Wolf states the theorem for a Hermitian $H$ and an antiunitary $T$ with $[H, T] = 0$ and
$T^2 = -1$, and immediately rewrites both hypotheses in matrix terms: with $T = \Gamma V$
for $\Gamma$ complex conjugation and $V$ unitary, commutation is
$H V^\dagger = V^\dagger H^T$ and $T^2 = -1$ is antisymmetry $V^T = -V$ (lines 500–501).
Those two matrix identities, together with $V^\dagger V = 1$, are the hypotheses below,
so the statement is Wolf's with the antiunitary rewritten exactly as he rewrites it; no
further hypothesis is imposed.

"At least two-fold degenerate" is `2 ≤ Module.finrank ℂ (Module.End.eigenspace H.toLin' μ)`:
Wolf's proof produces a second eigenvector orthogonal to the first, so the eigenspace
dimension is what the argument bounds.

The relation to the corrected Kramers theorem II is direct: this is the case
`A = Vᴴ` of `two_le_finrank_eigenspace_of_antisymmetric_isUnit`, where `Vᴴ` is
antisymmetric because `V` is, and invertible because `V` is unitary.  Wolf's proof is
exactly this specialization: from $H \psi = \mu \psi$ the partner
$\varphi = V^\dagger \overline{\psi}$ is nonzero by unitarity, satisfies
$H \varphi = \mu \varphi$ by transport, and is orthogonal to $\psi$ because the
quadratic form of the antisymmetric matrix $V^\dagger$ vanishes. -/
theorem two_le_finrank_eigenspace_of_antisymmetric_unitary {H V : Matrix n n ℂ}
    (hH : H.IsHermitian) (hVunit : Vᴴ * V = 1) (hHV : H * Vᴴ = Vᴴ * Hᵀ) (hVanti : Vᵀ = -V)
    {μ : ℂ} (hμ : Module.End.HasEigenvalue (Matrix.toLin' H) μ) :
    2 ≤ Module.finrank ℂ (Module.End.eigenspace (Matrix.toLin' H) μ) :=
  hH.two_le_finrank_eigenspace_of_antisymmetric_isUnit
    (isUnit_iff_exists.mpr ⟨V, hVunit, mul_eq_one_comm.mp hVunit⟩) hHV
    (Matrix.transpose_conjTranspose_eq_neg_of_transpose_eq_neg hVanti) hμ

/-- **Kramers' theorem** in Wolf's printed antiunitary form (Thm 3.1, ch03 lines
503–505).

Let $H$ be Hermitian and let $T$ be antiunitary. If $H$ commutes with $T$ and
$T^2=-\Id$, then every eigenspace of $H$ has dimension at least two. Here
antiunitarity is represented by a conjugate-linear isometric equivalence; the two
operator identities are stated pointwise, without choosing a matrix factorization
of $T$.

Indeed, if $H\psi=\mu\psi$, then Hermiticity makes $\mu$ real and commutation gives
$H(T\psi)=\mu T\psi$. The vectors $\psi$ and $T\psi$ are independent: a relation
$T\psi=a\psi$ would imply $-\psi=T^2\psi=\overline a a\psi$, contradicting
$\overline a a=|a|^2\geq 0$.

Source: Wolf, *Quantum Channels & Operations*, Chapter 3, Kramers' theorem;
`Notes/WolfNoteTexSource/ch03_positive_not_completely.tex`, lines 500–505. -/
theorem two_le_finrank_eigenspace_of_antiunitary
    {H : Matrix n n ℂ} (hH : H.IsHermitian)
    (T : (n → ℂ) ≃ₗᵢ⋆[ℂ] (n → ℂ))
    (hcomm : ∀ ψ, H *ᵥ T ψ = T (H *ᵥ ψ))
    (hsq : ∀ ψ, T (T ψ) = -ψ)
    {μ : ℂ} (hμ : Module.End.HasEigenvalue (Matrix.toLin' H) μ) :
    2 ≤ Module.finrank ℂ (Module.End.eigenspace (Matrix.toLin' H) μ) := by
  obtain ⟨ψ, hψmem, hψne⟩ := hμ.exists_hasEigenvector
  have hψ : H *ᵥ ψ = μ • ψ := by
    have := Module.End.mem_eigenspace_iff.mp hψmem
    rwa [Matrix.toLin'_apply] at this
  have hconj : star μ = μ := by
    simpa using conj_eq_self_of_hasEigenvalue hH hμ
  let φ : n → ℂ := T ψ
  have hφ : H *ᵥ φ = μ • φ := by
    calc
      H *ᵥ φ = T (H *ᵥ ψ) := hcomm ψ
      _ = T (μ • ψ) := by rw [hψ]
      _ = star μ • φ := T.map_smulₛₗ μ ψ
      _ = μ • φ := by rw [hconj]
  have hφne : φ ≠ 0 := by
    intro hzero
    apply hψne
    exact T.injective (by simpa [φ] using hzero)
  have hLI : LinearIndependent ℂ ![ψ, φ] := by
    rw [LinearIndependent.pair_iff' hψne]
    intro a ha
    have hscalar : star a * a = -1 := by
      apply smul_left_injective ℂ hψne
      calc
        (star a * a) • ψ = star a • a • ψ := by rw [smul_smul]
        _ = star a • φ := by rw [ha]
        _ = T (a • ψ) := by
          simpa [φ] using (T.map_smulₛₗ a ψ).symm
        _ = T φ := by rw [ha]
        _ = -ψ := hsq ψ
        _ = (-1 : ℂ) • ψ := by simp
    have hnormSq : (Complex.normSq a : ℂ) = -1 := by
      rw [Complex.normSq_eq_conj_mul_self]
      exact hscalar
    have hre := congrArg Complex.re hnormSq
    norm_num at hre
    exact (not_lt_of_ge (Complex.normSq_nonneg a)) (by linarith)
  exact Matrix.two_le_finrank_eigenspace_of_linearIndependent_pair hψ hφ hLI

end Matrix.IsHermitian
