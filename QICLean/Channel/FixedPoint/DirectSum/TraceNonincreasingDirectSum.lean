/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Channel.FixedPoint.DirectSum.DirectSumExtension
import QICLean.Channel.FixedPoint.Stationary.MaximalSupportBasic
import QICLean.Channel.FixedPoint.MeanErgodic.MeanErgodicAdjoint

/-!
# Trace-nonincreasing maps on finite sums of matrix algebras

The canonical block-diagonal extension transfers trace nonincrease and fixed
product generators from a finite direct sum to a full matrix algebra.  The
full-matrix product-span theorem then gives trace preservation on the original
direct sum.  For a trace-preserving endomorphism, the same extension also
produces a componentwise positive-definite fixed family.

This is the finite-direct-sum form needed for arXiv:1606.00608, Appendix C.4.
Lines 1974--1980 identify the fixed contraction families, and lines
1980--1995 place them in the spanning argument.

It also contains the following results.

* `IsPositiveMap.exists_posDef_fixedPoint_of_traceNonincreasing_of_fixed_product_span`,
  `IsPositiveMap.tracePreserving_of_traceNonincreasing_of_fixed_product_span`: trace preservation
  from fixed product generators.
-/

section TraceNonincreasingProductSpan

/-!
## Trace preservation from fixed product generators

A positive trace-nonincreasing endomorphism is trace preserving when a
positive-length product family of its fixed points spans the identity.  The
mean-ergodic image of the identity has maximal support among fixed points.
Every product of fixed generators remains on that support; spanning the
identity therefore makes the mean-ergodic fixed point faithful.  The positive
trace-loss functional must then vanish.

This supplies the channel hypothesis used silently for the transported
vertical-sector composites in arXiv:1606.00608, Appendix C.4.  Lines
1974--1980 identify the fixed contraction generators, and lines 1980--1995
place them in the spanning argument.

### Main results

* `IsPositiveMap.exists_posDef_fixedPoint_of_traceNonincreasing_of_fixed_product_span`
* `IsPositiveMap.tracePreserving_of_traceNonincreasing_of_fixed_product_span`

### References

* M. Wolf, *Quantum Channels & Operations: Guided Tour*, Proposition 6.3 and
  Proposition 6.9.
* Cirac--Perez-Garcia--Schuch--Verstraete, arXiv:1606.00608, Appendix C.4,
  lines 1974--1980 and 1980--1995.
-/

open Filter Function Set
open scoped Matrix ComplexOrder MatrixOrder Matrix.Norms.Frobenius Topology

variable {D : ℕ}

open Kraus

/-- A positive trace-nonincreasing endomorphism has a positive-definite fixed
point when the identity lies in the span of positive-length products of a
fixed family.

No product is assumed to be fixed.  The fixed factors lie on the support of
the mean-ergodic image of the identity, so their products do as well.  The
product-span hypothesis forces this support to be the identity.

This is the channel-hypothesis step used at arXiv:1606.00608, Appendix C.4.
Lines 1974--1980 supply the fixed contraction factors; lines 1980--1995
supply their spanning context. -/
private theorem
    IsPositiveMap.exists_posDef_fixedPoint_of_traceNonincreasing_of_fixed_product_span_fin
    {J : Type*}
    {T : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ}
    (hT : IsPositiveMap T) (hTNI : IsTraceNonincreasingMap T)
    (V : J → Matrix (Fin D) (Fin D) ℂ) (L : ℕ) (hL : 0 < L)
    (hFixed : ∀ j, T (V j) = V j)
    (hOne : (1 : Matrix (Fin D) (Fin D) ℂ) ∈
      Submodule.span ℂ (Set.range fun x : Fin L → J =>
        (List.ofFn fun t => V (x t)).prod)) :
    ∃ ρ : Matrix (Fin D) (Fin D) ℂ, ρ.PosDef ∧ T ρ = ρ := by
  classical
  let hbounded := hT.hasBoundedOrbits_of_traceNonincreasing hTNI
  let ρ := LinearMap.meanErgodicProjection (𝕜 := ℂ)
    (E := Matrix (Fin D) (Fin D) ℂ) T hbounded 1
  obtain ⟨hρ, hρfixed, hMaxSupport⟩ :=
    hT.exists_maximalSupport_fixedPoint_of_hasBoundedOrbits hbounded
  let Q := stationaryProj hρ
  have hQidem : Q * Q = Q := (isOrthogonalProjection_stationaryProj hρ).2
  have hVsupport (j : J) : Q * V j * Q = V j := hMaxSupport _ (hFixed j)
  have hVleft (j : J) : Q * V j = V j := by
    calc
      Q * V j = Q * (Q * V j * Q) := by rw [hVsupport j]
      _ = (Q * Q) * V j * Q := by simp [Matrix.mul_assoc]
      _ = Q * V j * Q := by rw [hQidem]
      _ = V j := hVsupport j
  have hVright (j : J) : V j * Q = V j := by
    calc
      V j * Q = (Q * V j * Q) * Q := by rw [hVsupport j]
      _ = Q * V j * (Q * Q) := by simp [Matrix.mul_assoc]
      _ = Q * V j * Q := by rw [hQidem]
      _ = V j := hVsupport j
  have hProdAbsorb (l : List J) (hl : l ≠ []) :
      Q * (l.map V).prod = (l.map V).prod ∧
        (l.map V).prod * Q = (l.map V).prod := by
    induction l with
    | nil => exact (hl rfl).elim
    | cons a l ih =>
        constructor
        · simp only [List.map_cons, List.prod_cons]
          rw [← Matrix.mul_assoc, hVleft a]
        · cases l with
          | nil => simpa using hVright a
          | cons b l =>
              have ihtail := (ih (by simp)).2
              simp only [List.map_cons, List.prod_cons] at ihtail ⊢
              calc
                (V a * (V b * (List.map V l).prod)) * Q =
                    V a * ((V b * (List.map V l).prod) * Q) :=
                  Matrix.mul_assoc _ _ _
                _ = V a * (V b * (List.map V l).prod) := by rw [ihtail]
  have hProductSupport (x : Fin L → J) :
      Q * (List.ofFn fun t => V (x t)).prod * Q =
        (List.ofFn fun t => V (x t)).prod := by
    have hne : List.ofFn x ≠ [] := by
      intro hempty
      have hlen := congrArg List.length hempty
      simp only [List.length_ofFn, List.length_nil] at hlen
      omega
    have habsorb := hProdAbsorb (List.ofFn x) hne
    rw [List.map_ofFn] at habsorb
    have hfun : V ∘ x = fun t => V (x t) := rfl
    rw [hfun] at habsorb
    calc
      Q * (List.ofFn fun t => V (x t)).prod * Q =
          (List.ofFn fun t => V (x t)).prod * Q := by rw [habsorb.1]
      _ = (List.ofFn fun t => V (x t)).prod := habsorb.2
  have hOneSupport : Q * (1 : Matrix (Fin D) (Fin D) ℂ) * Q = 1 := by
    exact Submodule.span_induction (p := fun X _ => Q * X * Q = X)
      (fun Y hY => by
        obtain ⟨x, rfl⟩ := hY
        exact hProductSupport x)
      (by simp)
      (fun X Y _ _ hX hY => by
        rw [Matrix.mul_add, Matrix.add_mul, hX, hY])
      (fun c X _ hX => by
        rw [Matrix.mul_smul, Matrix.smul_mul, hX])
      hOne
  have hQone : Q = 1 := by
    simpa [hQidem] using hOneSupport
  have hρposDef : ρ.PosDef := hρ.posDef_of_supportProj_eq_one hQone
  exact ⟨ρ, hρposDef, hρfixed⟩

/-- A positive trace-nonincreasing endomorphism of a finite matrix algebra has
a positive-definite fixed point when the identity lies in the span of
positive-length products of a fixed family.

No product is assumed to be fixed. The maximal-support fixed point contains
every fixed factor, hence every positive-length product of those factors. The
spanning hypothesis makes its support the whole matrix algebra.

This is the faithful fixed-point step used in arXiv:1606.00608, Appendix C.4,
lines 1980--1995, before applying the density-block classification of the
fixed-point space. -/
theorem IsPositiveMap.exists_posDef_fixedPoint_of_traceNonincreasing_of_fixed_product_span
    {n J : Type*} [Fintype n] [DecidableEq n]
    {T : Matrix n n ℂ →ₗ[ℂ] Matrix n n ℂ}
    (hT : IsPositiveMap T) (hTNI : IsTraceNonincreasingMap T)
    (V : J → Matrix n n ℂ) (L : ℕ) (hL : 0 < L)
    (hFixed : ∀ j, T (V j) = V j)
    (hOne : (1 : Matrix n n ℂ) ∈
      Submodule.span ℂ (Set.range fun x : Fin L → J =>
        (List.ofFn fun t => V (x t)).prod)) :
    ∃ ρ : Matrix n n ℂ, ρ.PosDef ∧ T ρ = ρ := by
  classical
  let e : n ≃ Fin (Fintype.card n) := Fintype.equivFin n
  let Φ := Matrix.reindexLinearEquiv ℂ ℂ e e
  let TFin := Matrix.reindexEndomorphism e T
  let VFin : J → Matrix (Fin (Fintype.card n)) (Fin (Fintype.card n)) ℂ :=
    fun j => Matrix.reindex e e (V j)
  have hTFin : IsPositiveMap TFin :=
    Matrix.IsPositiveMap.reindexEndomorphism hT e
  have hTNIFin : IsTraceNonincreasingMap TFin :=
    Matrix.IsTraceNonincreasingMap.reindexEndomorphism hTNI e
  have hreindex_symm (A : Matrix n n ℂ) :
      Matrix.reindex e.symm e.symm (Matrix.reindex e e A) = A := by
    simpa only [Matrix.coe_reindexLinearEquiv,
      Matrix.symm_reindexLinearEquiv] using
      (Matrix.reindexLinearEquiv ℂ ℂ e e).symm_apply_apply A
  have hFixedFin (j : J) : TFin (VFin j) = VFin j := by
    change Matrix.reindex e e
        (T (Matrix.reindex e.symm e.symm (Matrix.reindex e e (V j)))) =
      Matrix.reindex e e (V j)
    rw [hreindex_symm, hFixed]
  have hreindexProd (l : List J) :
      Matrix.reindex e e (l.map V).prod = (l.map VFin).prod := by
    induction l with
    | nil =>
        ext i j
        simp [Matrix.reindex_apply, Matrix.one_apply]
    | cons a l ih =>
        simp only [List.map_cons, List.prod_cons]
        calc
          Matrix.reindex e e (V a * (l.map V).prod) =
              Matrix.reindex e e (V a) * Matrix.reindex e e (l.map V).prod :=
            (Matrix.reindexLinearEquiv_mul ℂ ℂ e e e _ _).symm
          _ = VFin a * (l.map VFin).prod := by rw [ih]
  let productSpanFin := Submodule.span ℂ
    (Set.range fun x : Fin L → J => (List.ofFn fun t => VFin (x t)).prod)
  have hOneFin :
      (1 : Matrix (Fin (Fintype.card n)) (Fin (Fintype.card n)) ℂ) ∈
        productSpanFin := by
    have hReindexOne : Matrix.reindex e e (1 : Matrix n n ℂ) = 1 := by
      simpa only [List.map_nil, List.prod_nil] using hreindexProd ([] : List J)
    rw [← hReindexOne]
    exact Submodule.span_induction (p := fun X _ =>
        Matrix.reindex e e X ∈ productSpanFin)
      (fun X hX => by
        obtain ⟨x, rfl⟩ := hX
        apply Submodule.subset_span
        refine ⟨x, ?_⟩
        have hprod := hreindexProd (List.ofFn x)
        rw [List.map_ofFn, List.map_ofFn] at hprod
        have hfun : V ∘ x = fun t => V (x t) := rfl
        have hfunFin : VFin ∘ x = fun t => VFin (x t) := rfl
        simpa only [hfun, hfunFin] using hprod.symm)
      (by
        change Φ 0 ∈ productSpanFin
        rw [map_zero]
        exact Submodule.zero_mem productSpanFin)
      (fun X Y _ _ hX hY => by
        change Φ (X + Y) ∈ productSpanFin
        rw [map_add]
        exact Submodule.add_mem productSpanFin hX hY)
      (fun c X _ hX => by
        change Φ (c • X) ∈ productSpanFin
        rw [_root_.map_smul]
        exact Submodule.smul_mem productSpanFin c hX)
      hOne
  obtain ⟨ρFin, hρFin, hρFinFixed⟩ :=
    hTFin.exists_posDef_fixedPoint_of_traceNonincreasing_of_fixed_product_span_fin
      hTNIFin VFin L hL hFixedFin hOneFin
  let ρ := Φ.symm ρFin
  have hρ : ρ.PosDef := by
    exact hρFin.reindex e.symm
  have hρFixed : T ρ = ρ := by
    have hΦρ : Φ ρ = ρFin := Φ.apply_symm_apply ρFin
    apply Φ.injective
    calc
      Φ (T ρ) = TFin (Φ ρ) := by
        change Matrix.reindex e e (T ρ) = Matrix.reindex e e
          (T (Matrix.reindex e.symm e.symm (Matrix.reindex e e ρ)))
        rw [hreindex_symm]
      _ = Φ ρ := by rw [hΦρ, hρFinFixed]
  exact ⟨ρ, hρ, hρFixed⟩

/-- A positive trace-nonincreasing endomorphism of a finite matrix algebra is
trace preserving when the identity lies in the span of positive-length
products of a fixed family.

This coordinate-free finite-index form is obtained from the preceding
`Fin`-indexed argument by simultaneous matrix reindexing.  In
arXiv:1606.00608, Appendix C.4, lines 1974--1980 supply the fixed factors to
which this criterion is applied. -/
theorem IsPositiveMap.tracePreserving_of_traceNonincreasing_of_fixed_product_span
    {n J : Type*} [Fintype n] [DecidableEq n]
    {T : Matrix n n ℂ →ₗ[ℂ] Matrix n n ℂ}
    (hT : IsPositiveMap T) (hTNI : IsTraceNonincreasingMap T)
    (V : J → Matrix n n ℂ) (L : ℕ) (hL : 0 < L)
    (hFixed : ∀ j, T (V j) = V j)
    (hOne : (1 : Matrix n n ℂ) ∈
      Submodule.span ℂ (Set.range fun x : Fin L → J =>
        (List.ofFn fun t => V (x t)).prod)) :
    IsTracePreservingMap T := by
  obtain ⟨ρ, hρposDef, hρfixed⟩ :=
    hT.exists_posDef_fixedPoint_of_traceNonincreasing_of_fixed_product_span
      hTNI V L hL hFixed hOne
  let gap : Matrix n n ℂ := 1 - Matrix.traceAdjointMap T 1
  have hAdjointOne : (Matrix.traceAdjointMap T 1).PosSemidef :=
    IsPositiveMap.traceAdjointMap hT 1 Matrix.PosSemidef.one
  have hGapHermitian : gap.IsHermitian := by
    exact Matrix.IsHermitian.sub Matrix.isHermitian_one hAdjointOne.isHermitian
  have hGap : gap.PosSemidef := by
    apply Matrix.PosSemidef.of_forall_trace_mul_nonneg hGapHermitian
    intro X hX
    have hloss : 0 ≤ Matrix.trace X - Matrix.trace (T X) :=
      sub_nonneg.mpr (hTNI X hX)
    simpa only [gap, Matrix.sub_mul, Matrix.trace_sub, Matrix.one_mul,
      Matrix.trace_traceAdjointMap_mul] using hloss
  have hGapTrace : Matrix.trace (ρ * gap) = 0 := by
    calc
      Matrix.trace (ρ * gap) = Matrix.trace (gap * ρ) := Matrix.trace_mul_comm _ _
      _ = Matrix.trace ρ - Matrix.trace (T ρ) := by
        simp only [gap, Matrix.sub_mul, Matrix.trace_sub, Matrix.one_mul,
          Matrix.trace_traceAdjointMap_mul]
      _ = 0 := by rw [hρfixed, sub_self]
  have hGapZero : gap = 0 :=
    Matrix.posSemidef_eq_zero_of_posDef_trace_mul_eq_zero hGap hρposDef hGapTrace
  change 1 - Matrix.traceAdjointMap T 1 = 0 at hGapZero
  have hAdjointOneEq : Matrix.traceAdjointMap T 1 = 1 :=
    (sub_eq_zero.mp hGapZero).symm
  exact isTracePreservingMap_iff_traceAdjointMap_one.mpr hAdjointOneEq

end TraceNonincreasingProductSpan

section TraceNonincreasingDirectSum

open scoped Matrix ComplexOrder MatrixOrder

namespace Matrix

variable {ι : Type*} {n : ι → Type*}
variable [Fintype ι] [DecidableEq ι]
variable [(k : ι) → Fintype (n k)] [(k : ι) → DecidableEq (n k)]

/-- The total trace on a finite direct sum of matrix algebras, as a complex
linear functional. -/
noncomputable def directSumTraceLinearMap :
    (∀ k, Matrix (n k) (n k) ℂ) →ₗ[ℂ] ℂ where
  toFun A := ∑ k, (A k).trace
  map_add' A B := by simp only [Pi.add_apply, trace_add, Finset.sum_add_distrib]
  map_smul' c A := by
    simp only [Pi.smul_apply, trace_smul, RingHom.id_apply, Finset.smul_sum]

/-- A map between two finite direct sums of matrix algebras preserves their
respective total traces. -/
def IsTracePreservingBetweenDirectSums
    {κ : Type*} {m : κ → Type*} [Fintype κ] [(l : κ) → Fintype (m l)]
    (T : (∀ k, Matrix (n k) (n k) ℂ) →ₗ[ℂ]
      (∀ l, Matrix (m l) (m l) ℂ)) : Prop :=
  ∀ A, ∑ l, (T A l).trace = ∑ k, (A k).trace

omit [DecidableEq ι] [(k : ι) → DecidableEq (n k)] in
/-- For an endomorphism of one finite direct sum, the rectangular and
endomorphism formulations of total-trace preservation agree. -/
theorem isTracePreservingBetweenDirectSums_iff_isTracePreservingDirectSumMap
    {T : (∀ k, Matrix (n k) (n k) ℂ) →ₗ[ℂ]
      (∀ k, Matrix (n k) (n k) ℂ)} :
    IsTracePreservingBetweenDirectSums T ↔ IsTracePreservingDirectSumMap T :=
  Iff.rfl

/-- A map between two finite direct sums does not increase the total trace of
a positive family. -/
def IsTraceNonincreasingBetweenDirectSums
    {κ : Type*} {m : κ → Type*} [Fintype κ] [(l : κ) → Fintype (m l)]
    (T : (∀ k, Matrix (n k) (n k) ℂ) →ₗ[ℂ]
      (∀ l, Matrix (m l) (m l) ℂ)) : Prop :=
  ∀ A, (∀ k, (A k).PosSemidef) →
    (∑ l, (T A l).trace) ≤ ∑ k, (A k).trace

omit [DecidableEq ι] [(k : ι) → DecidableEq (n k)] in
/-- Equality of total traces on positive families extends to every family. -/
theorem isTracePreservingBetweenDirectSums_of_posSemidef
    {κ : Type*} {m : κ → Type*}
    [Fintype κ] [(l : κ) → Fintype (m l)]
    {T : (∀ k, Matrix (n k) (n k) ℂ) →ₗ[ℂ]
      (∀ l, Matrix (m l) (m l) ℂ)}
    (hT : ∀ A, (∀ k, (A k).PosSemidef) →
      (∑ l, (T A l).trace) = ∑ k, (A k).trace) :
    IsTracePreservingBetweenDirectSums T := by
  classical
  let τin : (∀ k, Matrix (n k) (n k) ℂ) →ₗ[ℂ] ℂ := directSumTraceLinearMap
  let τout : (∀ l, Matrix (m l) (m l) ℂ) →ₗ[ℂ] ℂ := directSumTraceLinearMap
  have hHermitian (H : ∀ k, Matrix (n k) (n k) ℂ)
      (hH : ∀ k, (H k).IsHermitian) : τout (T H) = τin H := by
    let P : ∀ k, Matrix (n k) (n k) ℂ := fun k ↦ (H k)⁺
    let N : ∀ k, Matrix (n k) (n k) ℂ := fun k ↦ (H k)⁻
    have hP : ∀ k, (P k).PosSemidef := fun k ↦
      nonneg_iff_posSemidef.mp (CFC.posPart_nonneg (H k))
    have hN : ∀ k, (N k).PosSemidef := fun k ↦
      nonneg_iff_posSemidef.mp (CFC.negPart_nonneg (H k))
    have hdecomp : P - N = H := by
      funext k
      exact CFC.posPart_sub_negPart (H k) (isSelfAdjoint_iff.mpr (hH k))
    have hPtrace : τout (T P) = τin P := hT P hP
    have hNtrace : τout (T N) = τin N := hT N hN
    calc
      τout (T H) = τout (T (P - N)) := by rw [hdecomp]
      _ = τout (T P) - τout (T N) := by rw [map_sub, map_sub]
      _ = τin P - τin N := by rw [hPtrace, hNtrace]
      _ = τin (P - N) := by rw [map_sub]
      _ = τin H := by rw [hdecomp]
  intro X
  let H₁ : ∀ k, Matrix (n k) (n k) ℂ := fun k ↦ X k + (X k)ᴴ
  let H₂ : ∀ k, Matrix (n k) (n k) ℂ := fun k ↦
    Complex.I • (X k - (X k)ᴴ)
  have hH₁ : ∀ k, (H₁ k).IsHermitian := by
    intro k
    ext i j
    simp [H₁, add_comm]
  have hH₂ : ∀ k, (H₂ k).IsHermitian := by
    intro k
    ext i j
    simp [H₂, sub_eq_add_neg, add_comm]
  have hdecomp : X = (2 : ℂ)⁻¹ • (H₁ - Complex.I • H₂) := by
    funext k i j
    simp only [H₁, H₂, Pi.smul_apply, Pi.sub_apply, Matrix.add_apply,
      Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
    ring_nf
    rw [Complex.I_sq]
    ring
  have hH₁trace := hHermitian H₁ hH₁
  have hH₂trace := hHermitian H₂ hH₂
  change τout (T X) = τin X
  rw [hdecomp]
  simp only [map_smul, map_sub, hH₁trace, hH₂trace]

omit [DecidableEq ι] [(k : ι) → DecidableEq (n k)] in
/-- If two positive trace-nonincreasing maps have a trace-preserving square
composite, then the first map preserves the total trace.

For a positive input, trace nonincrease gives
`tr(S(T(X))) ≤ tr(T(X)) ≤ tr(X)`, while preservation by the composite makes
the endpoints equal. -/
theorem isTracePreservingBetweenDirectSums_of_comp_of_traceNonincreasing
    {κ : Type*} {m : κ → Type*}
    [Fintype κ] [(l : κ) → Fintype (m l)]
    {T : (∀ k, Matrix (n k) (n k) ℂ) →ₗ[ℂ]
      (∀ l, Matrix (m l) (m l) ℂ)}
    {S : (∀ l, Matrix (m l) (m l) ℂ) →ₗ[ℂ]
      (∀ k, Matrix (n k) (n k) ℂ)}
    (hTpos : ∀ A, (∀ k, (A k).PosSemidef) →
      ∀ l, (T A l).PosSemidef)
    (hTNI : IsTraceNonincreasingBetweenDirectSums T)
    (hSNI : IsTraceNonincreasingBetweenDirectSums S)
    (hComp : IsTracePreservingBetweenDirectSums (S.comp T)) :
    IsTracePreservingBetweenDirectSums T := by
  apply isTracePreservingBetweenDirectSums_of_posSemidef
  intro A hA
  apply le_antisymm (hTNI A hA)
  rw [← hComp A]
  exact hSNI (T A) (hTpos A hA)

omit [(k : ι) → DecidableEq (n k)] in
/-- Trace nonincrease passes to the canonical full-matrix extension. -/
theorem IsTraceNonincreasingBetweenDirectSums.directSumExtension
    {T : (∀ k, Matrix (n k) (n k) ℂ) →ₗ[ℂ]
      (∀ k, Matrix (n k) (n k) ℂ)}
    (hT : IsTraceNonincreasingBetweenDirectSums T) :
    IsTraceNonincreasingMap (directSumExtension T) := by
  intro A hA
  rw [directSumExtension_apply, trace_directSumDiagonalEmbedding]
  exact (hT (directSumDiagonalCompression A) fun k =>
    directSumDiagonalCompression_posSemidef hA k).trans_eq
      (sum_trace_directSumDiagonalCompression A)

omit [(k : ι) → DecidableEq (n k)] in
/-- Trace preservation of the full-matrix extension restricts to preservation
of the total trace on the direct sum. -/
theorem IsTracePreservingMap.isTracePreservingDirectSumMap_of_extension
    {T : (∀ k, Matrix (n k) (n k) ℂ) →ₗ[ℂ]
      (∀ k, Matrix (n k) (n k) ℂ)}
    (hT : IsTracePreservingMap (directSumExtension T)) :
    IsTracePreservingDirectSumMap T := by
  intro A
  have h := hT (directSumDiagonalEmbedding A)
  simpa only [directSumExtension_apply, directSumDiagonalCompression_embedding,
    trace_directSumDiagonalEmbedding] using h

/-- The block-diagonal embedding carries identity membership in a span of
pointwise products to identity membership in the corresponding full-matrix
product span. -/
private theorem directSumDiagonalEmbedding_one_mem_product_span
    {J : Type*}
    (V : J → (∀ k, Matrix (n k) (n k) ℂ))
    (L : ℕ)
    (hOne : (1 : ∀ k, Matrix (n k) (n k) ℂ) ∈
      Submodule.span ℂ (Set.range fun x : Fin L → J ↦
        (List.ofFn fun t ↦ V (x t)).prod)) :
    (1 : Matrix ((k : ι) × n k) ((k : ι) × n k) ℂ) ∈
      Submodule.span ℂ (Set.range fun x : Fin L → J ↦
        (List.ofFn fun t ↦ directSumDiagonalEmbedding (V (x t))).prod) := by
  classical
  let productSpan := Submodule.span ℂ
    (Set.range fun x : Fin L → J ↦
      (List.ofFn fun t ↦ directSumDiagonalEmbedding (V (x t))).prod)
  have hEmbeddingProd (l : List J) :
      directSumDiagonalEmbedding (l.map V).prod =
        (l.map (fun j ↦ directSumDiagonalEmbedding (V j))).prod := by
    induction l with
    | nil =>
        simp only [List.map_nil, List.prod_nil]
        exact Matrix.blockDiagonal'_one
    | cons a l ih =>
        simp only [List.map_cons, List.prod_cons]
        rw [directSumDiagonalEmbedding_mul, ih]
  have hOneEmbedded :
      directSumDiagonalEmbedding (1 : ∀ k, Matrix (n k) (n k) ℂ) = 1 :=
    Matrix.blockDiagonal'_one
  rw [← hOneEmbedded]
  exact Submodule.span_induction (p := fun X _ ↦
      directSumDiagonalEmbedding X ∈ productSpan)
    (fun X hX ↦ by
      obtain ⟨x, rfl⟩ := hX
      apply Submodule.subset_span
      refine ⟨x, ?_⟩
      have hprod := hEmbeddingProd (List.ofFn x)
      rw [List.map_ofFn, List.map_ofFn] at hprod
      have hfun : V ∘ x = fun t ↦ V (x t) := rfl
      have hfunW : (fun j ↦ directSumDiagonalEmbedding (V j)) ∘ x =
          fun t ↦ directSumDiagonalEmbedding (V (x t)) := rfl
      simpa only [hfun, hfunW] using hprod.symm)
    (by
      rw [map_zero]
      exact Submodule.zero_mem productSpan)
    (fun X Y _ _ hX hY ↦ by
      rw [map_add]
      exact Submodule.add_mem productSpan hX hY)
    (fun c X _ hX ↦ by
      rw [_root_.map_smul]
      exact Submodule.smul_mem productSpan c hX)
    hOne

omit [DecidableEq ι] in
/-- A positive trace-nonincreasing endomorphism of a finite sum of matrix
algebras preserves the total trace when the identity family lies in the span
of positive-length products of fixed families.

The block-diagonal embedding preserves products and the identity, so the
full-matrix fixed-product criterion applies to the canonical extension.  This
is the finite-sector form of the channel-hypothesis step in
arXiv:1606.00608, Appendix C.4.  Lines 1974--1980 supply the fixed
contraction families; lines 1980--1995 supply their spanning context. -/
theorem IsPositiveDirectSumMap.tracePreserving_of_traceNonincreasing_of_fixed_product_span
    {J : Type*}
    {T : (∀ k, Matrix (n k) (n k) ℂ) →ₗ[ℂ]
      (∀ k, Matrix (n k) (n k) ℂ)}
    (hT : IsPositiveDirectSumMap T)
    (hTNI : IsTraceNonincreasingBetweenDirectSums T)
    (V : J → (∀ k, Matrix (n k) (n k) ℂ))
    (L : ℕ) (hL : 0 < L)
    (hFixed : ∀ j, T (V j) = V j)
    (hOne : (1 : ∀ k, Matrix (n k) (n k) ℂ) ∈
      Submodule.span ℂ (Set.range fun x : Fin L → J ↦
        (List.ofFn fun t ↦ V (x t)).prod)) :
    IsTracePreservingDirectSumMap T := by
  classical
  let E := directSumExtension T
  let W : J → Matrix ((k : ι) × n k) ((k : ι) × n k) ℂ :=
    fun j ↦ directSumDiagonalEmbedding (V j)
  have hEpos : IsPositiveMap E := hT.directSumExtension_isPositiveMap
  have hETNI : IsTraceNonincreasingMap E := hTNI.directSumExtension
  have hWFixed (j : J) : E (W j) = W j := by
    exact (directSumExtension_embedding_eq_self_iff T (V j)).2 (hFixed j)
  have hOneFull :
      (1 : Matrix ((k : ι) × n k) ((k : ι) × n k) ℂ) ∈
        Submodule.span ℂ (Set.range fun x : Fin L → J ↦
          (List.ofFn fun t ↦ W (x t)).prod) := by
    simpa only [W] using directSumDiagonalEmbedding_one_mem_product_span V L hOne
  have hETrace : IsTracePreservingMap E :=
    hEpos.tracePreserving_of_traceNonincreasing_of_fixed_product_span
      hETNI W L hL hWFixed hOneFull
  exact Matrix.IsTracePreservingMap.isTracePreservingDirectSumMap_of_extension hETrace

omit [DecidableEq ι] in
/-- A positive trace-preserving endomorphism of a finite product of matrix
algebras has a positive-definite fixed family when the identity belongs to
the span of positive-length products of a fixed family.

No product of the fixed factors is assumed to be fixed.  The proof applies
the full-matrix maximal-support theorem to the canonical block-diagonal
extension and then takes its diagonal blocks.

Local finite-product consequence used to formalize arXiv:1606.00608,
Appendix C.4, lines 1980--1993.  CPSV16 instead applies Wolf's density-block
description directly, including its possible zero summand. -/
theorem IsPositiveDirectSumMap.exists_posDef_fixedFamily_of_fixed_product_span
    {J : Type*}
    {F : (∀ k, Matrix (n k) (n k) ℂ) →ₗ[ℂ]
      (∀ k, Matrix (n k) (n k) ℂ)}
    (hF : IsPositiveDirectSumMap F)
    (hTP : IsTracePreservingDirectSumMap F)
    (V : J → (∀ k, Matrix (n k) (n k) ℂ))
    (L : ℕ) (hL : 0 < L)
    (hFixed : ∀ j, F (V j) = V j)
    (hOne : (1 : ∀ k, Matrix (n k) (n k) ℂ) ∈
      Submodule.span ℂ (Set.range fun x : Fin L → J ↦
        (List.ofFn fun t ↦ V (x t)).prod)) :
    ∃ ρ : ∀ k, Matrix (n k) (n k) ℂ,
      (∀ k, (ρ k).PosDef) ∧ F ρ = ρ := by
  classical
  let E := directSumExtension F
  let W : J → Matrix ((k : ι) × n k) ((k : ι) × n k) ℂ :=
    fun j ↦ directSumDiagonalEmbedding (V j)
  have hEpos : IsPositiveMap E :=
    hF.directSumExtension_isPositiveMap
  have hETP : IsTracePreservingMap E :=
    hTP.directSumExtension_isTracePreservingMap
  have hETNI : IsTraceNonincreasingMap E := by
    intro X _
    exact (hETP X).le
  have hWFixed (j : J) : E (W j) = W j := by
    exact (directSumExtension_embedding_eq_self_iff F (V j)).2 (hFixed j)
  have hOneFull :
      (1 : Matrix ((k : ι) × n k) ((k : ι) × n k) ℂ) ∈
        Submodule.span ℂ (Set.range fun x : Fin L → J ↦
          (List.ofFn fun t ↦ W (x t)).prod) := by
    simpa only [W] using directSumDiagonalEmbedding_one_mem_product_span V L hOne
  obtain ⟨ρFull, hρFull, hρFullFixed⟩ :=
    hEpos.exists_posDef_fixedPoint_of_traceNonincreasing_of_fixed_product_span
      hETNI W L hL hWFixed hOneFull
  obtain ⟨ρ, hρFixed, hρFullEq⟩ :=
    (directSumExtension_apply_eq_self_iff F ρFull).mp hρFullFixed
  refine ⟨ρ, ?_, hρFixed⟩
  intro k
  have hρBlock : (directSumDiagonalCompression ρFull k).PosDef := by
    rw [directSumDiagonalCompression_apply]
    apply hρFull.submatrix
    intro a b hab
    simpa using hab
  rw [hρFullEq, directSumDiagonalCompression_embedding] at hρBlock
  exact hρBlock

end Matrix

end TraceNonincreasingDirectSum
