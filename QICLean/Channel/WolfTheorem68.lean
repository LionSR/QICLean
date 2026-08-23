/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Channel.KrausIterateChoi
import QICLean.Kraus.Wielandt.Primitivity.StronglyIrreducibleToFullWordSpan
import QICLean.Kraus.Wielandt.Primitivity.VectorSpreadToPrimitive
import Mathlib.Tactic.TFAE

/-!
# Wolf's primitive-channel criterion

For a trace-preserving finite Kraus family, Wolf, Theorem 6.8 identifies four
equivalent forms of primitivity: irreducibility with trivial peripheral
spectrum, eventual full vector spread, eventual full Kraus-word span, and
eventual positive definiteness of the iterate Choi matrices. The same threshold
works for the last two clauses; for minimal vector and word thresholds `n` and
`q`, respectively, one has `n ≤ q`.

The source calls the first clause simply "primitive" because its definition of
primitivity includes irreducibility. Here it is represented by the conjunction
`IsIrreducibleMap (mapLM K) ∧ IsPrimitive (mapLM K)`, since the project
predicate `IsPrimitive` records only triviality of the peripheral spectrum.

Source: `Notes/WolfNoteTexSource/ch06_spectral_properties.tex`, lines 829--833
and 904--984.
-/

open scoped Matrix ComplexOrder

namespace Kraus

variable {r D : ℕ}

/-- Starting at word length `n`, every nonzero vector has full Kraus-word
spread. This is the explicit-threshold form of Wolf, Theorem 6.8(2). -/
def HasFullVectorSpreadFrom
    (K : Fin r → Matrix (Fin D) (Fin D) ℂ) (n : ℕ) : Prop :=
  ∀ m, n ≤ m → ∀ φ : Fin D → ℂ, φ ≠ 0 → vectorSpreadSpan K φ m = ⊤

/-- Starting at word length `q`, the degree-`m` Kraus words span the full
matrix algebra. This is Wolf, Theorem 6.8(3). -/
def HasFullWordSpanFrom
    (K : Fin r → Matrix (Fin D) (Fin D) ℂ) (q : ℕ) : Prop :=
  ∀ m, q ≤ m → wordSpan K m = ⊤

/-- Starting at iterate `q`, every Choi matrix of a Kraus-map power is positive
definite. This is Wolf, Theorem 6.8(4). -/
def HasPosDefChoiFrom
    (K : Fin r → Matrix (Fin D) (Fin D) ℂ) (q : ℕ) : Prop :=
  ∀ m, q ≤ m →
    (ChoiJamiolkowski.choiMatrix ((mapLM K) ^ m)).PosDef

/-- Eventual full vector spread is equivalent to Wolf's explicit existence of
a threshold `n` after which all lengths have full vector spread. -/
theorem hasEventuallyFullVectorSpread_iff_exists_hasFullVectorSpreadFrom
    (K : Fin r → Matrix (Fin D) (Fin D) ℂ) :
    HasEventuallyFullVectorSpread K ↔ ∃ n, HasFullVectorSpreadFrom K n := by
  constructor
  · intro h
    exact Filter.eventually_atTop.mp h
  · rintro ⟨n, hn⟩
    exact Filter.eventually_atTop.mpr ⟨n, hn⟩

/-- Eventual full word span is equivalent to Wolf's explicit existence of a
threshold `q` after which all word spans are the full matrix algebra. -/
theorem hasEventuallyFullWordSpan_iff_exists_hasFullWordSpanFrom
    (K : Fin r → Matrix (Fin D) (Fin D) ℂ) :
    HasEventuallyFullWordSpan K ↔ ∃ q, HasFullWordSpanFrom K q := by
  constructor
  · intro h
    exact Filter.eventually_atTop.mp h
  · rintro ⟨q, hq⟩
    exact Filter.eventually_atTop.mpr ⟨q, hq⟩

/-- Eventual positive definiteness of iterate Choi matrices is equivalent to
Wolf's explicit existence of a threshold `q` valid at every later iterate. -/
theorem eventually_choiMatrix_mapLM_pow_posDef_iff_exists_hasPosDefChoiFrom
    (K : Fin r → Matrix (Fin D) (Fin D) ℂ) :
    (∀ᶠ m : ℕ in Filter.atTop,
      (ChoiJamiolkowski.choiMatrix ((mapLM K) ^ m)).PosDef) ↔
      ∃ q, HasPosDefChoiFrom K q := by
  constructor
  · intro h
    exact Filter.eventually_atTop.mp h
  · rintro ⟨q, hq⟩
    exact Filter.eventually_atTop.mpr ⟨q, hq⟩

/-- Wolf, Theorem 6.8, item 1 implies item 4: under trace preservation,
irreducibility and primitivity force the Choi matrices of all sufficiently
large Kraus-map powers to be positive definite. -/
theorem eventually_choiMatrix_mapLM_pow_posDef_of_isIrreducibleMap_of_isPrimitive
    [NeZero D] (K : Fin r → Matrix (Fin D) (Fin D) ℂ)
    (hTP : IsTP K)
    (hIrr : IsIrreducibleMap (mapLM K))
    (hPrim : IsPrimitive (mapLM K)) :
    ∀ᶠ m : ℕ in Filter.atTop,
      (ChoiJamiolkowski.choiMatrix ((mapLM K) ^ m)).PosDef :=
  (eventually_choiMatrix_mapLM_pow_posDef_iff_hasEventuallyFullWordSpan K).2
    (hasEventuallyFullWordSpan_of_isIrreducibleMap_of_isPrimitive K hTP hIrr hPrim)

/-- Wolf, Theorem 6.8: for a trace-preserving finite Kraus family, the source's
four characterizations of primitivity are equivalent. Clause 1 explicitly
includes irreducibility because Wolf's definition of "primitive" includes it,
whereas the project predicate `IsPrimitive` controls only the peripheral
spectrum. Clauses 2--4 retain Wolf's quantifiers over every `m` beyond a single
threshold. -/
theorem wolf_theorem_6_8_tfae [NeZero D]
    (K : Fin r → Matrix (Fin D) (Fin D) ℂ) (hTP : IsTP K) :
    List.TFAE [
      IsIrreducibleMap (mapLM K) ∧ IsPrimitive (mapLM K),
      ∃ n, HasFullVectorSpreadFrom K n,
      ∃ q, HasFullWordSpanFrom K q,
      ∃ q, HasPosDefChoiFrom K q] := by
  tfae_have h13 : 1 → 3 := by
    rintro ⟨hIrr, hPrim⟩
    exact (hasEventuallyFullWordSpan_iff_exists_hasFullWordSpanFrom K).mp
      (hasEventuallyFullWordSpan_of_isIrreducibleMap_of_isPrimitive
        K hTP hIrr hPrim)
  tfae_have h34 : 3 ↔ 4 := by
    constructor
    · rintro ⟨q, hq⟩
      refine ⟨q, fun m hqm ↦ ?_⟩
      exact (choiMatrix_mapLM_pow_posDef_iff_wordSpan_eq_top K m).mpr
        (hq m hqm)
    · rintro ⟨q, hq⟩
      refine ⟨q, fun m hqm ↦ ?_⟩
      exact (choiMatrix_mapLM_pow_posDef_iff_wordSpan_eq_top K m).mp
        (hq m hqm)
  tfae_have h32 : 3 → 2 := by
    rintro ⟨q, hq⟩
    refine ⟨q, fun m hqm φ hφ ↦ ?_⟩
    exact vectorSpreadSpan_eq_top_of_wordSpan_eq_top K (hq m hqm) φ hφ
  tfae_have h21 : 2 → 1 := by
    rintro ⟨n, hn⟩
    have hn' := hn n le_rfl
    exact ⟨isIrreducibleMap_mapLM_of_vectorSpreadSpan_eq_top K hn',
      isPrimitive_mapLM_of_isTP_of_vectorSpreadSpan_eq_top K hTP hn'⟩
  tfae_finish

/-- Wolf, Theorem 6.8, final sentence: the same minimal threshold `q` works for
full word span and positive-definite iterate Choi matrices, and the minimal
full-vector-spread threshold `n` satisfies `n ≤ q`.

The displayed minimality clauses make the source's phrase "chosen minimal"
explicit. -/
theorem wolf_theorem_6_8_minimal_indices [NeZero D]
    (K : Fin r → Matrix (Fin D) (Fin D) ℂ) (hTP : IsTP K)
    (hIrr : IsIrreducibleMap (mapLM K)) (hPrim : IsPrimitive (mapLM K)) :
    ∃ n q,
      HasFullVectorSpreadFrom K n ∧
      HasFullWordSpanFrom K q ∧
      HasPosDefChoiFrom K q ∧
      (∀ n', HasFullVectorSpreadFrom K n' → n ≤ n') ∧
      (∀ q', HasFullWordSpanFrom K q' → q ≤ q') ∧
      (∀ q', HasPosDefChoiFrom K q' → q ≤ q') ∧
      n ≤ q := by
  classical
  have hWord : ∃ q, HasFullWordSpanFrom K q :=
    (hasEventuallyFullWordSpan_iff_exists_hasFullWordSpanFrom K).mp
      (hasEventuallyFullWordSpan_of_isIrreducibleMap_of_isPrimitive
        K hTP hIrr hPrim)
  have hVector : ∃ n, HasFullVectorSpreadFrom K n := by
    obtain ⟨q, hq⟩ := hWord
    exact ⟨q, fun m hqm φ hφ ↦
      vectorSpreadSpan_eq_top_of_wordSpan_eq_top K (hq m hqm) φ hφ⟩
  let n := Nat.find hVector
  let q := Nat.find hWord
  have hn : HasFullVectorSpreadFrom K n := Nat.find_spec hVector
  have hq : HasFullWordSpanFrom K q := Nat.find_spec hWord
  have hqChoi : HasPosDefChoiFrom K q := fun m hqm ↦
    (choiMatrix_mapLM_pow_posDef_iff_wordSpan_eq_top K m).mpr (hq m hqm)
  refine ⟨n, q, hn, hq, hqChoi, ?_, ?_, ?_, ?_⟩
  · intro n' hn'
    exact Nat.find_min' hVector hn'
  · intro q' hq'
    exact Nat.find_min' hWord hq'
  · intro q' hq'
    apply Nat.find_min' hWord
    intro m hq'm
    exact (choiMatrix_mapLM_pow_posDef_iff_wordSpan_eq_top K m).mp
      (hq' m hq'm)
  · apply Nat.find_min' hVector
    intro m hqm φ hφ
    exact vectorSpreadSpan_eq_top_of_wordSpan_eq_top K (hq m hqm) φ hφ

end Kraus
