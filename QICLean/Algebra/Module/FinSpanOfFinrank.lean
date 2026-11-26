/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Pi
import Mathlib.Analysis.Complex.Basic

/-!
# Spanning families indexed by the dimension bound

A subspace of dimension at most `D` is contained in the span of a family of `D` of its own
vectors. Applied to the slices of a bipartite vector, whose span has dimension at most the
Schmidt rank across the cut, it gives `D` slices, indexed by `Fin D`, that span all of them.

Moved from TNLean, `TNLean/Algebra/FinSpanOfFinrank.lean` at commit `49b78ed821` (Apache-2.0).

Moved from TNLean, `TNLean/MPS/FundamentalTheorem/WordModule/FiniteTraceTest.lean` at commit
`021ba0bd19` (Apache-2.0).
-/

open Module

/-- A subspace of dimension at most `D` lies in the span of a family indexed by `Fin D`
of its own vectors. -/
theorem Submodule.exists_fin_span_of_finrank_le {K M : Type*} [Field K] [AddCommGroup M]
    [Module K M] (W : Submodule K M) [FiniteDimensional K W] {D : ℕ}
    (h : finrank K W ≤ D) :
    ∃ u : Fin D → M, (∀ α, u α ∈ W) ∧ W ≤ Submodule.span K (Set.range u) := by
  classical
  have hle : finrank K W ≤ finrank K (Fin D → K) := by simpa using h
  obtain ⟨e, he⟩ := finrank_le_iff_exists_linearMap.mp hle
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective e (LinearMap.ker_eq_bot.mpr he)
  refine ⟨fun α ↦ (g fun j ↦ if α = j then 1 else 0 : W), fun α ↦ (g _).2, fun w hw ↦ ?_⟩
  rw [Submodule.mem_span_range_iff_exists_fun]
  refine ⟨e ⟨w, hw⟩, ?_⟩
  have hgw : (g (e ⟨w, hw⟩) : M) = w := congrArg Subtype.val (LinearMap.congr_fun hg ⟨w, hw⟩)
  refine Eq.trans ?_ hgw
  rw [LinearMap.pi_apply_eq_sum_univ g]
  simp

section

variable {d : ℕ}

/-- **Plateau lemma.** Let `S` be a monotone chain in a partial order with a strictly monotone
rank `r`, such that a single plateau `S (n + 1) = S n` forces `S (n + 2) = S (n + 1)`. If the
rank grows by at most `N` along the chain, then every `S n` lies below `S N`: the chain is
constant from `N` on. -/
theorem Monotone.le_of_plateau {α : Type*} [PartialOrder α] {S : ℕ → α} (hS : Monotone S)
    (hstep : ∀ n, S (n + 1) = S n → S (n + 2) = S (n + 1))
    {r : α → ℕ} (hr : StrictMono r) {N : ℕ} (hN : ∀ n, r (S n) ≤ r (S 0) + N) (n : ℕ) :
    S n ≤ S N := by
  have hex : ∃ m ≤ N, S (m + 1) = S m := by
    by_contra hne
    simp only [not_exists, not_and] at hne
    have hgrow : ∀ k ≤ N + 1, r (S 0) + k ≤ r (S k) := by
      intro k hk
      induction k with
      | zero => simp
      | succ k ih =>
        have hlt : S k < S (k + 1) :=
          lt_of_le_of_ne (hS (Nat.le_succ k)) (fun h => hne k (by omega) h.symm)
        have h1 := hr hlt
        have h2 := ih (by omega)
        omega
    have h1 := hgrow (N + 1) le_rfl
    have h2 := hN (N + 1)
    omega
  obtain ⟨m, hm, hplat⟩ := hex
  have hsucc : ∀ j, S (m + j + 1) = S (m + j) := by
    intro j
    induction j with
    | zero => simpa using hplat
    | succ j ih => exact hstep (m + j) ih
  have hconst : ∀ j, S (m + j) = S m := by
    intro j
    induction j with
    | zero => rfl
    | succ j ih => rw [← Nat.add_assoc, hsucc j, ih]
  rcases le_or_gt n N with hn | hn
  · exact hS hn
  · obtain ⟨j, rfl⟩ : ∃ j, n = m + j := ⟨n - m, by omega⟩
    rw [hconst j]
    exact hS hm

/-- **Words in a finite dimensional algebra.** Let `z` be letters in a finite dimensional
algebra `A` and `k ≤ 1`. If `finrank A ≤ N + (1 - k)`, every word of length at least `k` lies in
the span of the words of lengths `k` to `N`. For `k = 1` the spans of the words of lengths
`1, …, n` start at `0`; for `k = 0` they start at the line through `1`. -/
theorem prod_map_mem_span_of_finrank_le {A : Type*} [Ring A] [Algebra ℂ A]
    [FiniteDimensional ℂ A] (z : Fin d → A) {k N : ℕ} (hk : k ≤ 1)
    (hN : Module.finrank ℂ A ≤ N + (1 - k)) (w : List (Fin d)) (hw : k ≤ w.length) :
    (w.map z).prod ∈ Submodule.span ℂ
      {x | ∃ u : List (Fin d), k ≤ u.length ∧ u.length ≤ N ∧ (u.map z).prod = x} := by
  set S : ℕ → Submodule ℂ A := fun n => Submodule.span ℂ
    {x | ∃ u : List (Fin d), k ≤ u.length ∧ u.length ≤ n ∧ (u.map z).prod = x} with hSdef
  have hmono : Monotone S := by
    intro m n hmn
    refine Submodule.span_mono ?_
    rintro x ⟨u, hu1, hu2, rfl⟩
    exact ⟨u, hu1, hu2.trans hmn, rfl⟩
  have hmem : ∀ n (u : List (Fin d)), k ≤ u.length → u.length ≤ n → (u.map z).prod ∈ S n :=
    fun n u hu1 hu2 => Submodule.subset_span ⟨u, hu1, hu2, rfl⟩
  have hmul : ∀ n (i : Fin d) {x : A}, x ∈ S n → z i * x ∈ S (n + 1) := by
    intro n i x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨u, hu1, hu2, rfl⟩ := hx
      have := hmem (n + 1) (i :: u) (by simp; omega) (by simp; omega)
      simpa using this
    | zero => simp
    | add x y _ _ hx hy => rw [mul_add]; exact Submodule.add_mem _ hx hy
    | smul c x _ hx => rw [mul_smul_comm]; exact Submodule.smul_mem _ c hx
  have hstep : ∀ n, S (n + 1) = S n → S (n + 2) = S (n + 1) := by
    intro n hn
    refine le_antisymm ?_ (hmono (Nat.le_succ _))
    refine Submodule.span_le.mpr ?_
    rintro x ⟨u, hu1, hu2, rfl⟩
    rcases Nat.lt_or_ge u.length (n + 2) with hlt | hge
    · exact hmem (n + 1) u hu1 (by omega)
    · obtain ⟨i, u', rfl⟩ : ∃ i u', u = i :: u' := by
        cases u with
        | nil => simp at hge
        | cons i u' => exact ⟨i, u', rfl⟩
      have hu' : (u'.map z).prod ∈ S n := by
        rw [← hn]
        exact hmem (n + 1) u' (by simp at hu2 hge; omega) (by simp at hu2; omega)
      simpa using hmul n i hu'
  have hr : StrictMono fun s : Submodule ℂ A => Module.finrank ℂ s :=
    fun _ _ h => Submodule.finrank_lt_finrank_of_lt h
  have hbound : ∀ n, Module.finrank ℂ (S n) ≤ Module.finrank ℂ (S 0) + N := by
    intro n
    have hle : Module.finrank ℂ (S n) ≤ Module.finrank ℂ A := Submodule.finrank_le _
    rcases Nat.eq_zero_or_pos k with hk0 | hk0
    · subst hk0
      by_cases h1 : (1 : A) = 0
      · have : Subsingleton A := subsingleton_of_zero_eq_one h1.symm
        have : Module.finrank ℂ A = 0 := Module.finrank_zero_of_subsingleton
        omega
      · have h1mem : (1 : A) ∈ S 0 := by simpa using hmem 0 [] le_rfl le_rfl
        have hspan : Submodule.span ℂ {(1 : A)} ≤ S 0 :=
          Submodule.span_le.mpr (by simpa using h1mem)
        have hone := finrank_span_singleton (K := ℂ) h1
        have := Submodule.finrank_mono hspan
        omega
    · have : 1 - k = 0 := by omega
      omega
  have hplat := hmono.le_of_plateau hstep hr hbound w.length
  exact hplat (hmem w.length w hw le_rfl)

end
