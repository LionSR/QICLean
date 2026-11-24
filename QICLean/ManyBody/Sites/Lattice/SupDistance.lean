/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.ManyBody.Sites.Lattice.Plane
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Ring

/-!
# Sup-norm distance in the square lattice and depth relative to a finite set

The sup-norm distance of two points of `ℤ × ℤ` is the larger of the absolute differences of
their coordinates. The depth of a point `x` relative to a finite nonempty set `T` is the
smallest sup-norm distance from `x` to a point of `T`. Its sublevel sets are the ambient
dilations of `T`: the depth is at most `r` exactly on `T^{+r}`, and equals `d ≥ 1` exactly on
the layer `T^{+d} \ T^{+(d-1)}`.

The depth changes by at most the sup-norm distance of two points. Along a walk of a graph whose
vertices have lattice coordinates, with adjacent vertices at sup-norm distance at most one, it
changes by at most the length of the walk. No connectedness or convexity is used, so the bound
holds on the nearest-neighbour graph of every finite domain, with holes or several components.

If every layer `T^{+d} \ T^{+(d-1)}` with `1 ≤ d ≤ L` has at most `n` points, then `T^{+L}` has
at most `|T| + n L` points, and so has every set of sites of a domain of depth at most `L`.

## Main definitions

* `ManyBody.supDist` — the sup-norm distance of two lattice points.
* `ManyBody.ambientDepth` — the depth of a lattice point relative to a finite nonempty set.

## Main results

* `ManyBody.supDist_comm`, `ManyBody.supDist_triangle` — symmetry and the triangle inequality.
* `ManyBody.natCast_supDist`, `ManyBody.cast_supDist` — the integer and real values.
* `ManyBody.supDist_le_latticeL1Distance`, `ManyBody.supDist_le_of_walk`,
  `ManyBody.supDist_le_one_of_planeDomainGraph_adj` — comparison with walks of a domain.
* `ManyBody.abs_ambientDepth_sub_le` — the depth is `1`-Lipschitz for the sup-norm distance.
* `ManyBody.ambientDepth_le_iff_mem_ambientDilation`,
  `ManyBody.ambientDepth_eq_iff_mem_ambientDilation_sdiff` — sublevel sets and layers.
* `ManyBody.abs_ambientDepth_sub_le_walk_length`, `ManyBody.abs_ambientDepth_sub_le_of_edist_le`,
  `ManyBody.abs_ambientDepth_sub_le_planeDomainGraph` — variation of the depth along walks.
* `ManyBody.card_ambientDilation_le_of_layers`, `ManyBody.card_filter_ambientDepth_le`,
  `ManyBody.card_filter_ambientDepth_le_quadratic` — counting by layers.

## References

* OpenAI, *A two-dimensional area law from a global spectral gap*, September 24, 2026:
  `02-initial.tex`, line 225 (`dist_∞`); `08-scanner.tex`, lines 13–18 (distance and depth),
  21–29 (the sets `T_j`), 43–59 and 83–87 (rows), 125–137 (graph balls), 323–337 (counting and
  the variation of the depth in a sampling window).
-/

namespace ManyBody

/-! ### The sup-norm distance -/

/-- The sup-norm distance of two lattice points. Source: `02-initial.tex`, line 225,
`dist_∞`. -/
def supDist (a b : ℤ × ℤ) : ℕ := max (a.1 - b.1).natAbs (a.2 - b.2).natAbs

/-- The real value of the lattice sup-norm distance is the maximum of the
absolute coordinate differences. Source: `02-initial.tex`, line 225, `dist_∞`. -/
theorem cast_supDist (p z : ℤ × ℤ) :
    (supDist p z : ℝ) = max |(p.1 : ℝ) - z.1| |(p.2 : ℝ) - z.2| := by
  simp only [supDist, Nat.cast_max, Nat.cast_natAbs, Int.cast_abs, Int.cast_sub]

/-- The integer value of the lattice sup-norm distance is the maximum of the absolute
coordinate differences. Source: `08-scanner.tex`, lines 13–18. -/
theorem natCast_supDist (x y : ℤ × ℤ) :
    ((supDist x y : ℕ) : ℤ) = max |x.1 - y.1| |x.2 - y.2| := by
  simp only [supDist, Nat.cast_max, Int.natCast_natAbs]

/-- A point is at sup-norm distance zero from itself. -/
@[simp] theorem supDist_self (x : ℤ × ℤ) : supDist x x = 0 := by
  simp [supDist]

/-- The sup-norm distance is symmetric. -/
theorem supDist_comm (x y : ℤ × ℤ) : supDist x y = supDist y x := by
  simp only [supDist]
  omega

/-- The triangle inequality for the sup-norm distance. -/
theorem supDist_triangle (x y z : ℤ × ℤ) : supDist x z ≤ supDist x y + supDist y z := by
  simp only [supDist]
  omega

/-- The sup-norm distance is invariant under a common translation. -/
@[simp] theorem supDist_add_right (x y c : ℤ × ℤ) : supDist (x + c) (y + c) = supDist x y := by
  simp only [supDist, Prod.fst_add, Prod.snd_add, add_sub_add_right_eq_sub]

/-- The sup-norm distance is bounded by the lattice path distance. -/
theorem supDist_le_latticeL1Distance (a b : ℤ × ℤ) : supDist a b ≤ latticeL1Distance a b := by
  simp only [supDist, latticeL1Distance]
  omega

/-- A walk of length at most `R` in an induced domain moves its endpoints by sup-norm distance
at most `R`. -/
theorem supDist_le_of_walk {Λ : Finset (ℤ × ℤ)} {x y : ↥Λ} {R : ℕ}
    (p : (planeDomainGraph Λ).Walk x y) (hp : p.length ≤ R) : supDist x.1 y.1 ≤ R :=
  (supDist_le_latticeL1Distance _ _).trans
    ((latticeL1Distance_le_walk_length Subtype.val
      (fun _ _ ↦ latticeL1Distance_le_one_of_planeDomainGraph_adj) p).trans hp)

/-- Adjacent sites of the nearest-neighbour graph of a domain are at sup-norm distance at most
one. Source: `08-scanner.tex`, lines 13–18. -/
theorem supDist_le_one_of_planeDomainGraph_adj {Λ : Finset (ℤ × ℤ)} {x y : ↥Λ}
    (hxy : (planeDomainGraph Λ).Adj x y) : supDist x.val y.val ≤ 1 :=
  (supDist_le_latticeL1Distance _ _).trans (latticeL1Distance_le_one_of_planeDomainGraph_adj hxy)

/-! ### Depth relative to a finite set -/

/-- The depth of a lattice point relative to a finite nonempty set `T`: the smallest sup-norm
distance to a point of `T`, as an integer. It does not depend on any graph.
Source: `08-scanner.tex`, lines 13–18, and the sets `T_j` of lines 21–24. -/
def ambientDepth (T : Finset (ℤ × ℤ)) (hT : T.Nonempty) (x : ℤ × ℤ) : ℤ :=
  T.inf' hT fun y ↦ (supDist x y : ℤ)

/-- The depth is attained at a point of the set. -/
theorem exists_mem_ambientDepth_eq (T : Finset (ℤ × ℤ)) (hT : T.Nonempty) (x : ℤ × ℤ) :
    ∃ y ∈ T, ambientDepth T hT x = (supDist x y : ℤ) :=
  T.exists_mem_eq_inf' hT fun y ↦ (supDist x y : ℤ)

/-- The depth is at most the sup-norm distance to any point of the set. -/
theorem ambientDepth_le_of_mem (T : Finset (ℤ × ℤ)) (hT : T.Nonempty) (x : ℤ × ℤ)
    {y : ℤ × ℤ} (hy : y ∈ T) : ambientDepth T hT x ≤ (supDist x y : ℤ) :=
  Finset.inf'_le _ hy

/-- The depth is nonnegative. -/
theorem ambientDepth_nonneg (T : Finset (ℤ × ℤ)) (hT : T.Nonempty) (x : ℤ × ℤ) :
    0 ≤ ambientDepth T hT x :=
  Finset.le_inf' hT _ fun _ _ ↦ Int.natCast_nonneg _

/-- The points of the set have depth zero. -/
theorem ambientDepth_eq_zero_of_mem (T : Finset (ℤ × ℤ)) (hT : T.Nonempty) {x : ℤ × ℤ}
    (hx : x ∈ T) : ambientDepth T hT x = 0 :=
  le_antisymm (by simpa using ambientDepth_le_of_mem T hT x hx) (ambientDepth_nonneg T hT x)

private theorem ambientDepth_le_add (T : Finset (ℤ × ℤ)) (hT : T.Nonempty) (x y : ℤ × ℤ) :
    ambientDepth T hT x ≤ (supDist x y : ℤ) + ambientDepth T hT y := by
  obtain ⟨z, hz, hmin⟩ := exists_mem_ambientDepth_eq T hT y
  calc
    ambientDepth T hT x ≤ (supDist x z : ℤ) := ambientDepth_le_of_mem T hT x hz
    _ ≤ (supDist x y : ℤ) + (supDist y z : ℤ) := by exact_mod_cast supDist_triangle x y z
    _ = (supDist x y : ℤ) + ambientDepth T hT y := by rw [hmin]

/-- The depth changes by no more than the sup-norm distance of the two points.
Source: the depth comparison used in `08-scanner.tex`, lines 331–337. -/
theorem abs_ambientDepth_sub_le (T : Finset (ℤ × ℤ)) (hT : T.Nonempty) (x y : ℤ × ℤ) :
    |ambientDepth T hT x - ambientDepth T hT y| ≤ (supDist x y : ℤ) := by
  have hxy := ambientDepth_le_add T hT x y
  have hyx := ambientDepth_le_add T hT y x
  rw [supDist_comm y x] at hyx
  rw [abs_le]
  omega

/-- The points of depth at most `r` are the points of the ambient dilation by `r`.
Source: `08-scanner.tex`, lines 21–24. -/
theorem ambientDepth_le_iff_mem_ambientDilation (T : Finset (ℤ × ℤ)) (hT : T.Nonempty)
    (x : ℤ × ℤ) (r : ℕ) :
    ambientDepth T hT x ≤ r ↔ x ∈ ambientDilation T r := by
  rw [ambientDepth, Finset.inf'_le_iff]
  simp only [natCast_supDist, max_le_iff, abs_le, mem_ambientDilation_iff]
  constructor <;> rintro ⟨y, hy, h⟩ <;> exact ⟨y, hy, by omega⟩

/-- The points of depth `d ≥ 1` are the points of one layer of the ambient dilations.
Source: the row hypothesis in `08-scanner.tex`, lines 43–48. -/
theorem ambientDepth_eq_iff_mem_ambientDilation_sdiff (T : Finset (ℤ × ℤ)) (hT : T.Nonempty)
    (x : ℤ × ℤ) {d : ℕ} (hd : 0 < d) :
    ambientDepth T hT x = d ↔ x ∈ ambientDilation T d \ ambientDilation T (d - 1) := by
  rw [Finset.mem_sdiff, ← ambientDepth_le_iff_mem_ambientDilation T hT,
    ← ambientDepth_le_iff_mem_ambientDilation T hT]
  omega

section Walk

variable {V : Type*} {G : SimpleGraph V}

/-- Along a walk of a graph whose adjacent vertices have coordinates at sup-norm distance at most
one, the depth changes by at most the length of the walk. Neither connectedness nor convexity is
assumed. Source: `08-scanner.tex`, graph balls in lines 125–137 and the use in lines 331–337. -/
theorem abs_ambientDepth_sub_le_walk_length (T : Finset (ℤ × ℤ)) (hT : T.Nonempty)
    (coord : V → ℤ × ℤ)
    (hstep : ∀ ⦃x y : V⦄, G.Adj x y → supDist (coord x) (coord y) ≤ 1)
    {x y : V} (p : G.Walk x y) :
    |ambientDepth T hT (coord x) - ambientDepth T hT (coord y)| ≤ p.length := by
  induction p with
  | nil => simp
  | @cons x y z hxy p ih =>
      calc
        |ambientDepth T hT (coord x) - ambientDepth T hT (coord z)| ≤
            |ambientDepth T hT (coord x) - ambientDepth T hT (coord y)| +
              |ambientDepth T hT (coord y) - ambientDepth T hT (coord z)| :=
          abs_sub_le _ _ _
        _ ≤ 1 + (p.length : ℤ) :=
          add_le_add ((abs_ambientDepth_sub_le T hT _ _).trans
            (by exact_mod_cast hstep hxy)) ih
        _ = (SimpleGraph.Walk.cons hxy p).length := by simp [add_comm]

/-- Every vertex at graph distance at most `r₀` from an anchor has depth within `r₀` of the depth
of the anchor. Vertices in different components are at infinite extended distance.
Source: the sampling-window argument in `08-scanner.tex`, lines 331–337. -/
theorem abs_ambientDepth_sub_le_of_edist_le (T : Finset (ℤ × ℤ)) (hT : T.Nonempty)
    (coord : V → ℤ × ℤ)
    (hstep : ∀ ⦃x y : V⦄, G.Adj x y → supDist (coord x) (coord y) ≤ 1)
    {x anchor : V} {r₀ : ℕ} (hx : G.edist x anchor ≤ (r₀ : ℕ∞)) :
    |ambientDepth T hT (coord x) - ambientDepth T hT (coord anchor)| ≤ r₀ := by
  obtain ⟨p, hp⟩ := SimpleGraph.exists_walk_of_edist_ne_top
    (ne_top_of_le_ne_top (by simp) hx)
  have hlength : p.length ≤ r₀ := ENat.natCast_le_natCast.mp (hp.le.trans hx)
  exact (abs_ambientDepth_sub_le_walk_length T hT coord hstep p).trans
    (Int.ofNat_le.mpr hlength)

end Walk

/-- In the nearest-neighbour graph of a finite domain, every site at graph distance at most `r₀`
from an anchor has depth within `r₀` of the depth of the anchor.
Source: `08-scanner.tex`, lines 13–18, 125–137, and 331–337. -/
theorem abs_ambientDepth_sub_le_planeDomainGraph (T : Finset (ℤ × ℤ)) (hT : T.Nonempty)
    {Λ : Finset (ℤ × ℤ)} {x anchor : ↥Λ} {r₀ : ℕ}
    (hx : (planeDomainGraph Λ).edist x anchor ≤ (r₀ : ℕ∞)) :
    |ambientDepth T hT x.val - ambientDepth T hT anchor.val| ≤ r₀ :=
  abs_ambientDepth_sub_le_of_edist_le T hT Subtype.val
    (fun _ _ ↦ supDist_le_one_of_planeDomainGraph_adj) hx

/-! ### Counting by layers -/

/-- If each of the layers `T^{+d} \ T^{+(d-1)}`, `1 ≤ d ≤ L`, has at most `n` points, then the
dilation `T^{+L}` has at most `|T| + n L` points. Source: `08-scanner.tex`, lines 21–29. -/
theorem card_ambientDilation_le_of_layers (T : Finset (ℤ × ℤ)) (n L : ℕ)
    (hrows : ∀ d : ℕ, 1 ≤ d → d ≤ L →
      (ambientDilation T d \ ambientDilation T (d - 1)).card ≤ n) :
    (ambientDilation T L).card ≤ T.card + n * L := by
  induction L with
  | zero => simp
  | succ L ih =>
    have hp := ih (fun d hd hL ↦ hrows d hd (Nat.le_succ_of_le hL))
    have hr := hrows (L + 1) (by omega) le_rfl
    simp only [Nat.add_sub_cancel] at hr
    have hc := Finset.card_le_card_sdiff_add_card
      (s := ambientDilation T (L + 1)) (t := ambientDilation T L)
    simp only [Nat.mul_add, Nat.mul_one]
    omega

/-- Under the same bound on the layers, at most `|T| + n L` sites of a set `A` of sites of a
domain have depth at most `L`. The domain may have holes and several components.
Source: `08-scanner.tex`, lines 323–329. -/
theorem card_filter_ambientDepth_le {Λ T : Finset (ℤ × ℤ)} (hT : T.Nonempty)
    (A : Finset ↥Λ) (n L : ℕ)
    (hrows : ∀ d : ℕ, 1 ≤ d → d ≤ L →
      (ambientDilation T d \ ambientDilation T (d - 1)).card ≤ n) :
    (A.filter fun x ↦ ambientDepth T hT x.val ≤ L).card ≤ T.card + n * L := by
  apply le_trans _ (card_ambientDilation_le_of_layers T n L hrows)
  apply Finset.card_le_card_of_injOn Subtype.val
  · intro x hx
    exact (ambientDepth_le_iff_mem_ambientDilation T hT x.val L).mp (Finset.mem_filter.mp hx).2
  · exact Subtype.val_injective.injOn

/-- If moreover `L ≤ n` and `|T| ≤ C n²`, at most `(C + 1) n²` sites of `A` have depth at most
`L`. The coefficient `C` may be zero. Source: `08-scanner.tex`, lines 323–329. -/
theorem card_filter_ambientDepth_le_quadratic {Λ T : Finset (ℤ × ℤ)} (hT : T.Nonempty)
    (A : Finset ↥Λ) {n L : ℕ} {C : ℝ} (hLn : L ≤ n)
    (hsize : (T.card : ℝ) ≤ C * (n : ℝ) ^ 2)
    (hrows : ∀ d : ℕ, 1 ≤ d → d ≤ L →
      (ambientDilation T d \ ambientDilation T (d - 1)).card ≤ n) :
    ((A.filter fun x ↦ ambientDepth T hT x.val ≤ L).card : ℝ) ≤
      (C + 1) * (n : ℝ) ^ 2 := by
  have hcard : ((A.filter fun x ↦ ambientDepth T hT x.val ≤ L).card : ℝ) ≤
      (T.card : ℝ) + (n : ℝ) * L := by
    exact_mod_cast card_filter_ambientDepth_le hT A n L hrows
  have hLnR : (L : ℝ) ≤ n := by exact_mod_cast hLn
  calc
    _ ≤ (T.card : ℝ) + (n : ℝ) * L := hcard
    _ ≤ C * (n : ℝ) ^ 2 + (n : ℝ) * n :=
      add_le_add hsize (mul_le_mul_of_nonneg_left hLnR (Nat.cast_nonneg _))
    _ = _ := by ring

end ManyBody
