/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Circuit.Party.Compression.SourceReplacement.PreparedMatrix
import QICLean.Analysis.TraceNorm.SourceContraction
import QICLean.Algebra.Module.MultilinearSelectedSum
import QICLean.Algebra.Kronecker.KroneckerSandwich

/-!
# Source contractions of prepared densities

The density coefficients of a word applied after prepared slots form a finite coefficient array;
its source contraction (`Matrix.sourceContraction`) with the rank-one matrices of the coordinates
of the ket and bra slot vectors is the mixed prepared density
(`Word.sourceContraction_preparedDensityCoefficient_single`). Replacing the rank-one matrices of a
weighted gate by arbitrary source operators defines `Word.sourceOperatorDensity`; exact source
operators give the density of the gate back, and the difference from it is the sum over the
nonempty sets of slots carrying a correction (`Word.sourceOperatorDensity_sub_prepared`).
Expanding only the operators at a selected set of slots, in the coordinates of the slot bases or
through arbitrary endpoint frames, gives a sum of prepared densities in which the other slots keep
their vectors (`Word.sourceContraction_preparedDensityCoefficient_selected`,
`Word.sourceContraction_preparedDensityCoefficient_selected_frames`). No spanning, normalization,
allowedness or positivity condition is needed.

## Main definitions

* `QuantumCircuit.Party.Word.sourceOperatorDensity`.

## Main results

* `QuantumCircuit.Party.Word.sourceContraction_preparedDensityCoefficient`,
  `QuantumCircuit.Party.Word.sourceContraction_preparedDensityCoefficient_single`.
* `QuantumCircuit.Party.Word.sourceOperatorDensity_sub`,
  `QuantumCircuit.Party.Word.sourceOperatorDensity_exact`,
  `QuantumCircuit.Party.Word.sourceOperatorDensity_sub_prepared`.
* `QuantumCircuit.Party.Word.sourceContraction_preparedDensityCoefficient_selected`,
  `QuantumCircuit.Party.Word.sourceContraction_preparedDensityCoefficient_selected_frames`.

## References

* Polynomial-PEPS manuscript (September 24, 2026), Theorem 5.2, `04-compression.tex`,
  lines 279–383 and 409–434 (equation `eq:compression-subset-expansion`).

Adapted from TNLean, `TNLean/Lattice/Compression/PreparedSourceContraction.lean`,
`TNLean/Lattice/Compression/PreparedSourceCorrections.lean`,
`TNLean/Lattice/Compression/PreparedSourceTransport.lean` and
`TNLean/Lattice/Compression/SelectedSourceContraction.lean` (Apache-2.0). Changes: the endpoint
bases are the coordinates of the slot bases; an endpoint frame is a family of vectors read as the
matrix of its coordinates.
-/

open Matrix ManyBody
open scoped ComplexConjugate

namespace QuantumCircuit.Party

/-- Pair the ket and bra coordinate assignments at each slot. Source: Theorem 5.2,
`04-compression.tex`, lines 279–317. -/
private theorem sourceContraction_vecMulVec {I m n : Type} [Fintype I] [DecidableEq I]
    {A A' : I → Type} [∀ i, Fintype (A i)] [∀ i, Fintype (A' i)] (c : ∀ i, A i → ℂ)
    (d : ∀ i, A' i → ℂ) (coeff : (∀ i, A i) → (∀ i, A' i) → Matrix m n ℂ) :
    sourceContraction (fun x ↦ coeff (fun i ↦ (x i).1) (fun i ↦ (x i).2))
        (fun i ↦ vecMulVec (c i) (fun b ↦ conj (d i b))) =
      ∑ a, ∑ b, (∏ i, c i (a i) * conj (d i (b i))) • coeff a b := by
  classical
  rw [sourceContraction_apply]
  let F : ((∀ i, A i) × (∀ i, A' i)) → Matrix m n ℂ := fun ab ↦
    (∏ i, c i (ab.1 i) * conj (d i (ab.2 i))) • coeff ab.1 ab.2
  calc
    _ = ∑ ab, F ab := Fintype.sum_equiv (Equiv.arrowProdEquivProdArrow I A A') _ F fun _ ↦ rfl
    _ = _ := Fintype.sum_prod_type F

variable {P : Type} [DecidableEq P] [Fintype P]

namespace Word

variable (R : SourceInventory P) (B : SourceInventory.SlotBases R.length) (X : P → Type)
  [∀ p, Fintype (X p)] [∀ p, DecidableEq (X p)] {Y : P → Type}

/-- **Finite endpoint expansions of the ket and bra slot vectors are evaluated by the source
contraction with their rank-one coefficient matrices.** No spanning, normalization, allowedness
or positivity condition is needed. Source: Theorem 5.2, `04-compression.tex`, lines 279–355. -/
theorem sourceContraction_preparedDensityCoefficient {K L K' L' : Fin R.length → Type}
    [∀ i, Fintype (K i)] [∀ i, Fintype (L i)] [∀ i, Fintype (K' i)] [∀ i, Fintype (L' i)]
    (uU : ∀ i, K i → EuclideanSpace ℂ (B.left i)) (uV : ∀ i, L i → EuclideanSpace ℂ (B.right i))
    (uU' : ∀ i, K' i → EuclideanSpace ℂ (B.left i))
    (uV' : ∀ i, L' i → EuclideanSpace ℂ (B.right i))
    (c : ∀ i, K i × L i → ℂ) (d : ∀ i, K' i × L' i → ℂ)
    (v v' : Word (SourceInventory.slotSystem R B X) Y) (ρ : Matrix (Config X) (Config X) ℂ) :
    sourceContraction
        (fun x ↦ v.preparedDensityCoefficient R B X uU uV uU' uV' v' ρ (fun i ↦ (x i).1)
          (fun i ↦ (x i).2))
        (fun i ↦ vecMulVec (c i) (fun b ↦ conj (d i b))) =
      v.preparedMatrix R B
          (fun i ↦ ∑ a, c i a • EuclideanSpace.vecKron (uU i a.1) (uV i a.2)) X * ρ *
        (v'.preparedMatrix R B
          (fun i ↦ ∑ b, d i b • EuclideanSpace.vecKron (uU' i b.1) (uV' i b.2)) X)ᴴ := by
  rw [sourceContraction_vecMulVec]
  exact (v.preparedMatrix_density_sum_smul R B X uU uV uU' uV' c d v' ρ).symm

/-- **The mixed prepared density is the source contraction of the coefficients of the basis
vectors with the rank-one matrices of the coordinates of the ket and bra slot vectors.** Source:
Theorem 5.2, `04-compression.tex`, lines 279–355. -/
theorem sourceContraction_preparedDensityCoefficient_single
    (η ζ : ∀ i, EuclideanSpace ℂ (B.left i × B.right i))
    (v v' : Word (SourceInventory.slotSystem R B X) Y) (ρ : Matrix (Config X) (Config X) ℂ) :
    sourceContraction
        (fun x ↦ v.preparedDensityCoefficient R B X (fun _ a ↦ EuclideanSpace.single a 1)
          (fun _ a ↦ EuclideanSpace.single a 1) (fun _ a ↦ EuclideanSpace.single a 1)
          (fun _ a ↦ EuclideanSpace.single a 1) v' ρ (fun i ↦ (x i).1) (fun i ↦ (x i).2))
        (fun i ↦ vecMulVec (fun a ↦ η i a) (fun b ↦ conj (ζ i b))) =
      v.preparedMatrix R B η X * ρ * (v'.preparedMatrix R B ζ X)ᴴ := by
  rw [sourceContraction_vecMulVec]
  exact (v.preparedMatrix_density_eq_sum_single R B X η ζ v' ρ).symm

/-- The source contraction with prescribed rank-one matrices at a set `S` of slots and the
coordinates of the slot vectors elsewhere. -/
private theorem sourceContraction_single_dite (S : Finset (Fin R.length))
    (η ζ : ∀ i, EuclideanSpace ℂ (B.left i × B.right i))
    (x y : ∀ i : S, EuclideanSpace ℂ (B.left i × B.right i))
    (v v' : Word (SourceInventory.slotSystem R B X) Y) (ρ : Matrix (Config X) (Config X) ℂ) :
    sourceContraction
        (fun z ↦ v.preparedDensityCoefficient R B X (fun _ a ↦ EuclideanSpace.single a 1)
          (fun _ a ↦ EuclideanSpace.single a 1) (fun _ a ↦ EuclideanSpace.single a 1)
          (fun _ a ↦ EuclideanSpace.single a 1) v' ρ (fun i ↦ (z i).1) (fun i ↦ (z i).2))
        (fun i ↦ if h : i ∈ S then vecMulVec (fun a ↦ x ⟨i, h⟩ a) (fun b ↦ conj (y ⟨i, h⟩ b))
          else vecMulVec (fun a ↦ η i a) (fun b ↦ conj (ζ i b))) =
      v.preparedMatrix R B (fun i ↦ if h : i ∈ S then x ⟨i, h⟩ else η i) X * ρ *
        (v'.preparedMatrix R B (fun i ↦ if h : i ∈ S then y ⟨i, h⟩ else ζ i) X)ᴴ := by
  rw [← sourceContraction_preparedDensityCoefficient_single]
  congr 1
  funext i
  by_cases h : i ∈ S <;> simp [h]

variable {ι : Type} [Fintype ι] {K L : ι → Fin R.length → Type}

/-- The density of the prepared words `v ξ` of a weighted gate with the original coefficients
`c ξ`, the rank-one source matrices replaced by arbitrary source operators `T ξ ζ i`. Source:
Theorem 5.2, `04-compression.tex`, lines 279–355. -/
noncomputable def sourceOperatorDensity [∀ ξ i, Fintype (K ξ i)] [∀ ξ i, Fintype (L ξ i)]
    (uU : ∀ ξ i, K ξ i → EuclideanSpace ℂ (B.left i))
    (uV : ∀ ξ i, L ξ i → EuclideanSpace ℂ (B.right i)) (c : ι → ℂ)
    (v : ι → Word (SourceInventory.slotSystem R B X) Y) (ρ : Matrix (Config X) (Config X) ℂ)
    (T : ∀ ξ ζ i, Matrix (K ξ i × L ξ i) (K ζ i × L ζ i) ℂ) : Matrix (Config Y) (Config Y) ℂ :=
  ∑ ξ, ∑ ζ, (c ξ * conj (c ζ)) •
    sourceContraction
      (fun x ↦ (v ξ).preparedDensityCoefficient R B X (uU ξ) (uV ξ) (uU ζ) (uV ζ) (v ζ) ρ
        (fun i ↦ (x i).1) (fun i ↦ (x i).2))
      (T ξ ζ)

/-- **Subtracting the exact source operators leaves exactly the nonempty sets of corrected
slots.** The source operators may be rectangular and the input matrix is arbitrary. Source:
Theorem 5.2, `eq:compression-subset-expansion`, `04-compression.tex`, lines 338–355. -/
theorem sourceOperatorDensity_sub [∀ ξ i, Fintype (K ξ i)] [∀ ξ i, Fintype (L ξ i)]
    (uU : ∀ ξ i, K ξ i → EuclideanSpace ℂ (B.left i))
    (uV : ∀ ξ i, L ξ i → EuclideanSpace ℂ (B.right i)) (c : ι → ℂ)
    (v : ι → Word (SourceInventory.slotSystem R B X) Y) (ρ : Matrix (Config X) (Config X) ℂ)
    (T E : ∀ ξ ζ i, Matrix (K ξ i × L ξ i) (K ζ i × L ζ i) ℂ) :
    sourceOperatorDensity R B X uU uV c v ρ (E + T) - sourceOperatorDensity R B X uU uV c v ρ T =
      ∑ S ∈ (Finset.univ : Finset (Finset (Fin R.length))).erase ∅,
        sourceOperatorDensity R B X uU uV c v ρ fun ξ ζ ↦ S.piecewise (E ξ ζ) (T ξ ζ) := by
  classical
  simp only [sourceOperatorDensity, Pi.add_apply, ← Finset.sum_sub_distrib, ← smul_sub]
  simp only [sourceContraction_sub, Finset.smul_sum]
  simp_rw [Finset.sum_comm (s := (Finset.univ : Finset ι))
    (t := (Finset.univ : Finset (Finset (Fin R.length))).erase ∅)]

/-- **The rank-one matrices of the coordinates of the slot vectors recover the density of the
weighted gate.** Source: Theorem 5.2, `04-compression.tex`, lines 279–355. -/
theorem sourceOperatorDensity_exact (c : ι → ℂ)
    (v : ι → Word (SourceInventory.slotSystem R B X) Y) (ρ : Matrix (Config X) (Config X) ℂ)
    (η : ι → ∀ i, EuclideanSpace ℂ (B.left i × B.right i)) :
    sourceOperatorDensity R B X (K := fun _ i ↦ B.left i) (L := fun _ i ↦ B.right i)
        (fun _ _ a ↦ EuclideanSpace.single a 1) (fun _ _ a ↦ EuclideanSpace.single a 1) c v ρ
        (fun ξ ζ i ↦ vecMulVec (fun a ↦ η ξ i a) (fun a ↦ conj (η ζ i a))) =
      (∑ ξ, c ξ • (v ξ).preparedMatrix R B (η ξ) X) * ρ *
        (∑ ξ, c ξ • (v ξ).preparedMatrix R B (η ξ) X)ᴴ := by
  rw [sourceOperatorDensity, Matrix.sum_smul_mul_mul_conjTranspose]
  refine Finset.sum_congr rfl fun ξ _ ↦ Finset.sum_congr rfl fun ζ _ ↦ ?_
  rw [(v ξ).sourceContraction_preparedDensityCoefficient_single R B X (η ξ) (η ζ) (v ζ) ρ]

/-- **Replacing the slot vectors by arbitrary corrected source operators** expands the error
relative to the density of the weighted gate over the nonempty sets of corrected slots. Source:
Theorem 5.2, `eq:compression-subset-expansion`, `04-compression.tex`, lines 338–355. -/
theorem sourceOperatorDensity_sub_prepared (c : ι → ℂ)
    (v : ι → Word (SourceInventory.slotSystem R B X) Y) (ρ : Matrix (Config X) (Config X) ℂ)
    (η : ι → ∀ i, EuclideanSpace ℂ (B.left i × B.right i))
    (E : ι → ι → ∀ i, Matrix (B.left i × B.right i) (B.left i × B.right i) ℂ) :
    sourceOperatorDensity R B X (K := fun _ i ↦ B.left i) (L := fun _ i ↦ B.right i)
        (fun _ _ a ↦ EuclideanSpace.single a 1) (fun _ _ a ↦ EuclideanSpace.single a 1) c v ρ
        (E + fun ξ ζ i ↦ vecMulVec (fun a ↦ η ξ i a) (fun a ↦ conj (η ζ i a))) -
        (∑ ξ, c ξ • (v ξ).preparedMatrix R B (η ξ) X) * ρ *
          (∑ ξ, c ξ • (v ξ).preparedMatrix R B (η ξ) X)ᴴ =
      ∑ S ∈ (Finset.univ : Finset (Finset (Fin R.length))).erase ∅,
        sourceOperatorDensity R B X (K := fun _ i ↦ B.left i) (L := fun _ i ↦ B.right i)
          (fun _ _ a ↦ EuclideanSpace.single a 1) (fun _ _ a ↦ EuclideanSpace.single a 1) c v ρ
          (fun ξ ζ ↦ S.piecewise (E ξ ζ)
            fun i ↦ vecMulVec (fun a ↦ η ξ i a) (fun a ↦ conj (η ζ i a))) := by
  rw [← sourceOperatorDensity_exact R B X c v ρ η]
  exact sourceOperatorDensity_sub R B X _ _ c v ρ _ E

/-- Pairs of choices at the selected slots, regrouped into one choice on each side. -/
private theorem sum_selected_pairs {S : Type} [Fintype S] [DecidableEq S] {A A' : S → Type}
    [∀ i, Fintype (A i)] [∀ i, Fintype (A' i)] {M : Type} [AddCommMonoid M]
    (F : (∀ i, A i) → (∀ i, A' i) → M) :
    ∑ z : ∀ i, A i × A' i, F (fun i ↦ (z i).1) (fun i ↦ (z i).2) = ∑ a, ∑ b, F a b := by
  rw [← Fintype.sum_prod_type']
  exact Fintype.sum_equiv (Equiv.arrowProdEquivProdArrow S A A') _ _ fun _ ↦ rfl

/-- **Expanding only the selected slots in the coordinates of the slot bases** is the source
contraction with arbitrary matrices on those slots and the rank-one matrices of the slot vectors
elsewhere. No normalization, allowedness or positivity condition is imposed. Source: Theorem 5.2,
`04-compression.tex`, lines 338–383. -/
theorem sourceContraction_preparedDensityCoefficient_selected
    (η ζ : ∀ i, EuclideanSpace ℂ (B.left i × B.right i)) (S : Finset (Fin R.length))
    (E : ∀ i, Matrix (B.left i × B.right i) (B.left i × B.right i) ℂ)
    (v v' : Word (SourceInventory.slotSystem R B X) Y) (ρ : Matrix (Config X) (Config X) ℂ) :
    sourceContraction
        (fun x ↦ v.preparedDensityCoefficient R B X (fun _ a ↦ EuclideanSpace.single a 1)
          (fun _ a ↦ EuclideanSpace.single a 1) (fun _ a ↦ EuclideanSpace.single a 1)
          (fun _ a ↦ EuclideanSpace.single a 1) v' ρ (fun i ↦ (x i).1) (fun i ↦ (x i).2))
        (fun i ↦ if i ∈ S then E i else vecMulVec (fun a ↦ η i a) (fun b ↦ conj (ζ i b))) =
      ∑ a : ∀ i : S, B.left i × B.right i, ∑ b : ∀ i : S, B.left i × B.right i,
        (∏ i : S, E i (a i) (b i)) •
          (v.preparedMatrix R B
              (fun i ↦ if h : i ∈ S then EuclideanSpace.single (a ⟨i, h⟩) 1 else η i) X * ρ *
            (v'.preparedMatrix R B
              (fun i ↦ if h : i ∈ S then EuclideanSpace.single (b ⟨i, h⟩) 1 else ζ i) X)ᴴ) := by
  classical
  have hE (i : Fin R.length) :
      ∑ z : (B.left i × B.right i) × (B.left i × B.right i),
        E i z.1 z.2 • vecMulVec (fun a ↦ EuclideanSpace.single z.1 (1 : ℂ) a)
          (fun a ↦ conj (EuclideanSpace.single z.2 (1 : ℂ) a)) = E i := by
    rw [Fintype.sum_prod_type]
    conv_rhs => rw [Matrix.matrix_eq_sum_single (E i)]
    refine Finset.sum_congr rfl fun a _ ↦ Finset.sum_congr rfl fun b _ ↦ ?_
    ext s t
    by_cases ha : s = a <;> by_cases hb : t = b <;>
      simp_all [vecMulVec_apply, PiLp.single_apply, eq_comm]
  have hpw : (fun i ↦ if i ∈ S then E i
      else vecMulVec (fun a ↦ η i a) (fun b ↦ conj (ζ i b))) =
      S.piecewise (fun i ↦ ∑ z : (B.left i × B.right i) × (B.left i × B.right i),
        E i z.1 z.2 • vecMulVec (fun a ↦ EuclideanSpace.single z.1 (1 : ℂ) a)
          (fun a ↦ conj (EuclideanSpace.single z.2 (1 : ℂ) a)))
        (fun i ↦ vecMulVec (fun a ↦ η i a) (fun b ↦ conj (ζ i b))) := by
    funext i
    simp only [Finset.piecewise, hE]
  rw [hpw, MultilinearMap.map_piecewise_sum_smul]
  refine (Finset.sum_congr rfl fun (z : ∀ i : S, (B.left i × B.right i) ×
      (B.left i × B.right i)) _ ↦ congrArg (_ • ·)
    (sourceContraction_single_dite R B X S η ζ (fun i ↦ EuclideanSpace.single (z i).1 1)
      (fun i ↦ EuclideanSpace.single (z i).2 1) v v' ρ)).trans ?_
  exact sum_selected_pairs (fun a b ↦ (∏ i : S, E i (a i) (b i)) •
    (v.preparedMatrix R B
        (fun i ↦ if h : i ∈ S then EuclideanSpace.single (a ⟨i, h⟩) 1 else η i) X * ρ *
      (v'.preparedMatrix R B
        (fun i ↦ if h : i ∈ S then EuclideanSpace.single (b ⟨i, h⟩) 1 else ζ i) X)ᴴ))

/-- **The selected source matrices may be read in arbitrary endpoint frames**: a matrix `M i`
sandwiched between the coordinate matrices of the frames `uU i, uV i` (ket) and `uU' i, uV' i`
(bra) gives the sum of its entries times the prepared densities with the frame vectors at the
selected slots and the slot vectors elsewhere. No orthonormality or spanning condition is
needed. For the Schmidt decompositions of the source, the columns of `uU i`, `uV i` are the
vectors `u_a`, `v_a` of the ket branch and those of `uU' i`, `uV' i` the vectors `ũ_c`, `ṽ_c` of
the bra branch (lines 281–290). Source: Theorem 5.2, `04-compression.tex`, lines 279–338 and
409–434. -/
theorem sourceContraction_preparedDensityCoefficient_selected_frames
    {K K' : Fin R.length → Type} [∀ i, Fintype (K i)] [∀ i, Fintype (K' i)]
    (uU : ∀ i, K i → EuclideanSpace ℂ (B.left i)) (uV : ∀ i, K i → EuclideanSpace ℂ (B.right i))
    (uU' : ∀ i, K' i → EuclideanSpace ℂ (B.left i))
    (uV' : ∀ i, K' i → EuclideanSpace ℂ (B.right i))
    (η ζ : ∀ i, EuclideanSpace ℂ (B.left i × B.right i)) (S : Finset (Fin R.length))
    (M : ∀ i, Matrix (K i × K i) (K' i × K' i) ℂ)
    (v v' : Word (SourceInventory.slotSystem R B X) Y) (ρ : Matrix (Config X) (Config X) ℂ) :
    sourceContraction
        (fun x ↦ v.preparedDensityCoefficient R B X (fun _ a ↦ EuclideanSpace.single a 1)
          (fun _ a ↦ EuclideanSpace.single a 1) (fun _ a ↦ EuclideanSpace.single a 1)
          (fun _ a ↦ EuclideanSpace.single a 1) v' ρ (fun i ↦ (x i).1) (fun i ↦ (x i).2))
        (fun i ↦ if i ∈ S then
          kroneckerSandwich (Matrix.of fun a j ↦ uU i j a) (Matrix.of fun a j ↦ uV i j a)
            (Matrix.of fun a j ↦ uU' i j a) (Matrix.of fun a j ↦ uV' i j a) (M i)
          else vecMulVec (fun a ↦ η i a) (fun b ↦ conj (ζ i b))) =
      ∑ a : ∀ i : S, K i × K i, ∑ b : ∀ i : S, K' i × K' i,
        (∏ i : S, M i (a i) (b i)) •
          (v.preparedMatrix R B
              (fun i ↦ if h : i ∈ S then
                EuclideanSpace.vecKron (uU i (a ⟨i, h⟩).1) (uV i (a ⟨i, h⟩).2) else η i) X * ρ *
            (v'.preparedMatrix R B
              (fun i ↦ if h : i ∈ S then
                EuclideanSpace.vecKron (uU' i (b ⟨i, h⟩).1) (uV' i (b ⟨i, h⟩).2)
              else ζ i) X)ᴴ) := by
  classical
  have hpw : (fun i ↦ if i ∈ S then
      kroneckerSandwich (Matrix.of fun a j ↦ uU i j a) (Matrix.of fun a j ↦ uV i j a)
        (Matrix.of fun a j ↦ uU' i j a) (Matrix.of fun a j ↦ uV' i j a) (M i)
      else vecMulVec (fun a ↦ η i a) (fun b ↦ conj (ζ i b))) =
      S.piecewise (fun i ↦ ∑ z : (K i × K i) × (K' i × K' i), M i z.1 z.2 •
          vecMulVec (fun a ↦ EuclideanSpace.vecKron (uU i z.1.1) (uV i z.1.2) a)
            (fun a ↦ conj (EuclideanSpace.vecKron (uU' i z.2.1) (uV' i z.2.2) a)))
        (fun i ↦ vecMulVec (fun a ↦ η i a) (fun b ↦ conj (ζ i b))) := by
    funext i
    simp only [Finset.piecewise, kroneckerSandwich_eq_sum_vecMulVec]
    rfl
  rw [hpw, MultilinearMap.map_piecewise_sum_smul]
  refine (Finset.sum_congr rfl fun (z : ∀ i : S, (K i × K i) × (K' i × K' i)) _ ↦
    congrArg (_ • ·) (sourceContraction_single_dite R B X S η ζ
      (fun i ↦ EuclideanSpace.vecKron (uU i (z i).1.1) (uV i (z i).1.2))
      (fun i ↦ EuclideanSpace.vecKron (uU' i (z i).2.1) (uV' i (z i).2.2)) v v' ρ)).trans ?_
  exact sum_selected_pairs (fun a b ↦ (∏ i : S, M i (a i) (b i)) •
    (v.preparedMatrix R B (fun i ↦ if h : i ∈ S then
        EuclideanSpace.vecKron (uU i (a ⟨i, h⟩).1) (uV i (a ⟨i, h⟩).2) else η i) X * ρ *
      (v'.preparedMatrix R B (fun i ↦ if h : i ∈ S then
        EuclideanSpace.vecKron (uU' i (b ⟨i, h⟩).1) (uV' i (b ⟨i, h⟩).2) else ζ i) X)ᴴ))

end Word

end QuantumCircuit.Party
