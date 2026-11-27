/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.Order.RationalCertificate
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-!
# Tests and kernel-checked witnesses for `RationalCertificate`

1. Synthetic regression checks covering zero matrices, singular rank-1 matrices,
   zero leading pivots with vanishing residual columns, rectangular Gram factors
   (`k ≠ n`), positive rational rescaling, and permutation congruence.
2. Concrete kernel-checked `decide` (no `native_decide`) proofs of complex
   positive semidefiniteness for all 27 stabilizer-reduced representative blocks
   (9 blocks of size ≤ 6 per operator) of `40(J+Q)`, `40(J-Q)`, and `40Q^Gamma_in`
   exported from `arXiv:2611.34921v1`, including all three singular blocks of
   `40(J-Q)`: `(-2):trivial_4x4` (rank 3, zero pivot at index 1),
   `(-1,-1):trivial_sym_6x6` (rank 5, zero pivot at index 3), and
   `(-1,-1):trivial_antisym_6x6` (rank 5, zero pivot at index 3).
3. Strict transitive axiom audit allowing only `propext`, `Classical.choice`,
   and `Quot.sound`.

Scope boundary: these theorems certify PSD of all 27 concrete reduced blocks
individually. Connecting them to the global 4096-dimensional operators via
concrete matrix definitions, phase-block coverage, `S_8` orbit transport, and
the `P_22` / `P_42` stabilizer congruences is proved separately.
-/

open scoped ComplexOrder

open QICLean

namespace QICLeanTest.RationalCertificate

section SyntheticRegressions

/-- Zero 2×2 matrix certified via all-zero pivots. -/
private def zero2_A : Matrix (Fin 2) (Fin 2) ℤ := ![![0, 0], ![0, 0]]
private def zero2_L : Matrix (Fin 2) (Fin 2) QPair := ![![⟨1, 1⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨1, 1⟩]]
private def zero2_d : Fin 2 → QPair := ![⟨0, 1⟩, ⟨0, 1⟩]

theorem zero2_posSemidef : (zero2_A.map (Int.cast : ℤ → ℂ)).PosSemidef :=
  posSemidef_complex_of_checkLDLPairIntBool zero2_L zero2_d (by decide)

/-- Singular rank-1 PSD 2×2 matrix `[[1, 1], [1, 1]]` with a trailing zero pivot. -/
private def rankOne2_A : Matrix (Fin 2) (Fin 2) ℤ := ![![1, 1], ![1, 1]]
private def rankOne2_L : Matrix (Fin 2) (Fin 2) QPair := ![![⟨1, 1⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨1, 1⟩]]
private def rankOne2_d : Fin 2 → QPair := ![⟨1, 1⟩, ⟨0, 1⟩]

theorem rankOne2_posSemidef : (rankOne2_A.map (Int.cast : ℤ → ℂ)).PosSemidef :=
  posSemidef_complex_of_checkLDLPairIntBool rankOne2_L rankOne2_d (by decide)

/-- Singular 2×2 matrix with zero leading pivot and vanishing residual column. -/
private def zeroLead2_A : Matrix (Fin 2) (Fin 2) ℤ := ![![0, 0], ![0, 2]]
private def zeroLead2_L : Matrix (Fin 2) (Fin 2) QPair := ![![⟨1, 1⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨1, 1⟩]]
private def zeroLead2_d : Fin 2 → QPair := ![⟨0, 1⟩, ⟨2, 1⟩]

theorem zeroLead2_posSemidef : (zeroLead2_A.map (Int.cast : ℤ → ℂ)).PosSemidef :=
  posSemidef_complex_of_checkLDLPairIntBool zeroLead2_L zeroLead2_d (by decide)

/-- Rectangular weighted Gram certificate (`3 × 2` factor) for a singular rank-2
3×3 rational matrix with fractional weights, checked via `checkGramPairBool`. -/
private def rect3_A : Matrix (Fin 3) (Fin 3) QPair :=
  ![![⟨5, 2⟩, ⟨3, 2⟩, ⟨1, 2⟩], ![⟨3, 2⟩, ⟨3, 2⟩, ⟨3, 2⟩], ![⟨1, 2⟩, ⟨3, 2⟩, ⟨5, 2⟩]]

private def rect3_L : Matrix (Fin 3) (Fin 2) QPair :=
  ![![⟨1, 1⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨1, 1⟩], ![⟨-1, 1⟩, ⟨1, 1⟩]]

private def rect3_d : Fin 2 → QPair := ![⟨1, 1⟩, ⟨3, 2⟩]

theorem rect3_posSemidef_pair :
    ((rect3_A.map QPair.toRat).map (Rat.cast : ℚ → ℂ)).PosSemidef :=
  posSemidef_complex_of_checkGramPairBool rect3_L rect3_d (by decide)

/-- Also exercise `RationalGramCertificate.IsValid.posSemidef_complex` directly via `norm_num`. -/
private def rect3_rat_A : Matrix (Fin 3) (Fin 3) ℚ :=
  ![![5 / 2, 3 / 2, 1 / 2], ![3 / 2, 3 / 2, 3 / 2], ![1 / 2, 3 / 2, 5 / 2]]

private def rect3_cert : RationalGramCertificate (Fin 3) (Fin 2) :=
  { factor := ![![1, 1], ![0, 1], ![-1, 1]]
    weights := ![1, 3 / 2] }

theorem rect3_posSemidef_struct : (rect3_rat_A.map (Rat.cast : ℚ → ℂ)).PosSemidef := by
  refine RationalGramCertificate.IsValid.posSemidef_complex (cert := rect3_cert) ?_
  constructor
  · intro r
    fin_cases r <;> norm_num [rect3_cert]
  · intro i j
    fin_cases i <;> fin_cases j <;>
      norm_num [rect3_rat_A, rect3_cert, RationalGramCertificate.reconstruct, Fin.sum_univ_two]

/-- Positive rational rescaling: `(1/40) • rankOne2` is PSD over `ℂ`. -/
theorem scaled_rankOne2_posSemidef :
    ((((1 / 40 : ℚ) • (rankOne2_A.map (Int.cast : ℤ → ℚ))).map
      (Rat.cast : ℚ → ℂ))).PosSemidef := by
  refine QICLean.Matrix.posSemidef_map_ratCast_of_smul_pos (c := 40) (by norm_num) ?_
  have h : ((40 : ℚ) • ((1 / 40 : ℚ) • (rankOne2_A.map (Int.cast : ℤ → ℚ)))).map
      (Rat.cast : ℚ → ℂ) = rankOne2_A.map (Int.cast : ℤ → ℂ) := by
    ext i j
    simp
  rw [h]
  exact rankOne2_posSemidef

/-- Permutation congruence transports PSD across swapped coordinates. -/
theorem reindexed_zeroLead2_posSemidef :
    (((zeroLead2_A.map (Int.cast : ℤ → ℚ)).submatrix
      (Equiv.swap (0 : Fin 2) 1) (Equiv.swap (0 : Fin 2) 1)).map
      (Rat.cast : ℚ → ℂ)).PosSemidef := by
  refine QICLean.Matrix.posSemidef_map_ratCast_submatrix_equiv (Equiv.swap (0 : Fin 2) 1) ?_
  have h : (zeroLead2_A.map (Int.cast : ℤ → ℚ)).map (Rat.cast : ℚ → ℂ) =
      zeroLead2_A.map (Int.cast : ℤ → ℂ) := by
    ext i j
    simp
  rw [h]
  exact zeroLead2_posSemidef

end SyntheticRegressions

section AppendixAReducedBlocks

/-- `40(J+Q)` reduced block `(+1,-3)` (size 1, rank 1). -/
private def jPlusQ_orbit_1x1_A : Matrix (Fin 1) (Fin 1) ℤ :=
  ![
    ![2797]]

private def jPlusQ_orbit_1x1_L : Matrix (Fin 1) (Fin 1) QPair :=
  ![
    ![⟨1, 1⟩]]

private def jPlusQ_orbit_1x1_d : Fin 1 → QPair :=
  ![⟨2797, 1⟩]

theorem jPlusQ_orbit_1x1_posSemidef :
    (jPlusQ_orbit_1x1_A.map (Int.cast : ℤ → ℂ)).PosSemidef :=
  posSemidef_complex_of_checkLDLPairIntBool
    jPlusQ_orbit_1x1_L jPlusQ_orbit_1x1_d (by decide)

/-- `40(J+Q)` reduced block `(+1,-2,-1)` (size 3, rank 3). -/
private def jPlusQ_orbit_3x3_A : Matrix (Fin 3) (Fin 3) ℤ :=
  ![
    ![2412, -799, 1184],
    ![-799, 5748, -2152],
    ![1184, -2152, 3765]]

private def jPlusQ_orbit_3x3_L : Matrix (Fin 3) (Fin 3) QPair :=
  ![
    ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩],
    ![⟨-799, 2412⟩, ⟨1, 1⟩, ⟨0, 1⟩],
    ![⟨296, 603⟩, ⟨-4244608, 13225775⟩, ⟨1, 1⟩]]

private def jPlusQ_orbit_3x3_d : Fin 3 → QPair :=
  ![⟨2412, 1⟩, ⟨13225775, 2412⟩, ⟨34638604603, 13225775⟩]

theorem jPlusQ_orbit_3x3_posSemidef :
    (jPlusQ_orbit_3x3_A.map (Int.cast : ℤ → ℂ)).PosSemidef :=
  posSemidef_complex_of_checkLDLPairIntBool
    jPlusQ_orbit_3x3_L jPlusQ_orbit_3x3_d (by decide)

/-- `40(J+Q)` reduced block `(+1,-1,-1,-1)` (size 6, rank 6). -/
private def jPlusQ_orbit_6x6_A : Matrix (Fin 6) (Fin 6) ℤ :=
  ![
    ![3688, 77, -1276, -876, -876, 2060],
    ![77, 3688, -876, 2060, -1276, -876],
    ![-1276, -876, 3688, 77, 2060, -876],
    ![-876, 2060, 77, 3688, -876, -1276],
    ![-876, -1276, 2060, -876, 3688, 77],
    ![2060, -876, -876, -1276, 77, 3688]]

private def jPlusQ_orbit_6x6_L : Matrix (Fin 6) (Fin 6) QPair :=
  ![
    ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩],
    ![⟨77, 3688⟩, ⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩],
    ![⟨-319, 922⟩, ⟨-3132436, 13595415⟩, ⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩],
    ![⟨-219, 922⟩, ⟨7664732, 13595415⟩, ⟨3436395179, 41477232248⟩, ⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩],
    ![
      ⟨-219, 922⟩,
      ⟨-4638436, 13595415⟩,
      ⟨4986574157, 10369308062⟩,
      ⟨-20596037681732, 94870904391825⟩,
      ⟨1, 1⟩,
      ⟨0, 1⟩],
    ![
      ⟨515, 922⟩,
      ⟨-3389308, 13595415⟩,
      ⟨-1274604829, 10369308062⟩,
      ⟨-9851312265532, 94870904391825⟩,
      ⟨2922842363, 17140550488⟩,
      ⟨1, 1⟩]]

private def jPlusQ_orbit_6x6_d : Fin 6 → QPair :=
  ![
    ⟨3688, 1⟩,
    ⟨13595415, 3688⟩,
    ⟨41477232248, 13595415⟩,
    ⟨94870904391825, 41477232248⟩,
    ⟨212271988212939112, 94870904391825⟩,
    ⟨37236499948225, 17140550488⟩]

theorem jPlusQ_orbit_6x6_posSemidef :
    (jPlusQ_orbit_6x6_A.map (Int.cast : ℤ → ℂ)).PosSemidef :=
  posSemidef_complex_of_checkLDLPairIntBool
    jPlusQ_orbit_6x6_L jPlusQ_orbit_6x6_d (by decide)

/-- `40(J+Q)` reduced block `(-2):trivial_4x4` (size 4, rank 4). -/
private def jPlusQ_orb22_trivial_4x4_A : Matrix (Fin 4) (Fin 4) ℤ :=
  ![
    ![5335, 3465, -7336, 21637],
    ![3465, 46935, -22904, 19803],
    ![-7336, -22904, 32592, -41461],
    ![21637, 19803, -41461, 192696]]

private def jPlusQ_orb22_trivial_4x4_L : Matrix (Fin 4) (Fin 4) QPair :=
  ![
    ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩],
    ![⟨63, 97⟩, ⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩],
    ![⟨-7336, 5335⟩, ⟨-1571, 3870⟩, ⟨1, 1⟩, ⟨0, 1⟩],
    ![⟨1967, 485⟩, ⟨83, 645⟩, ⟨-28504839, 46039232⟩, ⟨1, 1⟩]]

private def jPlusQ_orb22_trivial_4x4_d : Fin 4 → QPair :=
  ![⟨5335, 1⟩, ⟨4334400, 97⟩, ⟨322274624, 21285⟩, ⟨4530235050229, 46039232⟩]

theorem jPlusQ_orb22_trivial_4x4_posSemidef :
    (jPlusQ_orb22_trivial_4x4_A.map (Int.cast : ℤ → ℂ)).PosSemidef :=
  posSemidef_complex_of_checkLDLPairIntBool
    jPlusQ_orb22_trivial_4x4_L jPlusQ_orb22_trivial_4x4_d (by decide)

/-- `40(J+Q)` reduced block `(-2):standard_3x3` (size 3, rank 3). -/
private def jPlusQ_orb22_standard_3x3_A : Matrix (Fin 3) (Fin 3) ℤ :=
  ![
    ![3765, -2152, 1184],
    ![-2152, 5748, -799],
    ![1184, -799, 2412]]

private def jPlusQ_orb22_standard_3x3_L : Matrix (Fin 3) (Fin 3) QPair :=
  ![
    ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩],
    ![⟨-2152, 3765⟩, ⟨1, 1⟩, ⟨0, 1⟩],
    ![⟨1184, 3765⟩, ⟨-460267, 17010116⟩, ⟨1, 1⟩]]

private def jPlusQ_orb22_standard_3x3_d : Fin 3 → QPair :=
  ![⟨3765, 1⟩, ⟨17010116, 3765⟩, ⟨34638604603, 17010116⟩]

theorem jPlusQ_orb22_standard_3x3_posSemidef :
    (jPlusQ_orb22_standard_3x3_A.map (Int.cast : ℤ → ℂ)).PosSemidef :=
  posSemidef_complex_of_checkLDLPairIntBool
    jPlusQ_orb22_standard_3x3_L jPlusQ_orb22_standard_3x3_d (by decide)

/-- `40(J+Q)` reduced block `(-1,-1):trivial_sym_6x6` (size 6, rank 6). -/
private def jPlusQ_orb42_trivialSym_6x6_A : Matrix (Fin 6) (Fin 6) ℤ :=
  ![
    ![11466, 1558, 742, 900, -10656, 34272],
    ![1558, 20452, -2072, 7860, -10704, 45876],
    ![742, -2072, 4712, 3120, -3792, -5964],
    ![900, 7860, 3120, 75420, -37344, 31128],
    ![-10656, -10704, -3792, -37344, 57744, -62292],
    ![34272, 45876, -5964, 31128, -62292, 287280]]

private def jPlusQ_orb42_trivialSym_6x6_L : Matrix (Fin 6) (Fin 6) QPair :=
  ![
    ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩],
    ![⟨779, 5733⟩, ⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩],
    ![⟨53, 819⟩, ⟨-6228397, 58018817⟩, ⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩],
    ![⟨50, 637⟩, ⟨22180140, 58018817⟩, ⟨11291655423, 12853278337⟩, ⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩],
    ![
      ⟨-592, 637⟩,
      ⟨-26532504, 58018817⟩,
      ⟨-59412257928, 64266391685⟩,
      ⟨-196619322523, 461725856595⟩,
      ⟨1, 1⟩,
      ⟨0, 1⟩],
    ![
      ⟨272, 91⟩,
      ⟨118154610, 58018817⟩,
      ⟨-54492996474, 64266391685⟩,
      ⟨106980851273, 461725856595⟩,
      ⟨-317793607483069, 1050970670890532⟩,
      ⟨1, 1⟩]]

private def jPlusQ_orb42_trivialSym_6x6_d : Fin 6 → QPair :=
  ![
    ⟨11466, 1⟩,
    ⟨116037634, 5733⟩,
    ⟨257065566740, 58018817⟩,
    ⟨886513644662400, 12853278337⟩,
    ⟨4203882683562128, 153908618865⟩,
    ⟨24044285305204684959, 262742667722633⟩]

theorem jPlusQ_orb42_trivialSym_6x6_posSemidef :
    (jPlusQ_orb42_trivialSym_6x6_A.map (Int.cast : ℤ → ℂ)).PosSemidef :=
  posSemidef_complex_of_checkLDLPairIntBool
    jPlusQ_orb42_trivialSym_6x6_L jPlusQ_orb42_trivialSym_6x6_d (by decide)

/-- `40(J+Q)` reduced block `(-1,-1):trivial_antisym_6x6` (size 6, rank 6). -/
private def jPlusQ_orb42_trivialAntisym_6x6_A : Matrix (Fin 6) (Fin 6) ℤ :=
  ![
    ![33514, -31754, 3834, 20412, -11616, -144288],
    ![-31754, 39804, -2456, -19500, 14352, 150348],
    ![3834, -2456, 4216, -912, -2736, -6060],
    ![20412, -19500, -912, 67812, -34752, -127752],
    ![-11616, 14352, -2736, -34752, 33072, 67596],
    ![-144288, 150348, -6060, -127752, 67596, 869136]]

private def jPlusQ_orb42_trivialAntisym_6x6_L : Matrix (Fin 6) (Fin 6) QPair :=
  ![
    ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩],
    ![⟨-15877, 16757⟩, ⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩],
    ![⟨1917, 16757⟩, ⟨266449, 2200505⟩, ⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩],
    ![⟨10206, 16757⟩, ⟨-1340088, 81418685⟩, ⟨-90693, 102133⟩, ⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩],
    ![
      ⟨-5808, 16757⟩,
      ⟨28034616, 81418685⟩,
      ⟨-356448, 714931⟩,
      ⟨-115065734, 206703187⟩,
      ⟨1, 1⟩,
      ⟨0, 1⟩],
    ![
      ⟨-72144, 16757⟩,
      ⟨22852086, 16283737⟩,
      ⟨1729890, 714931⟩,
      ⟨-125324590, 206703187⟩,
      ⟨-54026312819, 1292332791732⟩,
      ⟨1, 1⟩]]

private def jPlusQ_orb42_trivialAntisym_6x6_d : Fin 6 → QPair :=
  ![
    ⟨33514, 1⟩,
    ⟨162837370, 16757⟩,
    ⟨7998648028, 2200505⟩,
    ⟨198435059520, 3778921⟩,
    ⟨15507993500784, 1446922309⟩,
    ⟨20267058562768211, 107694399311⟩]

theorem jPlusQ_orb42_trivialAntisym_6x6_posSemidef :
    (jPlusQ_orb42_trivialAntisym_6x6_A.map (Int.cast : ℤ → ℂ)).PosSemidef :=
  posSemidef_complex_of_checkLDLPairIntBool
    jPlusQ_orb42_trivialAntisym_6x6_L jPlusQ_orb42_trivialAntisym_6x6_d (by decide)

/-- `40(J+Q)` reduced block `(-1,-1):standard_sym_3x3` (size 3, rank 3). -/
private def jPlusQ_orb42_standardSym_3x3_A : Matrix (Fin 3) (Fin 3) ℤ :=
  ![
    ![7530, -4304, 2368],
    ![-4304, 11496, -1598],
    ![2368, -1598, 4824]]

private def jPlusQ_orb42_standardSym_3x3_L : Matrix (Fin 3) (Fin 3) QPair :=
  ![
    ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩],
    ![⟨-2152, 3765⟩, ⟨1, 1⟩, ⟨0, 1⟩],
    ![⟨1184, 3765⟩, ⟨-460267, 17010116⟩, ⟨1, 1⟩]]

private def jPlusQ_orb42_standardSym_3x3_d : Fin 3 → QPair :=
  ![⟨7530, 1⟩, ⟨34020232, 3765⟩, ⟨34638604603, 8505058⟩]

theorem jPlusQ_orb42_standardSym_3x3_posSemidef :
    (jPlusQ_orb42_standardSym_3x3_A.map (Int.cast : ℤ → ℂ)).PosSemidef :=
  posSemidef_complex_of_checkLDLPairIntBool
    jPlusQ_orb42_standardSym_3x3_L jPlusQ_orb42_standardSym_3x3_d (by decide)

/-- `40(J+Q)` reduced block `(-1,-1):standard_antisym_3x3` (size 3, rank 3). -/
private def jPlusQ_orb42_standardAntisym_3x3_A : Matrix (Fin 3) (Fin 3) ℤ :=
  ![
    ![7222, -800, -5872],
    ![-800, 3256, 1906],
    ![-5872, 1906, 9928]]

private def jPlusQ_orb42_standardAntisym_3x3_L : Matrix (Fin 3) (Fin 3) QPair :=
  ![
    ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩],
    ![⟨-400, 3611⟩, ⟨1, 1⟩, ⟨0, 1⟩],
    ![⟨-2936, 3611⟩, ⟨2266883, 5718708⟩, ⟨1, 1⟩]]

private def jPlusQ_orb42_standardAntisym_3x3_d : Fin 3 → QPair :=
  ![⟨7222, 1⟩, ⟨11437416, 3611⟩, ⟨13313013925, 2859354⟩]

theorem jPlusQ_orb42_standardAntisym_3x3_posSemidef :
    (jPlusQ_orb42_standardAntisym_3x3_A.map (Int.cast : ℤ → ℂ)).PosSemidef :=
  posSemidef_complex_of_checkLDLPairIntBool
    jPlusQ_orb42_standardAntisym_3x3_L jPlusQ_orb42_standardAntisym_3x3_d (by decide)

/-- `40(J-Q)` reduced block `(+1,-3)` (size 1, rank 1). -/
private def jMinusQ_orbit_1x1_A : Matrix (Fin 1) (Fin 1) ℤ :=
  ![
    ![83]]

private def jMinusQ_orbit_1x1_L : Matrix (Fin 1) (Fin 1) QPair :=
  ![
    ![⟨1, 1⟩]]

private def jMinusQ_orbit_1x1_d : Fin 1 → QPair :=
  ![⟨83, 1⟩]

theorem jMinusQ_orbit_1x1_posSemidef :
    (jMinusQ_orbit_1x1_A.map (Int.cast : ℤ → ℂ)).PosSemidef :=
  posSemidef_complex_of_checkLDLPairIntBool
    jMinusQ_orbit_1x1_L jMinusQ_orbit_1x1_d (by decide)

/-- `40(J-Q)` reduced block `(+1,-2,-1)` (size 3, rank 3). -/
private def jMinusQ_orbit_3x3_A : Matrix (Fin 3) (Fin 3) ℤ :=
  ![
    ![468, 799, -1184],
    ![799, 1452, -2168],
    ![-1184, -2168, 3435]]

private def jMinusQ_orbit_3x3_L : Matrix (Fin 3) (Fin 3) QPair :=
  ![
    ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩],
    ![⟨799, 468⟩, ⟨1, 1⟩, ⟨0, 1⟩],
    ![⟨-296, 117⟩, ⟨-68608, 41135⟩, ⟨1, 1⟩]]

private def jMinusQ_orbit_3x3_d : Fin 3 → QPair :=
  ![⟨468, 1⟩, ⟨41135, 468⟩, ⟨8024357, 41135⟩]

theorem jMinusQ_orbit_3x3_posSemidef :
    (jMinusQ_orbit_3x3_A.map (Int.cast : ℤ → ℂ)).PosSemidef :=
  posSemidef_complex_of_checkLDLPairIntBool
    jMinusQ_orbit_3x3_L jMinusQ_orbit_3x3_d (by decide)

/-- `40(J-Q)` reduced block `(+1,-1,-1,-1)` (size 6, rank 6). -/
private def jMinusQ_orbit_6x6_A : Matrix (Fin 6) (Fin 6) ℤ :=
  ![
    ![3512, -77, -3044, 876, 876, -2060],
    ![-77, 3512, 876, -2060, -3044, 876],
    ![-3044, 876, 3512, -77, -2060, 876],
    ![876, -2060, -77, 3512, 876, -3044],
    ![876, -3044, -2060, 876, 3512, -77],
    ![-2060, 876, 876, -3044, -77, 3512]]

private def jMinusQ_orbit_6x6_L : Matrix (Fin 6) (Fin 6) QPair :=
  ![
    ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩],
    ![⟨-77, 3512⟩, ⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩],
    ![⟨-761, 878⟩, ⟨2842124, 12328215⟩, ⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩],
    ![⟨219, 878⟩, ⟨-7167268, 12328215⟩, ⟨14211317461, 8470347112⟩, ⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩],
    ![
      ⟨219, 878⟩,
      ⟨-10623076, 12328215⟩,
      ⟨-1859720717, 2117586778⟩,
      ⟨-750944168132, 1465303689105⟩,
      ⟨1, 1⟩,
      ⟨0, 1⟩],
    ![
      ⟨-515, 878⟩,
      ⟨2917892, 12328215⟩,
      ⟨-3393430211, 2117586778⟩,
      ⟨-1692997864252, 1465303689105⟩,
      ⟨1263478117, 1693133192⟩,
      ⟨1, 1⟩]]

private def jMinusQ_orbit_6x6_d : Fin 6 → QPair :=
  ![
    ⟨3512, 1⟩,
    ⟨12328215, 3512⟩,
    ⟨8470347112, 12328215⟩,
    ⟨1465303689105, 8470347112⟩,
    ⟨163690423869368, 1465303689105⟩,
    ⟨83814408865, 1693133192⟩]

theorem jMinusQ_orbit_6x6_posSemidef :
    (jMinusQ_orbit_6x6_A.map (Int.cast : ℤ → ℂ)).PosSemidef :=
  posSemidef_complex_of_checkLDLPairIntBool
    jMinusQ_orbit_6x6_L jMinusQ_orbit_6x6_d (by decide)

/-- `40(J-Q)` reduced block `(-2):trivial_4x4` (size 4, rank 3, zero pivots [1]). -/
private def jMinusQ_orb22_trivial_4x4_A : Matrix (Fin 4) (Fin 4) ℤ :=
  ![
    ![3465, -3465, 7336, 19803],
    ![-3465, 3465, -7336, -19803],
    ![7336, -7336, 17808, 41461],
    ![19803, -19803, 41461, 117544]]

private def jMinusQ_orb22_trivial_4x4_L : Matrix (Fin 4) (Fin 4) QPair :=
  ![
    ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩],
    ![⟨-1, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩],
    ![⟨1048, 495⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩],
    ![⟨943, 165⟩, ⟨0, 1⟩, ⟨-32907, 160976⟩, ⟨1, 1⟩]]

private def jMinusQ_orb22_trivial_4x4_d : Fin 4 → QPair :=
  ![⟨3465, 1⟩, ⟨0, 1⟩, ⟨1126832, 495⟩, ⟨687645455, 160976⟩]

theorem jMinusQ_orb22_trivial_4x4_posSemidef :
    (jMinusQ_orb22_trivial_4x4_A.map (Int.cast : ℤ → ℂ)).PosSemidef :=
  posSemidef_complex_of_checkLDLPairIntBool
    jMinusQ_orb22_trivial_4x4_L jMinusQ_orb22_trivial_4x4_d (by decide)

/-- `40(J-Q)` reduced block `(-2):standard_3x3` (size 3, rank 3). -/
private def jMinusQ_orb22_standard_3x3_A : Matrix (Fin 3) (Fin 3) ℤ :=
  ![
    ![3435, -2168, -1184],
    ![-2168, 1452, 799],
    ![-1184, 799, 468]]

private def jMinusQ_orb22_standard_3x3_L : Matrix (Fin 3) (Fin 3) QPair :=
  ![
    ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩],
    ![⟨-2168, 3435⟩, ⟨1, 1⟩, ⟨0, 1⟩],
    ![⟨-1184, 3435⟩, ⟨177653, 287396⟩, ⟨1, 1⟩]]

private def jMinusQ_orb22_standard_3x3_d : Fin 3 → QPair :=
  ![⟨3435, 1⟩, ⟨287396, 3435⟩, ⟨8024357, 287396⟩]

theorem jMinusQ_orb22_standard_3x3_posSemidef :
    (jMinusQ_orb22_standard_3x3_A.map (Int.cast : ℤ → ℂ)).PosSemidef :=
  posSemidef_complex_of_checkLDLPairIntBool
    jMinusQ_orb22_standard_3x3_L jMinusQ_orb22_standard_3x3_d (by decide)

/-- `40(J-Q)` reduced block `(-1,-1):trivial_sym_6x6` (size 6, rank 5, zero pivots [3]). -/
private def jMinusQ_orb42_trivialSym_6x6_A : Matrix (Fin 6) (Fin 6) ℤ :=
  ![
    ![14774, 1642, -742, -900, 10656, 36768],
    ![1642, 5788, 2072, -7860, 10704, 25164],
    ![-742, 2072, 1048, -3120, 3792, 5964],
    ![-900, -7860, -3120, 10980, -14496, -31128],
    ![10656, 10704, 3792, -14496, 28656, 62292],
    ![36768, 25164, 5964, -31128, 62292, 173520]]

private def jMinusQ_orb42_trivialSym_6x6_L : Matrix (Fin 6) (Fin 6) QPair :=
  ![
    ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩],
    ![⟨821, 7387⟩, ⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩],
    ![⟨-371, 7387⟩, ⟨7957523, 20703937⟩, ⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩],
    ![⟨-450, 7387⟩, ⟨-28661460, 20703937⟩, ⟨-1, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩],
    ![⟨5328, 7387⟩, ⟨35160936, 20703937⟩, ⟨1153049816, 315163305⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩],
    ![
      ⟨18384, 7387⟩,
      ⟨77849970, 20703937⟩,
      ⟨-501228322, 315163305⟩,
      ⟨0, 1⟩,
      ⟨27310514471, 61932423572⟩,
      ⟨1, 1⟩]]

private def jMinusQ_orb42_trivialSym_6x6_d : Fin 6 → QPair :=
  ![
    ⟨14774, 1⟩,
    ⟨41407874, 7387⟩,
    ⟨3781959660, 20703937⟩,
    ⟨0, 1⟩,
    ⟨247729694288, 105054435⟩,
    ⟨28491803547405, 15483105893⟩]

theorem jMinusQ_orb42_trivialSym_6x6_posSemidef :
    (jMinusQ_orb42_trivialSym_6x6_A.map (Int.cast : ℤ → ℂ)).PosSemidef :=
  posSemidef_complex_of_checkLDLPairIntBool
    jMinusQ_orb42_trivialSym_6x6_L jMinusQ_orb42_trivialSym_6x6_d (by decide)

/-- `40(J-Q)` reduced block `(-1,-1):trivial_antisym_6x6` (size 6, rank 5, zero pivots [3]). -/
private def jMinusQ_orb42_trivialAntisym_6x6_A : Matrix (Fin 6) (Fin 6) ℤ :=
  ![
    ![28246, -24246, -3834, -20412, 11616, -139872],
    ![-24246, 21956, 2456, 19500, -14352, 133812],
    ![-3834, 2456, 1544, 912, 2736, 6060],
    ![-20412, 19500, 912, 18588, -17088, 127752],
    ![11616, -14352, 2736, -17088, 53328, -67596],
    ![-139872, 133812, 6060, 127752, -67596, 974064]]

private def jMinusQ_orb42_trivialAntisym_6x6_L : Matrix (Fin 6) (Fin 6) QPair :=
  ![
    ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩],
    ![⟨-12123, 14123⟩, ⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩],
    ![⟨-1917, 14123⟩, ⟨-5896747, 8075165⟩, ⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩],
    ![⟨-10206, 14123⟩, ⟨13971912, 8075165⟩, ⟨-1, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩],
    ![⟨5808, 14123⟩, ⟨-30936264, 8075165⟩, ⟨694496, 258073⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩],
    ![
      ⟨-69936, 14123⟩,
      ⟨19415862, 1615033⟩,
      ⟨-23403890, 3354949⟩,
      ⟨0, 1⟩,
      ⟨1083082943, 618742236⟩,
      ⟨1, 1⟩]]

private def jMinusQ_orb42_trivialAntisym_6x6_d : Fin 6 → QPair :=
  ![
    ⟨28246, 1⟩,
    ⟨16150330, 14123⟩,
    ⟨3341529204, 8075165⟩,
    ⟨0, 1⟩,
    ⟨7424906832, 258073⟩,
    ⟨5269453027091, 670304089⟩]

theorem jMinusQ_orb42_trivialAntisym_6x6_posSemidef :
    (jMinusQ_orb42_trivialAntisym_6x6_A.map (Int.cast : ℤ → ℂ)).PosSemidef :=
  posSemidef_complex_of_checkLDLPairIntBool
    jMinusQ_orb42_trivialAntisym_6x6_L jMinusQ_orb42_trivialAntisym_6x6_d (by decide)

/-- `40(J-Q)` reduced block `(-1,-1):standard_sym_3x3` (size 3, rank 3). -/
private def jMinusQ_orb42_standardSym_3x3_A : Matrix (Fin 3) (Fin 3) ℤ :=
  ![
    ![6870, -4336, -2368],
    ![-4336, 2904, 1598],
    ![-2368, 1598, 936]]

private def jMinusQ_orb42_standardSym_3x3_L : Matrix (Fin 3) (Fin 3) QPair :=
  ![
    ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩],
    ![⟨-2168, 3435⟩, ⟨1, 1⟩, ⟨0, 1⟩],
    ![⟨-1184, 3435⟩, ⟨177653, 287396⟩, ⟨1, 1⟩]]

private def jMinusQ_orb42_standardSym_3x3_d : Fin 3 → QPair :=
  ![⟨6870, 1⟩, ⟨574792, 3435⟩, ⟨8024357, 143698⟩]

theorem jMinusQ_orb42_standardSym_3x3_posSemidef :
    (jMinusQ_orb42_standardSym_3x3_A.map (Int.cast : ℤ → ℂ)).PosSemidef :=
  posSemidef_complex_of_checkLDLPairIntBool
    jMinusQ_orb42_standardSym_3x3_L jMinusQ_orb42_standardSym_3x3_d (by decide)

/-- `40(J-Q)` reduced block `(-1,-1):standard_antisym_3x3` (size 3, rank 3). -/
private def jMinusQ_orb42_standardAntisym_3x3_A : Matrix (Fin 3) (Fin 3) ℤ :=
  ![
    ![7178, -7840, 5872],
    ![-7840, 11144, -1906],
    ![5872, -1906, 13112]]

private def jMinusQ_orb42_standardAntisym_3x3_L : Matrix (Fin 3) (Fin 3) QPair :=
  ![
    ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩],
    ![⟨-3920, 3589⟩, ⟨1, 1⟩, ⟨0, 1⟩],
    ![⟨2936, 3589⟩, ⟨8088803, 4631508⟩, ⟨1, 1⟩]]

private def jMinusQ_orb42_standardAntisym_3x3_d : Fin 3 → QPair :=
  ![⟨7178, 1⟩, ⟨9263016, 3589⟩, ⟨1009812155, 2315754⟩]

theorem jMinusQ_orb42_standardAntisym_3x3_posSemidef :
    (jMinusQ_orb42_standardAntisym_3x3_A.map (Int.cast : ℤ → ℂ)).PosSemidef :=
  posSemidef_complex_of_checkLDLPairIntBool
    jMinusQ_orb42_standardAntisym_3x3_L jMinusQ_orb42_standardAntisym_3x3_d (by decide)

/-- `40Q^Gamma_in` reduced block `(+1,-3)` (size 1, rank 1). -/
private def qGammaIn_orbit_1x1_A : Matrix (Fin 1) (Fin 1) ℤ :=
  ![
    ![245]]

private def qGammaIn_orbit_1x1_L : Matrix (Fin 1) (Fin 1) QPair :=
  ![
    ![⟨1, 1⟩]]

private def qGammaIn_orbit_1x1_d : Fin 1 → QPair :=
  ![⟨245, 1⟩]

theorem qGammaIn_orbit_1x1_posSemidef :
    (qGammaIn_orbit_1x1_A.map (Int.cast : ℤ → ℂ)).PosSemidef :=
  posSemidef_complex_of_checkLDLPairIntBool
    qGammaIn_orbit_1x1_L qGammaIn_orbit_1x1_d (by decide)

/-- `40Q^Gamma_in` reduced block `(+1,-2,-1)` (size 3, rank 3). -/
private def qGammaIn_orbit_3x3_A : Matrix (Fin 3) (Fin 3) ℤ :=
  ![
    ![104, 101, 40],
    ![101, 104, 40],
    ![40, 40, 165]]

private def qGammaIn_orbit_3x3_L : Matrix (Fin 3) (Fin 3) QPair :=
  ![
    ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩],
    ![⟨101, 104⟩, ⟨1, 1⟩, ⟨0, 1⟩],
    ![⟨5, 13⟩, ⟨8, 41⟩, ⟨1, 1⟩]]

private def qGammaIn_orbit_3x3_d : Fin 3 → QPair :=
  ![⟨104, 1⟩, ⟨615, 104⟩, ⟨6125, 41⟩]

theorem qGammaIn_orbit_3x3_posSemidef :
    (qGammaIn_orbit_3x3_A.map (Int.cast : ℤ → ℂ)).PosSemidef :=
  posSemidef_complex_of_checkLDLPairIntBool
    qGammaIn_orbit_3x3_L qGammaIn_orbit_3x3_d (by decide)

/-- `40Q^Gamma_in` reduced block `(+1,-1,-1,-1)` (size 6, rank 6). -/
private def qGammaIn_orbit_6x6_A : Matrix (Fin 6) (Fin 6) ℤ :=
  ![
    ![88, 77, 16, 24, 24, 16],
    ![77, 88, 24, 16, 16, 24],
    ![16, 24, 88, 77, 16, 24],
    ![24, 16, 77, 88, 24, 16],
    ![24, 16, 16, 24, 88, 77],
    ![16, 24, 24, 16, 77, 88]]

private def qGammaIn_orbit_6x6_L : Matrix (Fin 6) (Fin 6) QPair :=
  ![
    ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩],
    ![⟨7, 8⟩, ⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩],
    ![⟨2, 11⟩, ⟨16, 33⟩, ⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩],
    ![⟨3, 11⟩, ⟨-8, 33⟩, ⟨2477, 2648⟩, ⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩],
    ![⟨3, 11⟩, ⟨-8, 33⟩, ⟨58, 331⟩, ⟨240, 779⟩, ⟨1, 1⟩, ⟨0, 1⟩],
    ![⟨2, 11⟩, ⟨16, 33⟩, ⟨67, 331⟩, ⟨-88, 779⟩, ⟨56527, 59848⟩, ⟨1, 1⟩]]

private def qGammaIn_orbit_6x6_d : Fin 6 → QPair :=
  ![⟨88, 1⟩, ⟨165, 8⟩, ⟨2648, 33⟩, ⟨292125, 29128⟩, ⟨59848, 779⟩, ⟨496125, 59848⟩]

theorem qGammaIn_orbit_6x6_posSemidef :
    (qGammaIn_orbit_6x6_A.map (Int.cast : ℤ → ℂ)).PosSemidef :=
  posSemidef_complex_of_checkLDLPairIntBool
    qGammaIn_orbit_6x6_L qGammaIn_orbit_6x6_d (by decide)

/-- `40Q^Gamma_in` reduced block `(-2):trivial_4x4` (size 4, rank 4). -/
private def qGammaIn_orb22_trivial_4x4_A : Matrix (Fin 4) (Fin 4) ℤ :=
  ![
    ![935, 3465, -6643, 8008],
    ![3465, 21735, -39557, 43792],
    ![-6643, -39557, 74032, -79261],
    ![8008, 43792, -79261, 93240]]

private def qGammaIn_orb22_trivial_4x4_L : Matrix (Fin 4) (Fin 4) QPair :=
  ![
    ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩],
    ![⟨63, 17⟩, ⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩],
    ![⟨-6643, 935⟩, ⟨-907, 540⟩, ⟨1, 1⟩, ⟨0, 1⟩],
    ![⟨728, 85⟩, ⟨857, 540⟩, ⟨284867, 369773⟩, ⟨1, 1⟩]]

private def qGammaIn_orb22_trivial_4x4_d : Fin 4 → QPair :=
  ![⟨935, 1⟩, ⟨151200, 17⟩, ⟨2588411, 1485⟩, ⟨450333275, 369773⟩]

theorem qGammaIn_orb22_trivial_4x4_posSemidef :
    (qGammaIn_orb22_trivial_4x4_A.map (Int.cast : ℤ → ℂ)).PosSemidef :=
  posSemidef_complex_of_checkLDLPairIntBool
    qGammaIn_orb22_trivial_4x4_L qGammaIn_orb22_trivial_4x4_d (by decide)

/-- `40Q^Gamma_in` reduced block `(-2):standard_3x3` (size 3, rank 3). -/
private def qGammaIn_orb22_standard_3x3_A : Matrix (Fin 3) (Fin 3) ℤ :=
  ![
    ![165, 40, 40],
    ![40, 104, 101],
    ![40, 101, 104]]

private def qGammaIn_orb22_standard_3x3_L : Matrix (Fin 3) (Fin 3) QPair :=
  ![
    ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩],
    ![⟨8, 33⟩, ⟨1, 1⟩, ⟨0, 1⟩],
    ![⟨8, 33⟩, ⟨3013, 3112⟩, ⟨1, 1⟩]]

private def qGammaIn_orb22_standard_3x3_d : Fin 3 → QPair :=
  ![⟨165, 1⟩, ⟨3112, 33⟩, ⟨18375, 3112⟩]

theorem qGammaIn_orb22_standard_3x3_posSemidef :
    (qGammaIn_orb22_standard_3x3_A.map (Int.cast : ℤ → ℂ)).PosSemidef :=
  posSemidef_complex_of_checkLDLPairIntBool
    qGammaIn_orb22_standard_3x3_L qGammaIn_orb22_standard_3x3_d (by decide)

/-- `40Q^Gamma_in` reduced block `(-1,-1):trivial_sym_6x6` (size 6, rank 6). -/
private def qGammaIn_orb42_trivialSym_6x6_A : Matrix (Fin 6) (Fin 6) ℤ :=
  ![
    ![570, 742, -42, 900, -1632, 3072],
    ![742, 8376, -2072, 15696, -29340, 33312],
    ![-42, -2072, 788, -4716, 8196, -8928],
    ![900, 15696, -4716, 32220, -58056, 64416],
    ![-1632, -29340, 8196, -58056, 108960, -116292],
    ![3072, 33312, -8928, 64416, -116292, 137184]]

private def qGammaIn_orb42_trivialSym_6x6_L : Matrix (Fin 6) (Fin 6) QPair :=
  ![
    ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩],
    ![⟨371, 285⟩, ⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩],
    ![⟨-7, 95⟩, ⟨-287469, 1055939⟩, ⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩],
    ![⟨30, 19⟩, ⟨2069730, 1055939⟩, ⟨-7344621, 2488933⟩, ⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩],
    ![⟨-272, 95⟩, ⟨-3878214, 1055939⟩, ⟨35193672, 12444665⟩, ⟨-433912, 719025⟩, ⟨1, 1⟩, ⟨0, 1⟩],
    ![
      ⟨512, 95⟩,
      ⟨4177104, 1055939⟩,
      ⟨-38091072, 12444665⟩,
      ⟨-101051, 1438050⟩,
      ⟨26267393, 28101782⟩,
      ⟨1, 1⟩]]

private def qGammaIn_orb42_trivialSym_6x6_d : Fin 6 → QPair :=
  ![
    ⟨570, 1⟩,
    ⟨2111878, 285⟩,
    ⟨248893300, 1055939⟩,
    ⟨690264000, 2488933⟩,
    ⟨112407128, 47935⟩,
    ⟨5789999250, 14050891⟩]

theorem qGammaIn_orb42_trivialSym_6x6_posSemidef :
    (qGammaIn_orb42_trivialSym_6x6_A.map (Int.cast : ℤ → ℂ)).PosSemidef :=
  posSemidef_complex_of_checkLDLPairIntBool
    qGammaIn_orb42_trivialSym_6x6_L qGammaIn_orb42_trivialSym_6x6_d (by decide)

/-- `40Q^Gamma_in` reduced block `(-1,-1):trivial_antisym_6x6` (size 6, rank 6). -/
private def qGammaIn_orb42_trivialAntisym_6x6_A : Matrix (Fin 6) (Fin 6) ℤ :=
  ![
    ![4858, -4934, 566, 4740, -1824, -25344],
    ![-4934, 7880, -2456, -11664, -4284, 34368],
    ![566, -2456, 2380, 6924, 6108, -9024],
    ![4740, -11664, 6924, 24612, 16968, -45408],
    ![-1824, -4284, 6108, 16968, 20448, -8004],
    ![-25344, 34368, -9024, -45408, -8004, 161568]]

private def qGammaIn_orb42_trivialAntisym_6x6_L : Matrix (Fin 6) (Fin 6) QPair :=
  ![
    ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩],
    ![⟨-2467, 2429⟩, ⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩],
    ![⟨283, 2429⟩, ⟨-2284651, 3484171⟩, ⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩],
    ![⟨2370, 2429⟩, ⟨-8319138, 3484171⟩, ⟨6684441, 3841639⟩, ⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩],
    ![⟨-912, 2429⟩, ⟨-7452822, 3484171⟩, ⟨8165208, 3841639⟩, ⟨795256, 2883953⟩, ⟨1, 1⟩, ⟨0, 1⟩],
    ![
      ⟨-12672, 2429⟩,
      ⟨10478112, 3484171⟩,
      ⟨-1471680, 3841639⟩,
      ⟨5126369, 2883953⟩,
      ⟨393693749, 415286126⟩,
      ⟨1, 1⟩]]

private def qGammaIn_orb42_trivialAntisym_6x6_d : Fin 6 → QPair :=
  ![
    ⟨4858, 1⟩,
    ⟨6968342, 2429⟩,
    ⟨3764806220, 3484171⟩,
    ⟨1384297440, 3841639⟩,
    ⟨4983433512, 2883953⟩,
    ⟨114888098250, 207643063⟩]

theorem qGammaIn_orb42_trivialAntisym_6x6_posSemidef :
    (qGammaIn_orb42_trivialAntisym_6x6_A.map (Int.cast : ℤ → ℂ)).PosSemidef :=
  posSemidef_complex_of_checkLDLPairIntBool
    qGammaIn_orb42_trivialAntisym_6x6_L qGammaIn_orb42_trivialAntisym_6x6_d (by decide)

/-- `40Q^Gamma_in` reduced block `(-1,-1):standard_sym_3x3` (size 3, rank 3). -/
private def qGammaIn_orb42_standardSym_3x3_A : Matrix (Fin 3) (Fin 3) ℤ :=
  ![
    ![330, 80, 80],
    ![80, 208, 202],
    ![80, 202, 208]]

private def qGammaIn_orb42_standardSym_3x3_L : Matrix (Fin 3) (Fin 3) QPair :=
  ![
    ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩],
    ![⟨8, 33⟩, ⟨1, 1⟩, ⟨0, 1⟩],
    ![⟨8, 33⟩, ⟨3013, 3112⟩, ⟨1, 1⟩]]

private def qGammaIn_orb42_standardSym_3x3_d : Fin 3 → QPair :=
  ![⟨330, 1⟩, ⟨6224, 33⟩, ⟨18375, 1556⟩]

theorem qGammaIn_orb42_standardSym_3x3_posSemidef :
    (qGammaIn_orb42_standardSym_3x3_A.map (Int.cast : ℤ → ℂ)).PosSemidef :=
  posSemidef_complex_of_checkLDLPairIntBool
    qGammaIn_orb42_standardSym_3x3_L qGammaIn_orb42_standardSym_3x3_d (by decide)

/-- `40Q^Gamma_in` reduced block `(-1,-1):standard_antisym_3x3` (size 3, rank 3). -/
private def qGammaIn_orb42_standardAntisym_3x3_A : Matrix (Fin 3) (Fin 3) ℤ :=
  ![
    ![22, -16, 16],
    ![-16, 144, 106],
    ![16, 106, 144]]

private def qGammaIn_orb42_standardAntisym_3x3_L : Matrix (Fin 3) (Fin 3) QPair :=
  ![
    ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩],
    ![⟨-8, 11⟩, ⟨1, 1⟩, ⟨0, 1⟩],
    ![⟨8, 11⟩, ⟨647, 728⟩, ⟨1, 1⟩]]

private def qGammaIn_orb42_standardAntisym_3x3_d : Fin 3 → QPair :=
  ![⟨22, 1⟩, ⟨1456, 11⟩, ⟨10125, 364⟩]

theorem qGammaIn_orb42_standardAntisym_3x3_posSemidef :
    (qGammaIn_orb42_standardAntisym_3x3_A.map (Int.cast : ℤ → ℂ)).PosSemidef :=
  posSemidef_complex_of_checkLDLPairIntBool
    qGammaIn_orb42_standardAntisym_3x3_L qGammaIn_orb42_standardAntisym_3x3_d (by decide)

end AppendixAReducedBlocks

end QICLeanTest.RationalCertificate

/-! Strict transitive axiom audit allowing only `propext`, `Classical.choice`,
and `Quot.sound`. -/
run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let decls := #[
    ``QICLean.Matrix.posSemidef_mul_diagonal_mul_conjTranspose,
    ``QICLean.Matrix.posSemidef_map_of_ratWeightedGram,
    ``QICLean.Matrix.posSemidef_map_ratCast_of_weightedGram,
    ``QICLean.Matrix.posSemidef_map_ratCast_of_eq_mul_diagonal_mul_transpose,
    ``QICLean.Matrix.posSemidef_map_ratCast_real_of_weightedGram,
    ``QICLean.Matrix.posSemidef_map_ratCast_of_smul_pos,
    ``QICLean.Matrix.posSemidef_map_ratCast_of_scaled_weightedGram,
    ``QICLean.Matrix.posSemidef_map_ratCast_submatrix_equiv,
    ``QICLean.RationalGramCertificate.IsValid.posSemidef_complex,
    ``QICLean.RationalGramCertificate.IsValid.posSemidef_real,
    ``QICLean.posSemidef_complex_of_checkGramBool,
    ``QICLean.posSemidef_complex_of_checkLDLBool,
    ``QICLean.posSemidef_complex_of_checkGramPairBool,
    ``QICLean.posSemidef_complex_of_checkLDLPairIntBool,
    ``QICLeanTest.RationalCertificate.zero2_posSemidef,
    ``QICLeanTest.RationalCertificate.rankOne2_posSemidef,
    ``QICLeanTest.RationalCertificate.zeroLead2_posSemidef,
    ``QICLeanTest.RationalCertificate.rect3_posSemidef_pair,
    ``QICLeanTest.RationalCertificate.rect3_posSemidef_struct,
    ``QICLeanTest.RationalCertificate.scaled_rankOne2_posSemidef,
    ``QICLeanTest.RationalCertificate.reindexed_zeroLead2_posSemidef,
    ``QICLeanTest.RationalCertificate.jPlusQ_orbit_1x1_posSemidef,
    ``QICLeanTest.RationalCertificate.jPlusQ_orbit_3x3_posSemidef,
    ``QICLeanTest.RationalCertificate.jPlusQ_orbit_6x6_posSemidef,
    ``QICLeanTest.RationalCertificate.jPlusQ_orb22_trivial_4x4_posSemidef,
    ``QICLeanTest.RationalCertificate.jPlusQ_orb22_standard_3x3_posSemidef,
    ``QICLeanTest.RationalCertificate.jPlusQ_orb42_trivialSym_6x6_posSemidef,
    ``QICLeanTest.RationalCertificate.jPlusQ_orb42_trivialAntisym_6x6_posSemidef,
    ``QICLeanTest.RationalCertificate.jPlusQ_orb42_standardSym_3x3_posSemidef,
    ``QICLeanTest.RationalCertificate.jPlusQ_orb42_standardAntisym_3x3_posSemidef,
    ``QICLeanTest.RationalCertificate.jMinusQ_orbit_1x1_posSemidef,
    ``QICLeanTest.RationalCertificate.jMinusQ_orbit_3x3_posSemidef,
    ``QICLeanTest.RationalCertificate.jMinusQ_orbit_6x6_posSemidef,
    ``QICLeanTest.RationalCertificate.jMinusQ_orb22_trivial_4x4_posSemidef,
    ``QICLeanTest.RationalCertificate.jMinusQ_orb22_standard_3x3_posSemidef,
    ``QICLeanTest.RationalCertificate.jMinusQ_orb42_trivialSym_6x6_posSemidef,
    ``QICLeanTest.RationalCertificate.jMinusQ_orb42_trivialAntisym_6x6_posSemidef,
    ``QICLeanTest.RationalCertificate.jMinusQ_orb42_standardSym_3x3_posSemidef,
    ``QICLeanTest.RationalCertificate.jMinusQ_orb42_standardAntisym_3x3_posSemidef,
    ``QICLeanTest.RationalCertificate.qGammaIn_orbit_1x1_posSemidef,
    ``QICLeanTest.RationalCertificate.qGammaIn_orbit_3x3_posSemidef,
    ``QICLeanTest.RationalCertificate.qGammaIn_orbit_6x6_posSemidef,
    ``QICLeanTest.RationalCertificate.qGammaIn_orb22_trivial_4x4_posSemidef,
    ``QICLeanTest.RationalCertificate.qGammaIn_orb22_standard_3x3_posSemidef,
    ``QICLeanTest.RationalCertificate.qGammaIn_orb42_trivialSym_6x6_posSemidef,
    ``QICLeanTest.RationalCertificate.qGammaIn_orb42_trivialAntisym_6x6_posSemidef,
    ``QICLeanTest.RationalCertificate.qGammaIn_orb42_standardSym_3x3_posSemidef,
    ``QICLeanTest.RationalCertificate.qGammaIn_orb42_standardAntisym_3x3_posSemidef
  ]
  for decl in decls do
    unless (← Lean.getEnv).contains decl do
      throwError "Missing declaration {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"
