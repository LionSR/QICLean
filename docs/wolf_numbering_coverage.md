# Wolf-chapter numbering coverage

Concordance between formalized declarations and the theorem/proposition
numbering of M. Wolf, *Quantum Channels & Operations: Guided Tour* (2012),
Chapters 2–6 and the currently compiled Chapter 8 prerequisites. This table
used to live as compiled Lean documentation
modules (`WolfChapter2Index.lean`, `WolfChapter6Index.lean`,
`WolfChapter6Wrappers.lean`); those modules carried zero declarations of
mathematical content beyond two dead re-export theorems, so the concordance
now lives here as plain markdown, its natural medium.

The `Kraus.wolf_prop_6_6` and `IsPositiveMap.wolf_prop_6_8` re-export
theorems formerly provided by `WolfChapter6Wrappers.lean` had zero call sites
outside their own docstring mentions; the substantive theorems they wrapped
are consumed under their real names (`isIrreducibleMap_full_similarity`,
`IsPositiveMap.exists_posSemidef_fixedPoints_decomposition`) elsewhere in the
library, so the wrapper theorems are noted below without a live Lean
counterpart.

The tensor-network-layer companion concordance (including the quantum
Wielandt inequality and the assembled quantum Perron-Frobenius theorem) lives
in the sibling TNLean project, not in this repository. The source-facing
Kraus-span characterization of primitive channels is formalized here.

## Complete named-environment audit

The August 25, 2026 audit covers all 153 literal lemma, proposition, theorem,
and corollary environments in the transcribed Wolf chapters. Definitions and
examples are outside this named-result count. After the SIC--POVM migration,
the dispositions are: 71 exact, 15 corrected or otherwise dispositioned, 10
partial-packaging, 13 partial-scope, 2 obstructed, and 42 open. Fourteen of the
15 corrected/dispositioned entries have an implemented corrected theorem; the
remaining entry is a documented disposition rather than a replacement
declaration. Thus 67 environments remain audit-unresolved
(10 partial-packaging + 13 partial-scope + 2 obstructed + 42 open), and 68 do
not have an implemented exact or corrected theorem.

Here "partial-packaging" means that substantial clauses or equation-level
components are proved but no declaration packages the full source environment.
"Partial-scope" means that the implemented theorem has a genuinely narrower
hypothesis or object class, such as a finite-Kraus or channel specialization.
These classifications concern the complete containing source environment, not
whether an individual displayed equation or supporting lemma has been proved.

## Wolf Lecture Notes — Chapter 2: Representations

This file indexes the formalization of Chapter 2 of Wolf's
*Quantum Channels & Operations: Guided Tour*, which covers the main
representations of quantum channels.

The Lorentz-normal-form statements are recorded in
`QICLean.Channel.LorentzNormalForm`.  The compactness/minimisation result is
proved there, and the `SL(2, ℂ)` action on Pauli--Minkowski coordinates is
formalized in `QICLean.Channel.LorentzNormalForm.SpinorAction`.  The displayed
diagonal, non-diagonal, and singular representatives and their exact
Choi/Kraus ranks are formalized.  The remaining proof obligations for
Proposition 2.11 are the Lorentz-orbit classification and the final scalar
normalization.  This index imports the assembling module
so that the cited formal statements are available from the main project import.

### Coverage summary

#### Section 2.1 Choi–Jamiolkowski and Kraus

* **Proposition 2.1** (CJ isomorphism, square specialization only):
  - `ChoiJamiolkowski.choiMatrix` — Choi matrix `τ = (T ⊗ id)(|Ω⟩⟨Ω|)` ✓
  - `ChoiJamiolkowski.cp_iff_choi_posSemidef` — CP ↔ `τ ≥ 0` ✓
  - `ChoiJamiolkowski.traceLeft_choiMatrix_of_tp` — TP ⟹ `tr_A(τ) = 𝟙/D` ✓
  - `ChoiJamiolkowski.choiMatrix_isHermitian_iff_hermiticityPreserving` —
    Hermiticity-preserving ↔ `τ` is Hermitian ✓
  - `ChoiJamiolkowski.trace_choiMatrix_of_tp` — `tr(τ) = 1` for TP ✓
  - `ChoiJamiolkowski.choiMatrix_id` — `τ` of identity = `|Ω⟩⟨Ω|` ✓
  - `Channel.choiRank` — rank of the Choi matrix (dimension-generic,
    via `ChoiRectangular.choiMatrix`) ✓
  - `Channel.choiRank_le_of_hasKrausCard` / `Channel.choiRank_le_of_hasKrausRankLE`
    — Choi-rank upper bounds from exact / bounded Kraus families ✓
  - `Channel.hasKrausCard_choiRank_of_cp` /
    `Channel.hasKrausRankLE_choiRank_of_cp` /
    `Channel.hasKrausRankLE_choiRank_of_cptp`
    — minimal Kraus constructions from the Choi spectral decomposition ✓
  - **Rectangular (different-dimension) form** in
    `QICLean/Channel/ChoiRectangular.lean` (namespace `ChoiRectangular`):
    `choiMatrix` — `τ = (T ⊗ id_d)(|Ω⟩⟨Ω|)` on `ℂ^{d'} ⊗ ℂ^d` ✓
    `mapOfChoiMatrix_choiMatrix` / `choiMatrix_mapOfChoiMatrix` — mutual
    inverses ✓ `trace_pairing` — `tr[A T(B)] = d·tr[τ (A ⊗ Bᵀ)]` ✓
    `choiMatrix_isHermitian_iff_hermiticityPreserving` — Hermiticity clause ✓
    `isKrausCP_iff_choiMatrix_posSemidef` — CP clause ✓
    `unital_iff_traceRight_choiMatrix` — unitality clause ✓
    `traceLeft_choiMatrix` (`tr_A(τ) = (T*(𝟙))ᵀ/d`) and
    `tracePreserving_iff_traceLeft_choiMatrix` — trace-preservation clause ✓
    `trace_choiMatrix` (`tr(τ) = tr(T*(𝟙))/d`) — normalization clause ✓
    `doublyStochastic_iff_partialTraces_proportional` — doubly-stochastic
    clause ✓
  - `ChoiRectangular.choiMatrix_eq_choiJamiolkowski` — the square development
    is the specialization `d = d'` ✓
  - Remaining square-only declarations (the `ChoiJamiolkowski.choiMatrix`
    API, `IsTracePreservingMap`, `IsChannel`) are documented as specializations
    in `docs/paper-gaps/wolf_choi_rectangular_scope.tex`.

* **Theorem 2.1** (Kraus representation, dimension-generic development):
  the root/`Channel`-namespace Kraus API is stated for rectangular Kraus
  operators `Kⱼ : Matrix (Fin d') (Fin d) ℂ`; the square development is the
  specialization `d = d'`.
  - `kraus_tp_of_sum_conjTranspose_mul` — `∑Kᵢ†Kᵢ = 𝟙` ⟹ TP ✓
  - `kraus_sum_conjTranspose_mul_of_tp` — TP ⟹ `∑Kᵢ†Kᵢ = 𝟙` ✓
  - `kraus_sum_mul_conjTranspose_of_unital` — unital ⟹ `∑KᵢKᵢ† = 𝟙` ✓
  - `kraus_same_map_of_unitary_combination` — unitary freedom (sufficient direction) ✓
  - `kraus_same_map_of_unitaryGroup_combination` / `kraus_same_map_of_exists_unitary_combination`
    — bundled/existential unitary-witness formulations for reuse in the converse roadmap ✓
  - `kraus_transition_unitary_of_hs_orthonormal`
    — converse linear-algebra core: orthonormal Kraus frames force unitary transition
    (square form only) ✓
  - `kraus_dual_eq_of_map_eq` — dual map equality from primal map equality ✓
  - `kraus_conjTranspose_mul_eq_of_map_eq` — equal Stinespring Gramians ✓
  - `kraus_rectangular_freedom` / `kraus_rectangular_freedom'`
    — Kraus freedom (necessary direction) ✓
  - `kraus_isometry_freedom_iff`
    — Wolf Theorem 2.1(4) in isometric form, including zero-padding of the smaller family ✓
  - `kraus_unitary_freedom_iff`
    — Wolf Theorem 2.1(4) in same-size unitary form ✓
  - `Channel.HasKrausCard` / `Channel.HasKrausRankLE` / `Channel.choiRank` /
    `Channel.hasKrausCard_mono` / `Channel.choiRank_le_of_hasKrausCard` /
    `Channel.hasKrausCard_choiRank_of_cp`
    — Kraus cardinality and the minimal Kraus number `r = rank(τ)` ✓
  - **Rectangular-specific form** in `QICLean/Channel/KrausRectangular.lean`
    (namespace `ChoiRectangular`, no square counterpart):
    `kraus_tp_iff_sum_conjTranspose_mul` / `kraus_unital_iff_sum_mul_conjTranspose`
    — normalization item 1 as iffs ✓
    `choiRank_isLeast_hasKrausCard_of_isKrausCP` / `choiRank_le_mul`
    — minimality of the Kraus rank and the bound `r = rank(τ) ≤ d·d'` ✓
    `exists_kraus_orthogonal_of_isKrausCP`
    — Hilbert–Schmidt orthogonal minimal family (`tr[Kᵢ†Kⱼ] ∝ δᵢⱼ`) ✓

* **Theorem 2.2** (Stinespring dilation):
  - `stinespring_dual_representation` — `T*(A) = V†(A ⊗ 𝟙)V` ✓
  - `stinespringV_isometry_iff_kraus_normalized` — `V†V = 𝟙` ↔ TP ✓
  - `stinespring_schrodinger_representation` — `T(ρ) = tr_r(VρV†)` ✓
  - **Full statement** in `QICLean/Channel/StinespringRectangular.lean`
    (namespace `ChoiRectangular`):
    `exists_stinespringV_of_isKrausCP` /
    `exists_stinespringV_pairing_of_isKrausCP`
    — for a completely positive `T : M_d → M_{d'}` and every `r ≥ rank(τ)`
    there is a `V : ℂ^d → ℂ^{d'} ⊗ ℂ^r` with `T*(A) = V†(A ⊗ 𝟙_r)V`, an
    isometry exactly when `T` is trace preserving ✓
    `exists_stinespringV_schrodinger_of_isKrausCP` /
    `exists_stinespringV_schrodinger_of_isKrausCPTP`
    — the corresponding rectangular Schrödinger-picture realization
    `T(ρ) = tr_{ℂ^r}(VρV†)`, with an isometric witness for CPTP maps ✓
    `exists_stinespringV_choiRank_of_isKrausCP` /
    `exists_stinespringV_pairing_choiRank_of_isKrausCP`
    — the dilation at the Choi-rank ancilla dimension `r = rank(τ)` ✓
    `choiRank_le_of_stinespring_dual_representation`
    — the converse bound: a dilation with ancilla dimension `r` forces
    `rank(τ) ≤ r`, so `r = rank(τ)` is the least admissible ancilla dimension
    and dilations with it are minimal (discussion after Thm. 2.2) ✓

* **Theorem 2.3** (ordered CP-maps):
  - `CPDominates` — rectangular CP partial order: `S - T` is completely
    positive ✓
  - `stinespringW` / `stinespringW_conjTranspose_mul_self` — Wolf's
    normalized auxiliary operator for a supplied rectangular Stinespring
    matrix and the source identity `WᴴW = τ` ✓
  - the inverse of `V ↦ W` uses the coefficient `d'` in tensor form (or
    `√d'` in coordinates), rather than the `d'^2` printed in the source
    footnote; the normalization typo is recorded in
    `docs/paper-gaps/wolf_lecture_notes_errata.tex` ✓
  - `Matrix.sqNorm_mulVec_le_of_conjTranspose_mul_le` /
    `Matrix.exists_contraction_mul_of_sqNorm_le` — Equation (2.13), in
    squared form, and the rectangular factorization `W₁ = C W₂` by a
    contraction `C : ℂ^{r₂} → ℂ^{r₁}` ✓
  - `CPDominates.exists_supplied_stinespring_contraction` — **source-facing
    Wolf Theorem 2.3**: for CP maps `Tᵢ : M_{d'} → M_d` with `T₁ ≤ T₂`
    and supplied Stinespring matrices with potentially distinct ancilla
    dimensions, returns `C` with `V₁ = (𝟙_{d'} ⊗ C)V₂`; if
    `r₂ = Channel.choiRank T₂`, the supplied `W₂` is surjective and `C`
    is unique ✓
  - `Matrix.blockTopRows` / `Matrix.blockTopRows_mul_conjTranspose` /
    `Matrix.blockTopRows_conjTranspose_mul_le_one` — explicit block-top
    contraction used in the canonical square corollary ✓
  - `stinespringV_eq_kronecker_blockTopRows_mul_append` — intertwining
    `V_{K} = (𝟙_D ⊗ C) · V_{K ++ L}` for the block-top projector ✓
  - `CPDominates.exists_stinespring_contraction` — canonical square
    corollary that constructs compatible dilations by appending Kraus
    families; it is no longer identified with the supplied source theorem ✓

* **Theorem 2.4** (Radon–Nikodym for quantum instruments):
  - `Matrix.blockDiagTopProj` / `Matrix.blockDiagBotProj` — orthogonal
    block projectors on the dilation space, PSD and summing to `𝟙`; these
    support only the separately constructed binary corollary, not the
    source-facing finite-family proof ✓
  - `Matrix.kroneckerMap_conjTranspose_mul_kroneckerMap` — Kronecker
    identity `A ⊗ (CᴴC) = (𝟙 ⊗ C)ᴴ (A ⊗ 𝟙) (𝟙 ⊗ C)` ✓
  - `IsKrausCP.radon_nikodym_of_stinespring` — the source-facing rectangular
    Heisenberg theorem: for a nonempty finite family of CP maps
    `Tᵢ, T : M_{d'}(ℂ) → M_d(ℂ)` with `∑ᵢ Tᵢ = T` and a supplied
    `V : ℂ^d → ℂ^{d'} ⊗ ℂ^r` satisfying `T(A) = V†(A ⊗ 𝟙_r)V`, there are
    PSD `Pᵢ ∈ M_r(ℂ)` with `∑ᵢ Pᵢ = 𝟙_r` and
    `Tᵢ(A) = V†(A ⊗ Pᵢ)V` ✓
    - Proof route: form the aggregate outcome-labelled dilation `V̂`, apply
      `CPDominates.exists_supplied_stinespring_contraction` to
      `CPDominates.refl T`, and restrict the resulting contraction `C` by
      outcome. The preliminary effects `Eᵢ` sum to `CᴴC`. The residual
      `𝟙 - CᴴC`, whose Stinespring compression under `V` vanishes, is assigned
      to a chosen outcome. The `d' = 0` case is handled separately ✓
  - `IsCPMap.radon_nikodym_of_stinespring` — the retained square-algebra
    specialization `d' = d`, proved directly from the rectangular theorem ✓
  - `IsCPMap.exists_radon_nikodym` — binary block-diagonal corollary:
    for square CP maps `T₁, T₂`, a constructed Stinespring matrix for
    `T₁ + T₂` yields PSD `P₁ + P₂ = 𝟙` with
    `Tᵢ(A) = V†(A ⊗ Pᵢ)V` ✓

* **Theorem 2.5, Equation (2.14)** (open-system representation):
  - `Channel.IsKrausCPTP.exists_openSystem_unitary` — the source-facing
    rectangular theorem for every CPTP map `T : M_d(ℂ) → M_{d'}(ℂ)` with
    `d ≥ 1`: take a Stinespring dilation space of dimension `r = dd'`, a
    normalized `φ ∈ ℂ^{d'} ⊗ ℂ^{d'}`, and a unitary on
    `ℂ^d ⊗ ℂ^{d'} ⊗ ℂ^{d'}` of total dimension `d(d')²`; tracing the first
    two tensor factors `ℂ^d ⊗ ℂ^{d'}` retains the final `d'`-dimensional
    factor and gives
    `T(ρ) = tr_E[U(ρ ⊗ |φ⟩⟨φ|)U†]` ✓
  - `IsChannel.exists_stinespring_open_system` — the older square-algebra
    specialization gives
    `T(ρ)_{ij} = ∑ₖ (V ρ V†)_{(i,k),(j,k)}` for an isometric `V` ✓
  - `IsChannel.exists_stinespring_open_system_traceRight` — equivalent
    square form via `Matrix.traceRight`: `T(ρ) = tr_E[V ρ V†]` ✓
  - `IsChannel.exists_stinespring_open_system_unitary` — square unitary form
    `T(ρ) = tr_E[U W₀ ρ W₀† U†]`, where `W₀` inserts the system into the
    first environment coordinate ✓

* **Proposition “Environment induced instruments,” Equation (2.15)**:
  - `Channel.exists_environment_povm_of_sum_eq_stinespring` — the
    source-faithful finite-family statement relative to a supplied
    rectangular Stinespring representation ✓
  - `Channel.exists_environment_povm_of_sum_eq_openSystem` — the downstream
    system-plus-environment form relative to Equation (2.14), with a POVM on
    the `dd'`-dimensional environment and the bound
    `krausRank(Tᵢ) ≤ rank(Pᵢ)` ✓

* **Theorem 2.6** (Naimark / Neumark dilation for POVMs):
  - `POVM` — positive operator-valued measure structure ✓
  - `POVM.naimarkIsometry_isometry` — `V†V = 𝟙` ✓
  - `POVM.naimarkProjection_mul_self` / `_hermitian` / `_orthogonal` /
    `_sum_eq_one` — projective-measurement axioms on the dilation ✓
  - `POVM.naimark_recovers_povm` — `V† P_i V = E_i` ✓
  - `POVM.exists_naimark_dilation` — existential Naimark dilation ✓
  - `POVM.IsNaimarkDilation` / `POVM.isNaimarkDilation_naimark`
    — formulated Naimark-dilation predicate and canonical witness ✓
  - `POVM.exists_isometry_mul_naimarkIsometry_of_recovery`
    — concrete uniqueness: any dilation using the canonical projectors factors
      through the canonical Naimark isometry via a dilation isometry ✓
  - `POVM.exists_orthonormal_basis_restriction` — a rank-one resolution
    forces `d ≤ n` and extends to an orthonormal basis of `ℂⁿ` ✓
  - `POVM.exists_orthonormal_basis_restriction_of_rank_one` — sharp
    rank-one specialization for a POVM ✓
  - `POVM.ofPSDResolutionOfIdentity` — converse construction: PSD resolution
    of identity on a dilation pulls back to a POVM ✓
  - `Instrument` — quantum-instrument structure + `total_isChannel`,
    `sum_probability`, `posteriorState` interface ✓

* **Proposition 2.7 (SIC POVMs) — CORRECTED / SOURCE-DISPOSITIONED**:
  - `Matrix.sicPOVM_offDiag_overlap_sq_bound` — Wolf Equation (2.30) for PSD
    Hilbert--Schmidt-normalized families ✓
  - `Matrix.sicPOVM_offDiag_overlap_sq_eq_iff` — equality iff each matrix is a
    rank-one orthogonal projection, the family sums to `(n/d) • 1`, and all
    off-diagonal overlaps are constant ✓
  - `Matrix.sicPOVM_linearIndependent_of_overlap_bound_eq` — Wolf's
    coefficient proof with the necessary correction `2 ≤ d` ✓
  - `Matrix.singleton_linearIndependent_of_trace_sq_eq_one` — the corrected
    singleton branch ✓
  - `SICPOVM` — the specialized SIC structure of unscaled rank-one projectors,
    with `∑ᵢ Pᵢ = d𝟙` and off-diagonal overlap `1/(d+1)` ✓
  - `SICPOVM.toPOVM` — the effects `Pᵢ/d` form a POVM ✓
  - `SICPOVM.linearIndependent_projector` — the `d²` projectors form an
    operator basis ✓
  - `SICPOVM.diagonal_representation` — Wolf Equation (2.33) ✓
  - `SICPOVM.krausMap_eq` / `SICPOVM.isChannel_krausMap` — the Kraus
    operators `Pᵢ/√d` define the channel in Wolf Equation (2.34) ✓

  The source's unqualified linear-independence conclusion fails for `d = 1`
  and `n > 1`; the formalization records this correction and proves all valid
  branches.

#### Section 2.1 Representation corollaries (Propositions 2.2–2.4)

* **Proposition 2.2** (decomposition into completely positive maps), in
  `QICLean/Channel/CPDecomposition.lean`:
  - `ChoiRectangular.exists_four_isKrausCP_complexCombination` — every linear
    map `M_d(ℂ) → M_{d'}(ℂ)` is a ℂ-linear combination of four CP maps ✓
  - `ChoiRectangular.exists_two_isKrausCP_realCombination_of_hermiticityPreserving`
    — a Hermitian map is an ℝ-linear combination of two CP maps ✓

* **Proposition 2.2, sandwich-sum specialization** (square algebra, with the
  four CP maps written out through the polarization identity of Chapter 1,
  `Notes/WolfNoteTexSource/ch01_deconstructing_quantum.tex`, lines 586–591):
  - `WolfProps.polarization_sandwich` — `4 • (A X Bᴴ) = (A+B) X (A+B)ᴴ
    − (A−B) X (A−B)ᴴ + I•(A+I·B) X (A+I·B)ᴴ − I•(A−I·B) X (A−I·B)ᴴ` ✓
  - `WolfProps.cp_decomposition_of_sandwich_sum` — every map of `M_D(ℂ)` given
    in the sandwich-sum form `X ↦ ∑ᵢ Aᵢ X Bᵢᴴ` is a signed ℂ-linear
    combination of four CP maps ✓

* **Proposition 2.3** (no information without disturbance):
  - `WolfProps.vecMulVec_star_eq_polarization` — rank-one outer products
    polarize into rank-one self-outer-products ✓
  - `WolfProps.linearMap_eq_id_of_fixes_rankOne` — a linear map fixing
    every `vecMulVec v (star v)` is the identity ✓
  - `WolfProps.channel_eq_id_of_fixes_pureStates` — a channel fixing
    every pure-state projector is the identity channel ✓
  - `Channel.exists_nonneg_smul_id_of_isCPMap_of_sum_eq_id` — the
    source-faithful statement: a finite family of CP maps with
    `∑ α, T α = id` has `T α = c α • id` with `c α ≥ 0` ✓
  - `Channel.exists_nonneg_weights_of_isCPMap_of_sum_eq_id` — the weights
    satisfy `∑ α, c α = 1` ✓
  - `Channel.exists_nonneg_forall_trace_map_eq_of_isCPMap_of_sum_eq_id` —
    `tr[T α ρ] = c α` for every `ρ` of unit trace ✓
  - `Instrument.exists_nonneg_forall_probability_eq_of_total_eq_id` — the
    same conclusion for the `Instrument` structure ✓

* **Proposition 2.4** (equivalence of ensembles, Hughston–Jozsa–Wootters):
  - `WolfProps.pureEnsembleDensity` — density operator of a pure-state
    ensemble `∑ᵢ |ψᵢ⟩⟨ψᵢ|` ✓
  - `WolfProps.pureEnsembleDensity_eq_of_isometric_mixing` — sufficient
    direction: ensembles related by an isometric mixing matrix share
    the same density ✓
  - `WolfProps.exists_isometric_mixing_of_pureEnsembleDensity_eq` —
    necessary direction (HJW converse): equal densities force an
    isometric mixing matrix between the two ensembles ✓
  - `WolfProps.pureEnsembleDensity_eq_iff_exists_isometric_mixing` —
    both directions stated as an iff, under the cardinality hypothesis
    `card ι₂ ≤ card ι₁` ✓
  - `WolfProps.pureEnsembleDensity_eq_iff_exists_unitary_mixing` — Wolf's
    own statement, in `QICLean.Channel.EnsembleEquivalence`: after padding
    both ensembles with zero vectors onto `ι₁ ⊕ ι₂`, equal densities are
    equivalent to unitary mixing, with no cardinality hypothesis ✓
  - `WolfProps.pureEnsembleDensity_eq_iff_exists_unitary_mixing_fin` —
    the same statement with `Fin (max m n)` as common index set ✓

#### Section 2.3 Transfer matrix

* `transferMatrix` — the `D² × D²` matrix representing `T` in the
  standard-basis vectorization ✓
* `transferMatrix_mulVec_eq` — `T̂ *ᵥ vec(ρ) = vec(T(ρ))` ✓
* `transferMatrix_comp` — `(S ∘ T)^ = Ŝ * T̂` ✓
* `transferMatrix_id` — transfer matrix of identity = identity ✓
* `transferMatrix_injective` — the representation is faithful ✓
* `transferMatrix_kraus` — Kraus form: `T̂ = ∑ᵢ K'ᵢ ⊗ₖ Kᵢ` ✓
* `MPSTensor.transferMatrix_eq` — MPS transfer-operator specialization, stated in
  `TNLean.MPS.Core.TransferMatrix`: `E_A` has transfer matrix `∑ᵢ Āᵢ ⊗ₖ Aᵢ` ✓

#### Sections 2.3–2.4 Transfer-matrix characterizations and unitary actions

* `transferMatrix_tp_iff` — Section 2.3, Equation (2.20), entrywise consequence:
  TP ↔ column-diagonal sums = δ ✓
* `transferMatrix_unital_iff` — Section 2.3, Equation (2.20), entrywise consequence:
  unital ↔ row-diagonal sums = δ ✓
* `transferMatrix_hermiticityPreserving_iff` — Section 2.3, Equation (2.20),
  entrywise consequence: HP ↔ conjugation symmetry of transfer-matrix entries ✓
* `unitaryConjLM` — unitary conjugation map `Ad_U(X) = U X U†` ✓
* `transferMatrix_unitaryConj` — Section 2.4, lines 1000–1010, matrix-unit
  analogue of the qubit unitary action: `(Ad_U)^ = Ū ⊗ₖ U` ✓
* `unitaryConjLM_isChannel_of_unitary` — `Ad_U` is a channel for unitary `U` ✓
* `transferMatrix_unitaryConj_sandwich` — Section 2.4 unitary-action identity:
  `(Ad_{U₁} ∘ T ∘ Ad_{U₂})^ = (Ū₁⊗U₁) * T̂ * (Ū₂⊗U₂)` ✓

#### General matrix SVD results

* `Matrix.svd_of_posSemidef` — **SVD for PSD matrices** (spectral theorem
  formulated): `M = U * diagonal σ * Uᴴ` with `σ ≥ 0` ✓
* `Matrix.svd_of_isUnit` — **SVD existence for invertible complex matrices**:
  `M = U * diagonal σ * Vᴴ` with `U, V` unitary and `σ > 0` ✓
* `transferMatrix_svd_of_isUnit` — **SVD representation of a transfer
  matrix**: every invertible transfer matrix admits an SVD ✓

#### Section 2.4 Lorentz normal form (existence)

* `Wolf.SLFiltering` — **SL(d, ℂ)-filtering operation**: a CP map
  Φ(X) = S X S† with det(S) = 1 ✓ (definitional)
* `Wolf.SLFiltering.comp` — composition of SL-filterings ✓
* `Wolf.SLFiltering.S_isUnit` — `S` invertible follows from det=1 ✓
* `Wolf.InvertibleFilter` / `Wolf.InvertibleFilter.map` — **general
  invertible Kraus-rank-one filtering operation**
  `Φ_X(A) = X A X†` for `X ∈ GL(d, ℂ)` ✓ (definitional)
* `Wolf.InvertibleFilter.comp` / `Wolf.InvertibleFilter.inv` — composition
  and inverse filterings, with map composition in the source order ✓
* `Wolf.InvertibleFilter.choiRank_eq_one` — an invertible filter has Kraus
  rank exactly one when `d ≥ 1` ✓
* `Wolf.InvertibleFilter.exists_scalar_slFiltering` — every invertible
  filtering matrix has a decomposition `X = cS`, with `c ≠ 0`,
  `c^d = det X`, `S ∈ SL(d, ℂ)`, and
  `Φ_X = |c|² Φ_S`, where `|c|² > 0` ✓
* `Wolf.InvertibleFilter.filteredMap_eq_normSq_smul` — for a rectangular
  `T : M_{d₁} → M_{d₂}`, the source-ordered filtering
  `Φ₂ ∘ T ∘ Φ₁` has scalar factor `|c₁c₂|²` after decomposing both filters ✓
* `Wolf.DoublyStochastic` — doubly-stochastic condition: T(1) ∝ 1 and
  tr₁[τ] ∝ 1 ✓ (definitional)
* `pauliMatrices` — the four Pauli matrices (qubit basis) ✓ (definitional)
* `pauliTransferEntry` — Pauli-basis transfer matrix entry ✓ (definitional)
* `Wolf.pauliMinkowskiEquiv` — the real-linear identification
  `M₂†(ℂ) ≃ ℝ⁴` by Hermitian Pauli coordinates ✓
* `Wolf.det_pauliMatrixOfMinkowski` — the determinant identity immediately
  before Equation (2.41): `det(M(x)) = x₀² - x₁² - x₂² - x₃²` ✓
* `Wolf.posSemidef_pauliMatrixOfMinkowski_iff` — positive-semidefinite
  Hermitian qubit matrices correspond exactly to the closed future Lorentz
  cone ✓
* `Wolf.spinorMatrix` / `Wolf.pauliMatrixOfMinkowski_spinorMatrix_mulVec` —
  Equation (2.41), the four-dimensional congruence
  `M ↦ X M X†` in Pauli--Minkowski coordinates ✓. This is distinct from the
  three-dimensional adjoint action `SpinCover.pauliConjAd`
* `Wolf.spinorMatrix_isSpecialOrthochronousLorentz` — the spinor image obeys
  all three conditions printed in Equation (2.42): determinant one,
  `L η Lᵀ = η`, and `L₀₀ > 0` ✓
* `Wolf.spinorMatrix_neg` — `X` and `-X` induce the same congruence action ✓
* `Wolf.specialOrthochronousLorentzGroup` / `Wolf.spinorCoverHom` — the
  special orthochronous Lorentz matrices as a group and the bundled
  homomorphism `SL(2, ℂ) →* SO⁺(1,3)` ✓
* `Wolf.exists_sl2_spinorMatrix_eq` / `Wolf.spinorCoverHom_surjective` — every
  special orthochronous Lorentz matrix has a spinor preimage, constructed by
  the canonical boost followed by an `SU(2)` lift of the residual `SO(3)`
  rotation ✓
* `Wolf.spinorCoverHom_eq_iff_eq_or_eq_neg` /
  `Wolf.spinorCoverHom_eq_one_iff` — every fibre is exactly `{X, -X}` and the
  kernel is exactly `{1, -1}` ✓
* `Wolf.boostSpinor_posDef` — the canonical boost lift
  `P_u = (M(u) + I)/√(2(1+u₀))` satisfies `P_u > 0`, matching the
  positive factor in Wolf's polar decomposition immediately before
  Equation (2.44) (source lines 1067–1077) ✓
* `Wolf.pauliTransferMatrix_two_sided_filtering` — Equation (2.43) over the
  complex Pauli transfer matrix, in the exact order `L₂ T̂ L₁` ✓
* `Wolf.coe_pauliTransferMatrixReal_of_preservesHermiticity` /
  `Wolf.pauliTransferMatrixReal_slFiltering` — identification with the real
  transfer matrix for Hermiticity-preserving maps and the bundled
  `SLFiltering` specialization of Equation (2.43) ✓
* `Wolf.spinorMatrix_boostExpSL2` — the boost formula in Equation (2.44),
  `exp(t n·σ/2) ↦ exp(t n·B)`, including the identification of the Lorentz
  exponential with the canonical rapidity boost ✓
* `Wolf.spinorMatrix_rotationExpSL2` — the rotation formula in Equation
  (2.44), with the corrected congruence-action sign
  `exp(-i t n·σ/2) ↦ exp(+t n·R)` ✓. Wolf's printed negative Lorentz sign is
  documented in `docs/paper-gaps/wolf_ch2_spinor_rotation_sign.tex`
* `IsLorentzDiagonal` — diagonal Lorentz normal form (Wolf Proposition 2.11 case 1) ✓
* `IsLorentzNonDiagonal` — non-diagonal Lorentz normal form (case 2) ✓
* `IsLorentzSingular` — singular Lorentz normal form (case 3) ✓
  These are the same three transfer-matrix cases stated in Wolf--Cirac,
  *Dividing Quantum Channels*, arXiv:math-ph/0611057v3, Theorem 18.  Its rank
  statements concern only the non-diagonal and singular cases 2 and 3.
* `Wolf.diagonalBellWeight` / `Wolf.diagonalKraus` / `Wolf.diagonalMap` —
  the bistochastic Pauli family in Verstraete--Verschelde Theorem 8,
  Equation (18), with its four Bell weights derived directly from Pauli
  conjugation and with Pauli transfer matrix `diag(1, s₁, s₂, s₃)` under their
  nonnegativity hypothesis. Verstraete--Verschelde's printed constraint
  `1 - s₁ - s₂ - s₃ ≥ 0` is not used: their preceding Equation (16) makes
  `R_Φ` the Bloch transfer matrix, so that constraint incorrectly excludes the
  identity channel. The local final inequality
  `1 - s₁ - s₂ + s₃ ≥ 0` is the direct Equation (18) calculation and agrees
  with Wolf's Equation (2.40); the partial-transpose `σ₂` sign has already been
  absorbed in `R_Φ` and does not provide a parameter conversion ✓
* `Wolf.choiRank_diagonalMap` — the diagonal representative's Choi/Kraus
  rank is the number of nonzero Bell weights, including ranks 1 through 4;
  this is the direct Equation (18) Bell-family calculation, not a rank claim
  from Wolf--Cirac Theorem 18 ✓
* `Wolf.nonDiagonalKraus` / `Wolf.nonDiagonalMap` — the exact three-operator
  non-diagonal representative in Verstraete--Verschelde Theorem 8,
  Equation (19), with its arbitrary-matrix action and Pauli transfer matrix ✓
* `Wolf.choiRank_nonDiagonalMap_eq_three` /
  `Wolf.choiRank_nonDiagonalMap_one` — the non-diagonal representative has
  Choi/Kraus rank 3 for `0 ≤ x < 1` and rank 2 at `x = 1` ✓
* `Wolf.singularKraus` / `Wolf.singularMap` — the singular representative,
  the third normal form in Verstraete--Verschelde Theorem 8, Equation (17),
  realizes `X ↦ tr(X)|0⟩⟨0|`, has the stated Pauli transfer matrix, and satisfies
  `Wolf.choiRank_singularMap : Channel.choiRank singularMap = 2` ✓
* `Wolf.infimum_is_attained` — **key compactness lemma**: trace minimisation
  over SL(d₁, ℂ) × SL(d₂, ℂ) filterings of a positive-definite operator on
  ℂ^{d₂} ⊗ ℂ^{d₁} attains its infimum ✓ (rectangular form)
* `Wolf.exists_normal_form_generic_tau` — **Wolf Proposition 2.8, normal form
  for generic τ** (source lines 894–919): for every positive-definite operator
  on ℂ^{d₂} ⊗ ℂ^{d₁}, there are determinant-one local filters attaining the
  infimum in Equation (2.36) whose filtered operator has both partial traces
  proportional to the respective identity matrices ✓ (distinct dimensions
  d₁ and d₂ are preserved)
* `Wolf.exists_normal_form_generic` — **Wolf Proposition 2.9, square case**:
  every CP map `T : M_D → M_D` with full Kraus rank admits SL-filterings
  making it doubly-stochastic ✓ (proved via the global-minimum/AM–GM
  argument at the minimiser, using the trace-determinant AM-GM equality
  characterisation). This is the equal-dimension specialization; the general
  rectangular statement is `Wolf.exists_normal_form_generic_rect` below
* `Wolf.DoublyStochasticRect` — rectangular doubly-stochastic condition:
  `T(𝟙) ∝ 𝟙` and `T*(𝟙) ∝ 𝟙` ✓ (definitional)
* `Wolf.exists_normal_form_generic_rect` — **Wolf Proposition 2.9, rectangular
  form**: every CP map `T : M_{d₁} → M_{d₂}` with full Kraus rank
  (positive-definite `ChoiRectangular.choiMatrix T`) admits SL-filterings
  `Φ₁ : SLFiltering d₁`, `Φ₂ : SLFiltering d₂` making `Φ₂ ∘ T ∘ Φ₁`
  doubly-stochastic ✓ (derived from `Wolf.exists_normal_form_generic_tau` by
  the rectangular Choi transformation and partial-trace identities)
* **Wolf Proposition 2.11 (Lorentz normal form for qubit channels)** remains
  pending as an existence and orbit-classification theorem. The required
  general invertible Kraus-rank-one CP filters and their scalar freedom, the
  determinant-one spinor action, and its exact action on Pauli transfer
  matrices are formalized. The source-displayed diagonal, non-diagonal, and
  singular representatives, including their exact actions and Choi/Kraus
  ranks, are also formalized. The Lorentz-orbit classification, necessity of the
  non-diagonal parameter range, and final trace-preserving normalization have
  no Lean declaration yet. The former determinant-one `SLFiltering`
  formulation was false and was removed.

#### Formalization

| Definition | File | Lean name |
|------------|------|-----------|
| Partial trace (left) | `PartialTrace.lean` | `Matrix.traceLeft` |
| Partial trace (right) | `PartialTrace.lean` | `Matrix.traceRight` |
| Maximally entangled vector | `MaximallyEntangled.lean` | `Matrix.omegaVec` |
| Maximally entangled projector | `MaximallyEntangled.lean` | `Matrix.omegaProj` |
| SWAP operator F | `MaximallyEntangled.lean` | `Matrix.swapMatrix` |
| Tensor product of maps | `TensorMap.lean` | `Matrix.tensorMapId` |
| Choi matrix | `ChoiJamiolkowski.lean` | `ChoiJamiolkowski.choiMatrix` |
| Rectangular Choi matrix | `ChoiRectangular.lean` | `ChoiRectangular.choiMatrix` |
| Rectangular Kraus rank | `KrausRank.lean` | `Channel.choiRank` |
| Stinespring isometry | `Stinespring.lean` | `stinespringV` |
| POVM | `POVM.lean` | `POVM` |
| Naimark isometry | `POVM.lean` | `POVM.naimarkIsometry` |
| Naimark projector | `POVM.lean` | `POVM.naimarkProjection` |
| Rank-one Naimark | `POVM/RankOneNaimark.lean` | `POVM.exists_orthonormal_basis_restriction` |
| Quantum instrument | `POVM.lean` | `Instrument` |
| Transfer matrix | `TransferMatrix.lean` | `transferMatrix` |
| Unitary conjugation | `TransferMatrix.lean` | `unitaryConjLM` |
| Vectorization | `Mathlib.LinearAlgebra.Matrix.Vec` | `Matrix.vec` |
| SL-filtering | `LorentzNormalForm.lean` | `Wolf.SLFiltering` |
| SL-filtering composition | `LorentzNormalForm.lean` | `Wolf.SLFiltering.comp` |
| Invertible filtering | `LorentzNormalForm/InvertibleFilter.lean` |
  `Wolf.InvertibleFilter` |
| Exact invertible-filter Kraus rank | `LorentzNormalForm/InvertibleFilter.lean` |
  `Wolf.InvertibleFilter.choiRank_eq_one` |
| Scalar/SL filtering decomposition | `LorentzNormalForm/InvertibleFilter.lean` |
  `Wolf.InvertibleFilter.exists_scalar_slFiltering` |
| Doubly-stochastic | `LorentzNormalForm.lean` | `Wolf.DoublyStochastic` |
| Rectangular doubly-stochastic | `LorentzNormalForm.lean` | `Wolf.DoublyStochasticRect` |
| Rectangular generic normal form | `LorentzNormalForm.lean` |
  `Wolf.exists_normal_form_generic_rect` |
| Pauli matrices | `LorentzNormalForm.lean` | `pauliMatrices` |
| Pauli transfer entry | `LorentzNormalForm.lean` | `pauliTransferEntry` |
| Pauli--Minkowski equivalence | `LorentzNormalForm/SpinorAction.lean` |
  `Wolf.pauliMinkowskiEquiv` |
| Minkowski determinant identity | `LorentzNormalForm/SpinorAction.lean` |
  `Wolf.det_pauliMatrixOfMinkowski` |
| Spinor Lorentz action | `LorentzNormalForm/SpinorAction.lean` |
  `Wolf.spinorMatrix_isSpecialOrthochronousLorentz` |
| Spinor epimorphism and exact two-point fibres |
  `LorentzNormalForm/SpinorCover.lean` |
  `Wolf.spinorCoverHom_surjective`, `Wolf.spinorCoverHom_eq_iff_eq_or_eq_neg` |
| Spinor boost and rotation exponentials |
  `LorentzNormalForm/SpinorExponential.lean` |
  `Wolf.spinorMatrix_boostExpSL2`, `Wolf.spinorMatrix_rotationExpSL2` |
| Filtered Pauli transfer action | `LorentzNormalForm/SpinorAction.lean` |
  `Wolf.pauliTransferMatrixReal_slFiltering` |
| Diagonal Lorentz form | `LorentzNormalForm.lean` | `IsLorentzDiagonal` |
| Non-diagonal Lorentz form | `LorentzNormalForm.lean` | `IsLorentzNonDiagonal` |
| Singular Lorentz form | `LorentzNormalForm.lean` | `IsLorentzSingular` |
| Canonical diagonal, non-diagonal, and singular representatives |
  `LorentzNormalForm/CanonicalQubitChannels.lean` |
  `Wolf.diagonalMap`, `Wolf.nonDiagonalMap`, `Wolf.singularMap` |
| Canonical representative Choi/Kraus ranks |
  `LorentzNormalForm/CanonicalQubitChannels.lean` |
  `Wolf.choiRank_diagonalMap`, `Wolf.choiRank_nonDiagonalMap_eq_three`,
  `Wolf.choiRank_nonDiagonalMap_one`, `Wolf.choiRank_singularMap` |

#### Not yet formalized

| Result | Notes |
|--------|-------|
| Section 2.4 Lorentz normal form (Proposition 2.11) | Correctly formulated
  statement and proof remain pending. The general invertible Kraus-rank-one
  filters, their scalar/SL decomposition, and the determinant-one Lorentz
  action on Pauli transfer matrices are available. The displayed diagonal,
  non-diagonal, and singular representatives and their ranks are also
  available. The proof still needs the Lorentz-orbit classification, the
  necessity of the parameter bounds, and the final trace-preserving
  normalization. |
| Section 2.4 Sorted singular values | Current SVD is unsorted; later uses want sorted values |

### References

* [M. Wolf, *Quantum Channels & Operations: Guided Tour*, Chapter 2][Wolf2012QChannels]
* [F. Verstraete and H. Verschelde, *On Quantum Channels*,
  arXiv:quant-ph/0202124v2](https://arxiv.org/abs/quant-ph/0202124v2)

---

## Wolf Lecture Notes — Chapter 3: Positive Maps

### Section 3.1 Choi criteria for n-positive maps

#### Wolf Proposition 3.1 — FORMALIZED WITH A SOURCE WORDING CORRECTION

- `ChoiJamiolkowski.isNPositiveMap_iff_forall_rightCompression_posSemidef`
  — Equation (3.4) for a rectangular map `M_d(ℂ) → M_{d'}(ℂ)`: positivity
  of every input-factor compression by `X : M_{d×k}(ℂ)` is equivalent to
  `k`-positivity ✓
- `ChoiJamiolkowski.isNPositiveMap_iff_forall_rankProjection_choiMatrix_sandwich_posSemidef_rectangular`
  — item 2, with rank-`k` Hermitian projections on the input factor, under
  `d > 0` and `k ≤ d` ✓
- `ChoiJamiolkowski.isNPositiveMap_iff_forall_hasSchmidtRankLE_choiMatrix_quadraticForm_nonneg_rectangular`
  — item 3 on the output-first space `ℂ^{d'} ⊗ ℂ^d`, using the mathematically
  correct condition `SR(ψ) ≤ k` ✓
- Wolf prints exact Schmidt rank `k`, which is vacuous when `k > d'` and is
  not what the displayed compression proof establishes. The counterexample,
  corrected statement, and scope of a possible exact-rank reformulation are
  recorded in
  `docs/paper-gaps/wolf_prop3_1_exact_schmidt_rank_scope.tex`.

### Section 3.2 Detecting entanglement and Schmidt number

#### Wolf Proposition 3.3 — FORMALIZED WITH A SOURCE WORDING CORRECTION

- `Matrix.not_hasSchmidtNumberLE_iff_exists_witness` — a trace-one Hermitian
  state lies outside `S_n` iff a Hermitian witness is negative on the state
  and nonnegative on every vector of Schmidt rank at most `n` ✓
- Wolf prints exact Schmidt rank `n`. This is vacuous when
  `n > min(d,d')` and does not describe the pure generators of `S_n` used by
  the separating-hyperplane proof. The counterexample, corrected statement,
  and exact-rank scope are recorded alongside the same defect in Proposition
  3.1 at `docs/paper-gaps/wolf_prop3_1_exact_schmidt_rank_scope.tex`.

#### Wolf Proposition 3.4 — FORMALIZED (RECTANGULAR FORM)

- `Matrix.HasSchmidtNumberLE.tensorMapId_posSemidef` — the only-if direction
  for an `n`-positive map `T : M_d(ℂ) → M_r(ℂ)`, with an independent
  bystander dimension; the pure-state proof uses the rectangular
  right-factor parametrization
  `ChoiJamiolkowski.exists_compression_of_vector` ✓
- `ChoiJamiolkowski.exists_isNPositiveMap_choiMatrix_eq_of_witness` — Equation
  (3.13) in Wolf's orientation: a witness `W` on `ℂ^d ⊗ ℂ^{d'}` is the
  rectangular Choi matrix of an `n`-positive map
  `P : M_{d'}(ℂ) → M_d(ℂ)` ✓
- `ChoiJamiolkowski.trace_choiMatrix_mul_eq_omegaVec_quadraticForm_traceAdjointMap`
  — Equation (3.14), with `T = traceAdjointMap P` and the test vector
  `omegaVec d'` ✓
- `Matrix.exists_isNPositiveMap_tensorMapId_not_posSemidef` — if a trace-one
  Hermitian state on `ℂ^d ⊗ ℂ^{d'}` lies outside `S_n`, an `n`-positive map
  `T : M_d(ℂ) → M_{d'}(ℂ)` detects it ✓
- `Matrix.hasSchmidtNumberLE_iff_forall_isNPositiveMap_tensorMapId_posSemidef`
  — the full rectangular equivalence in Proposition 3.4 for density operators ✓

#### Wolf Proposition 3.5 — FORMALIZED (RECTANGULAR FORM)

- `IsCompletelyCopositiveMap`, `IsDecomposablePositiveMap`, and
  `IsIndecomposablePositiveMap` — Wolf Equation (3.2), now for maps
  `T : M_d(ℂ) → M_{d'}(ℂ)` rather than only square endomorphisms ✓
- `IsDecomposablePositiveMap.tensorMapId_posSemidef_of_isPPT` — a rectangular
  decomposable map preserves positivity on a PPT input, with an independent
  bystander dimension ✓
- `Matrix.exists_isIndecomposablePositiveMap_of_isPPT_not_isSeparable` — a PPT
  entangled density operator on `ℂ^d ⊗ ℂ^{d'}` yields an indecomposable positive
  map `T : M_d(ℂ) → M_{d'}(ℂ)`, by Proposition 3.4 at `n = 1` and the
  contrapositive of decomposable-PPT preservation ✓
- `Matrix.IsDecomposableWitness` and
  `ChoiRectangular.isDecomposablePositiveMap_iff_choiMatrix_traceAdjointMap_isDecomposableWitness`
  — the explicit Equation (3.15) cone `W = P₁ + P₂^{T₁}` and its rectangular
  trace-adjoint Choi correspondence with decomposable maps ✓
- `Matrix.convex_setOf_isDecomposableWitness` — convexity of the explicit
  Equation (3.15) decomposable-witness cone, as used in the proof of
  Proposition 3.5 ✓
- `Matrix.IsNormalizedDecomposableWitness` — the trace-one decomposable
  operators `a P₁ + (1-a) P₂^{T₁}` of
  Lewenstein–Kraus–Cirac–Horodecki Theorem 3, with `a ∈ [0,1]` and
  positive trace-one `P₁,P₂` ✓
- `Matrix.isCompact_setOf_isNormalizedDecomposableWitness`,
  `Matrix.isNormalizedDecomposableWitness_iff`, and
  `Matrix.convex_setOf_isNormalizedDecomposableWitness` — compactness and
  convexity of the normalized set, and its identification with the trace-one
  section of Wolf's Equation (3.15) cone in nonzero dimensions ✓
- `Matrix.PosSemidef.hasSchmidtNumberLE_left` and
  `Matrix.isCompact_setOf_posSemidef_trace_one` — the rectangular
  positive-semidefinite trace-one section used in the compactness proof ✓
- `Matrix.partialTransposeLeft_smul` and
  `Matrix.continuous_partialTransposeLeft` — scalar compatibility and
  continuity of Wolf's first-factor partial transpose, used for the compact
  continuous-image description ✓
- `Matrix.trace_partialTransposeLeft_mul` and
  `Matrix.trace_partialTransposeLeft_mul_re` — self-adjointness of
  first-factor partial transpose for the complex bilinear and real trace
  pairings ✓
- `Matrix.exists_posSemidef_isPPT_negative_separator_of_not_isDecomposableWitness`
  — strict separation of a trace-one Hermitian operator outside the
  decomposable cone from the compact convex normalized set; its `a = 1` and
  `a = 0` endpoints give positivity of the separator and of its first-factor
  partial transpose ✓
- `Matrix.exists_isPPT_not_isSeparable_of_not_isDecomposableWitness` — the
  nonzero separator is normalized to a PPT density operator, and its negative
  pairing with the block-positive witness proves entanglement ✓
- `Matrix.IsIndecomposablePositiveMap.exists_isPPT_not_isSeparable` — for
  `T : M_d(ℂ) → M_{d'}(ℂ)`, the nonzero block-positive witness is the
  output-first rectangular matrix
  `ChoiRectangular.choiMatrix (traceAdjointMap T)` on
  `Fin d × Fin d'`; its positive trace permits normalization without changing
  decomposability, and the normalized separation theorem produces a PPT
  entangled state on `ℂ^d ⊗ ℂ^{d'}` ✓
- `Matrix.exists_isIndecomposablePositiveMap_iff_exists_isPPT_not_isSeparable`
  — Wolf Proposition 3.5 for fixed nonzero dimensions, with the printed map
  orientation `M_d(ℂ) → M_{d'}(ℂ)` and first-factor partial transpose ✓
- `Matrix.exists_isIndecomposablePositiveMap_iff_exists_isPPT_not_isSeparable_all_dimensions`
  — the same equivalence in arbitrary finite dimensions; if either dimension
  is zero, every relevant map is the zero decomposable map and no trace-one
  state exists ✓
- The reverse implication is resolved by the compact trace-one separation
  route of Lewenstein–Kraus–Cirac–Horodecki Theorem 3. No closedness theorem
  for the full unbounded cone and no dual definition of decomposability are
  used. Both directions, and hence the full rectangular proposition, are
  formalized; see
  `docs/paper-gaps/wolf_prop3_5_reverse_implication.tex`.

#### Wolf Example 3.1, Equation (3.20) (Choi-type maps) — POSITIVITY FORMALIZED; INDECOMPOSABILITY IN PROGRESS

- `Matrix.choiTypeMap` and `Matrix.choiTypeMap_vecMulVec` formalize the map
  and its rank-one reduction on the cyclic index set `ZMod d` ✓
- `Matrix.choiTypeMap_isPositiveMap_one` proves positivity for the complete
  bottom slice `n = 1` in every dimension `d ≥ 3`, including rank-one vectors
  with vanishing coordinates ✓
- `Matrix.choiTypeMap_isPositiveMap_sub_two` proves positivity for the complete
  top slice `n = d - 2` in every dimension `d ≥ 3` ✓
- `Matrix.haTwoSimpleVector_hasSchmidtRankLE_two` and
  `Matrix.haAGamma_hasSchmidtNumberLE_two` formalize Ha's root-average
  decomposition into projectors onto 2-simple vectors ✓
- `Matrix.haArGamma_apply` and
  `Matrix.partialTransposeRight_haAGamma_eq_haBlockTransposeDecomposition`
  formalize Ha's root-average entry formula and the displayed
  block-transpose identity on pp. 594--595 ✓
- `Matrix.partialTransposeRight_haAGamma_hasSchmidtNumberLE_two` proves that
  the displayed block transpose also belongs to the two-simple cone ✓
- `Matrix.tensorFactorSwap_haAGamma_hasSchmidtNumberLE_two` and
  `Matrix.partialTransposeLeft_tensorFactorSwap_haAGamma_hasSchmidtNumberLE_two`
  transport Ha's two decompositions to the Eom--Kye orientation: if
  `ρ = A_γ^σ`, then both `ρ` and `ρ^{T₁} = (A_γ^{T₂})^σ` belong to the
  two-simple cone ✓
- `Matrix.eomKyePairing_eq_JPairing_tensorMapId_factorSwap` proves the exact
  tensor-factor order in the Eom--Kye pairing, and
  `Matrix.eomKyePairing_eq_omegaVec_quadraticForm_factorSwap` records the
  factor `d` required by the normalized vector
  `Ω = d⁻¹ᐟ² ∑ᵢ eᵢ ⊗ eᵢ` ✓
- `Matrix.eomKyePairing_haAGamma_choiTypeMap` and
  `Matrix.choiTypeMapFin_haAGamma_omegaVec_quadraticForm` prove, for the full
  source range `d ≥ 3`, `1 ≤ n ≤ d - 2`, and `γ > 0`, that both the
  Eom--Kye pairing and its normalized factor-swapped quadratic form equal
  `γ² - 1`; the corresponding strict-negativity theorems cover
  `0 < γ < 1` ✓
- `Yamagami.norm_symbol_sub_half_lt_half` formalizes the corrected
  Wolf-range (`m ≤ d - 2`) part of Yamagami's stride-one Lemma 6 open-disk
  condition, one dependency of the remaining variational proof. The printed
  endpoint `m = d - 1`, `s = d` is false with a strict inequality and is
  recorded in the paper-gap note; this theorem does not prove the cyclic
  inequality ✓
- `Yamagami.forwardMatrix`, `Yamagami.dft_map_hessianMatrix_mulVec`,
  `Yamagami.hessianMatrix_forwardMatrix_posSemidef`,
  `Yamagami.hessianMatrix_forwardMatrix_mulVec_eq_zero_iff_isScalarVector`,
  `Yamagami.forwardMatrix_isUnit_det`, and
  `Yamagami.functional_eq_lambdaT_inverseOperator_mulVec` formalize the
  stride-one Fourier--Hessian prerequisite from Yamagami's Lemmas 2--4 and
  Corollary 5. In the exact range `d ≥ 3`, `1 ≤ m ≤ d - 2`, and `s ≥ d`, the
  cyclic matrix is nonnegative and invertible, its negative-Hessian
  representative is positive semidefinite with kernel `ℝ · 1`, and the
  concrete functional is exactly `λ_{S⁻¹}(Sx)` ✓
- `Yamagami.deleteLastCoordinate` and
  `Yamagami.functional_le_deleteLastCoordinate` formalize the p. 525
  regular-boundary recurrence. In the exact range `N ≥ 3`,
  `2 ≤ m ≤ N - 2`, and `s ≥ N`, deleting a zero final coordinate gives
  `f_{N,m,s}(x) ≤ f_{N-1,m-1,s-1}(x')`, including when the reduced vector has
  a singular denominator under Lean's totalized division ✓
- `Nowosad.inducedHilbertNorm_sq` and
  `Nowosad.exists_inducedHilbertNorm_bound` identify the norm induced by the
  faithful coordinate-sum functional with the finite `L²` norm and prove that
  every finite-coordinate linear operator is bounded for this norm. This is
  the Hilbert-norm hypothesis in Nowosad's Theorem 1.8, rather than the
  supremum norm on a raw function space ✓
- `Nowosad.mem_laurentSubalgebra_of_eq_on_valueClass`,
  `Nowosad.valueClassIdempotent_mem_laurentSubalgebra`, and
  `Nowosad.coordinate_pointDerivation_eq_zero` identify the finite Laurent
  algebra `P(w)` with the functions constant on the value classes of `w` and
  kill its coordinate point derivations with the corresponding value-class
  idempotents. This is the genuine Laurent-algebra specialization of the
  Singer--Wermer step, including repeated coordinates of `w` ✓
- `Nowosad.finiteCoordinate_theorem_one_eight` and
  `Nowosad.lambdaT_eq_on_laurentSubalgebra_of_two_localMinOn` formalize the
  finite real-coordinate conclusion of Nowosad's local-minimum Theorem 1.8:
  multiplication, and hence constancy of `λ_T`, on the regular part of
  `u · P(u⁻¹v)`. `Nowosad.isLocalMinOn_lambdaT_neg_of_isLocalMaxOn` and
  `Nowosad.lambdaT_eq_on_laurentSubalgebra_of_two_localMaxOn` expose the
  source-prescribed `T ↦ -T` passage to Yamagami's local maxima ✓
- `Yamagami.pulledBackTangent_mem_hessianKernel_and_not_isScalarVector` and
  `Yamagami.lemma_three_localMax_isScalar` formalize the uniqueness assertion
  of Yamagami's Lemma 3. The Nowosad generator is exactly `b = (S a)/s`, and
  the original-coordinate curve is `x(t) = s S⁻¹(b^t)`. With
  `H = s(S+Sᵀ)-2SᵀS`, the Euclidean Hessian convention is
  `D²f_S(1)[h,h] = -s⁻³⟨h,Hh⟩`. A non-scalar local maximum therefore yields
  the named non-scalar tangent `s S⁻¹(log b)` in `ker H` ✓
- The displayed analytic Hessian identity fixes the normalization used in the
  source; it is not separately formalized as a Fréchet-derivative theorem.
  The Lean proof instead uses `Yamagami.dotProduct_hessianMatrix_mulVec` and
  `Yamagami.minimumQuadraticForm_normalizedNegativeInverse_eq`, the exact
  algebraic second-variation identity needed by Nowosad's argument.
- The preceding Lemma 3 declaration proves uniqueness only. The cyclic
  Fourier--Hessian package specializes its algebraic hypotheses and identifies
  the generic `lambdaT` composition with the concrete stride-one
  `Yamagami.functional`; the compactness argument below supplies the separate
  existence and global-maximality step.
- `Yamagami.limsup_functional_le_card_ratio_of_singularDenominator`
  formalizes the omitted simultaneous-singularity boundary count: one
  least-next-positive zero string supplies all `m` vanishing summands, without
  a maximal-block decomposition ✓
- `Yamagami.functional_le_card_ratio_of_strictlyPositive` transfers an
  already proved strictly positive inequality to Lean's direct nonnegative
  `0 / 0 = 0` value. This general theorem remains conditional and is recorded
  independently of the source-ordered inductive proof. See
  `docs/paper-gaps/yamagami93_simultaneous_singularity_boundary.tex` ✓
- `Yamagami.functional_card_le_one` proves the nonnegative cardinal-parameter
  cyclic reciprocal inequality in the exact range `N ≥ 3`,
  `1 ≤ m ≤ N - 2`. Strong induction handles regular boundary points, the
  simultaneous-singularity estimate excludes singular points from the compact
  superlevel closure, and the Fourier--Hessian/Nowosad theorem makes the
  positive maximizer scalar ✓
- `Matrix.choiTypeRankOneWeight_reciprocal_sum_middle` and
  `Matrix.choiTypeMap_vecMulVec_posSemidef_middle` transport the cyclic
  inequality by index negation to the backward Choi weights and prove
  rank-one positivity for `2 ≤ n ≤ d - 3` ✓
- `Matrix.choiTypeMap_isPositiveMap` combines the bottom endpoint, the middle
  range, and the top endpoint to prove positivity for every `d ≥ 3` and
  `1 ≤ n ≤ d - 2` ✓
- The former positivity scope restriction is resolved and recorded in
  `docs/paper-gaps/wolf_ex3_1_choi_positivity_subcase_scope.tex`. The final
  theorem combining positivity with the negative witness to conclude
  indecomposability remains open in issue #18; its completed witness algebra
  is recorded in `docs/paper-gaps/ha98_choi_type_witness_scope.tex`.

### Section 3.3 Transposition and time reversal

#### Wolf Theorem 3.1 (Kramers' theorem) — FORMALIZED

- `Matrix.IsHermitian.two_le_finrank_eigenspace_of_antiunitary` — the printed
  antiunitary statement: `[H,T] = 0` and `T² = -1` for Hermitian `H` and
  antiunitary `T` imply every eigenvalue is at least two-fold degenerate ✓
  (in `QICLean/Algebra/KramersDegeneracy.lean`)
- `Matrix.IsHermitian.two_le_finrank_eigenspace_of_antisymmetric_unitary` —
  Wolf's matrix reduction `T = ΓV` of the same theorem: `H` Hermitian,
  `Vᴴ * V = 1`, `H * Vᴴ = Vᴴ * Hᵀ`, `Vᵀ = -V` ✓ — proved as the unitary
  special case `A = Vᴴ` of the corrected Theorem 3.2 below

#### Wolf Theorem 3.2 (Kramers' theorem II) — FALSE AS PRINTED; CORRECTED FORM FORMALIZED

- The original statement (`H` Hermitian, `Aᵀ = -A ≠ 0`, `H * A = A * Hᵀ` ⟹
  every eigenvalue at least two-fold degenerate) is false: the partner
  `A *ᵥ star ψ` of an eigenvector can vanish. The counterexample
  (`H = diag(0,1,1)`, `A` the antisymmetric unit of the `1`-eigenspace) and
  the corrected statements are recorded in
  `docs/paper-gaps/wolf_ch3_kramers_theorem_ii.tex`; the false printed form
  is deliberately not formalized.
- `Matrix.IsHermitian.transpose_mulVec_star_of_mulVec_eq_smul` and
  `Matrix.IsHermitian.mulVec_star_intertwiner_of_mul_eq_mul_transpose` —
  eigenvector transport: `A *ᵥ star ψ` is again a `μ`-eigenvector ✓
- `Matrix.dotProduct_star_mulVec_star_eq_zero_of_transpose_eq_neg` —
  orthogonality `star ψ ⬝ᵥ (A *ᵥ star ψ) = 0` ✓
- `Matrix.IsHermitian.two_le_finrank_eigenspace_of_intertwiner_mulVec_star_ne_zero`
  — corrected conditional form: the eigenspace of `μ` has dimension `≥ 2`
  whenever the partner `A *ᵥ star ψ` is nonzero ✓
- `Matrix.IsHermitian.two_le_finrank_eigenspace_of_antisymmetric_isUnit` —
  invertible-`A` global corollary: if `A` is invertible, every eigenvalue of
  `H` is at least two-fold degenerate ✓

---

## Wolf Lecture Notes — Chapter 4: Convex Structure

### Equation 4.3 and lines 85–105 (semidefinite duality) — FORMALIZED WITH FINITENESS CORRECTION

- `SemidefiniteProgram.HermitianMatrix.psdCone`, `innerDual_psdCone`, and
  `interior_psdCone_eq_posDef` realize the Hermitian positive-semidefinite
  matrices as a self-dual proper cone for the real trace pairing, with the
  zero-dimensional case included.
- `SemidefiniteProgram.traceAnalysisMap` and `traceAnalysisMap_adjoint` prove
  the source identities `T(X)ᵢ = tr(FᵢX)` (the trace is real) and
  `T†(y) = ∑ᵢ yᵢFᵢ`. The primal/dual and strict-feasibility iff lemmas expose
  exactly Wolf's trace constraints and Loewner signs.
- `SemidefiniteProgram.weak_duality_pointwise` and `weak_duality` specialize
  the existing conic values to Equation 4.3, retaining their documented
  empty and unbounded extended-real semantics.
- The four `*_of_primalStrict_of_primalValue_eq_coe` and
  `*_of_dualStrict_of_dualValue_eq_coe` declarations specialize corrected
  Slater duality and attainment. They require a finite value on the strictly
  feasible side; the unqualified printed claim at lines 100–105 is false
  without this boundary, as recorded in
  `docs/paper-gaps/wolf_slater_attainment_conditions.tex`.

### Equation 4.4 and lines 107–116 (complementary slackness) — FORMALIZED

- `SemidefiniteProgram.complementary_slackness` proves
  `(F₀ - ∑ᵢ yᵢFᵢ)X = 0` from explicit primal/dual feasibility and equal
  objectives; `complementary_slackness_supports` proves the orthogonal-support
  consequence.
- `SemidefiniteProgram.isDualOptimizer_iff_exists_complementary` gives Wolf's
  optimizer characterization under equality of the conic values and explicit
  primal attainment, with every trace and Loewner feasibility hypothesis in
  the statement.

The surrounding complexity prose at source lines 80–83 is not formalized.

---

## Wolf Lecture Notes — Chapter 5: Schwarz Inequalities

### Theorem 5.2 (block Schur complement) — CORRECTED FORM FORMALIZED

- `SchurComplement.blockMatrix_posSemidef_iff` proves the equivalence between
  positivity of the block matrix and the pseudoinverse Schur-complement
  condition, including the necessary right-support condition.
- `SchurComplement.blockMatrix_posSemidef_iff_contraction` proves the corrected
  contraction criterion. In the singular case the off-diagonal block must
  satisfy support conditions on both sides; the printed condition omits the
  left-support condition.
- `SchurComplement.wolf_condition_three_not_sufficient` records the scalar
  counterexample to the uncorrected condition. The correction is documented in
  `docs/paper-gaps/wolf_schur_complement_tfae.tex`.

### Consequence of Equation 5.56 and Proposition 5.3, Equation 5.57 — FORMALIZED WITH THE ORDER-HYPOTHESIS CORRECTION

- `LinearMap.IsSymmetric.eigenvalues_le_of_sub_isPositive` proves the
  cross-operator Weyl monotonicity step by a finite-dimensional variational
  argument. For the `j`th decreasing eigenvalue, the span of the first
  `j + 1` ordered eigenvectors of the smaller operator and the span of the
  last `d - j` ordered eigenvectors of the larger operator have dimensions
  summing to `d + 1`. A common nonzero vector gives the lower and upper
  quadratic-form bounds, while positivity of the difference gives the middle
  inequality. Thus no pointwise cross-matrix eigenvalue comparison is assumed
  ✓
- `Matrix.IsHermitian.eigenvalues₀_mono` and
  `Matrix.IsHermitian.eigenvalues_mono` transport this result to Hermitian
  matrices in the Loewner order:
  `A ≤ B` implies `λⱼ↓(A) ≤ λⱼ↓(B)` for every decreasing-eigenvalue index.
  This is the consequence of Equation 5.56 used immediately before
  Proposition 5.3 ✓
- `Matrix.IsHermitian.exists_unitary_cfc_le_cfc_of_le` formalizes the corrected
  Proposition 5.3. For Hermitian `A ≤ B`, it first chooses one unitary from
  their decreasingly ordered eigenbases; that same unitary then works for
  every interval containing both spectra and every scalar function
  non-decreasing on that interval. Hence the quantifier order is
  `∃ U, ∀ I, ∀ f`, and the conclusion is the corrected Equation 5.57,
  `f(A) ≤ U f(B) U†` ✓
- The hypothesis `A ≤ B` is indispensable. The printed unqualified
  proposition is false already for `d = 1`: take `A = [1]`, `B = [0]`,
  `I = [0,1]`, and `f(x) = x`. Every one-dimensional unitary is a phase, so
  the claimed conclusion becomes `1 ≤ 0`. The resolved false-source note is
  `docs/paper-gaps/wolf_ch5_unitary_comparison_missing_order.tex`.

---

## Wolf Chapter 6 — Spectral Properties: Public Theorem Index

This module serves as a **navigational index** that maps the formalized theorems
in this project to the numbering in:

> M. Wolf, *Quantum Channels & Operations: Guided Tour* (2012), Chapter 6.

Each entry lists the Wolf result, its status (fully formalized / partially
formalized / not yet formalized), and the Lean declaration(s) that correspond.

No new proofs are introduced here; this is a documentation-only index module.

This module covers the sections of Wolf Chapter 6 whose formalization lives in
the quantum-channel layer.  The sections formalized in the tensor-network layer
— the quantum Wielandt inequality (Theorem 6.9), the unique-fixed-point theorem
for tensors with eventually full Kraus rank (Theorem 6.15), and the assembled
quantum Perron–Frobenius theorem — are indexed in
`TNLean.Wielandt.WolfChapter6TNIndex`.

---

### Section 6.1 Spectral radius and determinant

#### Wolf Proposition 6.1 (Spectral radius of positive maps) — FORMALIZED

* `IsPositiveMap.norm_apply_le_norm_map_one_mul_norm` — the sharp
  Russo--Dye estimate `‖T(X)‖∞ ≤ ‖T(1)‖∞ ‖X‖∞` for every positive
  matrix map, using the matrix C*-operator norm.
* `IsPositiveMap.eigenvalue_norm_le_norm_map_one` — Wolf Equation (6.3),
  `|μ| ≤ ‖T(1)‖∞` for every eigenvalue.
* `IsPositiveMap.spectralRadius_le_nnnorm_map_one` — Wolf Equation (6.2),
  `ρ(T) ≤ ‖T(1)‖∞` for every positive map on a nonzero matrix algebra.
* `eigenvalue_one_of_map_one_eq_one`,
  `IsPositiveMap.eigenvalue_norm_le_one_of_map_one_eq_one`, and
  `IsPositiveMap.spectralRadius_eq_one_of_map_one_eq_one` — for a positive
  unital map, eigenvalue $1$, the closed-unit-disk bound, and spectral radius
  exactly $1$, without complete positivity.
* `IsPositiveMap.eigenvalue_norm_le_one_of_tracePreserving` — every eigenvalue of a
  positive trace-preserving map lies in the closed unit disk, in
  `QICLean.Channel.Determinant.Bound`.
* `IsPositiveMap.eigenvalue_one_exists_of_tracePreserving` — eigenvalue $1$ exists
  (nonzero PSD fixed point), in `QICLean.Channel.Peripheral.SpectralRadius`.
* `IsPositiveMap.spectralRadius_eq_one_of_tracePreserving` — a positive
  trace-preserving map has spectral radius exactly $1$, by combining the two
  preceding results.

The pinned Mathlib has no standalone Russo--Dye theorem. The formal proof
derives its sharp matrix norm estimate from Wolf Theorem 5.6, using the
identity as a commuting dominant operator after normalizing by `‖T(1)‖∞`.
Thus no four-positive-parts estimate and no factor $4$ occur. The resolved
proof-route note is
`docs/paper-gaps/wolf_prop61_russo_dye_factor.tex`.

#### Wolf Theorem "Determinants" and Equation (6.22) — FORMALIZED

* `channelDet_comp` — Wolf Equation (6.22),
  `det(T₁.comp T₂) = det(T₁) det(T₂)`, with Lean composition in the
  source's displayed order.
* `channelDet_norm_le_one_of_positive_tracePreserving` — the magnitude bound
  `|det T| ≤ 1` for every positive trace-preserving map.
* `ChannelDeterminant.Internal.exists_real_channelDet_mem_Icc_of_positive_tracePreserving`
  — the full first clause: `det T` is real and belongs to `[-1,1]`.
* `ChannelDeterminant.Internal.channelDet_norm_eq_one_iff_exists_unitary_or_transpose_of_positive_tracePreserving`
  — for positive matrix dimension, the source-general saturation alternative:
  `|det T| = 1` exactly for unitary conjugations and unitary conjugations after
  ordinary transposition.
* `ChannelDeterminant.Internal.channelDet_transposeLinearMapComplex` and
  `ChannelDeterminant.Internal.channelDet_transposeLinearMapComplex_eq_neg_one_iff`
  — ordinary transposition has determinant `(-1)^(d(d-1)/2)`, which equals
  `-1` exactly when `⌊d/2⌋` is odd.
* `ChannelDeterminant.Internal.channelDet_eq_neg_one_iff_exists_unitary_transpose_of_positive_tracePreserving`
  and
  `ChannelDeterminant.Internal.channelDet_eq_one_iff_exists_unitary_of_positive_tracePreserving_of_odd`
  — the source-facing sign classifications in Wolf Theorem "Determinants"(3).
* `channelDet_norm_eq_one_iff_exists_unitaryChannel` — the CPTP specialization
  of determinant saturation: a quantum channel has determinant magnitude one
  exactly when it is a unitary conjugation.

The proof follows Wolf's route: phase-spectrum saturation, Dirichlet recurrent
powers converging to `T_φ = id`, positivity of the inverse, the existing
cone/rank/Wigner classification, and trace-preserving normalization of its
implementer.  The transposition sign is the same pair count as Wolf's
Gell--Mann-basis argument, represented by the matrix-unit pair-swap
permutation.  Positive matrix dimension is explicit as `[NeZero d]` in the
saturation and sign-classification declarations.

#### Wolf Corollary "Monotonicity of the determinant" — PARTIALLY FORMALIZED

* `channelDet_norm_comp_le_of_positive_tracePreserving` — for positive
  trace-preserving `T₁,T₂`,
  `|det(T₁.comp T₂)| ≤ |det T₁|`.
* `channelDet_norm_comp_eq_iff` — the exact algebraic equality split
  `|det(T₁.comp T₂)| = |det T₁|` iff
  `det T₁ = 0` or `|det T₂| = 1`.

The general positive trace-preserving saturation classification above now
replaces `|det T₂| = 1` by Wolf's geometric alternative "unitary conjugation
or matrix transposition".  The declarations here deliberately retain the
algebraic equality split as a reusable separate theorem.

#### Wolf Corollary "Positive invertible maps" — FORMALIZED

* `ChannelDeterminant.Internal.inverseOfBijective_isTracePreservingMap` — the
  source's observation that the inverse of a bijective trace-preserving linear
  map is automatically trace preserving.
* `ChannelDeterminant.Internal.channelDet_norm_eq_one_of_inverseOfBijective_isPositiveMap`
  — if a positive trace-preserving bijection and its inverse are positive, the
  determinant bounds and multiplicativity force `|det T| = 1`.
* `ChannelDeterminant.Internal.inverseOfBijective_unitaryChannel` and
  `ChannelDeterminant.Internal.inverseOfBijective_unitaryChannel_comp_transpose`
  — the explicit inverses of the two standard forms, with the correct reversed
  composition order in the transpose branch.
* `ChannelDeterminant.Internal.wolfPositiveInvertibleMaps` — for positive
  matrix dimension, the inverse of a positive trace-preserving bijection is
  positive exactly when the map is unitary conjugation or unitary conjugation
  after ordinary transposition.

The forward implication follows Wolf's determinant route and consumes the
source-general saturation theorem above.  The converse uses the explicit
positive inverse of each standard form; it does not strengthen the hypotheses
to complete positivity and therefore retains Wolf's transpose branch.

#### Wolf Proposition "Positive determinant for small Kraus rank" and Equation (6.26) — FORMALIZED

* `channelDet_nonneg_of_two_kraus` proves the source-facing two-operator
  statement without a trace-preservation hypothesis.
* `channelDet_nonneg_of_hasKrausRankLE_two` includes exact Kraus cardinalities
  zero and one through Wolf's zero-padding operation.
* `IsKrausCP.channelDet_nonneg_of_choiRank_le_two` states the proposition using
  Kraus rank in Wolf's sense, namely the Choi rank of a completely positive
  map.

The proof follows Equation (6.26): it factors the two-Kraus transfer matrix,
uses unitary Schur triangularization to pair the factors
`1 + conj(λᵢ) * λⱼ`, and realizes the source's final density step by the
explicit perturbation `Aₙ = A + (1 / (n + 1)) I`.  In Schur coordinates the
perturbed diagonal is eventually nonzero, and continuity of the Kronecker
transfer determinant closes the singular case.  The repository's
column-stacking convention writes `conj(A) ⊗ A`; the Blueprint records its
relation to Wolf's printed `A ⊗ conj(A)` ordering explicitly.


#### Wolf Lemma 6.1 (Dirichlet's simultaneous approximation) — FORMALIZED

* `Dirichlet.exists_int_near_mul_simultaneous` — the $m$-variable simultaneous
  approximation $1\le n\le q^m$ with $|x_k n-p_k|\le 1/q$ for all $k$, in
  `QICLean.Analysis.Dirichlet`.

#### Wolf Proposition 6.2 (Trivial Jordan blocks for peripheral spectrum) — FORMALIZED

* `IsPositiveMap.no_rank_two_genEigenvector_of_tracePreserving` and
  `IsPositiveMap.no_rank_two_genEigenvector_of_unital` — rank-2
  generalized eigenvectors do not exist at peripheral eigenvalues, in
  `QICLean.Channel.Peripheral.JordanBlocks`.
* `IsPositiveMap.peripheral_Jordan_trivial_of_tracePreserving` and
  `IsPositiveMap.peripheral_Jordan_trivial_of_unital` —
  $\ker(T-\lambda)^k = \ker(T-\lambda)$ for all $k$ when $|\lambda| = 1$, in
  `QICLean.Channel.Peripheral.JordanBlocks`.
* `IsPositiveMap.pow_apply_rank_two_genEig` — binomial expansion:
  $T^n X = \lambda^n X + n \lambda^{n-1} (T-\lambda)X$ when $(T-\lambda)^2 X = 0$.
* `IsPositiveMap.hasBoundedOrbits_of_unital` — a positive unital map has
  bounded forward orbits, the unital counterpart of
  `IsPositiveMap.hasBoundedOrbits_of_tracePreserving`, in
  `QICLean.Channel.Peripheral.JordanBlocks`.

Both cases follow Wolf's proof directly (not by duality): the uniform bound
$\operatorname{tr}[A\,T(B)] \le \|A\|_\infty \|B\|_\infty \operatorname{tr}[1\,T(1)]
= d \|A\|_\infty \|B\|_\infty$ holds verbatim for trace-preserving and unital
positive maps alike, since $\operatorname{tr}[1\,T(1)] = d$ in both cases.
Formerly documented as a scope restriction in
`docs/paper-gaps/wolf_prop62_jordan_blocks.tex`; that gap is now closed.

#### Wolf Proposition 6.3 (Cesàro means) — FORMALIZED

The three clauses of the proposition are represented by:

* `IsPositiveMap.exists_strictMono_tendsto_pow_peripheralProjection` — an
  increasing sequence $(n_i)$ for which $T^{n_i}\to T_\phi$;
* `Module.End.peripheralWeightedProjection_eq_comp` —
  $T_\varphi=T\,T_\phi$;
* `IsPositiveMap.tendsto_birkhoffAverage_meanErgodicProjection_of_tracePreserving`
  — the Cesàro means converge to $T_\infty$ for the positive trace-preserving
  maps of the proposition;
* `Module.End.mem_range_peripheralProjection_iff` — the recurrent-vector
  characterization after Equation (6.15): $X$ lies in the range of $T_\phi$
  exactly when, for every $\varepsilon>0$, some positive power satisfies
  $\lVert T^n(X)-X\rVert\leq\varepsilon$. The explicit requirement $n>0$
  records Wolf's positive-integer convention; allowing $n=0$ would make the
  condition vacuous.

For the positive and trace-preserving conclusions concerning $T_\infty$:

* `IsPositiveMap.meanErgodicProjection_isPositiveMap` — positivity;
* `IsTracePreservingMap.meanErgodicProjection_isTracePreservingMap` — trace
  preservation;
* `IsCPMap.meanErgodicProjection_isCPMap` — complete positivity;
* `IsChannel.meanErgodicProjection` — the resulting channel.

These results are in `QICLean.Channel.FixedPoint.MeanErgodicProjection`.  For
the peripheral projection $T_\phi$ and the phase-weighted map $T_\varphi$:

* `IsPositiveMap.peripheralProjection_isPositiveMap` and
  `IsPositiveMap.peripheralProjection_isTracePreservingMap` — positivity and
  trace preservation of $T_\phi$;
* `IsPositiveMap.peripheralWeightedProjection_isPositiveMap` and
  `IsPositiveMap.peripheralWeightedProjection_isTracePreservingMap` — the same
  conclusions for $T_\varphi$;
* `IsPositiveMap.peripheralProjection_isCPMap` — complete positivity of
  $T_\phi$ under the completely positive hypothesis;
* `IsChannel.peripheralProjection` and
  `IsChannel.peripheralWeightedProjection` — both maps are channels in the
  completely positive case.

These results are in `QICLean.Channel.Peripheral.CesaroRecurrence`.  Thus the
basic hypothesis is positivity together with trace preservation, exactly as in
Wolf's statement; complete positivity gives the corresponding stronger
conclusions.  The boundedness needed to form $T_\infty$ follows from
`IsPositiveMap.hasBoundedOrbits_of_tracePreserving`.

### Section 6.2 Irreducible maps and Perron–Frobenius theory

#### Wolf Theorem 6.2 (Irreducible positive maps) — PARTIAL-SCOPE

**Item 1** (definition via invariant projections):
* `IsIrreducibleMap` — `QICLean.Channel.Irreducible.Basic`

**Item 2** (growth condition `(id + T)^{d-1}(A) > 0`):
* `growth_posDef_of_irreducible` — `QICLean.Channel.Irreducible.Growth`:
  the (1)→(2) direction for arbitrary positive maps, with no CP hypothesis.
* `posDef_of_ker_subset_irreducible` — structural lemma:
  `ker(A) ⊆ ker(T(A))` + positive irreducible `T` → `A` is PosDef.
* `mulVecLin_ker_idPlusE_lt_of_not_posDef_of_positive` — strict kernel
  decrease. The declarations with the former CP signatures remain as direct
  specializations.

**Item 3** (exponential condition `exp[tT](A) > 0`):
* `exp_posDef_of_irreducible_cp` and `irreducible_iff_exp_posDef_forall`
  formalize the completely positive specialization. The source theorem is for
  positive maps, and there is no single declaration packaging all four source
  clauses.

**Item 4** (orthogonal trace condition):
* `orthogonal_trace_pos_of_irreducible_cp` — `QICLean.Channel.Irreducible.Growth`
  For orthogonal PSD `A, B` (tr(BA)=0), ∃ t ∈ {1,...,D-1}, tr(B·T^t(A)) > 0.

#### Wolf Theorem 6.3 (Spectral radius of irreducible maps) — FORMALIZED FOR POSITIVE MAPS

The headline declarations are in
`QICLean.Channel.Irreducible.SpectralRadius`:

* `exists_wolfTheorem63_of_irreducible_positive` — corrected boundary form for
  a positive irreducible map on a nonzero matrix algebra, with `r ≥ 0`;
* `exists_wolfTheorem63_of_irreducible_positive_of_ne_zero` — Wolf's printed
  `r > 0` form under the necessary explicit hypothesis `T ≠ 0`.

They package the four source conclusions in order:

1. `lowerCollatzWielandtSet` and `upperCollatzWielandtSet` are the two sets in
   Equations (6.29)–(6.30), and `lowerCollatzWielandtValue` and
   `upperCollatzWielandtValue` take their extended-real supremum and infimum.
   The zero boundary is explicit: the values are respectively `⊤` and `⊥`;
   an empty upper set has value `⊤`.
   `lowerCollatzWielandtValue_le_upperCollatzWielandtValue` proves the corrected
   pointwise order for every nonzero positive semidefinite matrix, and
   `lower_and_upperCollatzWielandtValue_eq_of_eigenvector` proves equality at
   positive eigenvectors, exactly as used at source lines 649–651.
   `LowerCollatzWielandtFeasible` and `UpperCollatzWielandtFeasible` encode the
   corresponding trace-one pairs, with the scalar ranging over all real
   numbers as in the source.
   `exists_lowerCollatzWielandt_maximizer` constructs the lower maximizer
   first. `idPlus_pow_apply_map_sub_smul` is Equation (6.31), and
   `exists_posDef_eigenvector_of_irreducible_positive` uses it with Wolf
   Theorem 6.2 to obtain a positive-definite eigenvector. After that,
   `exists_posDef_common_collatzWielandt_value_of_irreducible_positive`
   identifies the global lower maximum with the global upper minimum, while
   `exists_posDef_collatzWielandt_extrema_of_irreducible_positive` and
   `lowerCollatzWielandtGlobal_eq_upperCollatzWielandtGlobal` state the same
   conclusion for the corrected pointwise functionals.
2. `eigenspace_eq_span_of_irreducible_positive` and
   `finrank_eigenspace_eq_one_of_irreducible_positive` formalize Equation
   (6.32): the ordinary complex eigenspace at `r` is one-dimensional. This is
   geometric non-degeneracy, not a claim about algebraic multiplicity.
3. `IsIrreducibleMap.traceAdjointMap` proves the positive-map observation at
   source lines 604–606. `exists_posDef_traceAdjointMap_eigenvector_at_perron`
   and `positive_eigenvalue_eq_perron_of_irreducible_positive` then formalize
   the trace-pairing argument in Equation (6.33), with no Kraus or CP premise.
4. `spectralRadius_eq_of_posDef_eigenvector_of_positive` conjugates by the
   square root of the positive-definite Perron vector, rescales to a positive
   unital map, and invokes Wolf Proposition 6.1. Thus the Perron value is the
   spectral radius. The former CP spectral-radius declaration is retained as a
   direct specialization.

There are two source corrections. On `M₁(ℂ)` the zero map is positive and
irreducible but has spectral radius zero, so the general theorem must allow
`r = 0`; the source form needs `T ≠ 0`. At source lines 617–619 the second
global extremum is printed as a supremum with a reversed inequality. The
correct upper quantity is an infimum. No false pointwise lower/upper equality
is used, and the separate pointwise development is not a prerequisite. Both
corrections and the former CP scope restriction are recorded in the resolved note
`docs/paper-gaps/wolf_thm6_3_positive_map_cp_scope.tex`.

#### Wolf Corollary 6.3 (Time-average / ergodicity) — PARTIAL-SCOPE

* `IsChannel.exists_unique_density_fixedPoint_of_irreducible` —
  `QICLean.Channel.Irreducible.Ergodicity`
  Qualitative form: an irreducible channel has a unique density-matrix fixed
  point, and it is positive definite. This is the quantum-channel
  specialization of the source result.
* `IsChannel.cesaroMean_tendsto_of_irreducible` — `QICLean.Channel.Irreducible.Ergodicity`
  Full Cesàro convergence: for every density matrix `ρ`,
  `(1/N) ∑_{t=0}^{N-1} E^[t](ρ) → σ`.

Supporting formalization in `QICLean.Channel.Irreducible.Ergodicity`:
* `IsChannel.iter_mem_densityMatrices`: iterates of a channel preserve density matrices.
* `IsChannel.cesaroMean_subseq_limit_fixedPoint`: any subsequential Cesàro limit is
  a density-matrix fixed point (compactness + telescoping argument).

#### Wolf Theorem 6.4 (Irreducibility from spectral properties) — PARTIAL-SCOPE

In `QICLean.Channel.Irreducible.FromSpectral`:
* `HasSpectralProperties` — Kraus-witness bundle of the spectral assumptions
  in Wolf's theorem (PD right/left eigenvectors, PSD uniqueness, spectral radius).
* `hasSpectralProperties_of_irreducible_cp` — the forward implication
  `irreducible → spectral properties`.
* `isIrreducibleMap_of_hasSpectralProperties` — the reverse implication via
  TP gauge reduction + channel fixed-point contradiction.
* `isIrreducibleMap_iff_spectral_properties` — the final iff statement for
  the restricted finite-Kraus/complete-positive bundle. The source theorem is
  stated for positive maps, so the containing environment remains a
  partial-scope formalization.

#### Wolf Theorem 6.5 (Spectral radius and positive eigenvectors) — PARTIAL-SCOPE

* `exists_posSemidef_eigenvector` — `QICLean.Channel.PerronFrobenius.Existence`
* `exists_posSemidef_eigenvector_general` — gives SOME nonnegative eigenvalue with
  PSD eigenvector, but does NOT identify it with the spectral radius.
* `exists_wolfTheorem63_of_irreducible_positive` — completes the
  spectral-radius eigenvector statement for the irreducible positive-map case.
  Thus the remaining Theorem 6.5 gap is only the reduction from an arbitrary
  positive map to a suitable irreducible invariant face.
* Paper-gap: `docs/paper-gaps/wolf_ch6_spectral_radius_eigenvalue.tex`

Uses Brouwer's fixed-point theorem on density matrices (proved in
`QICLean.Channel.FixedPoint.BrouwerDensityMatrices`).

#### Wolf Proposition 6.6 (Similarity preserving irreducibility) — FORMALIZED

* Scalar case: `isIrreducibleMap_smul` — `QICLean.Channel.Irreducible.Scaling`
* Similarity case: `isIrreducibleMap_similarity` — `QICLean.Channel.Irreducible.Similarity`
* Full Wolf form `T' = c C⁻¹ T(C · C†) C⁻†`:
  `isIrreducibleMap_full_similarity` (and the stronger
  `isIrreducibleMap_similarity_smul`) — `QICLean.Channel.Irreducible.Similarity`
* Former re-export theorem `Kraus.wolf_prop_6_6` restated
  `isIrreducibleMap_full_similarity` under Wolf numbering; the wrapper
  had zero call sites and is not restored here.

#### Wolf Theorem 6.6 (Peripheral spectrum of irreducible Schwarz maps) — PARTIAL-SCOPE

**Item 1** (cyclic peripheral spectrum): FINITE-KRAUS SPECIALIZATION FORMALIZED
* `Kraus.peripheralEigenvalues_eq_range_primitiveRoot` —
  `QICLean.Channel.Peripheral.CyclicGroupKraus`: the peripheral spectrum is the
  full cyclic group generated by a primitive root.
* The source bound on the order, `m ≤ D²`, is not included.

**Items 2–4** (non-degeneracy, unitary eigenvector, cyclic projections):
finite-Kraus companion specializations are formalized in
`QICLean.Channel.Peripheral.GroupStructure` and
`QICLean.Channel.Peripheral.CyclicDecomposition`.

The abstract positive unital Schwarz-map theorem remains open; the existing
results are finite-Kraus, hence completely positive, specializations, and the
order bound is not packaged. See
`docs/paper-gaps/wolf_thm6_6_kraus_scope.tex`.

#### Wolf Proposition 6.7 (Covariance and eigensystem) — OPEN

The multiplicative-domain and peripheral-unitary API supplies ingredients used
inside the finite-Kraus development, but there is no public source declaration
for either the covariance identity or the two eigenvector-shift formulas under
Wolf's abstract positive unital Schwarz hypotheses.

---

### Section 6.3 Primitive maps

#### Wolf Theorem 6.7 (Primitive maps, 4 equivalent conditions) — PARTIAL-SCOPE

**Item 4** (trivial peripheral spectrum, PD eigenvector):
* `IsPrimitive` — `QICLean.Channel.Peripheral.Spectrum`
* `isPrimitive_of_compl_eigenvalues_lt_one` / `compl_eigenvalue_norm_lt_one_of_primitive`

Other items: PARTIALLY via the transfer-operator gap formalization on the
tensor-network side; see `TNLean.Wielandt.WolfChapter6TNIndex`.

#### Wolf Theorem 6.8 (CP primitive maps, Kraus span characterizations)

**FORMALIZED** in `QICLean.Channel.WolfTheorem68`:

* `Kraus.wolf_theorem_6_8_tfae` packages all four source clauses: Wolf
  primitivity (represented by irreducibility together with the project's
  spectral `IsPrimitive` predicate), full vector reachability for every
  `m ≥ n`, full homogeneous Kraus-word span for every `m ≥ q`, and positive
  definiteness of the Choi matrix of every power `m ≥ q`.
* `Kraus.wolf_theorem_6_8_minimal_indices` chooses a single threshold `q`
  minimal for both the word-span and Choi clauses, chooses the minimal vector
  threshold `n`, and proves `n ≤ q`.
* `Kraus.hasEventuallyFullVectorSpread_iff_exists_hasFullVectorSpreadFrom`,
  `Kraus.hasEventuallyFullWordSpan_iff_exists_hasFullWordSpanFrom`, and
  `Kraus.eventually_choiMatrix_mapLM_pow_posDef_iff_exists_hasPosDefChoiFrom`
  identify the reusable eventual predicates with Wolf's explicitly quantified
  threshold clauses.

The Kraus-map presentation supplies complete positivity; trace preservation is
an explicit hypothesis. No stronger CP-independent primitivity predicate is
introduced.

#### Wolf Theorem 6.9 (Quantum Wielandt inequality) and the low-dimensional corollary — PARTIAL-PACKAGING IN THIS TRACKER

The general inequality is formalized and packaged in the tensor-network layer,
not by a QICLean declaration, and is indexed in
`TNLean.Wielandt.WolfChapter6TNIndex`. In this repository the source
environment therefore has only partial packaging. QICLean contains the dimension-two
nilpotent-space classification and the resulting one-step nonzero-eigenvalue
conclusion in
`Kraus.exists_nonzero_eigenvector_mem_wordSpan_one_fin_two`.  In dimension three,
`QICLean.exists_common_ker_of_forall_sq_eq_zero` and
`Kraus.exists_mem_wordSpan_one_sq_ne_zero_fin_three` cover and exclude the
square-zero branch.  The nilpotency-index-three classification, its exceptional
primitive-channel obstruction, and the assembled QICLean index bound remain open;
see `docs/paper-gaps/wolf_ch6_lowdim_wielandt_classification.tex`.

---

### Section 6.4 Fixed points

#### Wolf Section 6 stationary-support state (Propositions 6.9--6.11, Lemma 6.5)

In `QICLean.Channel.FixedPoint.MaximalSupportBasic`:

* `IsPositiveMap.exists_maximalSupport_fixedPoint` — Wolf Proposition 6.9:
  the support of the fixed point $T_\infty(\mathbf 1)$ contains the support
  and range of every fixed point.

In `QICLean.Channel.FixedPoint.StationarySupportRestriction`:

* `IsPositiveMap.trace_one_sub_stationaryProj_mul_map_stationaryProj_eq_zero`
  and `IsPositiveMap.map_density_le_stationaryProj` — the displayed trace and
  order conclusions of Wolf Proposition 6.10.
* `IsPositiveMap.map_density_le_projection_iff_le_traceAdjointMap` — Wolf
  Proposition 6.11: density operators below a Hermitian projection $Q$ are
  preserved below $Q$ exactly when $T^*(Q)\succeq Q$.

In `QICLean.Channel.FixedPoint.SupportCompressedDensityBlocks`:

* `Matrix.traceAdjointMap_stationarySupportCompression_fixed` — Wolf
  Equation (6.53): an adjoint fixed point compresses to an adjoint fixed point
  of the stationary-support restriction.

In `QICLean.Channel.FixedPoint.StationarySupport`:

* `Channel.support_proj_fixed` — support projection of a PSD fixed point is
  invariant under the compressed channel action.
* `Channel.stationarySupport` — support projection of the unique density-matrix
  fixed point of an irreducible channel.
* `Channel.stationarySupport_eq_one` — irreducible channels have full
  stationary support. This is a channel-specific consequence, not an alternate
  formulation of Wolf Propositions 6.9--6.11.

#### Wolf Theorem 6.12 (Fixed points form a *-algebra) — PARTIAL-SCOPE

In `QICLean.Channel.FixedPoint.AbstractAlgebra`:

* `SchwarzMap.fixedPointsStarSubalgebra` — for a positive unital Schwarz map
  whose trace adjoint has an explicitly chosen positive definite fixed point,
  the fixed points form a `StarSubalgebra`.

This is the algebra step after the faithful invariant weight has been chosen.
The source theorem begins with an arbitrary full-rank fixed point and invokes
its proposition on positive fixed points to obtain that weight.  The
full-rank-to-positive-definite reduction theorem remains open.  The explicit
trace-adjoint block realization from Equation (1.39) also remains open at this
level of generality.  The downstream Schrödinger-picture density-block
classification and its complementary zero summand are completed in
`QICLean.Channel.FixedPoint.WolfTheorem614`.

In `QICLean.Channel.FixedPoint.Algebra`:

* `Kraus.fixedPointsStarSubalgebra` — Kraus specialization in the
  Schrödinger picture:
  if `map K` is unital and `adjointMap K` has a positive definite fixed point,
  the fixed points of `map K` form a `StarSubalgebra`.
* `Kraus.adjointFixedPointsStarSubalgebra` — Kraus specialization in the
  Heisenberg picture:
  if `adjointMap K` is unital (`IsTP K`) and `map K` has a positive definite
  fixed point, the fixed points of `adjointMap K` form a `StarSubalgebra`.
* `Kraus.fixedPoints_in_multiplicativeDomain` — the key intermediate step:
  every fixed point of the adjoint map lies in the multiplicative domain.
* `Kraus.fixedPoints_starSubalgebra` / `Kraus.mem_fixedPoints_starSubalgebra`
  — numbered theorem with Wolf naming convention.

#### Wolf Theorem 6.13 (Fixed points and Kraus commutant) — FORMALIZED

In `QICLean.Channel.FixedPoint.Algebra`:

* `Kraus.fixedPoint_commutes_kraus` — if `X` and `Xᴴ * X` are both fixed by
  the Heisenberg-picture map `adjointMap K`, then `X` commutes with every
  Kraus operator `K i`.
* `Kraus.krausCommutantStarSubalgebra` — the commutant of {K_i, K_i†} forms
  a `StarSubalgebra`.
* `Kraus.krausCommutantStarSubalgebra_isGreatest_adjointFixedPointStarSubalgebras`
  — the Kraus commutant is the **largest** `*`-subalgebra contained in the
  fixed-point set of the adjoint map.
* `Kraus.adjointFixedPointsStarSubalgebra_eq_krausCommutantStarSubalgebra`
  — under the hypotheses of Theorem 6.12, the full adjoint fixed-point
  `*`-subalgebra coincides with the Kraus commutant.

#### Wolf Theorem 6.10 (Brouwer's fixed point theorem) — FORMALIZED

* `brouwer_fixedPoint_compactConvex` — `QICLean.Topology.CompactConvexFixedPoint`;
  the original statement for every nonempty compact convex
  `S ⊆ Fin n → ℝ` and continuous self-map of `S`.
* `fixedPoint_of_compact_convex` — coordinate-free form for finite-dimensional
  real inner-product spaces.
* `CompactConvex.metricProjection_lipschitzWith` — the reusable metric-projection
  step: projection onto a nonempty compact convex set is 1-Lipschitz.
* `brouwer_fixedPoint_densityMatrices` — `QICLean.Channel.FixedPoint.BrouwerDensityMatrices`
  (density-matrix specialization; kernel-checked).
* `Brouwer (vendored Gametheory library)` — exact import citation: Brouwer for the
  standard simplex (LionSR/Brouwer library).
* `exists_fixedPoint_closedCube` — `QICLean.Topology.BrouwerProduct`;
  extends Brouwer to closed cubes.
* `fixedPoint_of_compact_retract` — `QICLean.Topology.CompactRetractFixedPoint`;
  extends Brouwer to compact retracts of finite-dimensional real normed spaces.
* The former general compact-convex paper gap is resolved by metric projection;
  see `docs/paper-gaps/wolf_brouwer_general_compact_convex.tex`.

#### Wolf Theorem 6.11 (Stationary states) — FORMALIZED

The theorem is formalized for continuous (not necessarily linear) maps, exactly
matching Wolf's statement ("continuous, trace-preserving, positive (not
necessarily linear)").  The linear specializations are also provided.

In `QICLean.Channel.FixedPoint.StationaryStates`:

* `IsStationaryMap.IsPositive` — positivity predicate for arbitrary (nonlinear) maps.
* `IsStationaryMap.IsTracePreserving` — trace-preservation predicate for arbitrary maps.
* `IsStationaryMap` — conjunction of continuity, positivity, trace preservation.
* `IsStationaryMap.exists_stationaryState` — Wolf Theorem 6.11: existence of a
  density-matrix fixed point for a stationary map.  The proof uses
  `brouwer_fixedPoint_densityMatrices`.
* `IsStationaryMap.exists_stationaryState_of_linear` — specialization to linear
  positive trace-preserving maps.
* `IsStationaryMap.exists_stationaryState_of_channel` — specialization to
  quantum channels (linear CPTP maps).  This recovers the existence result
  already proved by Cesàro means in `Cesaro.lean`, but now via Brouwer.

Additionally:

* Via Cesàro: `IsChannel.exists_posSemidef_fixedPoint` —
  `QICLean.Channel.FixedPoint.Cesaro`.
* Via Brouwer (linear): `exists_posSemidef_eigenvector` —
  `QICLean.Channel.PerronFrobenius.Existence`.

#### Wolf Proposition 6.8 (Positive fixed-points) — FORMALIZED

* `IsPositiveMap.posPart_negPart_fixed_of_fixedPoint` — the source-faithful positive
  trace-preserving statement for the four canonical positive parts in
  `QICLean.Channel.FixedPoint.Cesaro`.
* `IsPositiveMap.exists_posSemidef_fixedPoints_decomposition` — the existential form.
* `IsPositiveMap.posPart_negPart_fixed_of_hermitian_fixedPoint` and
  `IsPositiveMap.posSemidef_parts_of_hermitian_fixedPoint` — Hermitian intermediate
  forms.
* `IsChannel.posSemidef_parts_of_hermitian_fixedPoint` — the channel specialization.
* Former re-export theorem `IsPositiveMap.wolf_prop_6_8` restated
  `IsPositiveMap.exists_posSemidef_fixedPoints_decomposition` under Wolf
  numbering; the wrapper had zero call sites and is not restored here.

#### Wolf Corollary 6.5 (Linearly independent stationary states) — FORMALIZED

In `QICLean.Channel.FixedPoint.StationarySpan`:

* `IsStationaryDensity` — predicate for a stationary density matrix (PSD,
  trace 1, fixed by the map).
* `IsPositiveMap.fixedPointsSubmodule` — the fixed-point subspace as a
  `Submodule ℂ M_D(ℂ)`.
* `IsPositiveMap.span_posSemidefFixedPointsSet_eq_fixedPointsSubmodule` —
  the fixed-point subspace is spanned (over ℂ) by its positive semidefinite
  elements.
* `IsPositiveMap.fixedPointsSubmodule_spanned_by_stationaryDensities` —
  the fixed-point subspace is spanned (over ℂ) by stationary density matrices
  (PSD, trace 1, fixed by `E`).
* `IsPositiveMap.exists_stationaryDensity_basis_of_fixedPointsSubmodule` —
  Wolf Corollary 6.5: when the fixed-point subspace has dimension `r`, there
  exist `r` linearly independent stationary density matrices spanning it.

#### Wolf Corollary 6.6 (projected support corner) — FORMALIZED

In `QICLean.Channel.FixedPoint.AbstractCornerFixedPoints`:

* `IsPositiveMap.stationaryCornerAdjointFixedPointsStarSubalgebra` — for a
  positive trace-preserving map `T` whose trace adjoint is Schwarz, and a PSD
  fixed point `ρ` with support projection `Q := stationaryProj`, the
  corner-restricted fixed-point set `{Y ∈ Q M_D(ℂ) Q | Q T*(Y) Q = Y}` is a
  `StarSubalgebra` of the corner algebra `Q M_D(ℂ) Q`.
* `IsPositiveMap.mem_stationaryCornerAdjointFixedPointsStarSubalgebra` —
  membership is exactly the displayed corner fixed-point condition of Wolf
  Equation (6.61).

These are the source hypotheses: positivity and trace preservation of `T`,
and the Schwarz inequality for `T*`; no Kraus representation or complete
positivity is assumed. Wolf chooses a maximum-rank fixed point, while the Lean
theorem proves the same conclusion for every PSD fixed point. The proof uses
the source support-compression route and the abstract Wolf Theorem 6.12 fixed
point algebra. The earlier declarations in
`QICLean.Channel.FixedPoint.CornerFixedPoints` remain available as finite-Kraus
specializations.

#### Wolf Theorem 6.14 (density-block form of fixed points) — FORMALIZED

The general finite-dimensional convergence argument is provided by
`LinearMap.HasBoundedOrbits.tendsto_birkhoffAverage_meanErgodicProjection` in
`QICLean.Analysis.MeanErgodic`. It constructs the Cesàro projection onto the
fixed-point space for an endomorphism with bounded orbits. The matrix
specialization is provided by
`IsPositiveMap.hasBoundedOrbits_of_tracePreserving`,
`IsPositiveMap.meanErgodicProjection_isPositiveMap`, and
`IsTracePreservingMap.meanErgodicProjection_isTracePreservingMap`: a positive
trace-preserving matrix endomorphism has bounded orbits, and its mean-ergodic
projection is a positive trace-preserving retraction onto its fixed-point
space. If the original endomorphism is unital, the projection is unital as
well.

The trace-pairing adjoint step is now complete.  The adjoint of the
mean-ergodic projection is a positive unital idempotent retraction onto the
fixed-point space of the adjoint endomorphism.  Combining this retraction with
the full-support star-algebra description, restricting to maximal stationary
support, and adjoining the complementary zero summand gives the full statement
of Theorem 6.14 and Equation (6.63).

In `QICLean.Channel.FixedPoint.StationarySupportRestriction`:

* `IsPositiveMap.map_posSemidef_supported_on_fixedPoint_support` — the order
  argument of Wolf Proposition 6.10 for a positive matrix supported on the
  support of an arbitrary stationary positive matrix.
* `IsPositiveMap.map_supported_on_fixedPoint_support` — the extension to every
  supported matrix by decomposition into four positive matrices.
* `IsPositiveMap.trace_one_sub_stationaryProj_mul_map_stationaryProj_eq_zero`
  and `IsPositiveMap.map_density_le_stationaryProj` — Wolf Proposition 6.10
  in its displayed trace and density-order forms.
* `IsPositiveMap.map_density_le_projection_iff_le_traceAdjointMap` — Wolf
  Proposition 6.11, identifying stationary projections with the
  sub-harmonic inequality $Q\preceq T^*(Q)$.
* `IsPositiveMap.stationarySupportCompression_isPositiveMap` and
  `IsPositiveMap.stationarySupportCompression_isTracePreservingMap` — the
  supported compression is positive and trace-preserving.
* `IsPositiveMap.exists_posDef_fixedPoint_stationarySupportCompression` — the
  compressed stationary matrix is positive definite.
* `IsPositiveMap.fixedPoint_iff_exists_fixedPoint_stationarySupportCompression`
  — the scope-restricted auxiliary form of Wolf Equation (6.51), conditional
  on a fixed-point space already known to be supported in the chosen corner.
* `IsPositiveMap.exists_maximalSupportCompression` — the source-faithful
  restriction theorem: it chooses $T_\infty(\mathbf 1)$ through
  `IsPositiveMap.exists_maximalSupport_fixedPoint` and packages positivity,
  trace preservation, a positive-definite compressed fixed point,
  Equation (6.52), and the complementary zero summand of Equation (6.51).

In `QICLean.Channel.FixedPoint.FullSupportBlockRetraction`:

* `IsPositiveMap.exists_block_densities_of_adjoint_meanErgodicProjection` —
  when the positive trace-preserving map has a positive definite fixed point
  and its trace adjoint satisfies the Schwarz inequality, the adjoint
  mean-ergodic projection is a positive retraction onto the adjoint
  fixed-point star-algebra and has the weighted partial-trace block form of
  Wolf Equation (1.40).

In `QICLean.Channel.FixedPoint.TraceAdjointDensityBlocks`:

* `IsPositiveMap.exists_block_densities_of_meanErgodicProjection` — under the
  same full-support hypotheses, the mean-ergodic projection has the
  Schrödinger-picture density-block form
  `U (⊕_k σ_k ⊗ tr_{m_k}((U† B U)_{kk})) U†`, and the fixed-point space is
  `U (⊕_k σ_k ⊗ M_{d_k}(ℂ)) U†`.

In `QICLean.Channel.FixedPoint.SupportCompressedDensityBlocks`:

* `Matrix.traceAdjointMap_stationarySupportCompression_fixed` — Wolf
  Equation (6.53), transporting trace-adjoint fixed points through the
  stationary-support compression.
* `IsPositiveMap.exists_block_densities_of_maximalSupportCompression` — the
  maximal-support compression has positive-definite density blocks, and its
  fixed points correspond exactly to the ambient fixed points carried by the
  support isometry.

In `QICLean.Algebra.MatrixGramUnitary`:

* `Matrix.exists_unitary_zero_extension_eq` — an isometric inclusion extends
  to an ambient unitary that identifies every compressed matrix with one
  complementary zero block followed by that matrix.

In `QICLean.Channel.FixedPoint.WolfTheorem614`:

* `IsPositiveMap.exists_fixedPoints_densityBlocks_with_zero` — for every
  positive trace-preserving matrix endomorphism whose trace adjoint satisfies
  the Schwarz inequality, the fixed-point space is the unitary conjugate of
  one complementary zero summand followed by positive-definite trace-one
  density blocks, exactly as in Wolf Equation (6.63).

In `QICLean.Channel.FixedPoint.DirectSumBlockRetraction`:

* `Matrix.IsPositiveDirectSumMap.exists_block_densities_of_fixedPoints` — the
  full-support consequence for a finite direct sum of full matrix algebras.

In `QICLean.Channel.FixedPoint.WedderburnDecomp`:

* `Kraus.starSubalgebra_isSemisimpleRing` — every finite-dimensional
  `*`-subalgebra of `M_D(ℂ)` is semisimple.
* `Kraus.FixedPointAlgebra` — type alias for the carrier of the
  adjoint-fixed-point `StarSubalgebra`.
* `Kraus.fixedPointAlgebra_isSemisimpleRing` — the adjoint-fixed-point
  algebra is semisimple.
* `Kraus.fixedPointAlgebra_wedderburnArtin` — abstract Wedderburn--Artin:
  `Fix(T*) ≃ₐ[ℂ] Π i, M_{d_i}(ℂ)`.
* `Kraus.IsWedderburnBlockDecomp` — bundled decomposition data consisting of
  block sizes, multiplicities, an ambient-dimension bound, and an algebra
  isomorphism to a product of full matrix algebras.
* `Kraus.adjointFixedPoints_wedderburnDecomp` — existence of this
  decomposition data for the adjoint-fixed-point algebra.

In `QICLean.Channel.FixedPoint.BlockForm` (unital case, positive definite fixed
point of the pre-dual, no zero block):

* `Kraus.adjointFixedPoints_blockDiagonal_iff` — the unitary realization
  `Fix(T*) = U (⊕_k 1_{m_k} ⊗ M_{d_k}) U†` with `∑_k d_k m_k = D`.
* `Kraus.fixedPoints_blockDiagonal_iff` — the companion for the fixed points
  of a unital Kraus map.

In `QICLean.Channel.FixedPoint.CornerBlockForm` (corner-restricted case, any
positive semidefinite fixed point):

* `Kraus.cornerFixedPoints_blockDiagonal_iff` — the corner-restricted
  fixed-point set is carried by an isometry `W` (`W† W = 1`, `W W† = Q`) onto
  `⊕_k 1_{m_k} ⊗ M_{d_k}` with `∑_k d_k m_k = r` for the support-sector
  dimension `r ≤ D`; embedded in `M_D(ℂ)` this is the block representation
  in the `∑_k d_k m_k ≤ D` form. The equivalence characterizes the
  corner-restricted set only; extending by zero on the complement does not
  produce ambient fixed points in general.

The full Wolf statement is therefore complete.  Its application to the
transported sector maps of arXiv:1606.00608 is a separate tensor-attached
problem: one must still prove the channel hypotheses for those maps on the
whole direct-sum algebras.  This remaining boundary is recorded in
`https://sirui-lu.com/TNLean/paper-gaps/cpsv16_vertical_sector_invertibility.pdf`.

#### Wolf Corollary 6.7 (weighted fixed-point star-algebra) — FORMALIZED

In `QICLean.Channel.FixedPoint.AbstractMaximalRank`:

* `IsPositiveMap.maximalSupport_of_maximalRank` — for a positive
  trace-preserving map and every positive semidefinite fixed point `ρ` whose
  rank bounds the rank of every stationary density matrix, the support
  projection `Q` satisfies `Q X Q = X` for every fixed point `X`.  Thus the
  quantifier is Wolf's arbitrary maximum-rank stationary density, not one
  chosen canonical witness.

In `QICLean.Channel.FixedPoint.AbstractWeightedFixedPoints`:

* `IsPositiveMap.weightedFixed_mul_of_posDef` — multiplication closure in the
  full-support case, proved through Wolf Theorem 6.14 density blocks:
  `(σ_k ⊗ X_k)(σ_k⁻¹ ⊗ R_k⁻¹)(σ_k ⊗ Z_k)
  = σ_k ⊗ (X_k R_k⁻¹ Z_k)`.
* `IsPositiveMap.weightedCornerFixedPointsStarSubalgebra` — for a positive
  trace-preserving `T` whose trace adjoint is Schwarz and any positive
  semidefinite stationary `ρ`, the corner elements `Y` for which
  `T (√ρ Y √ρ) = √ρ Y √ρ` form a `StarSubalgebra` of `Q M_D(ℂ) Q`.
  Compression to `supp(ρ)` supplies the positive-definite density-block
  calculation; zero support gives the zero corner algebra.
* `IsPositiveMap.mem_weightedCornerFixedPointsStarSubalgebra_iff_inverseSandwich`
  — at every maximum-rank stationary density, membership is equivalent to
  the exact displayed condition
  `Y = ρ⁻¹ᐟ² X ρ⁻¹ᐟ²` for some `X` with `T X = X`, where the inverse square
  root is totalized to zero off `supp(ρ)`.
* `IsPositiveMap.wolfCorollary67` — the source-facing result under exactly
  Wolf's hypotheses: `T` is positive and trace preserving, `T*` is Schwarz,
  and `ρ` is an arbitrary maximum-rank stationary density matrix.  It returns
  the star-algebra together with the exact carrier equality above.

The earlier declarations in `QICLean.Channel.FixedPoint.Corollaries`,
`WeightedCornerFixedPoints`, `MaximalSupport`, and `MaximalRank` remain
finite-Kraus compatibility specializations.  In particular,
`Kraus.maximalSupport_of_maximalRank` and
`Kraus.exists_weightedCorner_sqrt_eq_of_maximalRank` now delegate to the
source-general declarations rather than maintaining a second proof route.
The former scope restriction is resolved in
`docs/paper-gaps/wolf_cor67_maximal_support_restriction.tex`.

#### Conditional expectation used in Wolf Theorem 6.14 — FORMALIZED

In `QICLean.Channel.FixedPoint.ConditionalExpectation`:

* `Kraus.IsConditionalExpectation` — a positive, idempotent, unital matrix
  map whose range is contained in a star-subalgebra and which fixes that
  subalgebra pointwise, following Wolf Proposition 1.5 and Equation (1.40).
* `Kraus.scalarConditionalExpectation` — the linear map
  `E_σ(X) = (tr(σ X) / tr(σ)) • 1` for the scalar fixed-point algebra case.
* `Kraus.scalarConditionalExpectation_idempotent` — `E_σ² = E_σ`.
* `Kraus.scalarConditionalExpectation_unital` — `E_σ(1) = 1`.
* `Kraus.scalarConditionalExpectation_absorbs_adjointMap` —
  `E_σ(T*(X)) = E_σ(X)` when `T(σ) = σ`.
* `Kraus.adjointMap_absorbs_scalarConditionalExpectation` —
  `T*(E_σ(X)) = E_σ(X)` when `T` is TP.
* `Kraus.scalarConditionalExpectation_isConditionalExpectation` —
  bundles everything into `IsConditionalExpectation` for the scalar case.
* `Kraus.meanErgodicAdjoint_isConditionalExpectation` — the trace adjoint of
  the mean-ergodic projection is a conditional expectation onto the adjoint
  fixed-point star-subalgebra.

The general conditional expectation is the trace adjoint of the mean-ergodic
projection, which is positive, idempotent, unital, and fixes exactly the fixed
points of `T*`; the star-algebra structure follows from Theorem 6.12. This is
the conditional-expectation step in the proof of Theorem 6.14. The theorem's
explicit density-block formula is developed in
`QICLean.Channel.FixedPoint.FullSupportBlockRetraction`.

#### Wolf Theorem 6.15 (Unique fixed point from full Kraus-word span) — FORMALIZED

Formalized in the tensor-network layer; indexed in
`TNLean.Wielandt.WolfChapter6TNIndex`.

---

### Section 6.5 Cycles and recurrences

#### Wolf Proposition 6.12 (Asymptotic image) — FORMALIZED

For a positive trace-preserving `T` on `M_D(ℂ)`, write `X_T` for the span of
the peripheral eigenvectors and `T_φ` for the peripheral spectral projection.
All three clauses live in `QICLean.Channel.Peripheral.AsymptoticImage`:

* `IsPositiveMap.range_peripheralProjection_eq_iSup_eigenspace` —
  clause 1, `T_φ (M_D(ℂ)) = X_T`.
* `IsPositiveMap.exists_posSemidef_span_eq_iSup_eigenspace` —
  clause 2, `X_T` is the span of a set of positive semidefinite matrices; the
  spanning form `IsPositiveMap.span_stationaryDensity_peripheralProjection_eq_peripheralSubspace`
  identifies that set with the stationary densities of `T_φ`.
* `IsPositiveMap.map_peripheralSubspace` — clause 3, `T (X_T) = X_T`.
* `IsPositiveMap.asymptotic_image` — the three clauses together.

The auxiliary `IsPositiveMap.fixedPointsSubmodule_peripheralProjection`
records that `X_T` is the fixed-point space of `T_φ`, and
`Module.End.map_eigenspace_of_ne_zero` supplies the one-eigenvalue case of
clause 3.

#### Wolf Theorem 6.16 (Structure of cycles) — FORMALIZED

The source-contract audit is resolved in
`docs/paper-gaps/wolf_theorem6_16_schwarz_orientation.tex`.  The printed
proof uses the Schwarz inequality for `T` itself when it excludes the
transpose branch, but obtains Equation (6.66) by applying Theorem 6.14 to the
recurrent projection `I`; that theorem requires the trace adjoint `I*` to be
Schwarz.  Closure under powers and limits transports the two orientations
separately.  Therefore the source-facing assembly explicitly assumes that
both `T` and `T*` are Schwarz.  No implication between these hypotheses is
silently introduced, and the note does not claim that the theorem's conclusion
is false under the single printed hypothesis.

* The recurrent projection and positive inverse step at source lines
  1629--1640 is formalized by:
  - `IsPositiveMap.exists_strictMono_tendsto_pow_peripheralProjection_and_predecessor`,
    which takes the existing Dirichlet subsequence `T^(n_i) → T_φ` and extracts
    a further subsequence for which `T^(n_i - 1)` converges, using bounded
    orbits, Banach--Steinhaus, and finite-dimensional compactness;
  - `IsPositiveMap.exists_peripheralRestrictedInverse`, which packages the
    limit `S` as positive and trace preserving with
    `S.comp T = T.peripheralProjection`,
    `T.comp S = T.peripheralProjection`, both absorption identities, and
    `range S = range T.peripheralProjection`; this is an inverse only on
    `X_T`, not a global inverse;
  - `IsPositiveMap.peripheralProjection_isSchwarzMap` and
    `IsPositiveMap.traceAdjointMap_peripheralProjection_isSchwarzMap`, which
    transport the two Schwarz orientations independently and do not infer
    Schwarz for `T*` from Schwarz for `T`;
  - `Module.End.peripheralRestrictedInverse_apply_map_of_mem_range` and
    `Module.End.map_peripheralRestrictedInverse_apply_of_mem_range`, which
    state the two inverse identities on `range T.peripheralProjection = X_T`.

* The literal continuity ingredients from source lines 1648--1654 are
  formalized without assuming a target block or a block classification:
  - `Matrix.continuous_pureStateProj` proves continuity of the map
    sending psi to its rank-one self-projector.
  - `Matrix.isPathConnected_unitVectors` transports Mathlib's
    path-connected complex Euclidean unit sphere to the existing matrix-vector
    `IsUnitVector` API.
  - `Matrix.isConnected_pureStateProj_image` proves that the rank-one
    pure-state projections in a nonzero full matrix block form a connected
    set.
  - `WolfProps.linearMap_eq_of_eq_on_rankOne` now has arbitrary
    complex-module codomain, so agreement on rank-one projectors determines
    any linear map out of a full matrix block by the existing polarization
    identity.

* The following auxiliary normalization and tensor-factor facts are
  prerequisites for the scalar/multiplicity comparison and block-Schwarz
  transport at source lines 1660--1663:
  - `IsPositiveMap.map_one_eq_one_of_tracePreserving_of_isSchwarzMap`, which
    proves that a positive trace-preserving Schwarz endomorphism of a nonzero
    full matrix algebra is unital, using the Hermitian trace-square equality
    case rather than complete positivity;
  - `Matrix.PosSemidef.right_of_one_kronecker`, which reflects positivity from
    \(\Id_m\otimes B\) to \(B\) for \(m>0\) by partial trace and positive
    scalar rescaling;
  - `Matrix.kronecker_eq_one_of_left_trace_eq_one`, which uses both partial
    traces to show that \(\tr(\sigma)=1\) and
    \(\sigma\otimes X=\Id_{md}\) force
    \(\sigma=m^{-1}\Id_m\) and \(X=m\Id_d\).
  These facts are assembled below to compare the matched block
  multiplicities and transport the ambient Schwarz defect to the individual
  weighted full-matrix block maps. No modified-product proof or
  complete-positivity hypothesis is introduced.

* The final classification step at source lines 1660--1663 is formalized
  under exactly Wolf's positive, trace-preserving, positive-inverse, and
  Schwarz hypotheses:
  - `ChannelDeterminant.Internal.transposeLinearMapComplex_not_isSchwarzMap`
    uses the matrix unit \(E_{01}\), whose transpose Schwarz defect is
    \(E_{11}-E_{00}\), to rule out ordinary transposition for \(d\geq 2\).
  - `ChannelDeterminant.Internal.isSchwarzMap_of_unitaryChannel_comp` proves
    that an outer unitary conjugation cannot repair a Schwarz defect.
  - `ChannelDeterminant.Internal.unitaryChannel_comp_transpose_not_isSchwarzMap`
    excludes Wolf's unitary-conjugation-after-transposition standard form.
  - `ChannelDeterminant.Internal.unitaryChannel_comp_transpose_fin_one`
    records that the transpose branch collapses to unitary conjugation for
    \(d=1\).
  - `ChannelDeterminant.Internal.wolfPositiveInvertibleSchwarzMaps` combines
    those facts with the completed positive-invertible-map corollary, without
    assuming complete positivity.

* Reusable formalization for the permutation-of-blocks direction lives in
  `QICLean.Channel.Peripheral.CyclicDecomposition` and
  `QICLean.Channel.Peripheral.Cycles`:
  - `preserves_corner_pow_orderOf_of_perm_decomp` — permutation-of-blocks
    iterate preserves each corner after `orderOf σ` steps.
  - `CycleStructure T` — bundled block-permutation data: a finite family of
    orthogonal projections `P : ι → M_D(ℂ)`, a permutation `σ : Equiv.Perm ι`,
    the compatibility `T (P (σ k)) = P k`, and the multiplicative-domain
    factorisations `T (P k * X) = T (P k) * T X` and `T (X * P k) = T X * T (P k)`.
  - `CycleStructure.map_proj_pow` — `T^n (P (σ^n k)) = P k`.
  - `CycleStructure.pow_orderOf_apply_proj` — `(T ^ orderOf σ) (P k) = P k`.
  - `CycleStructure.preserves_corner_pow_orderOf` — `T ^ orderOf σ` preserves
    each corner `P k · M_D(ℂ) · P k`, the corner-preservation half of
    Theorem 6.16 in its permutation-of-blocks form.
  - `CycleStructure.ofPermDecomp` — constructor from explicit permutation data.

* Multi-cycle block-permutation data (disjoint union of cycles with possibly
  distinct periods) is formulated in `QICLean.Channel.Peripheral.MultiCycleDecomposition`:
  - `MultiCycleDecomposition T` — bundled data: a finite cycle index `ι`, a
    per-cycle period `period : ι → ℕ` (each nonzero), a projection family
    `P : (c : ι) → Fin (period c) → M_D(ℂ)`, the per-cycle cyclic action
    `T (P c (k + 1)) = P c k`, and the multiplicative-domain factorisations.
  - `MultiCycleDecomposition.preserves_corner_pow_period` — per-cycle corner
    preservation: `T ^ (period c)` preserves each corner `P c k · M_D(ℂ) · P c k`.
  - `MultiCycleDecomposition.preserves_corner_pow_of_dvd` — common-period
    corner preservation: whenever every `period c` divides `N`, `T ^ N`
    preserves every corner.
  - `MultiCycleDecomposition.toCycleStructure` — flattens a multi-cycle
    decomposition to a single `CycleStructure` on the sigma index
    `Σ c : ι, Fin (period c)`, using `Equiv.Perm.sigmaCongrRight` of
    per-cycle cyclic shifts.

* The density-state convex geometry used at source lines 1641--1652 is now
  formalized without introducing a second block coordinate system:
  - `Matrix.extremePoints_densityMatrices` identifies the convex-extreme
    density matrices in a full matrix algebra with the rank-one orthogonal
    projections, using the spectral decomposition in Wolf's Chapter 1 sense.
  - `Matrix.directSumDensityMatrices` is the positive, total-trace-one state
    space in the dependent matrix-family coordinates already used by the
    direct-sum map APIs.
  - `Matrix.extremePoints_directSumDensityMatrices` identifies its
    convex-extreme points with families supported on one block, where the
    occupied block is a rank-one orthogonal projection.

* The density-block coordinate transport assembled from the recurrent-inverse
  setup at source lines 1637--1640, and used by the subsequent
  1641--1659 argument, is formalized in
  `QICLean.Channel.Peripheral.DensityBlockCoordinates` and
  `QICLean.Channel.Peripheral.DensityBlockDynamics`:
  - `Matrix.densityBlockWithZeroEmbedding` and
    `Matrix.densityBlockWithZeroCompression` are the maps `E` and `R` for the
    exact zero-extended witnesses of
    `IsPositiveMap.exists_fixedPoints_densityBlocks_with_zero`, in the
    established formal tensor-factor order `sigma k ⊗ X k`;
  - the round-trip, positivity, trace, density-state, and fixed-range lemmas
    show that these coordinates carry exactly the direct-sum density-state
    geometry, without introducing another decomposition;
  - `Matrix.densityBlockDynamics` is `R.comp (A.comp E)`, and
    `IsPositiveMap.exists_peripheralDensityBlockDynamics` packages the maps
    `Tbar` and `Sbar`, both embedding intertwinings, their two inverse
    identities, positivity, and preservation of total block trace.

* The relative-pure-state and permutation argument at source lines 1641--1659
  is formalized by:
  - `Matrix.IsPositiveBetweenDirectSums` and
    `Matrix.mapsTo_extremePoints_directSumDensityMatrices_of_mutualInverse`,
    which express positivity between dependent matrix families and
    preservation of their relative extreme states;
  - `Matrix.exists_directSumFacePermutation_of_mutualInverse`, which uses the
    connected rank-one-projector locus to make the occupied output block
    constant, applies the same construction to the inverse, and returns
    `Matrix.DirectSumFacePermutation` with positive, trace-preserving,
    mutually inverse matched block maps and equality only of their
    full-matrix dimensions;
  - the public full-family formulas
    `Matrix.DirectSumFacePermutation.map_apply`,
    `Matrix.DirectSumFacePermutation.map_apply_blockEquiv`, and
    `Matrix.DirectSumFacePermutation.inverse_apply`; the source-indexed
    `map_apply_blockEquiv` form avoids dependent casts when the matrix size
    varies with the block;
  - `IsPositiveMap.exists_peripheralDensityBlockFacePermutation`, which
    combines the exact Theorem 6.14 witnesses and recurrent inverse with that
    direct-sum argument. Its block equivalence is source-to-target, while its
    inverse is Wolf's output-to-input permutation `pi`, so
    `(Tbar X) j` depends only on `X (pi j)` and `d (pi j) = d j`.

* The scalar/multiplicity comparison and ordinary block-Schwarz transport at
  source lines 1660--1663 are formalized in
  `QICLean.Channel.Peripheral.DensityBlockSchwarz` and
  `QICLean.Channel.Peripheral.MatchedBlockEndomorphism`:
  - `IsPositiveMap.map_one_and_peripheralProjection_one_of_tracePreserving_of_isSchwarzMap`
    proves that both `T` and its recurrent projection fix the identity;
  - `Matrix.exists_densityBlockIdentityCoordinates` eliminates the zero
    summand, proves `n = D`, and identifies every density factor as
    `sigma k = (m k : ℂ)⁻¹ • 1`;
  - `Matrix.DirectSumFacePermutation.multiplicity_eq_of_fixed_scalar_identity`
    uses the matched block action, ordinary block trace preservation, and the
    already proved equality of the `d` dimensions to obtain
    `m i = m (F.blockEquiv i)`;
  - `Matrix.DirectSumFacePermutation.blockMap_one_of_fixed_scalar_identity`
    proves unitality of each raw matched block map;
  - `Matrix.densityBlockWithZeroEmbedding_single_conjTranspose_mul` computes
    the extra inverse-multiplicity scalar introduced by multiplication in the
    weighted coordinates;
  - `Matrix.DirectSumFacePermutation.rawBlock_isSchwarzMap_of_ambientDensityBlocks`
    compresses the ambient Schwarz defect. Before using the matched
    multiplicity equality, its two coefficients are respectively
    `c_i * c_j` and `c_j * c_j`, where `c_k = (m k : ℂ)⁻¹`. Only then
    does it cancel the common positive scalar and reflect positivity through
    `1 ⊗ₖ B`;
  - `Matrix.DirectSumFacePermutation.matchedBlockEndomorphism_isSchwarzMap_of_raw`
    transports that raw inequality along the proved equality of the `d`
    dimensions;
  - `IsPositiveMap.exists_peripheralDensityBlockSchwarz` consumes the exact
    face-permutation witnesses above and returns `n = D`, maximally mixed
    weights, equality of matched multiplicities, raw block unitality, the raw
    ordinary Schwarz inequalities, and Schwarz for the canonically reindexed
    matched endomorphisms. Its hypotheses keep Schwarz for `T` separate from
    Schwarz for `T*`.

  This also records two printed defects without silently changing the source.
  Source line 1499 writes `1_(m_k) ⊗ rho_k`, although
  `rho_k ∈ M_(m_k)` and the full algebra is `M_(d_k)`; the compatible
  identity is `1_(d_k) ⊗ rho_k`, written `sigma k ⊗ₖ 1_(d_k)` in the
  formal tensor-factor order. Source lines 1614--1616 require the permutation
  to preserve the whole block dimension `d_k * m_k`, whereas the pure-face
  argument at lines 1653--1656 proves only equality of `d_k`; the new trace
  calculation supplies the missing equality of `m_k`.

* The final source-facing assembly lives in
  `QICLean.Channel.Peripheral.StructureOfCycles`:
  - `Matrix.DirectSumFacePermutation.exists_reindexedUnitaryBlockAction`
    applies the positive-invertible Schwarz classification to each matched
    endomorphism, sets Wolf's output-to-input permutation to
    `pi = F.blockEquiv.symm`, and reindexes the classified source unitary to
    an output-indexed unitary `V k`;
  - `IsPositiveMap.exists_wolfTheorem616` is the compiled Theorem 6.16
    boundary. It identifies membership in `T.peripheralSubspace` with the
    literal zero-extended `Matrix.fromBlocks 0 0 0` density-block form of
    Equations (6.66)--(6.67), retains `e₀`, and separately proves `n = D`
    and `sigma k = (m k : ℂ)⁻¹ • 1`;
  - the same declaration returns `pi`, both equalities
    `d (pi k) = d k` and `m (pi k) = m k`, output-indexed unitaries, the
    coordinate action
    `A X k = V k * reindex (X (pi k)) * V kᴴ`, and the ambient Equation
    (6.68), `T (E X) = E (A X)`;
  - Schwarz for `T` and Schwarz for `T*` remain distinct hypotheses, and the
    positive trace-preserving inverse consumed by the block classification is
    only the recurrent inverse on the peripheral image.

  Thus the exact source theorem is complete without CP/Kraus hypotheses,
  a modified product, a global inverse for `T`, or a substitute through the
  conditional `CycleStructure` and `MultiCycleDecomposition` records. Those
  records remain independent downstream interfaces rather than part of the
  source theorem.

---

### The quantum Perron–Frobenius theorem

The assembled quantum Perron–Frobenius theorem for transfer maps lives in the
tensor-network layer; it is indexed in `TNLean.Wielandt.WolfChapter6TNIndex`.

---

## Wolf Lecture Notes — Chapter 7: Continuous one-parameter semigroups

The complete named-environment audit classifies exactly six Chapter 7
source environments as partial rather than exact:

- Proposition 7.1, “From continuous semigroups to differentiable groups”: the
  real nonnegative-time exponential representation is proved, but the claimed
  real/complex parameter group extension is not packaged (partial-scope).
- Corollary 7.1, “Perturbation of generators”: the displayed estimate is proved
  for the project's fixed operator norm, not for an arbitrary submultiplicative
  norm as printed (partial-scope).
- Proposition 7.4, “Freedom in representation of generators”: the shift,
  tracelessness, uniqueness, and Kraus-freedom ingredients are formalized, but
  not assembled under one source-facing proposition (partial-packaging).
- Theorem 7.1, “Generators for semigroups of quantum channels”: the GKSL and
  Lindblad forms are proved, but the public Kossakowski package does not retain
  the exact fixed basis of the traceless subspace used in Equation (7.23)
  (partial-scope).
- Proposition 7.5, “Irreducibility implies primitivity”: source clauses 1--3 are
  packaged, while clauses 4--5 on faithful convergence and the Liouvillian
  kernel are absent (partial-packaging).
- Corollary 7.2, “Necessary conditions for relaxation”: the three hypotheses
  yield non-reducibility, but the source's faithful stationary state and global
  relaxation conclusion are not packaged (partial-packaging).

Propositions 7.2 and 7.3 are exact completions. The `\leanok` markers in the
semigroup Blueprint certify individual Lean declarations; they must not be read
as exact-coverage markers for a larger containing Wolf environment.

---

## Wolf Lecture Notes — Chapter 8: Distance measures and convergence

The audit distinguishes equation-level coverage from coverage of the named
source environment containing the equation. A proved displayed equation or
proof prerequisite does not make the containing lemma, proposition, or theorem
exact when its other clauses, hypotheses, or conclusions remain absent. The
entries below therefore state both levels explicitly.

### Lemma 8.5 (Equations 8.103--8.104) — CORRECTED FORM FORMALIZED

* `Matrix.wolf_eq_103` and `Matrix.wolf_eq_103_refined` prove Equation (8.103)
  for an arbitrary submultiplicative seminorm in the mathematically meaningful
  range `D - 1 ≤ n`; the printed natural exponent is undefined below that
  range.
* `Matrix.jordanBlock_pow` gives the truncated binomial expansion of a Jordan
  block power.
* `Matrix.l2_opNorm_jordanBlock_pow_bounds` gives the two-sided operator-norm
  estimate in Equation (8.104). The false auxiliary assertion `‖N‖ = 1` at
  `D = 1` is replaced by the valid `‖N‖ ≤ 1` bound.

Together these declarations complete the containing lemma with the documented
natural-exponent and one-dimensional corrections.

### Theorem “Asymptotic convergence I” (Equations 8.106–8.109) — PREREQUISITES FORMALIZED

The full channel theorem is not yet formalized. The following compiled,
source-shaped prerequisites are available:

* `Module.End.subperipheralModulus` in
  `QICLean.Analysis.SubperipheralSpectrum` is Wolf's largest subperipheral
  modulus `μ`, totalized to zero for an empty subperipheral spectrum; the same
  module proves attainment and strict inequality `μ < 1` in the nonempty case.
* `Matrix.l2_opNorm_pow_similarity_bounds` in
  `QICLean.Analysis.JordanSimilarity` proves Equation (8.108) for one chosen
  similarity, retaining its actual condition factor rather than replacing it
  by the infimum `κ_T` without an attainment or limiting argument.
* `Matrix.l2_opNorm_jordanBlock_pow_polynomial_bounds` in
  `QICLean.Analysis.JordanBlockAsymptotics` derives the two-sided
  `μ^n n^(d_μ-1)` scaling for one supplied positive-modulus block in the
  source range `d_μ - 1 ≤ n`.

The remaining obligations for the norm of
`T̂^n - T̂_ϕ^n` are a Jordan-form existence/decomposition API, largest-block
data, the direct-sum eventual-maximum argument, the `μ = 0`/positive-exponent
qualification, and a justified passage to Wolf's `κ_T` infimum. These are
recorded in
`docs/paper-gaps/wolf_thm823_jordan_scaling_qualifications.tex`; issue #297
therefore remains open.

### Proposition 8.5, “Jordan condition number and detailed balance” (Equation 8.110) — PARTIAL-PACKAGING

In `QICLean.Channel.DetailedBalance`:

* `transferMatrix_detailedBalance` translates `Σ T* = T Σ` to
  `Σ̂ T̂† = T̂ Σ̂`.
* `Matrix.PosDef.inv_sqrt_mul_mul_sqrt_isHermitian_of_detailedBalance`
  proves that `Σ̂⁻¹/² T̂ Σ̂¹/²` is Hermitian.
* `Matrix.PosDef.exists_sqrt_mul_unitary_diagonalization_of_detailedBalance`
  constructs Wolf's particular diagonalizing similarity `Σ̂¹/² U`, its
  inverse, and its condition factor
  `sqrt (‖Σ̂‖∞ ‖Σ̂⁻¹‖∞)`.
* `transferMatrix_sigmaSandwich_eq_kronecker_and_posDef` and
  `fixedPoint_of_detailedBalance_sigmaSandwich` verify the square-root
  sandwich specialization and Wolf's fixed-point observation.

The final printed inequality `κ_T ≤ sqrt (κ(Σ̂))` is not yet marked
formalized. It depends on issue #297's source-shaped Jordan condition number
and a theorem bounding that infimum by the condition factor of each
admissible Jordan basis. The current declarations retain Wolf's chosen basis
instead of silently replacing its factor by `κ_T`; issue #298 remains open.

### Theorem 8.24, “Asymptotic convergence II” (Equation 8.111) — CORRECTED FORM FORMALIZED

In `QICLean.Channel.Peripheral.SchurAsymptoticConvergence`:

* `Module.End.pow_sub_peripheralWeightedProjection_pow` and
  `transferMatrix_pow_sub_peripheralWeightedProjection_pow` prove, for
  `n > 0`, the identity
  `T^n - T_ϕ^n = (T - T_ϕ)^n` and its transfer-matrix form. Here
  `T_φ` is the peripheral projection and `T_ϕ = T T_φ` is the
  phase-weighted map; the two are not identified.
* `IsPositiveMap.hasEigenvalue_sub_peripheralWeightedProjection_iff` proves
  that the eigenvalues of `T - T_ϕ` are exactly zero together with the
  subperipheral eigenvalues of `T`.
* `IsPositiveMap.exists_wolf_eq_111_schur_data_with_bound` constructs the
  unitary Schur representation on the `d²`-dimensional transfer space, proves
  `‖Λ‖∞ = μ`, and establishes Wolf's bound
  `‖N‖∞ ≤ μ + 2√d`.
* `IsPositiveMap.hilbertSchmidtOperatorNorm_le_sqrt_dim` supplies the analytic
  input `‖T‖₂→₂ ≤ √d` for every positive trace-preserving map; complete
  positivity is not assumed.
* `IsPositiveMap.exists_wolf_eq_111` proves the coarse estimate when
  `d² - 1 ≤ n`.
  `IsPositiveMap.exists_wolf_eq_111_refined` proves the binomial-coefficient
  refinement when `2(d² - 1) ≤ n`. Both include `μ = 0` without division
  and include the `d = 1`, `n = 0` boundary by a direct proof.

Wolf prints the coarse formula for every natural `n`, although its exponent
`n - d² + 1` is negative below `d² - 1` and no convention is given when
`μ = 0`. The natural-power formalization records precisely the range where
the displayed exponent is defined. At `d = 1`, `n = 0`, the auxiliary
positive-power identity fails, but the final inequality is the immediate
statement `0 ≤ 1`; the headline theorems therefore include this case. This
source qualification is recorded in
`docs/paper-gaps/wolf_ch8_eq_8_103_negative_exponent.tex`. With this explicit
qualification, the containing Theorem 8.24 has a corrected-source disposition.

### Proposition 8.6, “Convergence towards asymptotic states” — PARTIAL-PACKAGING

`Matrix.traceNormAsymptoticDistance`,
`Matrix.traceNormAsymptoticDistance_pow_le_hilbertSchmidtOperatorNorm`, and
`Matrix.traceNormAsymptoticDistance_pow_le_transferMatrix_l2_opNorm` prove the
upper bound in Equation (8.112) and its transfer-matrix estimates for positive
powers. The converse supremum lower bound in Equation (8.113), including the
four-positive-parts argument of Equation (8.117), remains absent. Thus the
proved upper bound does not complete the containing proposition.
