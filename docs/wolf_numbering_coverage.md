# Wolf-chapter numbering coverage

Concordance between formalized declarations and the theorem/proposition
numbering of M. Wolf, *Quantum Channels & Operations: Guided Tour* (2012),
Chapters 2, 6, and the currently compiled Chapter 8 prerequisites. This table
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

## Wolf Lecture Notes — Chapter 2: Representations

This file indexes the formalization of Chapter 2 of Wolf's
*Quantum Channels & Operations: Guided Tour*, which covers the main
representations of quantum channels.

The Lorentz-normal-form statements are recorded in
`QICLean.Channel.LorentzNormalForm`.  The compactness/minimisation result is
proved there, and the `SL(2, ℂ)` action on Pauli--Minkowski coordinates is
formalized in `QICLean.Channel.LorentzNormalForm.SpinorAction`.  The remaining
proof obligations for Proposition 2.11 are the Lorentz-orbit classification
and the final scalar normalization.  This index imports the assembling module
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

* **Proposition “SIC POVMs” and Equations (2.33)--(2.34)**:
  - `SICPOVM` — the unscaled rank-one projectors, with
    `∑ᵢ Pᵢ = d𝟙` and off-diagonal overlap `1/(d+1)` ✓
  - `SICPOVM.toPOVM` — the effects `Pᵢ/d` form a POVM ✓
  - `SICPOVM.linearIndependent_projector` — the `d²` projectors form an
    operator basis ✓
  - `SICPOVM.diagonal_representation` — Wolf Equation (2.33) ✓
  - `SICPOVM.krausMap_eq` / `SICPOVM.isChannel_krausMap` — the Kraus
    operators `Pᵢ/√d` define the channel in Wolf Equation (2.34) ✓

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
* `Wolf.spinorMatrix_neg` — `X` and `-X` induce the same congruence action ✓.
  Surjectivity onto `SO⁺(1,3)` and the assertion that every fibre has exactly
  these two elements remain pending
* `Wolf.pauliTransferMatrix_two_sided_filtering` — Equation (2.43) over the
  complex Pauli transfer matrix, in the exact order `L₂ T̂ L₁` ✓
* `Wolf.coe_pauliTransferMatrixReal_of_preservesHermiticity` /
  `Wolf.pauliTransferMatrixReal_slFiltering` — identification with the real
  transfer matrix for Hermiticity-preserving maps and the bundled
  `SLFiltering` specialization of Equation (2.43) ✓
* **Equation (2.44)** (rotation and boost exponential formulas) remains
  pending and is not inferred from the three-dimensional `SU(2)` spin cover
* `IsLorentzDiagonal` — diagonal Lorentz normal form (Wolf Proposition 2.11 case 1) ✓
* `IsLorentzNonDiagonal` — non-diagonal Lorentz normal form (case 2) ✓
* `IsLorentzSingular` — singular Lorentz normal form (case 3) ✓
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
  pending. The required general invertible Kraus-rank-one CP filters and their
  scalar freedom, the determinant-one spinor action, and its exact action on
  Pauli transfer matrices are now formalized. The Lorentz-orbit classification
  and the final trace-preserving normalization have no Lean declaration yet.
  The former determinant-one `SLFiltering` formulation was false and was
  removed.

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
| Filtered Pauli transfer action | `LorentzNormalForm/SpinorAction.lean` |
  `Wolf.pauliTransferMatrixReal_slFiltering` |
| Diagonal Lorentz form | `LorentzNormalForm.lean` | `IsLorentzDiagonal` |
| Non-diagonal Lorentz form | `LorentzNormalForm.lean` | `IsLorentzNonDiagonal` |
| Singular Lorentz form | `LorentzNormalForm.lean` | `IsLorentzSingular` |

#### Not yet formalized

| Result | Notes |
|--------|-------|
| Section 2.4 Lorentz normal form (Proposition 2.11) | Correctly formulated
  statement and proof remain pending. The general invertible Kraus-rank-one
  filters, their scalar/SL decomposition, and the determinant-one Lorentz
  action on Pauli transfer matrices are available. The proof still needs the
  Lorentz-orbit classification and the final trace-preserving normalization. |
| Section 2.4 full spinor double cover and Equation (2.44) | Image inclusion,
  multiplicativity, and the equality `L(-X) = L(X)` are available. Surjectivity,
  exact two-point fibres, and the rotation/boost exponential formulas remain
  pending. |
| Section 2.4 Sorted singular values | Current SVD is unsorted; later uses want sorted values |

### References

* [M. Wolf, *Quantum Channels & Operations: Guided Tour*, Chapter 2][Wolf2012QChannels]

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

#### Wolf Theorem 6.2 (Irreducible positive maps) — ITEMS 1–2 FORMALIZED; ITEM 4 CP SPECIALIZATION

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

**Item 3** (exponential condition `exp[tT](A) > 0`): NOT FORMALIZED.

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

1. `LowerCollatzWielandtFeasible` and `UpperCollatzWielandtFeasible` encode
   Equations (6.29)–(6.30) on density matrices, with the scalar ranging over
   all real numbers as in the source.
   `exists_lowerCollatzWielandt_maximizer` constructs the lower maximizer
   first. `idPlus_pow_apply_map_sub_smul` is Equation (6.31), and
   `exists_posDef_eigenvector_of_irreducible_positive` uses it with Wolf
   Theorem 6.2 to obtain a positive-definite eigenvector. After that,
   `exists_posDef_common_collatzWielandt_value_of_irreducible_positive`
   identifies the global lower maximum with the global upper minimum.
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

#### Wolf Corollary 6.3 (Time-average / ergodicity) — FORMALIZED

* `IsChannel.exists_unique_density_fixedPoint_of_irreducible` —
  `QICLean.Channel.Irreducible.Ergodicity`
  Qualitative form: an irreducible channel has a unique density-matrix fixed
  point, and it is positive definite.
* `IsChannel.cesaroMean_tendsto_of_irreducible` — `QICLean.Channel.Irreducible.Ergodicity`
  Full Cesàro convergence: for every density matrix `ρ`,
  `(1/N) ∑_{t=0}^{N-1} E^[t](ρ) → σ`.

Supporting formalization in `QICLean.Channel.Irreducible.Ergodicity`:
* `IsChannel.iter_mem_densityMatrices`: iterates of a channel preserve density matrices.
* `IsChannel.cesaroMean_subseq_limit_fixedPoint`: any subsequential Cesàro limit is
  a density-matrix fixed point (compactness + telescoping argument).

#### Wolf Theorem 6.4 (Irreducibility from spectral properties) — FORMALIZED

In `QICLean.Channel.Irreducible.FromSpectral`:
* `HasSpectralProperties` — Kraus-witness bundle of the spectral assumptions
  in Wolf's theorem (PD right/left eigenvectors, PSD uniqueness, spectral radius).
* `hasSpectralProperties_of_irreducible_cp` — the forward implication
  `irreducible → spectral properties`.
* `isIrreducibleMap_of_hasSpectralProperties` — the reverse implication via
  TP gauge reduction + channel fixed-point contradiction.
* `isIrreducibleMap_iff_spectral_properties` — the final iff statement.

#### Wolf Theorem 6.5 (Spectral radius and positive eigenvectors) — PARTIALLY FORMALIZED

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

#### Wolf Theorem 6.6 (Peripheral spectrum of irreducible Schwarz maps)

**Item 1** (cyclic peripheral spectrum): FINITE-KRAUS SPECIALIZATION FORMALIZED
* `Kraus.peripheralEigenvalues_eq_range_primitiveRoot` —
  `QICLean.Channel.Peripheral.CyclicGroupKraus`: the peripheral spectrum is the
  full cyclic group generated by a primitive root.
* The source bound on the order, `m ≤ D²`, is not included.

**Items 2–4** (non-degeneracy, unitary eigenvector, cyclic projections):
finite-Kraus companion specializations are formalized in
`QICLean.Channel.Peripheral.GroupStructure` and
`QICLean.Channel.Peripheral.CyclicDecomposition`.

The abstract positive unital Schwarz-map theorem remains open; see
`docs/paper-gaps/wolf_thm6_6_kraus_scope.tex`.

---

### Section 6.3 Primitive maps

#### Wolf Theorem 6.7 (Primitive maps, 4 equivalent conditions)

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

#### Wolf Theorem 6.9 (Quantum Wielandt inequality)

Formalized in the tensor-network layer; indexed in
`TNLean.Wielandt.WolfChapter6TNIndex`.

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

#### Wolf Theorem 6.12 (Fixed points form a *-algebra) — PARTIALLY FORMALIZED

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
  the printed statement for every nonempty compact convex
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

#### Wolf Theorem 6.16 (Structure of cycles) — PARTIALLY FORMALIZED

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

* The remaining **existence direction** — that every trace-preserving positive
  Schwarz map admits a `MultiCycleDecomposition` on its asymptotic image, with
  the cycles coming from the now-formalized density-block decomposition of the
  fixed-point space — is left to future work.

---

### The quantum Perron–Frobenius theorem

The assembled quantum Perron–Frobenius theorem for transfer maps lives in the
tensor-network layer; it is indexed in `TNLean.Wielandt.WolfChapter6TNIndex`.

---

## Wolf Lecture Notes — Chapter 8: Distance measures and convergence

### Equation 8.104 (Jordan-block power estimate) — FORMALIZED

In `QICLean.Analysis.JordanBlockPower`:

* `Matrix.jordanBlock_pow` gives the truncated binomial expansion of a Jordan
  block power.
* `Matrix.l2_opNorm_jordanBlock_pow_bounds` gives the two-sided operator-norm
  estimate in Equation (8.104), with its lower and upper halves also
  exposed separately.

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
