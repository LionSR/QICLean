# Library layers: inventory

Generated with the module map `scripts/library_layers_module_map.txt` from the per-module
classification behind `docs/library_layers.md`. Module names omit the prefix `QICLean.`;
the first column is the name after the reorganization.

## Modules placed by their imports, not by their statements

154 modules state objects of one layer but import a module of a higher one (placed
higher), or are imported by a module of a lower one (placed lower). Each is a candidate for
a split that moves the declarations the importer needs.

| Module | Statements | Placed in | Import that places it |
|---|---|---|---|
| `Analysis.FunctionalCalculus.SpectralKronecker` | Algebra | Analysis | `imports Analysis.Resolvent.Defect` |
| `Analysis.Real.EulerAngles` | Algebra | Analysis | `imports Analysis.Order.ComplexPhasePositivity` |
| `Analysis.Support.HermitianIntertwiner` | Algebra | Analysis | `imports Analysis.Projection.PosSemidefSupport` |
| `Analysis.Support.MatrixFamilySupport` | Algebra | Analysis | `imports Analysis.Support.MatrixFamilySupportProjection` |
| `Analysis.Support.MatrixFamilySupportProjection` | Algebra | Analysis | `imports Analysis.Projection.PosSemidefSupport` |
| `Analysis.TraceNorm.SourceContraction` | Algebra | Analysis | `imports Analysis.TraceNorm.RectangularTraceNormAlgebra` |
| `Channel.Positive.EnsembleEquivalence` | Algebra | Channel | `imports Channel.WolfProps` |
| `Channel.Positive.PositiveFunctional` | Algebra | Channel | `imports Channel.Schwarz.TwoPositive` |
| `ManyBody.Entropy.Cut.SupportedOperatorAlgebra` | Algebra | ManyBody/Entropy | `imports Entropy.Surprisal.FilterMoment` |
| `Probability.PoissonWord.PoissonWordAppend` | Algebra | Probability | `imports Probability.PoissonWord.Basic` |
| `Probability.PoissonWord.PoissonWordCounts` | Algebra | Probability | `imports Probability.PoissonWord.Basic` |
| `Probability.PoissonWord.PoissonWordMarked` | Algebra | Probability | `imports Probability.PoissonWord.PoissonWordAppend` |
| `Probability.PoissonWord.PoissonWordTelescope` | Algebra | Probability | `imports Probability.PoissonWord.PoissonWordAppend` |
| `Spectral.Eigenvalue.HermitianNilpotent` | Algebra | Spectral | `imports Spectral.Eigenvalue.HermitianExtremalEigenvalues` |
| `Spectral.Eigenvalue.KrausStateEffectCoupling` | Algebra | Spectral | `imports Spectral.Eigenvalue.MatrixSpectralDecomp` |
| `Spectral.Eigenvalue.ShiftedZeroTraceNilpotent` | Algebra | Spectral | `imports Spectral.Eigenvalue.ShiftedTracePowerSpectrum` |
| `Channel.Choi.OperatorNormFrobenius` | Analysis | Channel | `imports Channel.Choi.RectangularChoi` |
| `Channel.Convexity.LiebConcavity` | Analysis | Channel | `imports Spectral.Eigenvalue.HermitianExtremalEigenvalues` |
| `Channel.Convexity.LiebConvexity` | Analysis | Channel | `imports Channel.Convexity.LiebSubBoundary` |
| `Channel.Convexity.LiebSubBoundary` | Analysis | Channel | `imports Channel.Convexity.LiebConcavity` |
| `Channel.Convexity.TensorPowerConvexity` | Analysis | Channel | `imports Channel.Convexity.LiebConvexity` |
| `Channel.OperatorMean.BlockDiagonal` | Analysis | Channel | `imports Channel.OperatorMean.TreeDerivative` |
| `Channel.OperatorMean.Commutant` | Analysis | Channel | `imports Channel.OperatorMean.Defs` |
| `Channel.OperatorMean.Defs` | Analysis | Channel | `imports Channel.OperatorMean.BlockDiagonal` |
| `Channel.OperatorMean.Derivative` | Analysis | Channel | `imports Channel.OperatorMean.NormDerivative` |
| `Channel.OperatorMean.EnergyBlock` | Analysis | Channel | `imports Channel.OperatorMean.ErrorFourier` |
| `Channel.OperatorMean.ErrorFourier` | Analysis | Channel | `imports Channel.OperatorMean.Defs` |
| `Channel.OperatorMean.FilteringIntertwine` | Analysis | Channel | `imports Channel.OperatorMean.Defs` |
| `Channel.OperatorMean.GeometricMeanDerivativeIntertwine` | Analysis | Channel | `imports Channel.OperatorMean.PowerDerivativeIntertwine` |
| `Channel.OperatorMean.Intertwine` | Analysis | Channel | `imports Channel.OperatorMean.LeafStateIntertwine` |
| `Channel.OperatorMean.LeafDerivative` | Analysis | Channel | `imports Channel.OperatorMean.Derivative` |
| `Channel.OperatorMean.LeafStateIntertwine` | Analysis | Channel | `imports Channel.OperatorMean.MeanTreeDerivativeIntertwine` |
| `Channel.OperatorMean.LeafStates` | Analysis | Channel | `imports Channel.OperatorMean.TreeDerivative` |
| `Channel.OperatorMean.MeanDerivative` | Analysis | Channel | `imports Channel.OperatorMean.PowerDerivative` |
| `Channel.OperatorMean.MeanTreeDerivativeIntertwine` | Analysis | Channel | `imports Channel.OperatorMean.GeometricMeanDerivativeIntertwine` |
| `Channel.OperatorMean.MetricFloor` | Analysis | Channel | `imports Channel.OperatorMean.NormDerivative` |
| `Channel.OperatorMean.NormDerivative` | Analysis | Channel | `imports Channel.OperatorMean.PathDerivative` |
| `Channel.OperatorMean.PathDerivative` | Analysis | Channel | `imports Channel.OperatorMean.Defs` |
| `Channel.OperatorMean.PowerDerivative` | Analysis | Channel | `imports Channel.Positive.NPositiveIntegral` |
| `Channel.OperatorMean.PowerDerivativeIntertwine` | Analysis | Channel | `imports Channel.OperatorMean.MeanDerivative` |
| `Channel.OperatorMean.TreeDerivative` | Analysis | Channel | `imports Channel.OperatorMean.MeanDerivative` |
| `Channel.Positive.QuantumChernoff` | Analysis | Channel | `imports Channel.Schwarz.PetzOverlapDataProcessing` |
| `Channel.Schmidt.FilterConjugation` | Analysis | Channel | `imports Channel.Schmidt.SchmidtTilt` |
| `Channel.TraceNormNet` | Analysis | Channel | `imports Channel.Choi.OperatorNormFrobenius` |
| `Entropy.Conditional.DoubleCurve` | Analysis | Entropy | `imports Entropy.Conditional.BoundaryEnergy` |
| `Entropy.Conditional.MarginalPhaseLimit` | Analysis | Entropy | `imports Entropy.Conditional.MarginalPhaseApprox` |
| `Entropy.Conditional.ModularDistance` | Analysis | Entropy | `imports Entropy.VonNeumann.ConditionalContinuity` |
| `Entropy.Conditional.Optimizer` | Analysis | Entropy | `imports Entropy.Conditional.FilterEntropy` |
| `Entropy.Conditional.PhaseTransfer` | Analysis | Entropy | `imports Entropy.Conditional.Optimizer` |
| `Entropy.Relative.LiebTraceExponential` | Analysis | Entropy | `imports Entropy.Relative.KleinInequality` |
| `Probability.PoissonWord.PoissonWordOmissionBound` | Analysis | Probability | `imports Probability.PoissonWord.PoissonWordTelescope` |
| `Probability.Sampling.IntervalSamplingSchedule` | Analysis | Probability | `imports Probability.Sampling.ViableSubspaceBootstrap` |
| `Probability.Sampling.NestedSamplingNaturalParameters` | Analysis | Probability | `imports Probability.Sampling.ViableSubspaceBootstrap` |
| `Probability.Sampling.ViableSubspaceBootstrap` | Analysis | Probability | `imports Probability.Sampling.ViableSubspaceRandomSampling` |
| `Probability.Sampling.ViableSubspaceDyadicBootstrap` | Analysis | Probability | `imports Probability.Sampling.ViableSubspaceMinimum` |
| `Probability.Sampling.ViableSubspaceMinimum` | Analysis | Probability | `imports Probability.Sampling.ViableSubspaceBootstrap` |
| `Probability.Sampling.ViableSubspaceNestedCountSampling` | Analysis | Probability | `imports Probability.Sampling.NestedSamplingNaturalParameters` |
| `Probability.Sampling.ViableSubspaceNestedSampling` | Analysis | Probability | `imports Probability.Sampling.ViableSubspaceBootstrap` |
| `Probability.Sampling.ViableSubspaceSampleOrFull` | Analysis | Probability | `imports Probability.Sampling.ViableSubspaceBootstrap` |
| `Representation.Replica.ReplicaRatio` | Analysis | Representation | `imports Representation.Partition.ReplicaWeight` |
| `Spectral.Filter.ShiftedPowerDerivative` | Analysis | Spectral | `imports Spectral.Projection.ShiftedDensityTruncation` |
| `Spectral.Filter.SoftTruncationAccuracy` | Analysis | Spectral | `imports Spectral.Filter.SoftTruncationCoercivity` |
| `Spectral.Gap.SeparatedQuadraticForms` | Analysis | Spectral | `imports Spectral.Perturbation.GapPerturbation` |
| `Spectral.Gap.SupportedParentProjection` | Analysis | Spectral | `imports Spectral.Gap.IsometricCompressionGap` |
| `Spectral.Gap.WeightedPositiveKernel` | Analysis | Spectral | `imports Spectral.Gap.PositiveGapTransfer` |
| `Analysis.Convexity.DiagonalJensen` | Channel | Analysis | `imported by Analysis.Convexity.OperatorConvexity` |
| `Analysis.Norm.RootChannel` | Channel | Analysis | `imported by Spectral.Gap.ContractionWordDecay` |
| `Analysis.Norm.TraceNormContractivity` | Channel | Analysis | `imported by Spectral.Filter.ChebyshevSpectralFilter` |
| `Analysis.TraceNorm.RectangularTraceNormContraction` | Channel | Analysis | `imported by Analysis.TraceNorm.SubnormalizedPureStateError` |
| `Entropy.Markov.AmbientMarkovBipartiteBlockForm` | Channel | Entropy | `imports Entropy.Markov.MarkovBipartiteBlockForm` |
| `Entropy.Markov.InvariantConditionalBlockForm` | Channel | Entropy | `imports Entropy.Markov.InvariantConditionalFamily` |
| `Entropy.Markov.InvariantConditionalFamily` | Channel | Entropy | `imports Entropy.StrongSubadditivity.SSAEqualityPetzRecovery` |
| `Entropy.Markov.MarkovBipartiteBlockForm` | Channel | Entropy | `imports Entropy.Markov.InvariantConditionalBlockForm` |
| `Entropy.Markov.MarkovDilation.AmbientBlockAction` | Channel | Entropy | `imports Entropy.Markov.MarkovDilation.Basic` |
| `Entropy.Markov.MarkovDilation.Basic` | Channel | Entropy | `imports Entropy.Markov.AmbientMarkovBipartiteBlockForm` |
| `Entropy.Markov.MarkovDilation.SectorAction` | Channel | Entropy | `imports Entropy.Markov.MarkovDilation.Basic` |
| `Entropy.Markov.MarkovDilationBlockForm` | Channel | Entropy | `imports Entropy.Markov.MarkovDilation.AmbientBlockAction` |
| `Entropy.Markov.MarkovTripartiteBlockForm` | Channel | Entropy | `imports Entropy.Recovery.HayashiMarkovStructure` |
| `Entropy.Recovery.HayashiMarkovStructure` | Channel | Entropy | `imports Entropy.VonNeumann.Entropy` |
| `Entropy.Recovery.PetzEqualityPrerequisites` | Channel | Entropy | `imports Entropy.Recovery.PetzRecoverySupport` |
| `Entropy.Recovery.PetzRecoverySupport` | Channel | Entropy | `imports Entropy.Relative.RelativeEntropyDataProcessing` |
| `Entropy.Recovery.WeylSupportPetzRecovery` | Channel | Entropy | `imports Entropy.Recovery.PetzRecoverySupport` |
| `Entropy.Relative.PauliDissipation` | Channel | Entropy | `imports Entropy.VonNeumann.Entropy` |
| `Entropy.Relative.RelativeEntropyAncillaAdditivity` | Channel | Entropy | `imports Entropy.VonNeumann.Entropy` |
| `Entropy.Relative.RelativeEntropyConvexity` | Channel | Entropy | `imports Entropy.Relative.KleinInequality` |
| `Entropy.Relative.RelativeEntropyDataProcessing` | Channel | Entropy | `imports Entropy.Relative.EntropyReindex` |
| `Entropy.Relative.RelativeEntropyUnitaryInvariance` | Channel | Entropy | `imports Entropy.Relative.KleinInequality` |
| `Entropy.Relative.SupportLeftRightRelativeModular` | Channel | Entropy | `imports Entropy.Relative.SupportRelativeModular` |
| `Entropy.Relative.SupportRelativeEntropyEquality` | Channel | Entropy | `imports Entropy.Relative.SupportLeftRightRelativeModular` |
| `Entropy.Relative.SupportRelativeEntropyGap` | Channel | Entropy | `imports Entropy.Relative.SupportSourceDefect` |
| `Entropy.Relative.SupportRelativeModular` | Channel | Entropy | `imports Entropy.Relative.SupportLeftRightQuadratic` |
| `Entropy.Relative.SupportSourceDefect` | Channel | Entropy | `imports Entropy.Relative.SupportLeftRightQuadratic` |
| `Entropy.Relative.WeylRelativeEntropyIntegral` | Channel | Entropy | `imports Entropy.Relative.ResolventIntegral` |
| `Entropy.Relative.WeylSupportRelativeEntropyEquality` | Channel | Entropy | `imports Entropy.Recovery.PetzEqualityPrerequisites` |
| `Entropy.StrongSubadditivity.SSAEqualityDPI` | Channel | Entropy | `imports Entropy.StrongSubadditivity.StrongSubadditivityPosDef` |
| `Entropy.StrongSubadditivity.SSAEqualityPetzRecovery` | Channel | Entropy | `imports Entropy.StrongSubadditivity.SSAEqualityDPI` |
| `Entropy.StrongSubadditivity.StrongSubadditivityPosDef` | Channel | Entropy | `imports Entropy.Relative.RelativeEntropyAncillaAdditivity` |
| `Entropy.StrongSubadditivity.TripartiteDecorrelation` | Channel | Entropy | `imports Entropy.StrongSubadditivity.StrongSubadditivityPosDef` |
| `Entropy.VonNeumann.FilterEnergy` | Channel | Entropy | `imports Entropy.Surprisal.MarginalTails` |
| `Entropy.VonNeumann.PureMarginalRank` | Channel | Entropy | `imports Entropy.VonNeumann.Bipartite` |
| `Kraus.Wielandt.ChoiTraceFactorization` | Channel | Kraus | `imports Kraus.Wielandt.KrausIterateChoi` |
| `Kraus.Wielandt.KrausRectangularComposition` | Channel | Kraus | `imports Kraus.Transfer` |
| `ManyBody.Replica.Configuration.PhysicalSingletonDensity` | Channel | ManyBody/Replica | `imports ManyBody.Replica.Configuration.GoodConfigurationSingletonMoment` |
| `Channel.Schmidt.SurprisalMoment` | Entropy | Channel | `imported by Channel.Schmidt.SchmidtTilt` |
| `ManyBody.Replica.Configuration.PhysicalSingletonEntropy` | Entropy | ManyBody/Replica | `imports ManyBody.Replica.Configuration.PhysicalSingletonDensity` |
| `Channel.Irreducible.InvariantProjection` | Kraus | Channel | `imported by Channel.Irreducible.KrausGauge` |
| `Representation.Replica.SchurLabelCommutation` | ManyBody/Replica | Representation | `imported by Representation.TensorPower.CompatiblePhysicalLabel` |
| `ManyBody.Entropy.Cut.CutEnvironment` | ManyBody/Sites | ManyBody/Entropy | `imports ManyBody.Entropy.SupportedMarginalTails` |
| `ManyBody.Entropy.Cut.PositiveLocalLift` | ManyBody/Sites | ManyBody/Entropy | `imports ManyBody.Entropy.SupportedMarginalTails` |
| `ManyBody.Entropy.Cut.RegionPureApproximationTail` | ManyBody/Sites | ManyBody/Entropy | `imports ManyBody.Entropy.RegionEntropy` |
| `ManyBody.Entropy.Cut.RegionRank` | ManyBody/Sites | ManyBody/Entropy | `imports ManyBody.Entropy.RegionEntropy` |
| `ManyBody.Entropy.Cut.RegionSplit` | ManyBody/Sites | ManyBody/Entropy | `imports ManyBody.Entropy.Cut.RegionUnion` |
| `ManyBody.Entropy.Cut.RegionTensorSplitting` | ManyBody/Sites | ManyBody/Entropy | `imports ManyBody.Entropy.Cut.RegionalViability` |
| `ManyBody.Entropy.Cut.RegionTraceNorm` | ManyBody/Sites | ManyBody/Entropy | `imports ManyBody.Entropy.SupportedMarginalTails` |
| `ManyBody.Entropy.Cut.RegionUnion` | ManyBody/Sites | ManyBody/Entropy | `imports ManyBody.Entropy.Filter.Optimizer` |
| `ManyBody.Entropy.Cut.RegionalOperatorCoordinates` | ManyBody/Sites | ManyBody/Entropy | `imports ManyBody.Entropy.Cut.RegionUnion` |
| `ManyBody.Entropy.Cut.RegionalRightContraction` | ManyBody/Sites | ManyBody/Entropy | `imports ManyBody.Entropy.Cut.ThreeWayCut` |
| `ManyBody.Entropy.Cut.RegionalViability` | ManyBody/Sites | ManyBody/Entropy | `imports ManyBody.Entropy.Cut.SubregionCut` |
| `ManyBody.Entropy.Cut.RightLocalLift` | ManyBody/Sites | ManyBody/Entropy | `imports ManyBody.Entropy.SupportedMarginalTails` |
| `ManyBody.Entropy.Cut.SubregionCut` | ManyBody/Sites | ManyBody/Entropy | `imports ManyBody.Entropy.Cut.CutEnvironment` |
| `ManyBody.Entropy.Cut.SupportedOperatorSchmidtWords` | ManyBody/Sites | ManyBody/Entropy | `imports ManyBody.Entropy.Filter.ChainEnergy` |
| `ManyBody.Entropy.Cut.ThreeWayCut` | ManyBody/Sites | ManyBody/Entropy | `imports ManyBody.Entropy.SupportedMarginalTails` |
| `Analysis.Calculus.Kernel` | Probability | Analysis | `imported by Analysis.Calculus.CauchyTransform` |
| `Channel.Twirl.WeylTwirl` | Representation | Channel | `imported by Channel.Twirl.ComplementaryWeylTwirl` |
| `ManyBody.Replica.Configuration.BadCopyExponential` | Representation | ManyBody/Replica | `imports ManyBody.Replica.Configuration.GoodConfigurationDensity` |
| `ManyBody.Replica.Configuration.ComponentMergeMoment` | Representation | ManyBody/Replica | `imports ManyBody.Replica.Configuration.JointDensity` |
| `ManyBody.Replica.Configuration.FiveFactorAuxiliaryCoordinates` | Representation | ManyBody/Replica | `imports ManyBody.Replica.Configuration.GoodConfigurationDensity` |
| `ManyBody.Replica.Configuration.GoodConfigurationMergeTransport` | Representation | ManyBody/Replica | `imports ManyBody.Replica.Configuration.GoodConfigurationPairMarginal` |
| `ManyBody.Replica.Configuration.JointAuxiliaryExponential` | Representation | ManyBody/Replica | `imports ManyBody.Replica.Configuration.FiveFactorAuxiliaryCoordinates` |
| `ManyBody.Replica.LowDefect.ComponentInverseGoodExpectation` | Representation | ManyBody/Replica | `imports ManyBody.Replica.Configuration.BadCopyExponential` |
| `ManyBody.Replica.LowDefect.ComponentInverseRough` | Representation | ManyBody/Replica | `imports ManyBody.Replica.LowDefect.ComponentInverseGoodExpectation` |
| `ManyBody.Replica.LowDefect.ComponentInverseRoughUniform` | Representation | ManyBody/Replica | `imports ManyBody.Replica.LowDefect.ComponentInverseRough` |
| `ManyBody.Replica.LowDefect.ComponentInverseSharp` | Representation | ManyBody/Replica | `imports ManyBody.Replica.LowDefect.ComponentInverseGoodExpectation` |
| `ManyBody.Replica.LowDefect.ComponentInverseSharpUniform` | Representation | ManyBody/Replica | `imports ManyBody.Replica.Configuration.PhysicalSingletonEntropy` |
| `ManyBody.Replica.LowDefect.InverseRoughCompression` | Representation | ManyBody/Replica | `imports ManyBody.Replica.LowDefect.ComponentInverseRoughUniform` |
| `ManyBody.Replica.LowDefect.LowDefectCoordinateCovariance` | Representation | ManyBody/Replica | `imports ManyBody.Replica.Configuration.RegionalFiveFactorCoordinates` |
| `ManyBody.Replica.LowDefect.LowDefectRoughLowerPin` | Representation | ManyBody/Replica | `imports ManyBody.Replica.LowDefect.InverseRoughCompression` |
| `ManyBody.Replica.LowDefect.LowDefectSharpCompression` | Representation | ManyBody/Replica | `imports ManyBody.Replica.LowDefect.ComponentInverseSharpUniform` |
| `ManyBody.Replica.LowDefect.LowDefectSharpLowerPin` | Representation | ManyBody/Replica | `imports ManyBody.Replica.LowDefect.LowDefectSharpCompression` |
| `ManyBody.Replica.LowDefect.LowDefectSymmetricCoordinates` | Representation | ManyBody/Replica | `imports ManyBody.Replica.Configuration.GoodConfigurationDensity` |
| `ManyBody.Replica.Symbol.CoherentLog` | Representation | ManyBody/Replica | `imports ManyBody.Replica.BandMetric.Setup` |
| `ManyBody.Replica.Symbol.CoherentMeasure` | Representation | ManyBody/Replica | `imports ManyBody.Replica.Symbol.CoherentLog` |
| `ManyBody.Replica.Symbol.CoherentSymbolFunction` | Representation | ManyBody/Replica | `imports ManyBody.Replica.Symbol.RegionPowerSymbol` |
| `Analysis.Exponential.MatrixFilter` | Spectral | Analysis | `imported by Analysis.Exponential.HermitianProductFormula` |
| `Analysis.FunctionalCalculus.OrthogonalResolution` | Spectral | Analysis | `imported by Analysis.FunctionalCalculus.OrthogonalResolutionCfc` |
| `Analysis.FunctionalCalculus.OrthogonalResolutionCfc` | Spectral | Analysis | `imported by Analysis.FunctionalCalculus.OrthogonalResolutionCfc` |
| `Analysis.FunctionalCalculus.SpectralFunUnique` | Spectral | Analysis | `imported by Analysis.Support.Power` |
| `Analysis.FunctionalCalculus.SpectralQuadraticForm` | Spectral | Analysis | `imported by Analysis.TraceInequality.MatrixBernsteinInputs` |
| `Analysis.FunctionalCalculus.ViableSubspaceSpectralProjector` | Spectral | Analysis | `imported by Analysis.FunctionalCalculus.ViableSubspaceSpectralProjector` |
| `Analysis.Order.HermitianTracePower` | Spectral | Analysis | `imported by Analysis.TraceInequality.TracePurity` |
| `Analysis.Order.LowEnergyPerturbation` | Spectral | Analysis | `imported by Analysis.Order.WeylMonotonicity` |
| `Analysis.Order.WeylMonotonicity` | Spectral | Analysis | `imported by Analysis.Exponential.TraceExponentialPerturbation` |
| `Entropy.Relative.MarginalPhaseSupport` | Spectral | Entropy | `imports Entropy.Conditional.MarginalPhaseComparison` |
| `ManyBody.Entropy.Filter.FilterFeasibility` | Spectral | ManyBody/Entropy | `imports ManyBody.Entropy.Filter.Optimizer` |

## Modules that mix two layers

The classification found these modules to hold declarations of two layers. The note says
which declarations belong where; none of these splits needs a change of statement.

| Module | Note |
|---|---|
| `Algebra.Matrix.MatrixAux` | reindex_mulVec,piProduct_mulVec,dotProduct/vecMulVec identities -> Algebra/Matrix; faithfulDensity,trace_mul_nonneg,PSD trace positivity -> Algebra/Hermitian; l2_opNorm_*,Frobenius-norm and re_star_dotProduct_*_norm lemmas -> Analysis/Norm; filtering_min/quadratic_nonneg real lemmas -> Analysis/Real; Continuous.matrix_kronecker -> Analysis/Topology |
| `Algebra.PerronFrobenius.Substochastic` | Hadamard-square primitivity and entry comparisons -> Algebra/PerronFrobenius; linfty op-norm bounds and Tendsto-zero decay of (P⊙P)^k -> Analysis (Spectral/Radius power decay) |
| `Analysis.Calculus.Kernel` | kernel def, integrals, cexp transform, derivative -> Analysis/Calculus; gaussianReal tails, subgaussian MGF, integral_abs_gaussianReal_le -> Probability/Gaussian (with existing ComplexGaussian) |
| `Analysis.Exponential.MatrixFilter` | hermitianUnitaryPath lemmas and exp_mulVec_of_mulVec_eq_smul -> Analysis/Exponential; filterIntegral of a Hermitian matrix -> Spectral/Filter |
| `Analysis.FixedPoint.DensityRetract` | hermitianPart*, hermitianTraceOnePart*, trace_hermitianPart_eq_re -> Algebra/Hermitian; cfcAbs lemmas, densityRetract and its continuity -> Analysis/FixedPoint (Brouwer retraction onto density matrices); imports Channel.Basic only for densityMatrices |
| `Analysis.FunctionalCalculus.FiniteKroneckerPowers` | finKronecker_mul, trace_finKronecker -> Algebra/Kronecker; rpow_submatrix_equiv, rpow_finKronecker, smul_rpow -> Analysis/FunctionalCalculus |
| `Analysis.FunctionalCalculus.SpectralKronecker` | IsHermitian.spectralFun_eigenvectorUnitary -> Spectral/Eigenvalue; linMatrix, ext_star_* -> Algebra/Matrix; kroneckerUnitary, conjUnitary, spectralFun_kronecker/transpose/trace/leftRight -> Algebra/Unitary (no norms); imports ResolventDefect only for spectralFun |
| `Analysis.FunctionalCalculus.ViableSubspaceSpectralProjector` | finrank_iSup_le_sum, finrank_iSup_map_le_card_mul -> Algebra (linear algebra); IsViable.map_of_*tensor_decomposition -> Analysis/Subspace; IsSpectralProjector, contract*, IsViable.spectralProjector* stay Spectral/Filter |
| `Analysis.Isometry.CompressedPartialSwap` | Equiv.partialSwap and Matrix.partialSwap (apply, symm, involutive, Hermitian, unitary) -> Algebra/Matrix (permutation matrices on two copies); norm and isometric-compression overlap lemmas -> Analysis/Isometry |
| `Analysis.Logarithm.LogCompression` | log operator monotone under compression,log_kronecker,tensorLeft/RightHom -> Analysis/Logarithm (tensorHoms -> Algebra/Kronecker); Petz relative-entropy monotonicity -> Entropy/Relative |
| `Analysis.Norm.BipartiteDecomposition` | IsOneSided -> Algebra/OperatorSchmidt; HasProductDecomposition (norm bound ‖c‖‖d‖≤c₀) and its two lemmas -> Analysis/Norm |
| `Analysis.Norm.RootChannel` | l2_opNorm_kronecker_one_le, norm_sum_conjTranspose_mul_mul_le, norm_mul_mul_sub_mul_mul_le -> Analysis/Norm; sqrt_* and mulVec_eq_smul_of_mul_self_mulVec -> Analysis/FunctionalCalculus; rootChannel B = GBG+KBK (two-Kraus unital CP map) -> Channel/Kraus |
| `Analysis.Norm.TraceNormContractivity` | posPart/posPartSupportProj/Jordan trace-norm formula and exists_orthogonal_density_* -> Analysis/TraceNorm; positive TP map contractivity and Doeblin (Wolf 8.16-8.17) stay Channel/Contraction |
| `Analysis.Order.PosSemidefCommute` | PosSemidef.mul_of_commute/posSemidef_list_prod (PSD algebra) -> Algebra/Hermitian; smul_one_le_mul_of_commute/pow_smul_one_le_list_prod (Loewner floors) -> Analysis/Order |
| `Analysis.Real.EulerAngles` | surjectivity of SU(2) → SO(3) is algebraic; helper defs su2Diag/rotZ/rotX and exists_cos_sin use Real.cos/sin (Analysis/Real); imports Analysis-level ComplexPhasePositivity |
| `Analysis.Resolvent.Defect` | spectralFun API (spectralFun_mul/add/const/one, conjTranspose_spectralFun, dotProduct_spectralFun_mulVec, star_mulVec_dotProduct*) -> Algebra/Unitary (no norms); ResolventCompression, defect, discrepancy -> Analysis/Resolvent |
| `Analysis.Subspace.ViableSubspaceTensor` | Submodule.tensorProd, starProjection_tensorProd -> Analysis/TensorProduct; IsViable definition and IsViable.tensorProd stay (renamed ViableSubspace since it defines viability) |
| `Analysis.TensorProduct.OperatorPower` | prod_mapL_ofFn, pow_sum_mapL_eq_sum_words -> Analysis/TensorProduct; IsSpectralProjector.viability_word_power -> Spectral/Filter |
| `Analysis.TraceInequality.EntropyHolder` | entropy def,entropy_le_diagonal -> Entropy/VonNeumann (duplicate of vonNeumannEntropy); diagonal_rpow_le -> Analysis/Majorization; trace Hölder,gramMoment -> Analysis/TraceInequality |
| `Analysis.TraceNorm.SourceContraction` | sourceContraction multilinear map and its add/sub/piecewise expansions -> Algebra/Matrix; rectangularTraceNorm_sourceContraction_sub_le -> Analysis/TraceNorm |
| `Analysis.TraceNorm.SubnormalizedPureStateError` | euclideanOuterProduct and rectangularTraceNorm pure-density bounds -> Analysis/TraceNorm; the two partialTraceRight_* theorems -> Channel/PartialTrace |
| `Analysis.TraceNorm.TraceDistance` | traceDistance basics -> Analysis/TraceNorm; trace_partialTraceRight_mul, traceDistance_partialTraceRight_le -> Channel/PartialTrace |
| `Channel.Choi.OperatorNormFrobenius` | entrywise vs l2 operator norm lemmas -> Analysis/Norm; gramReshuffle_norm_sq_* (Gram reshuffle of linear maps on matrices) -> Channel/Choi with RectangularChoi |
| `Channel.Choi.RectangularChoi` | linearMapMatrix,rectangularChoi,gramReshuffleMatrix -> Channel/Choi; gramReshuffle as CLM,Frobenius parseval norms,IsHilbertSchmidtContraction and rank estimate -> Analysis/Norm (above Channel/Choi defs) |
| `Channel.ConditionNumberInterpolation` | conditionNumber, IsHermitian.le_norm_smul_one, smul_one_le_of_le_eigenvalues, isUnitVector_eigenvectorBasis, PosSemidef.exists_isUnitVector_mulVec_eq_norm_smul, PosDef.inv_norm_inv_spec -> Analysis/Norm; measurePrepareMap and CP-unital interpolation iff condition-number theorems -> Channel |
| `Channel.ConditionalExpectation.PositiveConditionalExpectationDirectSum` | unitaryReindexLinearEquiv and its _apply/_symm/_one/_mul/_star/_posSemidef/trace lemmas (~9 decls)->Algebra/Unitary (StarAlgEquiv by unitary conjugation); conditional-expectation results stay Channel |
| `Channel.Convexity.LiebConcavity` | posMap_rpow_concave_jensen, posMap_rpow_convex_jensen, posMap_log_concave_jensen (operator Jensen for positive maps) -> Channel/Positive; lieb_concavity_posDef/psd -> Analysis/Convexity; imports Channel.Basic and Channel.Schwarz.IntegralJensen |
| `Channel.DetailedBalance` | PosDef.inv_sqrt_mul_mul_sqrt_isHermitian_of_detailedBalance, PosDef.exists_sqrt_mul_unitary_diagonalization_of_detailedBalance, PosDef.jordanConditionNumber_le_of_detailedBalance -> Spectral/Jordan (one matrix); transferMatrix_* and fixedPoint_of_detailedBalance_sigmaSandwich -> Channel |
| `Channel.Dilation.ChronologicalGarbage` | euclideanTensorVector* and euclideanOuterProduct lemmas -> Analysis/Norm (or Algebra/Kronecker); garbage-register chains with partialTraceRight discard -> Channel/Dilation |
| `Channel.Dilation.RadonNikodym` | Matrix.blockDiagTopProj/BotProj (+sum,posSemidef) and kroneckerMap_conjTranspose_mul_kroneckerMap->Algebra/Matrix,Kronecker; Stinespring blocks, CP order Radon–Nikodym stay Channel/Dilation |
| `Channel.Dilation.RestoringMarginal` | partialTraceRight_mul_one_kronecker, partialTraceRight_mono, partialTraceRight_projection_sandwich(_le) -> Channel/PartialTrace; restoringMarginal, restoringMarginal_nonneg/_le -> Channel/Restoring |
| `Channel.Entanglement.DecomposableWitness` | partialTransposeLeft_smul, continuous_partialTransposeLeft, trace_partialTransposeLeft_mul(_re) -> Channel.PartialTranspose; isCompact_setOf_posSemidef_trace_one -> Analysis (compactness of density matrices); witness definitions and duality -> Channel/Entanglement |
| `Channel.Entanglement.EntanglementWitness` | traceFormReal*, traceFormRep*, exists_trace_form_re, exists_isHermitian_trace_form_re -> Algebra/Trace (trace duality); Hermitian witness from separating hyperplane for Schmidt number -> Channel/Entanglement |
| `Channel.NormalForm` | svd_of_posSemidef, svd_of_isUnit -> Algebra/Matrix (SVD from spectral decomposition); transferMatrix_svd_of_isUnit -> Channel (merge into Channel.TransferMatrix) |
| `Channel.OperatorMean.ErrorFourier` | eigConj, cfc_eq_eigConj, rpow_eq_eigConj, imagPow_eq_eigConj -> Analysis/FunctionalCalculus; Fourier form of transported square stays; imports Channel.Schwarz for proof |
| `Channel.OperatorMean.MeanDerivative` | Frechet derivatives of rpow/geomMean -> Analysis; isNPositiveMap_id/_rpowDeriv/_sandwichL/_geomMeanDeriv*/_normalizedDerivMap mention IsNPositiveMap -> Channel/Positive |
| `Channel.OperatorMean.NormDerivative` | sinhRatio and fourierWeight integral lemmas -> Analysis/Real; eigU/cfc_eq_eigen duplicate ErrorFourier eigConj -> Analysis/FunctionalCalculus; filtered-norm derivative stays |
| `Channel.OperatorMean.PowerDerivative` | rpow integral rep and Frechet derivative -> Analysis/FunctionalCalculus; isNPositiveMap_rpowFDeriv -> Channel/Positive (imports Channel.NPositiveIntegral) |
| `Channel.OperatorMean.TreeDerivative` | tree labels/derivLabel/leafMap -> Analysis; isNPositiveMap_derivLabel/_leafMap mention IsNPositiveMap -> Channel/Positive |
| `Channel.OrderedCP` | Matrix.exists_contraction_mul_of_conjTranspose_mul_le, sqNorm_mulVec_le_of_conjTranspose_mul_le, exists_contraction_mul_of_sqNorm_le -> Analysis/Order (Douglas factorization); Matrix.eq_of_mul_eq_mul_of_mulVec_surjective, blockTopRows* -> Algebra/Matrix; CPDominates, stinespringW* -> Channel (Wolf Thm 2.3) |
| `Channel.PartialTrace.Blocks` | eq_sum_single_kronecker_submatrix->Algebra/Kronecker; rectangularTraceNorm_le_sum_submatrix and integral_rectangularTraceNorm_le_sum_submatrix (integral over arbitrary measure)->Analysis/TraceNorm; only submatrix_partialTraceRight is about partial trace |
| `Channel.PartialTrace.ConditionalSkewStrip` | norm_toLp_sq,norm_star_dotProduct_le,0<=H<=1 entry bounds,kronecker_one_le_one -> Analysis/Order; strip bound of skew function -> Channel/Marginal |
| `Channel.PartialTrace.MarginalPhaseFaithful` | rpowSpec* -> Analysis/FunctionalCalculus (third duplicate of spectral powers); posDef_marginal* -> Channel/Marginal; sigmaF eigen data,resolvent compression -> Analysis/Resolvent |
| `Channel.PartialTrace.PartialTrace` | ptrR,ptrL,insR,duals,reindexing -> Channel/PartialTrace (duplicates Matrix.partialTraceLeft/Right); traceEntropy def+reindex lemmas -> Entropy/VonNeumann (duplicate vonNeumannEntropy) |
| `Channel.Peripheral.AsymptoticStateConvergence` | peripheralProjection/traceNormAsymptoticDistance of positive trace-preserving maps -> Channel/Peripheral; frobenius_norm_pureStateProj_sub and sSup_orthogonalPureStateTraceNorms_le_hilbertSchmidtOperatorNorm -> Analysis/Norm |
| `Channel.Peripheral.AsymptoticStateConverse` | hilbertSchmidtOperatorNorm_le_of_forall, exists_four_posSemidef_frobenius_norm_le, hilbertSchmidtOperatorNorm_le_four_mul_of_posSemidef -> Analysis/Norm; asymptotic-distance comparisons for positive TP maps -> Channel/Peripheral |
| `Channel.Positive.TraceNormContractionCoefficient` | linear-map contraction coefficient theorems stay Channel/Contraction; pureStateProj, IsUnitVector, AreOrthogonal, eigenprojector decomposition lemmas -> Analysis/TraceNorm |
| `Channel.Schmidt.AGSPGeometricTails` | LinearMap.inner_pow_eq_zero_and_norm_sq_le (inner-product-space iteration) -> Analysis/Norm; one_sub_kyFanNorm_le_of_orthogonal_decomposition and sum_eigenvalues_geometric_tail_of_operatorSchmidtRank -> Channel/Schmidt |
| `Channel.Schmidt.FilterNormalization` | exists_phase_normalized_filter_output (operator with invariant unit target, norms) -> Analysis/Norm; exists_phase_normalized_filter_output_of_operatorSchmidtRank -> Channel/Schmidt; Analysis.GlobalGap import |
| `Channel.Schmidt.MaximalOverlap` | trace_mul_re_le_kyFanNorm_of_rank_le, kyFanNorm_eq_sup_trace_rankLE, zero_lt_kyFanNorm_*, toEuclid*, normSq_trace_conjTranspose_mul_le_kyFanNorm*, exists_/isGreatest_normSq_trace_conjTranspose_mul -> Analysis/Norm (Ky Fan); maximalSchmidtOverlap_*, partialTraceRight_vecMulVec_eq, normSq_inner_le_kyFanNorm* -> Channel/Schmidt |
| `Channel.Schmidt.NPositivitySpectralCriterion` | eigenvector, rayleigh*, star_eigenvector_dotProduct*, sum_normSq_eigenvector_overlap*, spectral_lower/upper_bound_core, spectral_lower_bound_top -> Spectral/Eigenvalue; reducedEigDensity*, schmidtRankLEExpectations* -> Channel/Schmidt (no maps in statements) |
| `Channel.Schmidt.PureApproximationSpectralTail` | one_sub_normalized_overlap_le_half_pure_trace_error (one vector, pure-density trace norm)->Analysis/TraceNorm; sum_descEigenvalue_tail_le_half_pure_trace_error (marginal spectrum of bipartite vector) stays Channel/Schmidt |
| `Channel.Schmidt.SurprisalMoment` | surprisalMoment/surprisalTail of a probability vector stay Entropy/Classical; generic halving lemmas le_mul_of_halving, le_mul_add_of_halving -> Analysis/Real |
| `Channel.Schmidt.Trimming` | descEigenvalue_antitone,kyFanNorm_le_trace_re,kyFanNorm_add_le,succ_mul_descEigenvalue_le_trace_re,trace_mul_re_le_*,commute_of_forall_trace_mul_re_le (one PSD matrix)->Spectral/Eigenvalue; leftMarginal,leftApply,IsTrimmingProjection stay Channel/Schmidt |
| `Channel.Schmidt.TrimmingEnergy` | PosSemidef.re_inner_toEuclideanLin_* and mul_sq_norm_le_re_inner_toEuclideanLin (quadratic forms of one PSD matrix)->Analysis/Order; leftApply/rightApply/trimming energy stay Channel/Schmidt |
| `Channel.Schmidt.UhlmannIsometry` | exists_isIsometry_mul_eq_of_conjTranspose_mul_eq and exists_isIsometry_eq_mul_conjTranspose_of_mul_conjTranspose_eq (Gram equality -> isometry)->Algebra/Unitary; Uhlmann/rootFidelity/purification lemmas stay Channel/Schmidt |
| `Channel.Twirl.ComplementaryWeylTwirl` | weylShift_mem_unitary, weylClock_mem_unitary, weyl_mem_unitary -> Algebra/Unitary; Weyl twirl on one tensor factor equals partial trace (x) maximally mixed -> Channel/Twirl (with Channel.WeylTwirl) |
| `Channel.Twirl.WeylTwirl` | sum_pow_val_eq_ite,starRingEnd_eq_inv_of_isPrimitiveRoot,pow_mul_conj_pow_eq_one_iff,sum_rootOfUnity_pow_eq,addRight_one_pow (roots of unity over ZMod)->Algebra/Combinatorics; Weyl operators and 1-design twirl->Representation/Twirl; no channel objects |
| `Channel.WolfProps` | polarization_sandwich,vecMulVec_star_eq_polarization->Algebra/Matrix; cp_decomposition_of_sandwich_sum->Channel.CPDecomposition; linearMap_eq_id_of_fixes_rankOne,channel_eq_id_of_fixes_pureStates etc.->Channel.NoInformationWithoutDisturbance; pureEnsembleDensity HJW->Channel.EnsembleEquivalence; dissolve the source-named file |
| `Entropy.Conditional.BoundaryEnergy` | phase/power/hsEnergy lemmas -> Analysis/FunctionalCalculus; paired_entropy_boundary,one_filter_with_marginal_phase,boundary_pair_energy (conditionalEntropy) -> Entropy/Conditional |
| `Entropy.Conditional.ConditionalEntropy` | partialTraceLeft_real_smul,partialTrace*_sum,partialTraceRight_blockDiagonal -> Channel/PartialTrace; PosSemidef.blockDiagonal -> Algebra/Hermitian; conditionalEntropy defs/mixture interval -> Entropy/Conditional |
| `Entropy.Conditional.ConditionalPhase` | spectral_second_moment (scalar weights) -> Analysis/Real; conditional_* -> Entropy/Conditional |
| `Entropy.Conditional.FilterSlack` | reshuffle,reshuffle_sub,ptrL_reshuffle -> Algebra/Matrix; hsEnergy_reshuffle,optimizer_deficit_bound -> Analysis/FunctionalCalculus; conditional_* -> Entropy/Conditional |
| `Entropy.Conditional.MarginalPhaseApprox` | cpowSpec/rpowSpec_of_eq_cfc -> Analysis/FunctionalCalculus; marginal*_affine -> Channel/Marginal; approx state,vonNeumannEntropy_of_eq_cfc -> Entropy |
| `Entropy.Conditional.MarginalPhaseComparison` | spectralFun_kronecker_one_cpow,norm_ofReal_cpow_imag -> Analysis/FunctionalCalculus; norm_phaseDifference_le_of_posDef (conditional mutual information) -> Entropy/Conditional |
| `Entropy.Conditional.MarginalPhaseQuantities` | trace_marginal*,sigmaF/sigmaS -> Channel/Marginal; re_trace_mul_mul_mono -> Analysis/Order; condMutualInfo def (duplicate of conditional mutual information) and logGap -> Entropy/Conditional |
| `Entropy.Conditional.MovementEstimate` | coefficientVector,kronecker_one_mulVec,reshuffle_eq_zero_iff -> Algebra/Kronecker; movementMarginal*,conditionalMovement_norm_le -> Entropy/Conditional |
| `Entropy.Conditional.Optimizer` | powers,traces,hsSquare,optimizerWeights -> Analysis/FunctionalCalculus; conditional_gramMoment_bounds,conditional_optimizer_root_stability -> Entropy/Conditional |
| `Entropy.Conditional.Purification` | hsEnergy_neg,unitary_distance_four,renyi_deficit_nonneg -> Analysis/FunctionalCalculus; coefficient/uncoefficient,conditionalEntropy_eq,one_filter_purification_bound -> Entropy/Conditional |
| `Entropy.Conditional.SingularInterpolation` | regularWeights* -> Analysis/Real; power_regularWeights_tendsto -> Analysis/FunctionalCalculus; one_copy_interpolation,one_copy_move_schmidt -> Entropy/Conditional |
| `Entropy.Conditional.UnitaryCovariance` | tensorLeft/RightUnitary,transposeUnitary,gram_unitary_* -> Algebra/Unitary; entropy_unitary_conj -> Entropy/VonNeumann; conditional_gram_rotate,one_copy_move_* -> Entropy/Conditional |
| `Entropy.MutualInformation.DataProcessing` | IsKrausCPTP.tensorMapId_posSemidef,tensorMapBoth,trace*_submatrix_swap -> Channel; data processing of mutual information -> Entropy/MutualInformation |
| `Entropy.MutualInformation.PhysicalBuffer` | isHermitian_of_posSemidef_gap, physicalBuffer_ground_pair -> Spectral/Gap (doubled Hamiltonian gap); exists_physicalBuffer_gaussian_filter -> Entropy (hypothesis is relative entropy of marginals, i.e. mutual information, plus partial traces) |
| `Entropy.MutualInformation.PhysicalBufferOverlap` | bipartiteRegroup, doubledRegroup, regroupPurification and partial-swap overlap identities -> Channel/PartialTrace (equivs, kronecker, partial trace, purity); exists_hermitian_contraction_physicalBuffer_overlap -> Entropy (relative entropy to product of marginals); no sites |
| `Entropy.MutualInformation.PurificationSplitting` | Real.sqrt_two_mul_one_sub_exp_neg_half_le_sqrt -> Analysis/Real; norm_toLp_sq, star_mulVec_dotProduct_* -> Analysis/Norm; tensorPurification, canonicalPurification, exists_isIsometry_*_le (root fidelity, Uhlmann) -> Channel/Dilation (purifications); *_le_mutualInformation, *_le_sqrt, *_le_zpow -> Entropy/MutualInformation |
| `Entropy.Relative.EffectRelativeEntropy` | binaryRelativeEntropy and klFun monotonicity -> Entropy/Classical; quantumRelativeEntropy_conj_isometry,twoOutcomeIsometry,effect lower bound -> Entropy/Relative |
| `Entropy.Relative.EntropyReindex` | log_submatrix_equiv -> Analysis/FunctionalCalculus (beside cfc_submatrix_equiv in CfcConjugation); quantumRelativeEntropy_submatrix_equiv -> Entropy/Relative |
| `Entropy.Relative.KleinInequality` | trace_diag_conj, trace_mul_cfc_eq_double_sum, row/col_sum_normSq -> Analysis/TraceInequality; gibbs_core* -> Analysis/Real; Klein inequality for quantumRelativeEntropy -> Entropy/Relative |
| `Entropy.Relative.LiebTraceExponential` | quantumRelativeEntropy_smul_right, re_trace_sub_re_trace_le_quantumRelativeEntropy, quantumRelativeEntropy_exp_add_log, variational lemmas -> Entropy/Relative; posDef_exp, convex_setOf_posDef, concaveOn_re_trace_exp_add_log -> Analysis/Convexity (proof needs Entropy and Channel.Schwarz.RelativeEntropyDataProcessing) |
| `Entropy.Relative.MarginalPhaseSupport` | hatPhase,kerProj,suppProj,sqrtSpec of one Hermitian matrix -> Spectral/Projection; support inclusions of marginals -> Channel/Marginal |
| `Entropy.Relative.RootFidelityRelativeEntropy` | IsHermitian.trace_cfc_mul_cfc_eq_double_sum -> Spectral/Eigenvalue; fidelity lower bounds by quantumRelativeEntropy and extendedRelativeEntropy (EReal def) -> Entropy/Relative |
| `Entropy.Relative.SupportCompressedEntropy` | PosSemidef.eq_expansion_compression_of_kernel_le_... -> Analysis/Support/Compression; relative entropy and sandwiched Renyi-2 statements stay Entropy/Relative |
| `Entropy.Renyi.SandwichedRenyiTwo` | rpow_mul_mul_rpow, posDef_rpow_neg_quarter_mul_self -> Analysis/FunctionalCalculus; order-two sandwiched trace and its operator -> Entropy/Renyi; namespace TNLean; imports Analysis.Entropy |
| `Entropy.Renyi.Tail` | trace_cfc_eq_sum_eigenvalues0 -> Spectral/Eigenvalue (or Analysis/FunctionalCalculus); ordered tail and eigenvalue tail bounds by sum p^a (Renyi expression, written out) -> Entropy/Renyi; renyiEntropy not named, Analysis/Real for the scalar part |
| `Entropy.Surprisal.FilterMoment` | inner_toEuclideanLin_eq_trace -> Algebra/Trace; norm_kronecker_one_apply_sq -> Channel/PartialTrace; rpow_one_sub_le_exp_of_log_le -> Analysis/Real; filter norm vs exp(-aS) under gap -> Entropy/Surprisal (bipartite, no sites) |
| `Entropy.Surprisal.GapSurprisal` | log_two_mul_le_two_mul_log,cutLogBudget,tailRadius -> Analysis/Real; surprisal moments of the marginal of a gapped bipartite ground vector (terms h i,one-sided,Schmidt coords) -> Entropy/Surprisal; no sites |
| `Entropy.Surprisal.MarginalTails` | norm_one_matrix_le,isometry norm lemmas -> Analysis/Norm; cutBasisChange,isOneSided_conj,hasProductDecomposition_conj -> Algebra/Kronecker; surprisal moment/tail of gapped ground marginal -> Entropy/Surprisal |
| `Entropy.Typical.Density` | IsHermitian.spectralSelection, spectralRestrictionMass, normalizedSpectralRestriction and their projection/trace/rank/PSD lemmas -> Spectral/Projection; PosSemidef.entropy_normalizedSpectralRestriction, typicalSpectralRestriction_entropy_bounds -> Entropy/Typical |
| `Entropy.Typical.IidSurprisal` | private finKronecker_diagonal/one/star/mem_unitary -> Algebra/Kronecker (likely duplicates); surprisal tails of tensor powers -> Entropy/Typical |
| `Entropy.Typical.PureCompression` | IsHermitian.spectralSelectionEmbedding (+ isometry, mul_conjTranspose) -> Spectral/Projection; compressedTypicalPureState and its partial traces/norm -> Entropy/Typical (no entropy in statements) |
| `Entropy.VonNeumann.ConditionalContinuity` | traceDistance,hsEnergy defs and lemmas -> Analysis/TraceNorm (duplicate Analysis.TraceDistance and Frobenius norm); conditional_continuity,conditional_abs_le -> Entropy/Continuity |
| `Entropy.VonNeumann.ControlledContinuity` | binEntropy/log/sqrt scalar lemmas,winterModulus_le_sqrt -> Entropy/Classical (or Analysis/Real); conditionalEntropy add/abs/continuity -> Entropy/Continuity |
| `Entropy.VonNeumann.Entropy` | vonNeumannEntropy defs/bounds -> Entropy/VonNeumann; quantumRelativeEntropy -> Entropy/Relative; traceA_ABC/traceC_ABC/traceAC_ABC and traceLeft/traceRight PSD lemmas -> Channel/PartialTrace; eigenvalue sum-one facts -> Spectral/Eigenvalue; IsSSAEquality -> Entropy/StrongSubadditivity; mutualInformation -> Entropy/MutualInformation |
| `Entropy.VonNeumann.PureEntropy` | traceEntropy transpose/gram,purifyingSwap -> Entropy/VonNeumann; entropy_triangle,conditional_lower -> Entropy/Conditional; sum_eigen_stat_* -> Spectral/Eigenvalue |
| `Entropy.VonNeumann.SpectralTail` | IsHermitian.trace_complement_spectralProjectionGE -> Spectral/Projection; entropy bounds on spectralProjectionGE tails -> Entropy/VonNeumann; trace_shiftedRegulator_le_quarter_of_entropy ties to Analysis.PatchRegulator (area-law filter object) |
| `Kraus.MixedMap.GaugeConstruction` | gaugeTensor,gauged intertwining of transfer maps,injective tensors -> Kraus/MixedMap; injective_of_ker_all, det_ne_zero_of_ker_all, ungauge_scalar_of_conjugated_scalar, isUnit_det_of_self_mul_conjTranspose_scalar are Fin-D re-wrappings of Algebra.MatrixKernelRigidity -> delete |
| `Kraus.Wielandt.ChoiTraceFactorization` | choiMatrix_eq_kronecker_of_eq_trace_smul and choiMatrix_posDef_of_eq_trace_smul -> Channel/Choi; isInjective_of_mapLM_eq_trace_smul -> Kraus (injectivity of a family); Kraus.Injectivity imported only for that one |
| `Kraus.Wielandt.KrausRectangularComposition` | rectangularKrausMap_evalWord_ofFn -> Kraus (words, imports Kraus.MapIterate only for it); rectangularKrausMap_comp and linearMap_trace_rectangularKrausMap -> Channel/Kraus |
| `Kraus.Wielandt.LowDim` | isNilpotent_fin_two_of_trace_eq_zero_of_det_eq_zero,exists_nonzero_eigenvector_fin_two_of_not_isNilpotent,exists_nonzero_eigenvector_of_not_isNilpotent (one matrix)->Spectral/Eigenvalue; wordSpan/wielandtIndex bounds for families stay Kraus/Wielandt |
| `Kraus.Wielandt.ZeroErrorDichotomy` | HasOneShotZeroErrorBit,not_hasOneShotZeroErrorBit_of_posDef_outputs,exists_orthogonal_fixed_densities,exists_posSemidef_fixed_not_smul,pow_apply_of_apply_eq (maps E)->Channel/FixedPoint; zeroError_dichotomy(_eventually) mention wielandtIndex K -> Kraus/Wielandt |
| `ManyBody.Entropy.ConditionalMovementRegional` | FourPartition,frameEquiv*,unionEquiv*,restrict lemmas -> ManyBody/Sites; regional movement estimate -> ManyBody/Entropy |
| `ManyBody.Entropy.Cut.RegionUnion` | regionUnionEquiv, localLift_union_kronecker -> ManyBody/Sites (merge into QICLean.ManyBody.Sites.RegionUnion); isFeasibleFilter_union_kronecker -> ManyBody/RegionFilter (IsFeasibleFilter from Entropy.FilterOptimizer) |
| `ManyBody.Entropy.Cut.RegionalViability` | regionTensorCoordinates, regionTensorCoordinates_eq_exteriorFirst -> ManyBody/Sites; isCloseTo_prodExt_region_iff_isViable -> ManyBody/ViableSubspace |
| `ManyBody.Entropy.Filter.BufferDiscount` | IsFeasibleFilter.mono_floor -> Spectral/Filter; rest (regionEntropy,condEntropy of nested regions,region filters) ManyBody/Entropy |
| `ManyBody.Entropy.Filter.Chain` | List.eq_filter_lt_append_cons_filter_gt,pairwise_gt_reverse_filter_finRange -> Algebra/Combinatorics; chainList,liftProd splits -> ManyBody/RegionFilter |
| `ManyBody.Entropy.Filter.ChainEnergy` | List.filter_not_append lemma -> Algebra/Combinatorics; inv_conj_diagonal -> Algebra/Matrix; inner_cutOperator,cutOperator_mul -> ManyBody/Sites; excitation energy of filter chains -> ManyBody/RegionFilter (mentions H,E0 of a gapped Hamiltonian) |
| `ManyBody.Entropy.Filter.Clipping` | conjDiagonalCLM,hasDerivAt_conj_diagonal_rpow,trace_conj_diagonal_mul,abs_log_rpow_sub_le_of_ratio_le -> Analysis/FunctionalCalculus; toEuclideanLin_liftProd_localLift_mul,ratio_le_of_diagonal_max -> ManyBody/RegionFilter |
| `ManyBody.Entropy.Filter.Maximizer` | isCompact unitaries/floor simplex -> Analysis/Topology; isCompact_setOf_isFeasibleFilter,isFeasibleFilter_uniform -> Spectral/Filter; liftProd chains,exists_max_feasible_chain -> ManyBody/RegionFilter |
| `ManyBody.Entropy.Filter.Optimizer` | IsFeasibleFilter def,conj,posDef,of_common_basis,trace_cfc_conj_diagonal -> Spectral/Filter; unitary_mul_conjTranspose -> Algebra/Unitary; exists_clipped_of_max_feasible -> ManyBody/RegionFilter |
| `ManyBody.Entropy.Filter.PatchStationarity` | rpow_unitary_mul_diagonal_mul, PosSemidef.hasDerivAt_*_rpow_of_commute, PosSemidef.le_trace_smul_add_smul_one_of_forall_density -> Analysis/FunctionalCalculus; mulApplyCLM_apply, hasDerivAt_norm_sq_mulApply -> Analysis/Calculus; inner_mulLocalLift.., patchFilter_*, PatchFactor, IsPatchMinimizer, patch_stationarity -> ManyBody/RegionFilter (sites, RegionFilter, regionState, descending chains) |
| `ManyBody.Entropy.Filter.Power` | specPow defs and derivative/norm lemmas -> Analysis/FunctionalCalculus (duplicate of ConditionalMovement.SpectralPowers.power); localLift_injective -> ManyBody/Sites; vector three-lines for filter chains -> ManyBody/RegionFilter |
| `ManyBody.Entropy.Filter.Prefix` | pow_mul_le_prod_of_step -> Analysis/Real; sq_norm_inner_ge_of_gap,norm_inner_ge_of_gap -> Spectral/Gap; cutVector_toEuclideanLin -> ManyBody/Sites; chainOptimum comparisons -> ManyBody/RegionFilter (with Hamiltonian gap) |
| `ManyBody.Entropy.Filter.SchmidtPinning` | pinProj and its projection lemmas, eq_of_forall_trace_mul_eq, mul_prod_map_mul_of_idempotent, mul_prod_eq_prod_mul -> Algebra (Projection/Trace/Matrix); norm_toEuclideanLin_sq, norm_toEuclideanLin_le_of_proj -> Analysis/Norm; norm_sq_localLift_pinProj, inner_localLift_eq_sum_pinProj, regionState_eq_sum_pinProj -> ManyBody/Sites; norm_liftProd_trial_ge -> ManyBody/RegionFilter (FilterChain) |
| `ManyBody.Entropy.Filter.Stationarity` | hasDerivAt_exp_conj,mulApplyCLM,stationarity/commute lemmas on one matrix (first section) -> Analysis/Calculus; RegionFilter,liftProd,IsDescendingChain,localLift -> ManyBody/RegionFilter (defines the object) |
| `ManyBody.Entropy.Filter.ZeroFloor` | isFeasibleFilter_floorRaise -> Spectral/Filter; norm comparisons without floor -> ManyBody/RegionFilter |
| `ManyBody.Entropy.MutualInformationPerturbation` | traceDistance_regionState_le -> ManyBody/Sites (trace distance of regional states); regionMutualInformation_* -> ManyBody/Entropy; objects sites,regionState,mutual information,supported unitary,trace distance |
| `ManyBody.Entropy.RegionCovariance` | siteConfigurationEquiv, regionConfigurationEquiv, relabelVector, norm_relabelVector, regionState_relabel -> ManyBody/Sites (merge into QICLean.ManyBody.Sites.Relabel); regionEntropy_relabel -> ManyBody/Entropy |
| `ManyBody.Entropy.RegionEntropy` | regionState_compl_eq_partialTraceLeft, jointMatrix, jointMatrix_posSemidef -> ManyBody/Sites; regionEntropy_*, regionMutualInformation defs/lemmas -> ManyBody/Entropy; defining module of regionEntropy and regionMutualInformation |
| `ManyBody.Entropy.RegionPurificationSplitting` | splitTwoRegionsEquiv, splitTwoRegionsState, partialTraceRight_*, splitTwoRegionsState_unit -> ManyBody/Sites; exists_isIsometry_splitTwoRegionsState_* (bounds by regionMutualInformation) -> ManyBody/Entropy |
| `ManyBody.Entropy.SumSitesProduct` | disjSumEquiv, sumSitesProduct, norm_sumSitesProduct, regionState_sumSitesProduct -> ManyBody/Sites (merge into QICLean.ManyBody.Sites.SumSites); regionEntropy_sumSitesProduct, regionMutualInformation_sumSitesProduct_* -> ManyBody/Entropy |
| `ManyBody.Entropy.SupportedMarginalTails` | supportDim, cutLogBudget(_compl/_empty/_univ/_le/_const_le), norm_cutVector -> ManyBody/Sites; log_surprisalMoment_cut_le, surprisalTail_cut_le (gapped ground vector of sum of supported terms, vonNeumannEntropy of cut marginal) -> ManyBody/Entropy; Hamiltonian appears as raw sum of h i, not Interaction |
| `ManyBody.Entropy.Typical.CompressedPhysicalRegions` | extractExteriorRegion,monotone/pairwise exteriorRegion -> ManyBody/Sites (with CompressedSiteCoordinates); compressedRegionalThreshold* (regional entropy/selected mass) -> ManyBody/Typical |
| `ManyBody.Entropy.ViableSubspaceEntropy` | unit_cut_spectral_probability (no sites: Schmidt spectrum of a unit vector in a viable space, vonNeumannEntropy = probabilityEntropy) -> Entropy/VonNeumann; actualRegionSplit_marginal_and_entropy -> ManyBody/Entropy |
| `ManyBody.Replica.BandMetric.Energy` | Matrix.commute_inv_left,PosDef.rpow_conj_mul_of_commute,posDef_list_ofFn_prod,list_ofFn_prod_rpow_conj,rpow_one_div_eight_nonneg -> Analysis/FunctionalCalculus; copyMean/bandMetric/IsSupportedOn energy estimate -> ManyBody/Replica |
| `ManyBody.Replica.BandMetric.EntropyGain` | continuous_entropy (regionEntropy continuity) -> ManyBody/Entropy; bandRelRatio,entropy gain lower bound -> ManyBody/Replica; regionEntropy,cfc log,measure |
| `ManyBody.Replica.BandMetric.IntegratedEntropy` | hermPart,isHermitian_hermPart,re_trace_mul_hermPart -> Algebra/Hermitian; measurability/integrability of entropy gain of TransportData -> ManyBody/Replica |
| `ManyBody.Replica.BandMetric.RelativePinBound` | smul_vecMulVec_le_of_forall,rpow_neg_half_eq_inv_sqrt -> Analysis/Order,FunctionalCalculus; isBigO_neg_log_inv_poly -> Analysis/Real; logDim_eq,fourPartition,relativePinBound -> ManyBody/Replica |
| `ManyBody.Replica.BandMetric.Setup` | symDim,realCoherentIntegral -> Representation/Coherent; PYF tripartitions of Finset V,Move,bandMetric,symBandMetric,logDim,moveEta,TransportData,EnergyTerms -> ManyBody/Replica |
| `ManyBody.Replica.BandMetric.SplitSkewBound` | re_coherentIntegral_ofReal -> Representation/Coherent; card_regionConfig,one_sub_localLift,log_exp_mul_card_mul_card -> ManyBody/Sites; exists_tendsto_zero_forall_le -> Analysis/Real; skew bound at split leaf -> ManyBody/Replica |
| `ManyBody.Replica.Configuration.BadCopyExponential` | re_dotProduct_exp_grouped_signedLabelEntropy_le uses regions Finset V -> ManyBody/Replica; remaining lemmas (tripartite five-factor replicas,permOp,excitation components) -> Representation/Replica |
| `ManyBody.Replica.Configuration.GoodConfigurationDensity` | fiveFactorCopiesEquiv and private copy reindexings -> Representation/Replica; replicaGoodConfigurationMarginal (built with ManyBody.cutEquiv on the copy index) -> ManyBody/Replica; objects: replica copies, five physical factors, symProj, partialTraceRightAlong |
| `ManyBody.Replica.Configuration.GoodConfigurationSingletonMoment` | physicalSingletonEquiv, fiveFactorCopies_labelObservable_singleton, fiveFactorCopies_exp_labelEntropy_singleton -> Representation/Replica; trace_replicaGoodConfigurationMarginal_exp_singleton_labelEntropy -> ManyBody/Replica |
| `ManyBody.Replica.Configuration.JointDensity` | partialTraceRightAlong_kronecker -> Channel/PartialTrace; replicaGoodRegionalAuxiliaryMarginal (cutEquiv on copies) and its identity -> ManyBody/Replica |
| `ManyBody.Replica.Configuration.RegionalFiveFactorCoordinates` | regionalPhysicalEquiv (regions Q Y,RegionConfig) -> ManyBody/Sites; replicaPhysicalCoordinateEquiv,regionalFiveFactorSpace,globalReplicaCopiesEquiv,regionalFiveFactorCopyEquiv -> ManyBody/Replica; imports Analysis.ReplicaGoodConfigurationDensity (replica configurations in Analysis) |
| `ManyBody.Replica.Label.GroupedLabelSymmetricSupport` | labelEntropy_mul_symProj_of_eq_mul -> Representation/YoungSubgroup (abstract actions); rest (subsystemPerm on regions S T P Y F : Finset V,symProj) -> ManyBody/Replica |
| `ManyBody.Replica.Label.SubsystemTransport` | permOp/groupAlgebraRep/labelProj_of_intertwine,prodLeft,labelProj_copyPerm_equiv -> Representation/Isotypic; SubConfig,ComplConfig,splitEquiv,labelProj_subsystemPerm_eq -> ManyBody/Replica; SubConfig/ComplConfig duplicate ManyBody.RegionConfig/ComplConfig |
| `ManyBody.Replica.Label.SupportedSubsystemLabelDimension` | dim_le_card_of_labelProj_ne_zero -> Representation/Isotypic; dim_le_pow_card_of_subsystem_labelProj_ne_zero -> ManyBody/Replica |
| `ManyBody.Replica.Metric.Integral` | groupAlgebraRep_comp_embedding,labelProj_comp_embedding,tensorPow_submatrix -> Representation/TensorPower; posDef_unitary_conj_diagonal,specSample_rpow_posDef,subSample*,compression_posDef,re_trace_subSample_le -> Probability/Haar (random spectral samples); replicaMetric_reindex,exists_replicaMetric_integral (Q : Finset F) -> ManyBody/Replica |
| `ManyBody.Replica.Metric.Lift` | reindex_injective -> Algebra/Matrix; norm_tensorVec -> Representation/Coherent; norm_of_integral_mulVec_le,mul_of_integral -> Probability/Measurable (matrix-valued integrals); localLift_splitEquiv_apply,reindex_tensorPow_localLift,exists_replicaMetric_integral_localLift -> ManyBody/Replica |
| `ManyBody.Replica.Metric.Metric` | labelObservable_eq_groupAlgebraRep,sum_smul_centralIdem_mem_center -> Representation/Isotypic; replicaDim,replicaLabelWeight,replicaMetric and its Hermitian/PosDef facts (subsystems Q : Finset F) -> ManyBody/Replica |
| `ManyBody.Replica.Metric.RelativePinAlgebra` | norm_euclidean_sq,norm_star_dotProduct_sq_le_inv -> Analysis/Norm (PosDef Cauchy-Schwarz); IsLabelFunctionOn,replicaMetric invertibility,relativeMetric,moveWord (regions Q P x Y₀ F) -> ManyBody/Replica |
| `ManyBody.Replica.Metric.Similarity` | ManyBody.IsSupportedOn.exists_sum_mul -> ManyBody/Sites; labelObservable inverse/commute lemmas (labelObservable_inv etc.) -> Representation/Isotypic; leafRoot,leafMetric,copyMean similarity bounds -> ManyBody/Replica |
| `ManyBody.Replica.Metric.StarFunction` | IsOrthogonalResolution.hom_mul_self,norm_le_l2_opNorm_hom -> Spectral; l2_opNorm_starOp_le -> Representation/SymmetricGroup; abs_starValue_le_one and polynomial/cfc approximations of starOp (subsystemPerm Q) -> ManyBody/Replica (could be generalized to any φ) |
| `ManyBody.Replica.RelativePin` | trace_vecMulVec_star_eq -> Algebra/Trace; rpow_mul_cfc_kernelCompletion -> Analysis/FunctionalCalculus; Entropy.FourPartition.moveParts -> ManyBody/Sites (region partitions); frame marginals,relativePinConst,Lemma 6.3 over regions with regional entropy -> ManyBody/Replica; "Pin" is a paper term, keep only as file name |
| `ManyBody.Replica.SiteOp` | commute_permOp_of_apply_eq,siteOp_eq_reindex,l2_opNorm_siteOp_le,siteOp_sum,conjTranspose_siteOp -> Representation/TensorPower (siteOp = copy operator); IsSupportedOn/subsystemPerm lemmas -> ManyBody/Replica; imports Entropy.SupportedMarginalTails,Analysis.RootChannel, and is imported by UnitaryTwirl |
| `ManyBody.Replica.Symbol.CoherentLog` | logKernel,resolvent,cfc_logKernel,exists_spectrum_subset_Icc -> Analysis/Logarithm; letterCount,symDim_le,symProj_mul_self,trace_symProj,posSemidef_symProj -> Representation/TensorPower; coherentAverage operator Jensen -> Representation/Coherent; no sites |
| `ManyBody.Replica.Symbol.CoherentSymbolFunction` | abs_eigenvalues_le -> Spectral/Eigenvalue; rest (pow,aeval,cfc,abs,skew of coherent symbols) Coherent; imports RegionPowerSymbol (ManyBody/Replica) only for generic cfc lemmas -> upward import to remove |
| `ManyBody.Replica.Symbol.MarkedSimilaritySymbol` | norm_sandwich_approx_le,norm_pairing_approx_le,exists_rpow_le,sandwich_rearrange,star_dotProduct_mul_mulVec -> Analysis/Norm (and Algebra/Matrix for the last two); polyWordSymbol,polyWord,marked symbols over regions P Y : Finset V -> ManyBody/Replica |
| `ManyBody.Replica.Symbol.MarkedStar` | siteOp_mul_siteOp_apply_of_ne,injectionAverage_oneCopy_eq -> Representation/Coherent (copy-only); regionUnit,margLift,starOp of subsystemPerm,hasMarkedSymbol_starOp (RegionConfig,regions Q) -> ManyBody/Replica |
| `ManyBody.Replica.Symbol.RegionPowerSymbol` | cfc_mul_cfc,cfc_sub_cfc,mul_cfc,l2_opNorm_cfc_sub_aeval_le -> Analysis/FunctionalCalculus; commute_localLift_of_disjoint/_of_isSupportedOn,aeval_localLift,l2_opNorm_localLift_le,star_dotProduct_localLift_mulVec,trace_regionState_toLp -> ManyBody/Sites; powers of one-copy regional marginals -> ManyBody/Replica |
| `ManyBody.Replica.Symbol.SkewSymbolBound` | re_coherentIntegral_le,coherentIntegral_const_mul,continuous_comp_unitary_mulVec_single -> Representation/Coherent; continuous_partialTraceLeft/Right,continuous_submatrix,continuous_vecMulVec_self -> Analysis (Channel/PartialTrace); eigenvalues_mem_Icc_of_trace_eq_one -> Spectral; continuousOn_condMutualInfo -> Entropy/Continuity; SkewPartition of regions,markedScalarSymbol skew bound -> ManyBody/Replica |
| `ManyBody.Subspace.Trimming` | inner_leftApply_*, norm_rightApply_sq_le, leftApply_add/sub/zero/one, norm_leftApply_le_of_isHermitian_idem, mul_spectralProjectionGE_leftMarginal_* -> Channel/Schmidt (leftApply defined in Channel.SchmidtTrimming); stackVector, trimProj, trimStep, trimSubspace, isCloseTo_prodExt_trimSubspace -> ManyBody/ViableSubspace |
| `Probability.Concentration.MatrixCumulantSubadditivity` | IsHermitian.abs_re_trace_exp_le,le_smul_one_of_norm_le,neg_smul_one_le_of_norm_le,exp_mem_Icc_of_norm_le,posDef_of_smul_one_le,norm_exp_le_of_norm_le,continuous_exp,continuousOn_re_trace_exp_add_log -> Analysis (Order/Exponential); IsHermitian.spectrum_subset_Icc -> Spectral; integrable_re_trace_exp,integrable_exp,ae_norm_sum_le_card_mul,integral_re_trace_exp_add_le,integral_re_trace_exp_add_sum_le -> Probability/Concentration |
| `Probability.Concentration.WeightedSourceError` | sourceBlock,weightedSourceError,weightedSourceQuarter,weightedSourceError_eq_halfWeighted,quarterWeighted_source_sum_eq_transpose,rectangularTraceNorm_weightedSourceError_le,sourceProductProbability,sum_sourceProductProbability,weighted_source_block_aggregation,weighted_source_block_sum_le_one (lines 42-160) -> Analysis/TraceNorm; aestronglyMeasurable_rectangularTraceNorm_sum,integrable_*,integral_* (lines 161+) -> Probability/Moment |
| `Probability.Gaussian.ProductSource` | schmidtVector,schmidtSource,schmidtSource_apply,weighted_delta_eq_schmidtSource are deterministic matrices with sqrt/rpow weights (Analysis level, could be a definitional prelude); sourceU/V,sampledSource,sourceCorrection and all integral/integrable lemmas -> Probability |
| `Probability.Gaussian.ProductSourceTransport` | ambientSchmidtVector,ambientSchmidtSource,sourceTransport,ambientSchmidtVector_eq_mulVec,sourceTransport_kronecker,sourceTransport_schmidtSource,*_eq_transport (lines 39-147) are pointwise Kronecker identities -> Algebra/Kronecker (with sqrt weights: Analysis); integrable_*/integral_* (lines 148+) -> Probability |
| `Probability.Measurable.FiniteFamilyImageProjection` | range_toEuclideanLin_familySupportProj, projectionMatrix_iSup_map_eq_familySupportProj -> Analysis/Projection; measurable_projectionMatrix_iSup_map -> Probability/Measurable |
| `Probability.Measurable.SpectralProjectionMeasurable` | closedThresholdRamp lemmas scalar -> Analysis/Real; IsHermitian.supportProj_eq_one_sub_spectralProjectionGE_mul -> Spectral/Projection; measurability of spectralProjectionGE and supportProj -> Probability/Measurable |
| `Probability.PoissonWord.Basic` | Word (abbrev for Sigma m, Fin m -> iota) and nil -> Algebra/Combinatorics (new module FiniteWord, needed by Append/Marked/Counts/Partition/Thinning/Relabel/Telescope); measurable-space instances,weight,measure,sum_weight,hasSum_one_weight,integrability bounds -> Probability/PoissonWord |
| `Probability.PoissonWord.ContractionWordAppend` | contractionWord_append -> Analysis/Contraction (into ContractionWordDecay); contractionWord_word_append (PoissonWord.append) -> Probability/PoissonWord, could merge into QICLean.Probability.PoissonWord.PoissonWordAppend |
| `Probability.PoissonWord.Jump` | take_succ_eq_append_singleton,sum_prefix_increment are word combinatorics -> Algebra/Combinatorics (WordAppend/MarkedWord); integrable_*,measurable_integral_*,integral_sum_prefix_*,integral_sub_eq_integral_sum_increment,integral_le_add_* -> Probability |
| `Probability.PoissonWord.Partition` | partitionWords,partitionWords_nil,partitionWords_length,ofFn_partitionWords_fst/snd -> Algebra/Combinatorics; map_partitionWords,map_partitionWords_fst/snd,indepFun_partitionWords -> Probability |
| `Probability.PoissonWord.Relabel` | relabel,relabel_apply,length_relabel,relabel_nil -> Algebra/Combinatorics; map_relabel,measurePreserving_relabel -> Probability (small; could merge into PoissonWord Basic) |
| `Probability.PoissonWord.Thinning` | leftWord,rightWord,thinningEvent,thinningFiber,finite_thinningEvent,card_thinningFiber,length lemmas -> Algebra/Combinatorics (with Algebra.TaggedInterleavings); measure_thinningEvent*,choose_mul_weight_sum,map_leftWord*,map_rightWord,indepFun_leftWord_rightWord -> Probability |
| `Probability.PoissonWord.WeightedGrowth` | sum_length_succ,sum_length_succ_le_of_append_singleton,sum_length_le_pow_of_weighted_growth are deterministic finite-sum bounds over words -> Analysis/Real (or Algebra for sum_length_succ); integrable_and_integral_le_of_weighted_growth,eq_zero_of_weighted_growth_of_profile_eq_zero -> Probability |
| `Probability.Sampling.CompressionSampling` | sum_nonempty_subsets_*,inverse_half_power,binomial_error_le_*,exp_eighth_sub_one_le_quarter,ratio_le_of_sample_count,error_le_quarter_*,sampleCount,sampleCount_bounds -> Analysis/Real (scalar parameter arithmetic); integral_error_le_binomial,integral_norm_sum_*,exists_*_half_sampleCount (existence of a good sample on a probability space) -> Probability/Sampling; 'Compression' names the paper section, base could become FiniteExpansionSampling |
| `Probability.Sampling.ViableSubspaceRandomSampling` | basisEmbedding, randomSubspace, finrank_randomSubspace, isCloseTo_of_net, tensorProd_mono_left, starProjection_map_linearIsometry -> Analysis/Subspace; unitaryHaar_* bounds stay Probability/Sampling |
| `Representation.Partition.Alternant` | alternant,elemSymm,indic,alternant_eq_sum..alternant_geom,geomPoly,geomVand,eval_one_*,prod_Ioi_eq_vand -> Algebra/Polynomial (commutative ring, no labels); shiftedPart_add_indic,sum_vand_add_indic,sum_weylFormula_add_indic (vertical-strip Pieri) -> Representation/Partition |
| `Representation.Partition.HookFormula` | log_factorial_sub_nonneg,log_factorial_sub_le,mul_log_add_sub_bounds -> Analysis/Real (Stirling-type bounds); shiftedPart,rowPairs,hookFormula,entropyTerm,weylFormula and bounds -> Representation/Partition; imports nothing |
| `Representation.Partition.HookRecursion` | vand,vand_eq,vand_update_mul,exists_X_sq_mul_prod,sum_mul_prod_sub_one_div,sum_prod_add_one_div -> Algebra/Polynomial (Vandermonde and partial-fraction identities over ℝ); hookFormula recursions -> Representation/Partition |
| `Representation.Partition.ReplicaGammaIntegral` | orthant,orthMono,integrable*/integral_monomial*,Gamma_add_nat,Gamma_one_add_add_nat,risingPoly* -> Analysis/Calculus (Lebesgue integrals on the orthant, Gamma identities); alternant determinants,gammaIntegral,replicaWeight_eq_gammaIntegral -> Representation/Partition (no sites: replicaWeight is a function of a partition) |
| `Representation.Partition.ReplicaWeight` | Real.abs_log_Gamma_one_add_sub_le,log_mul_add_add_two_le,replicaConst,replicaRatio (scalar Gamma) -> Analysis/Real; replicaWeight of part vectors,marked ratio,entropy asymptotics -> Representation/Partition |
| `Representation.Partition.WeylRecursion` | sum_prod_add_one_div_eq_card (Lagrange-interpolation identity over ℝ) -> Algebra/Polynomial; weylFormula Pieri recursion on part vectors -> Representation/Partition |
| `Representation.Permutation.CentralLabelFunction` | Matrix.exists_eq_smul_of_commute_corner -> Algebra/Matrix (corner commutant is scalar); exists_eq_sum_labelProj_of_commute -> Representation/PermutationRepresentation |
| `Representation.Permutation.MergeDimensions` | dim_le_mul_dim_of_compatible(')pairAction,vecOfMatrix* -> Representation/PermutationRepresentation; merge_dim_le (subsystemPerm on disjoint regions Q E : Finset F) -> ManyBody/Replica |
| `Representation.Permutation.MergeMoment` | permOp_mul_labelProj,pairUnit*,pairUnitSpan,exists_trace_mul_eq,labelProj_mul_labelProj_eq_sum (two commuting actions) -> Representation/PermutationRepresentation; copyPerm_eq_mul_compl,merge_conditional_le,merge_moment_le (region Q : Finset F) -> ManyBody/Replica |
| `Representation.Permutation.SchurSurprisal` | Real.mul_exp_neg_mul_log_le_one -> Analysis/Real; label projector orthogonal resolution,labelEntropy,joint resolution with spectral projections -> Representation/Isotypic |
| `Representation.Replica.ExcitationCompression` | PosSemidef.re_dotProduct_sum_mulVec_le_card_sum (Cauchy-Schwarz over a finset) -> Analysis/Order; rest (defect cutoff, excitation components) needs only tensor-power + spectral-cutoff objects, kept with the Replica family |
| `Representation.Replica.SchurLabelCommutation` | commute_groupAlgebraRep_permOp_of_mem_center,permOp_of_eq_mul,commute_groupAlgebraRep_of_eq_mul,groupAlgebraRep_mulVec_eq_of_eq_mul -> Representation/Isotypic; subsystemPerm subset/disjoint/union lemmas -> ManyBody/Replica |
| `Representation.SymmetricGroup.BranchProbability` | eq_zero_of_mul_self_of_trace_eq_zero -> Algebra/Trace (duplicate of CoherentResolution.eq_zero_of_isHermitian_of_mul_self_of_trace); sub_one_div_le_two -> Analysis/Real; rest (removable-row branches of S_k labels,dim ratios) -> Representation/SymmetricGroup |
| `Representation.TensorPower.Action` | invariantSubspace,symProj,centralIdem center lemmas,copyPerm -> Representation/TensorPower; Config k ι,subsystemPerm (Q : Finset F),commute/union lemmas,symmetricSubspace -> ManyBody/Replica base module |
| `Representation.TensorPower.Rpow` | eq_unitary_conj_diagonal,rpow_eq_unitary_conj_diagonal -> Spectral (one matrix); tensorPow diagonal/unitary/rpow/trace,labelObservable norm -> Representation |
| `Representation.Twirl.ReplicaSpectralLaw` | specDensity,specNorm,measurable/integrable/positivity on the orthant -> Probability (random spectra density); specSample and integral_specSample_tensorPow (twirl = label function, Weyl character) -> Representation |
| `Spectral.Eigenvalue.HermitianExtremalEigenvalues` | min/maxEigenvalue and spectral shifts -> Spectral/Eigenvalue; Hermitian decompositions (exists_isHermitian_*), commute_of_commute_pow -> Algebra/Hermitian; one_sub_vecMulVec/diagonal_sub_vecMulVec PSD (normSq bounds) -> Analysis/Order |
| `Spectral.Eigenvalue.TailTraceNorm` | traceDistance_eq_rectangularTraceNorm -> Analysis/TraceNorm; descEigenvalue tails vs trace norm, trace distance, Ky Fan norm -> Spectral/Eigenvalue |
| `Spectral.Eigenvalue.TensorEnergyMinimum` | exists_unit_re_inner_le_of_tensor_energy -> Analysis/TensorProduct; exists_compression_min_eigenvalue_le_of_tensor_energy stays Spectral/Eigenvalue (Ritz compression) |
| `Spectral.Eigenvalue.VariationalBound` | commutatorCLM_pow_* identities -> Analysis (with GaussianFilter.CommutatorSeries); ground-energy lower bounds stay Spectral/Eigenvalue; docstring lists a sitePerm theorem not in the file |
| `Spectral.Filter.ExponentialWeights` | sub_mul_exp_weight_le, posPart_sub_mul_exp_weight_le scalar -> Analysis/Real; norm_projection_conjugated_mul_projection_le, norm_weighted_projection_forcing_le -> Analysis/Norm; exp weights times low projection -> Spectral/Filter |
| `Spectral.Filter.FilterLocality` | kernelExponent, kernelTailConst, abs_spectralKernel_le_tail, integrable_inv_one_add_abs_sq, neg_mul_le_sub_mul_rpow scalar -> Analysis/SpectralFilter; filterIntegral localization under an abstract linear map on matrices and \|M\| -> Spectral/Filter |
| `Spectral.Filter.Gaussian.SpectralGap` | eigenvector_ground_or_gap -> Spectral/Gap (with GlobalGap); norm_sub_ground_le_of_coefficients stays in Spectral/GaussianFilter |
| `Spectral.Filter.SoftTruncationCoercivity` | softTruncation_centered_coercivity (Hermitian family, spectralProjectionGE) -> Spectral/Filter; softTruncation_reverse_cutoff_bounds(_of_scale) scalar -> Analysis/Real |
| `Spectral.Filter.SoftTruncationHardResidual` | softTruncation_remainder_le_hard_remainder scalar -> Analysis/Real; PosSemidef.norm_softTruncation_residual_apply_le -> Spectral/Filter |
| `Spectral.Filter.SoftTruncationHeatExpansion` | softTruncationHeatCoefficient, softTruncation_eq_sum_heat, sum_abs_softTruncationHeatCoefficient_le scalar -> Analysis/Real; IsHermitian.cfc_softTruncation_eq_sum_heat -> Spectral/Filter; imports MatrixBernsteinInputs |
| `Spectral.Filter.SoftTruncationHighProjection` | softTruncation_high_energy_floor, softTruncation_reverse_barrier_margin scalar -> Analysis/Real; IsHermitian.smul_spectralProjectionGE_le_softTruncation -> Spectral/Filter |
| `Spectral.Filter.UntrimmedTensorFamilyPowers` | word_filter_error_ceil_log_le -> Analysis/Real; IsSpectralProjector.viability_word_power_ceil_log stays Spectral/Filter |
| `Spectral.Gap.OrthogonalKernelGap` | exists_pos_mul_norm_le_of_mem_orthogonal_ker -> Spectral/Gap; Nat.exists_pos_forall_of_eventually (pure real/Nat quantifier lemma) -> Analysis/Real |
| `Spectral.Gap.WeightedPositiveKernel` | kernel and Loewner lemmas stay Analysis/Order (its norm-gap transfer was deleted, having no user) |
| `Spectral.LowEnergy.Coordinates` | spectralSpanLE_eq_of_eigenbases, exists_canonical_isometric_spectral_data, spectralSpanLE_ne_bot_of_mem_spectrum -> Spectral/LowEnergy; two_le_local_dimension_of_two_spectral_values mentions site configurations Fin L -> Fin q -> ManyBody/Sites |
| `Spectral.LowEnergy.RitzCompression` | orthogonalCompression and its symmetry -> Analysis/Isometry; ritzSubspace of the compression -> Spectral/LowEnergy |
| `Spectral.Radius.UpperTriangularBound` | IsStrictlyUpperTriangular, IsDiag mul_apply, wordProd, add_pow_eq_sum_wordProd -> Algebra/Matrix; power bounds (Wolf 8.103/8.105) stay Spectral/Radius |

## Single-lemma modules

119 modules of one lemma were merged into the module that defines their object,
each inside a `section` named after it, with its Mathlib imports added to the target. A merge
was done only when the module imports nothing but the target and the target's imports, no
importer of it is imported by the target, the target leaves no top-level `variable` or open
namespace behind, and the target stays below 1000 lines. Two modules of namespace
aliases (`Entropy/VonNeumann/Aliases`, `Entropy/MutualInformation/Basic`) were kept apart,
since merging them would put the aliases in scope for every importer of the definitions. The
others are listed with the proposed target: 102 import modules beyond the target and its
imports, 6 name no target, 6 have a target that leaves a top-level `variable`, 4 would make an
importer import its own importer or cross a layer, 2 proposed merging into each other, and 2
would push the target past 1000 lines.

### Merged

| Former module | Now in |
|---|---|
| `Algebra.FinCastAddNatAdd` | `Algebra.Combinatorics.FinSum` |
| `Algebra.FinsetComplSubtype` | `Algebra.Combinatorics.FinSum` |
| `Algebra.HermitianUnitaryConjugacy` | `Spectral.Eigenvalue.HermitianSpectrumMultiplicity` |
| `Algebra.LowFrequencySelection` | `Algebra.Word.LowFrequencyWordPartition` |
| `Algebra.MatrixAlgEquiv` | `Algebra.MatrixAlgebra.SkolemNoether` |
| `Algebra.MatrixDependentEntries` | `Algebra.Matrix.MatrixReindex` |
| `Algebra.MatrixIsometryKronecker` | `Algebra.Unitary.MatrixUnitaryBetween` |
| `Algebra.MatrixKroneckerExt` | `Algebra.Kronecker.KroneckerEmbed` |
| `Algebra.MatrixPolynomialInterpolation` | `Algebra.Polynomial.MatrixPolynomialDegree` |
| `Algebra.MatrixPosDefTransport` | `Algebra.Unitary.MatrixUnitaryBetween` |
| `Algebra.MatrixProductIntertwine` | `Algebra.Matrix.OrderedMatrixAction` |
| `Algebra.MatrixRankKronecker` | `Algebra.Matrix.MatrixRankBaseChange` |
| `Algebra.MatrixReindexUnitary` | `Algebra.Unitary.MatrixUnitaryBetween` |
| `Algebra.OperatorBlock` | `Algebra.OperatorSchmidt.Basic` |
| `Algebra.OperatorSchmidtProducts` | `Algebra.OperatorSchmidt.Bounds` |
| `Algebra.PermutationMatrixUnitary` | `Algebra.Unitary.MatrixUnitaryBetween` |
| `Algebra.PiProductTrace` | `Algebra.Kronecker.KroneckerFactorPositivity` |
| `Algebra.PolynomialLinearFactor` | `Algebra.Polynomial.OrderedPolynomialGaps` |
| `Algebra.PolynomialTwoMarkerPower` | `Algebra.Polynomial.OrderedPolynomialGaps` |
| `Algebra.PureStateExpectation` | `Algebra.Matrix.MatrixTracePairing` |
| `Algebra.StabilizedWeightedTrace` | `Algebra.Matrix.MatrixStabilization` |
| `Algebra.StarSubalgebraUnitaryIntertwiner` | `Algebra.StarSubalgebra.IntertwinerIsometry` |
| `Algebra.SwapTrace` | `Channel.Entanglement.MaximallyEntangled` |
| `Algebra.TraceReindex` | `Algebra.Matrix.MatrixReindex` |
| `Algebra.WordCoefficient` | `Algebra.Word.WordMultiplicity` |
| `Analysis.AdaptiveBinaryProbability` | `Probability.Measure.AdaptiveSamplingProbability` |
| `Analysis.BootstrapFailureParameters` | `Probability.Sampling.ViableSubspaceBootstrap` |
| `Analysis.CfcScalarShift` | `Analysis.FunctionalCalculus.CfcConjugation` |
| `Analysis.CfcVectorNormOrder` | `Analysis.FunctionalCalculus.CfcConjugation` |
| `Analysis.CloseSubspaceEnergyTransfer` | `Analysis.Projection.ProjectedPositiveEnergy` |
| `Analysis.CommutingExponentialOrder` | `Analysis.Exponential.ExpConjugation` |
| `Analysis.ComplementProdKernel` | `Analysis.Projection.DetectabilityLemma` |
| `Analysis.ComplementProdPartition` | `Analysis.Projection.DetectabilityLemma` |
| `Analysis.CompressedInverseFloor` | `Analysis.Order.FloorPin` |
| `Analysis.ExponentialPolynomialAbsorption` | `Analysis.Real.FiniteExponentialRetainedMass` |
| `Analysis.FiniteFamilyImageCoordinates` | `Probability.Measurable.FiniteFamilyImageProjection` |
| `Analysis.FiniteProductUnionProbability` | `Probability.Measure.FiniteProductSectionProbability` |
| `Analysis.FiniteProductUpdateProbability` | `Probability.Measure.FiniteProductSectionProbability` |
| `Analysis.FiveMomentExponentialBound` | `Analysis.Real.FiniteExponentialRetainedMass` |
| `Analysis.GeometricDecay` | `Analysis.Real.GeometricOrderPolynomialBound` |
| `Analysis.GroundSpectrumMinimum` | `Spectral.Eigenvalue.GroundEnergyBounds` |
| `Analysis.HermitianEigenbasisFunctionalCalculus` | `Analysis.FunctionalCalculus.TraceCFC` |
| `Analysis.InterleavedTrimmingParameters` | `Analysis.Parameter.InterleavedTrimmingIteration` |
| `Analysis.IsometricIntertwiningCommute` | `Algebra.Unitary.MatrixUnitaryBetween` |
| `Analysis.IsometricLowerPin` | `Analysis.Order.InverseCompressionLowerPin` |
| `Analysis.IsometricProjection` | `Analysis.Isometry.IsometricCompression` |
| `Analysis.LogarithmicEnvelope` | `Analysis.Real.LogPowerAbsorption` |
| `Analysis.MatrixRangeOrthonormalBasis` | `Probability.Measurable.MatrixRangeFrameMeasurable` |
| `Analysis.MeanTreeLogFloorDeficit` | `Analysis.OperatorMean.MeanTreeLogFloorExp` |
| `Analysis.MeanTreeProjectionMassBound` | `Analysis.OperatorMean.MeanTreeProjectionLogBound` |
| `Analysis.NestedChebyshevViability` | `Spectral.LowEnergy.ChebyshevViability` |
| `Analysis.OptimizedPureErrorMass` | `Analysis.Real.OptimizedPureTraceError` |
| `Analysis.OrthonormalMatrixNorm` | `Analysis.Norm.KroneckerOperatorNorm` |
| `Analysis.PolarUnitaryCorrectionKronecker` | `Analysis.Isometry.PolarUnitaryCorrection` |
| `Analysis.PolynomialFilterDyadicGrowth` | `Analysis.Parameter.PolynomialFilterCounts` |
| `Analysis.PositiveFactorRepair` | `Analysis.Projection.HermitianFactorRepair` |
| `Analysis.ProbabilityEntropyGeometricTails` | `Entropy.Classical.ProbabilityEntropyRankTails` |
| `Analysis.ProjectionCalculus` | `Analysis.FunctionalCalculus.OrthogonalResolutionCfc` |
| `Analysis.QuadraticFormGap` | `Spectral.Gap.PositiveGapTransfer` |
| `Analysis.RandomRangeSubspaceDimension` | `Probability.Measurable.VariableRankSampleProjection` |
| `Analysis.RandomSubspaceProjection` | `Probability.Sampling.ViableSubspaceRandomSampling` |
| `Analysis.RectangularTraceNormTopology` | `Analysis.TraceNorm.RectangularTraceNorm` |
| `Analysis.ReplicaComponentUniformRate` | `Analysis.Real.ExcitationSubsetCounts` |
| `Analysis.ReplicaGoodConfigurationIndividualMergeMoment` | `ManyBody.Replica.Configuration.GoodConfigurationMergeMoment` |
| `Analysis.ReplicaGoodConfigurationSignedMoments` | `ManyBody.Replica.Configuration.GoodConfigurationSharpMoment` |
| `Analysis.ReplicaRegionalDensity` | `ManyBody.Replica.Configuration.GoodCopyDensity` |
| `Analysis.RootChannelWord` | `Analysis.Norm.RootChannel` |
| `Analysis.SoftTruncationOperatorBounds` | `Spectral.Filter.SoftHardTruncation` |
| `Analysis.SoftTruncationRestrictedResidual` | `Spectral.Filter.SoftTruncationHardResidual` |
| `Analysis.SoftTruncationScaledAccuracy` | `Spectral.Filter.SoftTruncationAccuracy` |
| `Analysis.SoftTruncationScaling` | `Analysis.Real.SoftTruncation` |
| `Analysis.SpectralCutoffMass` | `Spectral.Projection.ShiftedDensityTruncation` |
| `Analysis.SpectralProjectorPower` | `Analysis.FunctionalCalculus.ViableSubspaceSpectralProjector` |
| `Analysis.SpectralResidualGroundEnergy` | `Spectral.Perturbation.ResidualComparison` |
| `Analysis.SpectralWindowCount` | `Analysis.Parameter.SpectralWindowPrecision` |
| `Analysis.SurprisalFunctionalCalculus` | `Analysis.Logarithm.CfcLogAdditive` |
| `Analysis.TwoSidedResidual` | `Spectral.Perturbation.ResidualComparison` |
| `Analysis.ViableNodeLeafCount` | `Analysis.Parameter.ViableNodeParameters` |
| `Analysis.ViableProjectionNonzero` | `Analysis.Subspace.ViableSubspace` |
| `Analysis.ViableSubspaceDimension` | `Analysis.Subspace.ViableSubspace` |
| `Analysis.ViableSubspaceNestedEnlargement` | `Probability.Sampling.ViableSubspaceMinimum` |
| `Analysis.ViableSubspaceOrder` | `Analysis.Subspace.ViableSubspace` |
| `Analysis.ViableSubspaceProjectionEvent` | `Probability.Measurable.ViableSubspaceTensorProjectionMeasurable` |
| `Analysis.ViableSubspaceSharpErrorReduction` | `Analysis.Subspace.ViableSubspaceErrorReduction` |
| `Analysis.ViableSubspaceSymmetry` | `Analysis.Subspace.ViableSubspace` |
| `Analysis.ViableSubspaceUnitApproximation` | `Analysis.Subspace.ViableSubspace` |
| `Analysis.ViableTrimmingRadius` | `Analysis.Parameter.ViableRefinementParameters` |
| `Analysis.ViableTrimmingRank` | `Analysis.Parameter.ViableRefinementParameters` |
| `Analysis.WeightedTraceExponential` | `Analysis.TraceInequality.WeightedTraceHolder` |
| `Channel.FaithfulMarginalWhitenedChoi` | `Entropy.Renyi.MarginalSupportWhitenedChoi` |
| `Channel.GaugeConjugation` | `Channel.KrausMap.KrausGauge` |
| `Channel.SchmidtMarginalAction` | `Channel.Schmidt.Trimming` |
| `Entropy.CompressedTypicalRegionalMarginal` | `ManyBody.Entropy.Typical.CompressedTypicalSiteCoordinates` |
| `Entropy.CompressedTypicalRegionalTail` | `ManyBody.Replica.CompressedTypicalCommonRetainedMass` |
| `Entropy.CompressedTypicalSiteEntropy` | `ManyBody.Entropy.Typical.CompressedTypicalSiteCoordinates` |
| `Entropy.CompressedTypicalSiteNorm` | `ManyBody.Entropy.Typical.CompressedTypicalSiteCoordinates` |
| `Entropy.IidSchurExponentialMoments` | `Representation.SchurWeyl.IidSchurSignedMoments` |
| `Entropy.PatchNormalizedFirstVariation` | `ManyBody.Entropy.Filter.PatchStationarity` |
| `Entropy.RegionConditionalInformationSum` | `ManyBody.Entropy.RegionConditionalInformation` |
| `Entropy.RegionEntropyContinuity` | `ManyBody.Entropy.MutualInformationPerturbation` |
| `Entropy.SSAEqualityCharacterization` | `Entropy.StrongSubadditivity.MarkovChain` |
| `Entropy.SelectedSchmidtEntropy` | `Entropy.Typical.PureCompression` |
| `Entropy.TripartiteTrace` | `Entropy.VonNeumann.Entropy` |
| `Entropy.ViableSampling.StoppedHalfSamplingRank` | `ManyBody.Subspace.Sampling.CanonicalHalfSamplingDimension` |
| `Entropy.ViableSampling.ViableHalfSamplingTrimming` | `ManyBody.Subspace.Sampling.RankUnitaryHalfSampling` |
| `Entropy.ViableSampling.ViableSubspaceReferenceTrimming` | `ManyBody.Subspace.Trimming` |
| `Kraus.MapIterate` | `Kraus.Transfer` |
| `Kraus.MultiBlockWord` | `Kraus.Word` |
| `Probability.ComplexGaussian.SourceTransportExpansion` | `Probability.Gaussian.ProductSourceTransport` |
| `QPF.Primitive` | `Kraus.PrimitiveFixedPoint.Assembly` |
| `Representation.BellInsertionRegisterCoordinates` | `ManyBody.Replica.Bell.InsertionCoordinates` |
| `Representation.GroupAlgebraProductCoordinates` | `Representation.Permutation.PermutationRepresentation` |
| `Representation.RegionalAuxiliaryLabels` | `ManyBody.Replica.Configuration.RegionalFiveFactorCoordinates` |
| `Representation.RegionalPhysicalVector` | `ManyBody.Replica.Configuration.RegionalFiveFactorCoordinates` |
| `Representation.ReplicaPinnedMetricUpper` | `ManyBody.Replica.Metric.Similarity` |
| `Representation.ReplicaTransport.LabelPreservation` | `ManyBody.Replica.BandMetric.States` |
| `Representation.SchmidtBellCommonCutoffs` | `ManyBody.Replica.Bell.SchmidtBellPhysicalWitness` |
| `Representation.SubsystemLabelExponential` | `ManyBody.Replica.Label.SubsystemLabelCoordinates` |
| `Representation.SymmetricProjectionCoordinates` | `ManyBody.Replica.Label.SubsystemTransport` |

### Not merged

| Module | Proposed target (classification note) |
|---|---|
| `Algebra.Hermitian.FrameOperator` | merge into QICLean.Analysis.Support.MatrixFamilySupportProjection: one theorem, sum of vecMulVec is PosDef iff span = ⊤ (same Gram-of-a-family object) |
| `Algebra.Hermitian.IdempotentEndomorphism` | merge into QICLean.Algebra.Hermitian.OrthogonalProjection; one lemma P (P x) = P x, norm-free |
| `Algebra.Hermitian.ProjectionRangeIsometry` | merge into QICLean.Algebra.Hermitian.OrthogonalProjection: one lemma, a star projection has an isometric range parametrization |
| `Algebra.Polynomial.MatrixPolynomialParameter` | merge into QICLean.Algebra.Polynomial.MatrixPolynomialDegree: one interpolation lemma combining degree and interpolation |
| `Algebra.Unitary.UnitaryTraceZero` | merge into QICLean.Algebra.Unitary.MatrixUnitaryBetween: one theorem, a unitary with zero trace pairing against a Hermitian matrix |
| `Algebra.Word.OneWindowWordPartition` | merge into QICLean.Algebra.Word.LowFrequencyWordPartition: one-window case of the same partition theorem |
| `Analysis.Calculus.DifferentiableInnerAction` | one theorem (Hermitian generator of a differentiable family of inner actions); keep in Analysis/Calculus or merge into a matrix-derivative module |
| `Analysis.Convexity.ConvexHullCompact` | one theorem IsCompact.convexHull (Mathlib objects); merge into an Analysis/Convexity module or keep; arguably upstream to Mathlib |
| `Analysis.FunctionalCalculus.RealPowerIntertwine` | one lemma PSD rpow intertwine; merge into QICLean.Analysis.FunctionalCalculus.MatrixPowers; imports Entropy.ConditionalMovement.LogCompression only for proof |
| `Analysis.Isometry.EuclideanReindex` | one lemma (inner expectation invariant under coordinate relabelling); merge into an Isometry or reindex module; no defining module in QICLean |
| `Analysis.Isometry.PositiveProjectionCompression` | one lemma: posdef compression by isometry Z; merge into QICLean.Analysis.Isometry.IsometricCompression; imports Entropy.ConditionalMovement.LogCompression only for proof |
| `Analysis.Isometry.ProjectionIntertwiningNorm` | one lemma norm through isometric intertwiner; merge into QICLean.Analysis.Isometry.IsometricDomainExtension |
| `Analysis.Logarithm.CfcLogListProduct` | merge into QICLean.Analysis.Logarithm.CfcLogAdditive (log of commuting product, list version); imports OperatorMean.FiniteTree only for posDef_listProd_ofFn in the proof |
| `Analysis.Norm.PrincipalSubmatrixNorm` | one lemma l2 op norm of principal submatrix; merge into an Analysis/Norm matrix module (e.g. QICLean.Analysis.Norm.BlockDiagonalNorm) |
| `Analysis.Norm.SquaredTriangle` | one inequality in a seminormed group (Mathlib object); merge into a general Analysis/Norm vector-norm module (e.g. QICLean.Analysis.Projection.OverlapTriangle) |
| `Analysis.Norm.UnitNormalizationDistance` | one normed-space inequality; imported only by the aggregator; merge into a vector-norm host or delete |
| `Analysis.OperatorMean.GeometricMeanIntertwine` | one lemma geomMean_intertwine; merge into QICLean.Analysis.OperatorMean.WeightedGeometricMean (defines geomMean) |
| `Analysis.OperatorMean.MeanTreeExponentialLowerNorm` | merge into QICLean.Analysis.OperatorMean.MeanTreeMultibandLowerNorm; one explicit-rate corollary |
| `Analysis.OperatorMean.MeanTreeIntertwine` | one lemma eval_intertwine; merge into QICLean.Analysis.OperatorMean.FiniteTree (defines MeanTree.eval) |
| `Analysis.Order.HermitianTracePower` | merge into QICLean.Spectral.Eigenvalue.HermitianSpectrumMultiplicity: one lemma trace(A^k) = ∑ eigenvalue^k |
| `Analysis.Parameter.RoughLowerCoefficient` | merge into QICLean.ManyBody.Replica.LowDefect.RegionalRoughLowerThree (sole consumer): one scalar inequality |
| `Analysis.Projection.InvariantTensorWordPower` | merge into QICLean.Analysis.Subspace.ViableSubspaceTensor (defines IsViable); one theorem on Hilbert tensor product M ⊗ R, words of operators |
| `Analysis.Projection.ProjectedTrialSpaceEnergy` | one lemma IsCloseTo.map_starProjection_energy_le; merge into QICLean.Analysis.Projection.ProjectedPositiveEnergy |
| `Analysis.Projection.Residual` | one lemma star-projection residual; merge into QICLean.Analysis.Projection.Geometry; imports DetectabilityLemma only for proof |
| `Analysis.Subspace.ViableSubspaceSharpTensorReduction` | two sharp variants; merge with the map_of_tensor_decomposition part of QICLean.Analysis.FunctionalCalculus.ViableSubspaceSpectralProjector |
| `Analysis.Support.LogJensen` | merge into QICLean.Analysis.FunctionalCalculus.SpectralQuadraticForm (vector-state Jensen for cfc; one theorem adding support hypothesis) |
| `Channel.ConditionalExpectation.StarSubalgebraConditionalExpectation` | merge into QICLean.Channel.ConditionalExpectation.PositiveConditionalExpectationDirectSum; one theorem (CPTP conditional expectation onto any matrix star subalgebra) |
| `Channel.Gluing.BoundaryDensitySelection` | merge into QICLean.Channel.Gluing.BoundaryDensityMinimizer: one corollary (max-eigenvector of the minimizer) of its existence theorem |
| `Channel.Gluing.LeadingEigenvectorBounds` | merge into QICLean.Channel.Gluing.LeadingEigenvector: one choice-independent form of its theorem |
| `Channel.KrausMap.KrausFamilyDilation` | merge into QICLean.Channel.KrausMap.KrausFamilyEncoding: one theorem (unitary dilation of a TP Kraus family) built from embed/prod |
| `Channel.KrausMap.KrausFamilyTraceNorm` | merge into QICLean.Channel.KrausMap.KrausFamilyDilation (or KrausFamily): one trace-norm contraction corollary of Channel.RectangularTraceNormContraction for TP families |
| `Channel.KrausMap.SingleKraus` | merge into QICLean.Channel.KrausMap.KrausCPTP, which defines singleKrausMap; two identities (composition, trace adjoint) |
| `Channel.OperatorMean.LeafStateIntertwine` | one lemma on traceAdjoint of leafMap; merge into QICLean.Channel.OperatorMean.LeafStates; imports Channel.SingleKraus only for proof |
| `Channel.PartialTrace.MarginalRank` | merge into QICLean.Channel.PartialTrace.MarginalSupportAbsorption: one rank inequality rank rho <= rank marginals product proved from its support projections |
| `Channel.Positive.PositiveFunctional` | merge into QICLean.Algebra.Matrix.MatrixTracePairing: statement (positive normalized functional = trace pairing with density) needs only matrices/PSD/trace; proof imports Channel.Schwarz.TwoPositive (positive maps) and would need an algebraic proof |
| `Entropy.Classical.SurprisalProductMoment` | merge into QICLean.Channel.Schmidt.SurprisalMoment (defines surprisalMoment; one product identity) |
| `Entropy.MutualInformation.Basic` | namespaced alias plus congr; merge into the module defining mutualInformation (QICLean.Entropy.VonNeumann.Entropy, itself an Entropy-layer module) |
| `Entropy.MutualInformation.EffectMutualInformation` | one theorem (binary relative entropy <= mutual information) plus kernel helper; merge into QICLean.Entropy.Relative.EffectRelativeEntropy (defines binaryRelativeEntropy) |
| `Entropy.MutualInformation.OperatorSchmidt` | one theorem (I <= log operator-Schmidt rank); merge into QICLean.Entropy.MutualInformation.MutualInformation, or keep to avoid Channel.MarginalSupportWhitenedChoi import there |
| `Entropy.MutualInformation.PhysicalBufferUniform` | merge into QICLean.Entropy.MutualInformation.PhysicalBuffer; one uniform-parameter corollary, statement mentions quantumRelativeEntropy and partial traces |
| `Entropy.MutualInformation.ProductMarginals` | merge into QICLean.Entropy.MutualInformation.MutualInformation: one identity, relative entropy to product of marginals = mutual information |
| `Entropy.Typical.IidSurprisalMomentExponential` | main theorem plus exp_smul_sub_smul_one_eq_cfc (Analysis/FunctionalCalculus); merge into QICLean.Entropy.Typical.IidSurprisal |
| `Entropy.VonNeumann.Aliases` | alias-only module (0 decls besides aliases) of _root_.vonNeumannEntropy and quantumRelativeEntropy defined in QICLean.Entropy.VonNeumann.Entropy; move that definition to Entropy/VonNeumann and fold these aliases into it |
| `Entropy.VonNeumann.PureMarginalRank` | merge into QICLean.Channel.Schmidt.MaximalOverlap (home of partialTraceRight_vecMulVec_eq); one rank identity; imports Entropy.Bipartite only for proof (partialTraceLeft_vecMulVec_eq_map_conj, which should move down to Channel.PartialTrace) |
| `Kraus.IrreducibleAction` | merge into QICLean.Channel.Irreducible.InvariantProjection, which defines IsIrreducibleFamily; one equivalence with Matrix.IsIrreducibleAction plus its two directions |
| `Kraus.TraceFactorGauge` | merge into QICLean.Channel.KrausMap.KrausGauge (tpGauge of a family); two lemmas; KrausGauge is itself family-level and belongs in Kraus |
| `Kraus.TracePairing` | merge into QICLean.Kraus.Transfer (with MapIterate); one identity ∑_σ abs(tr(B† A_σ))² = re of a mapLM^n expression |
| `ManyBody.Entropy.AGSPRegionalEntropy` | merge into QICLean.ManyBody.Entropy.RegionEntropy (regionEntropy); one theorem transporting Channel.AGSPFavorableEntropy to sites; imports FilterPrefix only for cutVector_toEuclideanLin (a Sites lemma) |
| `ManyBody.Entropy.Cut.PositiveLocalLift` | merge into QICLean.ManyBody.Sites.Support: one lemma, IsSupportedOn PSD operator has PSD local lift with norm bound; imports Entropy.SupportedMarginalTails/FilterMoment only for proof |
| `ManyBody.Entropy.Cut.RegionPureApproximationTail` | merge with QICLean.ManyBody.Entropy.Cut.RegionTraceNorm (both: pure-state error of regional reductions); one lemma on descending eigenvalue tails of regionState; imports Entropy.RegionEntropy only for proof |
| `ManyBody.Entropy.Cut.RegionTraceNorm` | merge into QICLean.ManyBody.Sites.RegionState (or together with RegionPureApproximationTail): one trace-norm contraction of regional pure-state reduction |
| `ManyBody.Entropy.Cut.RegionalRightContraction` | merge into QICLean.ManyBody.Sites.OperatorSchmidtRank: one operatorSchmidtRank bound for right contraction across nested regions |
| `ManyBody.Entropy.Cut.RightLocalLift` | merge into QICLean.ManyBody.Sites.Support: one lemma, operator on the complement cut factor is IsSupportedOn the complement |
| `ManyBody.Entropy.Cut.SupportedOperatorAlgebra` | merge into QICLean.Algebra.Kronecker.KroneckerEmbed (or the Kronecker module): kronecker_one_mul_one_kronecker_comm is pure Kronecker algebra, no sites despite title |
| `ManyBody.Entropy.Cut.SupportedOperatorSchmidtWords` | merge into QICLean.ManyBody.Sites.OperatorSchmidtRank: one bound on operatorSchmidtRank of ordered products of supported operators; imports Entropy.FilterChainEnergy only for proof |
| `ManyBody.Replica.BandMetric.Integrated` | one theorem; merge into QICLean.ManyBody.Replica.BandMetric.IntegratedEntropy (integrated entropy gain of the same TransportData) |
| `ManyBody.Replica.BandMetric.RootCompression` | one theorem on rootPath; merge into QICLean.ManyBody.Replica.BandMetric.RootMetricFloor (both about the transport root) |
| `ManyBody.Replica.Bell.CompressedInverseNorm` | merge into QICLean.ManyBody.Replica.Bell.PinnedTreeAction (with BellPinnedProductAction and BellPinnedCompressedPowers: one chain of one-theorem modules about replica metrics acting on the Bell pin); objects replicaMetric,regions,op norm |
| `ManyBody.Replica.Bell.MetricFactorPositivity` | merge into QICLean.ManyBody.Replica.Bell.PinnedMetricCoordinates (defines the Bell metric factor); one positivity theorem; adds ReplicaLaminarBandMetrics import |
| `ManyBody.Replica.Bell.PhysicalRoughUpper` | merge into QICLean.ManyBody.Replica.Bell.SchmidtBellPhysicalWitness (defines the Schmidt-Bell prevector); one eventual upper bound over nested regions; imports Analysis.BellOverlapLogBound (Bell overlap in Analysis) |
| `ManyBody.Replica.Bell.PinnedCompressedPowers` | merge into QICLean.ManyBody.Replica.Bell.PinnedTreeAction; one rpow identity for the band product compressed to symmetric coordinates |
| `ManyBody.Replica.Bell.PinnedProductAction` | merge into QICLean.ManyBody.Replica.Bell.PinnedTreeAction; one ordered-product theorem for band roots on the Bell pin |
| `ManyBody.Replica.Bell.PrevectorRoughUpper` | one theorem; merge with QICLean.ManyBody.Replica.Bell.PrevectorSharpUpper (rough and sharp upper rate of the same supplied replica prevector on nested regions) |
| `ManyBody.Replica.Bell.PrevectorSharpUpper` | one theorem in enumerated coordinates; merge with ReplicaPrevectorRoughUpper (or into QICLean.ManyBody.Replica.Bell.SchmidtBellSharpUpper which it re-coordinatizes) |
| `ManyBody.Replica.Bell.SchmidtBellEnumeratedPrevector` | one theorem; merge into QICLean.ManyBody.Replica.Bell.SchmidtBellPrevectorOverlap (defines schmidtBellSitePrevector) |
| `ManyBody.Replica.Bell.SchmidtBellPhysicalWitness` | one theorem (nested regions,physical witness); merge with SchmidtBellCommonCutoffs; or into QICLean.ManyBody.Replica.Bell.SchmidtBellWitnessRange |
| `ManyBody.Replica.Bell.SchmidtBellSharpUpper` | one theorem; merge into QICLean.ManyBody.Replica.Bell.SelectedBellPostInverseTransport (it is the eventual rate built on that norm transport) |
| `ManyBody.Replica.Bell.SelectedBellPostInverseTransport` | one theorem (inverse-metric norm for selectedBellPost, regions); merge into QICLean.ManyBody.Replica.Bell.SelectedBellPostPin |
| `ManyBody.Replica.Bell.SymmetricPinProjection` | merge into QICLean.ManyBody.Replica.Bell.InsertionSymmetry (defines symProj_mul_bellInsertion); one star-projection theorem |
| `ManyBody.Replica.CompressedSite.CompressedTypicalExponentialDomination` | merge into QICLean.ManyBody.Replica.CompressedSite.CompressedTypicalExponential (its only input); one inequality form of the same exponential expectation; imports Algebra.FiniteKroneckerOrder (Loewner order in Algebra) |
| `ManyBody.Replica.CompressedTypicalCommonBellVector` | one theorem; merge into QICLean.ManyBody.Replica.CompressedTypicalCommonRetainedMass (same common-label-cutoff object); sites,Schur label cutoffs,Bell vector |
| `ManyBody.Replica.Configuration.FiveFactorAuxiliaryCoordinates` | merge into QICLean.ManyBody.Replica.Configuration.GoodConfigurationDensity (defines fiveFactorCopiesEquiv); copy permutation operators and group-algebra reps on k copies of five subsystems; subsystems, not sites |
| `ManyBody.Replica.Configuration.GoodPhysicalSupport` | merge into QICLean.ManyBody.Replica.Configuration.GoodCopyDensity: one symProj support identity for the same good-copy density (cutEquiv on copies) |
| `ManyBody.Replica.Configuration.PhysicalLabelMoment` | merge into QICLean.ManyBody.Replica.Configuration.GoodCopyDensity: one trace-exp labelEntropy identity on the same regional density (cutEquiv on copies); no importers |
| `ManyBody.Replica.Label.SubsystemLabelCommutation` | one theorem (labelObservables of nested/disjoint regions commute); merge into QICLean.Representation.Replica.SchurLabelCommutation; imports ReplicaSimilarity only for proof (labelObservable commute lemma) |
| `ManyBody.Replica.Label.SymmetricSupport` | one theorem on labelEntropy of subsystemPerm for a three-region partition; merge into QICLean.Representation.Permutation.MergeExponential (posSemidef_mergeDeficit, which it specializes) |
| `ManyBody.Replica.LowDefect.ComponentInverseRoughUniform` | one uniform version of ComponentInverseRough; merge into QICLean.ManyBody.Replica.LowDefect.ComponentInverseRough |
| `ManyBody.Replica.LowDefect.ComponentInverseSharpUniform` | one uniform version of ComponentInverseSharp; merge into QICLean.ManyBody.Replica.LowDefect.ComponentInverseSharp |
| `ManyBody.Replica.LowDefect.LowDefectRoughLowerPin` | merge into QICLean.ManyBody.Replica.LowDefect.InverseRoughCompression (its import source): one rough lower bound for the same low-defect projection |
| `ManyBody.Replica.LowDefect.LowDefectSharpLowerPin` | merge into QICLean.ManyBody.Replica.LowDefect.LowDefectSharpCompression (its import source): one sharp lower bound for the same projection |
| `ManyBody.Replica.LowDefect.LowDefectSymmetricCoordinates` | merge into QICLean.Representation.Replica.LowDefectProjection (defines replicaLowDefectProjection, replicaJointCopyPerm; that module is itself Representation/Bell content misplaced in Analysis); objects symProj,copyPerm,IrrepLabel,five fixed registers (no regions) |
| `ManyBody.Replica.LowDefect.RegionalRoughLowerThree` | one main theorem specializing RegionalRoughLowerNorm; merge into QICLean.ManyBody.Replica.LowDefect.RegionalRoughLowerNorm |
| `ManyBody.Replica.Metric.CutoffNorm` | one norm bound on replicaMetric; merge with ReplicaPinnedMetricUpper and ReplicaWholeInverse into one bounds module after QICLean.ManyBody.Replica.Metric.Similarity (cannot go into ReplicaMetric: needs Similarity and labelCutoff) |
| `ManyBody.Replica.Metric.SymmetricBandLabelPreservation` | one theorem; merge into QICLean.ManyBody.Replica.Metric.SymmetricMeanTreeProduct (same band product in fixed symmetric coordinates) |
| `ManyBody.Replica.Metric.SymmetricMeanTreeProduct` | one theorem; merge into QICLean.ManyBody.Replica.Metric.SymmetricBandCommute (same coordinates and mean-tree roots) |
| `ManyBody.Replica.Metric.WholeInverse` | one inverse-square bound on replicaMetric for P Y F; merge into a common bounds module with ReplicaMetricCutoffNorm,ReplicaPinnedMetricUpper (all after QICLean.ManyBody.Replica.Metric.Similarity) |
| `ManyBody.Entropy.RegionalResetEntropy` | merge into QICLean.ManyBody.Entropy.ReplicaSwap: one mutual-information comparison for the replica-swapped vector |
| `ManyBody.Subspace.ReferenceFilterTrimming` | merge into QICLean.ManyBody.Subspace.Trimming: one filter-then-trim closeness step |
| `ManyBody.Subspace.RegionalTensorMergeMeasurable` | one measurability lemma about regionTensorMerge (regions+measurable subspace families); merge beside QICLean.ManyBody.Subspace.RegionalTensorMerge in a ManyBody probability sublayer |
| `ManyBody.Subspace.Sampling.CanonicalHalfSamplingParentProbability` | merge into QICLean.ManyBody.Subspace.Sampling.CanonicalHalfSamplingParentProperties (or Parent): one probability theorem for canonicalHalfSamplingParent; sites+probability |
| `ManyBody.Subspace.Sampling.TrimmingProjectionMeasurable` | merge into QICLean.ManyBody.Subspace.Sampling.TrimmingMeasurable: one measurability lemma for the projection of trimSubspace |
| `Probability.Concentration.MatrixTraceNormIntegrability` | merge into the probability part of QICLean.Probability.Concentration.WeightedSourceError, which already holds aestronglyMeasurable_rectangularTraceNorm_sum; two integrability lemmas for trace norms of random finite matrix combinations; no importers in QICLean |
| `Probability.Haar.NativeRankUnitarySampling` | merge into QICLean.Probability.Haar.RankUnitaryUniformSampling: one theorem, the uniform failure bound transported along a coordinate relabelling e : Fin d = sigma |
| `Probability.PoissonWord.ExpectedOmission` | merge with PoissonWordTelescope and PoissonWordOmissionBound into one PoissonWord/Omission module: one theorem, expected norm of full minus retained chronological product under the Poisson word law; no importers in QICLean |
| `Probability.PoissonWord.PoissonWordOmissionBound` | merge with PoissonWordTelescope and PoissonWordExpectedOmission into one Omission module; one deterministic norm bound (contractive linear maps along a word), no measure; sole consumer ExpectedOmission |
| `Probability.PoissonWord.PoissonWordTelescope` | merge into the algebraic part of QICLean.Probability.PoissonWord.Partition (defines partitionWords), or with OmissionBound/ExpectedOmission into one Omission module; one identity for chronological products of linear maps, no measure |
| `Probability.PoissonWord.ShellGrowth` | merge into QICLean.Probability.PoissonWord.SpatialGrowth: one theorem specializing spatial growth to stretched-exponential ball kernels on a finite emetric label space kappa; imports Analysis.StretchedBallKernel |
| `Probability.Sampling.NestedSamplingNaturalParameters` | one scalar parameter lemma; merge into QICLean.Analysis.Parameter.NestedSamplingParameters; imports ViableSubspaceBootstrap only for proof |
| `Probability.Sampling.SampledWordImageBounds` | merge into QICLean.Probability.Sampling.SampledOperatorImage: one finrank bound for sampledWordImage; imports ViableNodeParameters for a Nat power bound |
| `Probability.Sampling.ViableSubspaceNestedCountSampling` | one lemma; merge with QICLean.Probability.Sampling.ViableSubspaceNestedSampling into QICLean.Probability.Sampling.ViableSubspaceDyadicBootstrap (its only importer chain) |
| `Probability.Sampling.ViableSubspaceNestedSampling` | one lemma (deterministic, sample U retained as data); merge into QICLean.Probability.Sampling.ViableSubspaceDyadicBootstrap |
| `Probability.Sampling.ViableSubspaceSamplingEvent` | one measurable Haar event; merge into the Haar part of QICLean.Probability.Sampling.ViableSubspaceRandomSampling |
| `Representation.Permutation.SchurLabelCutoff` | one theorem labelCutoff = spectralProjectionGE; merge into QICLean.Representation.Permutation.SchurLabelTails (defines labelCutoff) |
| `Representation.Replica.GoodAuxiliaryLabelBound` | merge into QICLean.Representation.Replica.GoodAuxiliaryMarginal: one labelEntropy bound on an excitation component; its public replicaGoodBadSplit duplicates the private one there |
| `Representation.SchurWeyl.IidSchurLabelExponential` | one theorem (Schur label cutoff tail for tensor powers); merge into QICLean.Representation.SchurWeyl.IidSchurSignedMoments; needs entropy+Schur labels so Representation |
| `Representation.TensorPower.PhysicalMergeHolder` | merge into QICLean.Representation.TensorPower.CompatiblePhysicalLabel (defines physicalMergeDeficit); one five-factor trace inequality; imports Analysis.WeightedTraceHolder |
| `Representation.TensorPower.ReplicaMeanIdentityExtension` | merge into QICLean.Representation.SchurWeyl.Commutant (defines siteOp = one-COPY operator, not a lattice site); kronecker,finKronecker,copies only |
| `Representation.YoungSubgroup.BadCopyLabelDimension` | merge into QICLean.Representation.YoungSubgroup.GroupedCopies (defines groupHom₂); one dimension bound for labels of the second Young factor on copyPerm; needs TensorPowerAction import there (no cycle: TensorPowerAction imports only LabelProjectors) |
| `Representation.YoungSubgroup.GoodAuxiliaryLabelCompression` | merge into QICLean.Representation.YoungSubgroup.GroupedLabelEntropy (defines the grouped-copy label entropy bound it compresses); one theorem |
| `Representation.YoungSubgroup.GoodAuxiliaryLabelEntropy` | merge into QICLean.Representation.YoungSubgroup.GroupedLabelEntropy; one whole-space bound for labelEntropy of groupHom₁ copies; "good/bad/auxiliary" are proof roles, not objects |
| `Spectral.Eigenvalue.CompressionEnergyInterval` | merge into QICLean.Spectral.Eigenvalue.CompressionEnergyBounds (one two-sided bound on the least eigenvalue of a compression) |
| `Spectral.Eigenvalue.DensityMaxEigenvector` | merge with QICLean.Spectral.Eigenvalue.DominantEigenvectorUniqueness (both single facts on top eigenvectors of a density matrix) |
| `Spectral.Eigenvalue.DominantEigenvectorUniqueness` | one theorem on uniqueness of a density-matrix eigenvector above 1/2; merge with QICLean.Spectral.Eigenvalue.DensityMaxEigenvector |
| `Spectral.Eigenvalue.EuclideanEigenvectorBasis` | one lemma on Mathlib eigenvectorBasis in Euclidean CLM form; merge into a Spectral/Eigenvalue basics module (e.g. QICLean.Spectral.Eigenvalue.AdjointEigenvalues) |
| `Spectral.Eigenvalue.ShiftedFilterClipping` | merge into QICLean.Spectral.Eigenvalue.ShiftedDensityClipping: one inverse-power bound for the same clipped eigenvalue form |
| `Spectral.Filter.ChebyshevGroundFilter` | merge into QICLean.Spectral.Filter.ChebyshevSpectralFilter (one Chebyshev filter from a ground vector and a gap of one Hermitian matrix) |
| `Spectral.Filter.EnergyWeightedPowerOrder` | one Loewner bound for H(1-H/A)^tau of one Hermitian matrix; merge into QICLean.Spectral.Filter.EnergyTruncation or keep beside it |
| `Spectral.Filter.Gaussian.UniformGroundEstimate` | merge into QICLean.Spectral.Filter.Gaussian.GroundEstimate; one uniform-constant version of the truncated ground estimate |
| `Spectral.Gap.GroundProjection` | merged into QICLean.Spectral.Filter.Gaussian.SpectralGap, which proves the ground-or-excited dichotomy it uses; one identity spectralProjectionGE = rank-one ground projection from a global gap |
| `Spectral.Gap.KernelSpectralGap` | merged into QICLean.Spectral.Gap.EigenvalueGap, the forms of the gap above a kernel; one lemma quadratic-form gap above the kernel of a Hermitian matrix |
| `Spectral.LowEnergy.Order` | merge into QICLean.Analysis.Order.LowEnergyPerturbation (defines spectralSpanLE); one monotonicity lemma |
| `Spectral.LowEnergy.RitzGroundSpaceCloseness` | merge into QICLean.Spectral.LowEnergy.RitzGroundSpace (sole importer target): one corollary for a trial space close to the ground space |
| `Spectral.Perturbation.ClusterNormPerturbation` | merge into QICLean.Spectral.Perturbation.BufferedSpectralNormPerturbation: one low-cluster stability theorem; imports ViableSubspaceDimension |
| `Spectral.Projection.ProjectionIntertwiner` | merge into QICLean.Spectral.Projection.ShiftedDensityTruncation (defines spectralProjectionGE); imports Entropy.ConditionalMovement.LogCompression only for cfc_intertwine, which belongs in Analysis/FunctionalCalculus |

## Modules that fail the strict check at the base revision

Moving a module makes `scripts/ci_lean_checks.py strict` elaborate it again with
warnings as errors and `autoImplicit` off. These modules fail that check with the same
errors at the base revision: single-letter variables bound automatically, deprecated
Mathlib names, and hypotheses the statement does not use. The move changes none of them
beyond import lines and module references (the last one is a target of a merge whose
merged module already had the error). Repairing them changes proofs or statements and is
left to a separate change.

- `QICLean/Algebra/Polynomial/ScalarPowerSumIdentity.lean`
- `QICLean/Analysis/Convexity/ConvexHullCompact.lean`
- `QICLean/Analysis/CyclicInequality/CyclicReciprocal.lean`
- `QICLean/Analysis/FixedPoint/BrouwerProduct.lean`
- `QICLean/Analysis/FunctionalCalculus/SpectralKronecker.lean`
- `QICLean/Analysis/Logarithm/LogCompression.lean`
- `QICLean/Analysis/Real/EulerAngles.lean`
- `QICLean/Channel/Choi/Jamiolkowski.lean`
- `QICLean/Channel/ChoiTypeMap/YamagamiPositivity.lean`
- `QICLean/Channel/Dilation/RadonNikodym.lean`
- `QICLean/Channel/Entanglement/PositiveMapDetection.lean`
- `QICLean/Channel/FixedPoint/Algebra/WedderburnDecomp.lean`
- `QICLean/Channel/OperatorSystem/Extension.lean`
- `QICLean/Channel/PartialTrace/ConditionalSkewSetup.lean`
- `QICLean/Channel/PartialTrace/ConditionalSkewStrip.lean`
- `QICLean/Channel/PartialTrace/MarginalPhaseFaithful.lean`
- `QICLean/Channel/PartialTrace/PartialTrace.lean`
- `QICLean/Channel/PartialTrace/PartialTraceDomination.lean`
- `QICLean/Channel/Schwarz/ChoiCompression.lean`
- `QICLean/Entropy/Conditional/Collision.lean`
- `QICLean/Entropy/Conditional/ConditionalPhase.lean`
- `QICLean/Entropy/Conditional/EntropyBounds.lean`
- `QICLean/Entropy/Conditional/FilterEntropy.lean`
- `QICLean/Entropy/Conditional/MarginalPhaseQuantities.lean`
- `QICLean/Entropy/Conditional/MarginalPhaseSingular.lean`
- `QICLean/Entropy/Conditional/Purification.lean`
- `QICLean/Entropy/Conditional/SingularInterpolation.lean`
- `QICLean/Entropy/Conditional/SkewPhase.lean`
- `QICLean/Entropy/Conditional/UnitaryCovariance.lean`
- `QICLean/Entropy/Relative/MarginalPhaseSupport.lean`
- `QICLean/Entropy/VonNeumann/ConditionalContinuity.lean`
- `QICLean/ManyBody/Replica/Metric/WholeInverse.lean`
- `QICLean/ManyBody/Replica/Symbol/CoherentLog.lean`
- `QICLean/Representation/SchurWeyl/SchurSectorMass.lean`
- `QICLean/Spectral/Jordan/FittingRange.lean`
- `QICLean/Spectral/Projection/KernelCompletion.lean`
- `QICLean/ManyBody/Replica/Bell/InsertionCoordinates.lean`
