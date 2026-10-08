import Mathlib.Tactic.Linter.TextBased

/-! Text style verification of the weighted exponential trace inequalities source. -/

set_option linter.hashCommand false
#eval Mathlib.Linter.TextBased.lintModules
  { toOptions := (({} : Lean.Options).setBool `linter.all true).setBool `linter.pythonStyle false,
    linterSets := {} }
  #[] #[`QICLean.Analysis.OrthogonalResolution, `QICLean.Analysis.WeightedTraceHolder,
    `QICLean.Representation.GroupedLabelEntropy, `QICLean.Representation.MergeExponential,
    `QICLean.Representation.SchurSurprisal]
  .humanReadable false
