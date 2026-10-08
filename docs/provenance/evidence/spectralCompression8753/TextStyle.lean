import Mathlib.Tactic.Linter.TextBased
set_option linter.hashCommand false
#eval Mathlib.Linter.TextBased.lintModules
  { toOptions := (({} : Lean.Options).setBool `linter.all true).setBool `linter.pythonStyle false,
    linterSets := {} }
  #[] #[`QICLean.Analysis.SpectralExponentialDrop,
        `QICLean.Analysis.InverseCompressionLowerBound]
  .humanReadable false
