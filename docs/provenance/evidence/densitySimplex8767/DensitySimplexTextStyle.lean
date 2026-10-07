import Mathlib.Tactic.Linter.TextBased

/-! Text style audit of the two owned Lean files. -/

set_option linter.hashCommand false

#eval Mathlib.Linter.TextBased.lintModules
  { toOptions := (({} : Lean.Options).setBool `linter.all true).setBool `linter.pythonStyle false, linterSets := {} }
  #[] #[`QICLean.Analysis.DensitySimplex, `QICLeanTest.DensitySimplex]
  .humanReadable false
