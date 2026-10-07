import Mathlib.Tactic.Linter.TextBased

/-! Text style verification of the two physical replica source files. -/
set_option linter.hashCommand false
#eval Mathlib.Linter.TextBased.lintModules
  { toOptions := (({} : Lean.Options).setBool `linter.all true).setBool `linter.pythonStyle false,
    linterSets := {} }
  #[] #[`QICLean.Analysis.ReplicaDefect, `QICLean.Analysis.ReplicaExcitationDecomposition]
  .humanReadable false
