import Mathlib.Tactic.Linter.TextBased

/-! Text style audit of the entire owned production module. -/

set_option linter.hashCommand false

#eval Mathlib.Linter.TextBased.lintModules
  { toOptions := (({} : Lean.Options).setBool `linter.all true).setBool `linter.pythonStyle false,
    linterSets := {} }
  #[] #[`QICLean.Entropy.TypicalBellPinPowers]
  .humanReadable false
