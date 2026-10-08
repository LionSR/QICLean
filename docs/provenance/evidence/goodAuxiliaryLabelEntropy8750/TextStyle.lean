import Mathlib.Tactic.Linter.TextBased

/-! Text style verification of the good-auxiliary label observables source. -/

set_option linter.hashCommand false
#eval Mathlib.Linter.TextBased.lintModules
  { toOptions := (({} : Lean.Options).setBool `linter.all true).setBool `linter.pythonStyle false,
    linterSets := {} }
  #[] #[`QICLean.Representation.GoodAuxiliaryLabelEntropy]
  .humanReadable false
