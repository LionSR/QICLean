import Mathlib.Tactic.Linter.TextBased

/-! Text style audit of the entire owned replica prevector module. -/

set_option linter.hashCommand false

#eval Mathlib.Linter.TextBased.lintModules
  { toOptions := (({} : Lean.Options).setBool `linter.all true).setBool `linter.pythonStyle false,
    linterSets := {} }
  #[] #[`QICLean.Representation.ReplicaPrevector]
  .humanReadable false
