import QICLean.Probability.ComplexGaussian.SourceTransportExpansion

set_option linter.hashCommand false
#print axioms QICLean.ComplexGaussian.sourceTransport_eq_sum_rankOne

run_cmd do
  let e ← Lean.getEnv
  let names := e.header.moduleNames.map (fun n ↦ Lean.Json.str n.toString)
  IO.FS.writeFile "imported-modules.json" (Lean.Json.compress (Lean.Json.arr names))
