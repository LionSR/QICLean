import QICLean.Analysis.OrthonormalMatrixNorm

set_option linter.hashCommand false
#print axioms ContinuousLinearMap.norm_toMatrix_orthonormal

run_cmd do
  let e ← Lean.getEnv
  let names := e.header.moduleNames.map (fun n ↦ Lean.Json.str n.toString)
  IO.FS.writeFile "imported-modules.json" (Lean.Json.compress (Lean.Json.arr names))
