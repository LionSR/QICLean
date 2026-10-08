import QICLean.Representation.SchurLabelMomentBounds

run_cmd do
  let e ← Lean.getEnv
  let ns := e.header.moduleNames.map (fun n ↦ Lean.Json.str n.toString)
  IO.FS.writeFile "before-modules.json" (Lean.Json.compress (Lean.Json.arr ns))
