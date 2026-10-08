import QICLean.Representation.SchurLabelMomentBounds
set_option linter.hashCommand false

namespace TensorPower
#print axioms log_centered_labelEntropy_moments_le
end TensorPower

namespace TensorPower
#print axioms log_centered_labelEntropy_moments_uniform
end TensorPower

run_cmd do
  let e ← Lean.getEnv
  let ns := e.header.moduleNames.map (fun n ↦ Lean.Json.str n.toString)
  IO.FS.writeFile "imported-modules.json" (Lean.Json.compress (Lean.Json.arr ns))
