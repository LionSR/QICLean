import QICLean.Representation.SchurLabelMoments
set_option linter.hashCommand false

namespace PermutationRepresentation
#print axioms re_trace_mul_exp_centered_labelEntropy_le
end PermutationRepresentation

namespace PermutationRepresentation
#print axioms re_trace_mul_exp_neg_centered_labelEntropy_le
end PermutationRepresentation

namespace TensorPower
#print axioms centered_labelEntropy_moments_le
end TensorPower

run_cmd do
  let e ← Lean.getEnv
  let ns := e.header.moduleNames.map (fun n ↦ Lean.Json.str n.toString)
  IO.FS.writeFile "imported-modules.json" (Lean.Json.compress (Lean.Json.arr ns))
