import QICLean

set_option linter.hashCommand false

namespace Matrix
#print axioms rectangularTraceNorm_partialTraceRight_isometries
end Matrix

namespace OrthonormalBasis
#print axioms tensorProduct_basisChange
end OrthonormalBasis

namespace OrthonormalBasis
#print axioms tensorProduct_rankOne_basisChange
end OrthonormalBasis

namespace OrthonormalBasis
#print axioms rectangularTraceNorm_partialTrace_sum_rankOne_basis_eq
end OrthonormalBasis

namespace Matrix
#print axioms eq_sum_single_kronecker_submatrix
end Matrix

namespace Matrix
#print axioms rectangularTraceNorm_le_sum_submatrix
end Matrix

namespace Matrix
#print axioms submatrix_partialTraceRight
end Matrix

namespace Matrix
#print axioms integral_rectangularTraceNorm_le_sum_submatrix
end Matrix

namespace ProbabilityTheory
#print axioms integrable_rectangularTraceNorm_sum
end ProbabilityTheory

namespace ProbabilityTheory
#print axioms integrable_rectangularTraceNorm_sum_of_memLp_two
end ProbabilityTheory

run_cmd do
  let e ← Lean.getEnv
  let ns := e.header.moduleNames.map (fun n ↦ Lean.Json.str n.toString)
  IO.FS.writeFile "imported-modules.json" (Lean.Json.compress (Lean.Json.arr ns))
