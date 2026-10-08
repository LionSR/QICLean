from pathlib import Path
import subprocess,hashlib,json
p=Path('.lake/packages/mathlib')
assert subprocess.check_output(['git','-C',str(p),'rev-parse','HEAD'],text=True).strip()=='c55e6e786f49471c72fbddbec5415808896aec1e'
modules=['Mathlib']+['Mathlib.Algebra.BigOperators.Ring.Finset', 'Mathlib.Algebra.Star.BigOperators', 'Mathlib.Analysis.CStarAlgebra.Matrix', 'Mathlib.Analysis.Complex.Basic', 'Mathlib.Analysis.Matrix.MeasurableSpace', 'Mathlib.Analysis.Matrix.Normed', 'Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Measurable', 'Mathlib.Analysis.SpecialFunctions.Pow.Deriv', 'Mathlib.Analysis.SpecialFunctions.Pow.Real', 'Mathlib.Analysis.SpecialFunctions.Sqrt', 'Mathlib.Basic.Complex.BigOperators', 'Mathlib.LinearAlgebra.Matrix.Kronecker', 'Mathlib.LinearAlgebra.Multilinear.Basic', 'Mathlib.MeasureTheory.Constructions.Pi', 'Mathlib.MeasureTheory.Integral.Average', 'Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap', 'Mathlib.MeasureTheory.Integral.Pi', 'Mathlib.MeasureTheory.SpecificCodomains.Pi', 'Mathlib.Probability.Distributions.Gaussian.Fernique', 'Mathlib.Probability.Distributions.Gaussian.Multivariate', 'Mathlib.Probability.Moments.Variance', 'Mathlib.Tactic']
for n in modules:
 o=p/'.lake/build/lib/lean'/Path(n.replace('.','/')+'.olean');assert o.is_file(),o
 print(n,hashlib.sha256(o.read_bytes()).hexdigest())
print('Named pinned prebuilt guard passed:',len(modules),'modules')
