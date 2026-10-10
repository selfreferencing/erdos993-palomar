module

public import Mathlib

/-! Literal Row A Step 4 scales. -/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.VarianceResponse.RowA

noncomputable def discriminantGamma (r : Fin 6) : ℝ :=
  ![432000, 6912000, 2764800, 5760000, 92160000, 36864000] r

noncomputable def discriminantScale (r : Fin 6) : ℝ :=
  if r.val < 3 then 10^6 else 10^9

end Erdos993Lean.Analytic.V213.VarianceResponse.RowA

#check Erdos993Lean.Analytic.V213.VarianceResponse.RowA.discriminantGamma
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.RowA.discriminantGamma
#check Erdos993Lean.Analytic.V213.VarianceResponse.RowA.discriminantScale
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.RowA.discriminantScale
