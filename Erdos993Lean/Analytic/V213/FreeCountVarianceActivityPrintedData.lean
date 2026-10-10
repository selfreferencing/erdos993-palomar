module

public import Erdos993Lean.Analytic.V213.FreeCountVarianceCaps

/-! Own transcription of the six-column activity table immediately before (22).
Six records, thirty scalar fields from twenty-four printed table cells.
These definitions assert no comparisons, identities, or coverage facts. -/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.FreeCountVariance.PrintedActivityData

inductive ActivityBand6 where
  | first
  | second
  | third
  | fourth
  | fifth
  | sixth
  deriving DecidableEq

noncomputable def a : ActivityBand6 → ℝ
  -- Data column 1, field a
  | .first => (1 / 3 : ℝ)
  -- Data column 2, field a
  | .second => (4 / 5 : ℝ)
  -- Data column 3, field a
  | .third => (263 / 200 : ℝ)
  -- Data column 4, field a
  | .fourth => (3 / 2 : ℝ)
  -- Data column 5, field a
  | .fifth => (7 / 4 : ℝ)
  -- Data column 6, field a
  | .sixth => (2 : ℝ)

noncomputable def b : ActivityBand6 → ℝ
  -- Data column 1, field b
  | .first => (4 / 5 : ℝ)
  -- Data column 2, field b
  | .second => (263 / 200 : ℝ)
  -- Data column 3, field b
  | .third => (3 / 2 : ℝ)
  -- Data column 4, field b
  | .fourth => (7 / 4 : ℝ)
  -- Data column 5, field b
  | .fifth => (2 : ℝ)
  -- Data column 6, field b
  | .sixth => (7 / 3 : ℝ)

noncomputable def H : ActivityBand6 → ℝ
  -- Data column 1, field H
  | .first => (7 / 8 : ℝ)
  -- Data column 2, field H
  | .second => (7 / 9 : ℝ)
  -- Data column 3, field H
  | .third => (663 / 926 : ℝ)
  -- Data column 4, field H
  | .fourth => (7 / 10 : ℝ)
  -- Data column 5, field H
  | .fifth => (15 / 22 : ℝ)
  -- Data column 6, field H
  | .sixth => (2 / 3 : ℝ)

noncomputable def K : ActivityBand6 → ℝ
  -- Data column 1, field K
  | .first => (4097 / 1500 : ℝ)
  -- Data column 2, field K
  | .second => (188909 / 60000 : ℝ)
  -- Data column 3, field K
  | .third => (1979 / 700 : ℝ)
  -- Data column 4, field K
  | .fourth => (4201 / 1600 : ℝ)
  -- Data column 5, field K
  | .fifth => (1111 / 450 : ℝ)
  -- Data column 6, field K
  | .sixth => (1192 / 525 : ℝ)

noncomputable def D : ActivityBand6 → ℝ
  -- Data column 1, field D
  | .first => (6 / 5 : ℝ)
  -- Data column 2, field D
  | .second => (6 / 5 : ℝ)
  -- Data column 3, field D
  | .third => (7 / 5 : ℝ)
  -- Data column 4, field D
  | .fourth => (8 / 5 : ℝ)
  -- Data column 5, field D
  | .fifth => (9 / 5 : ℝ)
  -- Data column 6, field D
  | .sixth => (21 / 10 : ℝ)

end Erdos993Lean.Analytic.V213.FreeCountVariance.PrintedActivityData

#check Erdos993Lean.Analytic.V213.FreeCountVariance.PrintedActivityData.a
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.PrintedActivityData.a
#check Erdos993Lean.Analytic.V213.FreeCountVariance.PrintedActivityData.b
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.PrintedActivityData.b
#check Erdos993Lean.Analytic.V213.FreeCountVariance.PrintedActivityData.H
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.PrintedActivityData.H
#check Erdos993Lean.Analytic.V213.FreeCountVariance.PrintedActivityData.K
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.PrintedActivityData.K
#check Erdos993Lean.Analytic.V213.FreeCountVariance.PrintedActivityData.D
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.PrintedActivityData.D
