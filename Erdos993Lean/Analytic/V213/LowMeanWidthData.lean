module

public import Erdos993Lean.Analytic.V213.LowMeanSeedGeometry

/-! The exact 43 printed Table-3 width pairs. -/

@[expose] public section

namespace Erdos993Lean.Analytic.V213

def lowMeanWidthPairs : List LowMeanWidthPair := [
  { certificate := 1, t := 23, r := 24, slope := 0 },
  { certificate := 1, t := 25, r := 26, slope := 0 },
  { certificate := 1, t := 28, r := 30, slope := 0 },
  { certificate := 1, t := 31, r := 33, slope := 0 },
  { certificate := 1, t := 34, r := 36, slope := 0 },
  { certificate := 1, t := 37, r := 39, slope := 0 },
  { certificate := 1, t := 40, r := 41, slope := 0 },
  { certificate := 1, t := 42, r := 43, slope := 0 },
  { certificate := 1, t := 44, r := 45, slope := 0 },
  { certificate := 1, t := 46, r := 47, slope := 0 },
  { certificate := 1, t := 48, r := 51, slope := 0 },
  { certificate := 2, t := 18, r := 19, slope := 1 },
  { certificate := 2, t := 22, r := 23, slope := 1 },
  { certificate := 3, t := 19, r := 21, slope := 2 },
  { certificate := 3, t := 24, r := 29, slope := 2 },
  { certificate := 10, t := 19, r := 20, slope := 3 },
  { certificate := 13, t := 19, r := 20, slope := 4 },
  { certificate := 19, t := 19, r := 20, slope := 5 },
  { certificate := 20, t := 19, r := 20, slope := 6 },
  { certificate := 20, t := 22, r := 23, slope := 6 },
  { certificate := 20, t := 25, r := 28, slope := 6 },
  { certificate := 23, t := 22, r := 24, slope := 7 },
  { certificate := 23, t := 25, r := 28, slope := 7 },
  { certificate := 23, t := 29, r := 32, slope := 7 },
  { certificate := 23, t := 33, r := 35, slope := 7 },
  { certificate := 23, t := 37, r := 38, slope := 7 },
  { certificate := 23, t := 39, r := 40, slope := 7 },
  { certificate := 23, t := 43, r := 44, slope := 7 },
  { certificate := 25, t := 21, r := 23, slope := 8 },
  { certificate := 25, t := 24, r := 26, slope := 8 },
  { certificate := 25, t := 27, r := 28, slope := 8 },
  { certificate := 25, t := 29, r := 30, slope := 8 },
  { certificate := 25, t := 37, r := 38, slope := 8 },
  { certificate := 26, t := 43, r := 48, slope := 9 },
  { certificate := 26, t := 50, r := 62, slope := 9 },
  { certificate := 27, t := 10, r := 11, slope := 10 },
  { certificate := 28, t := 21, r := 24, slope := 11 },
  { certificate := 28, t := 25, r := 28, slope := 11 },
  { certificate := 28, t := 29, r := 31, slope := 11 },
  { certificate := 28, t := 32, r := 34, slope := 11 },
  { certificate := 28, t := 36, r := 38, slope := 11 },
  { certificate := 28, t := 39, r := 40, slope := 11 },
  { certificate := 28, t := 41, r := 45, slope := 11 }]

def lowMeanWidthPairAt (i : ℕ) : LowMeanWidthPair :=
  lowMeanWidthPairs.getD i { certificate := 0, t := 0, r := 0, slope := 0 }

theorem lowMean_widthPairs_length : lowMeanWidthPairs.length = 43 := by decide +kernel

theorem lowMean_widthPairs_kernel : (List.range 43).all (fun i => lowMeanWidthPairCheck (lowMeanWidthPairAt i)) = true := by
  decide +kernel

theorem lowMean_widthPair_checked (i : ℕ) (hi : i < 43) : lowMeanWidthPairCheck (lowMeanWidthPairAt i) = true :=
  Erdos993Lean.F4Fast.forall_lt_of_range_all lowMean_widthPairs_kernel i hi

end Erdos993Lean.Analytic.V213
