module
public import Erdos993Lean.F4U.Light.Linking.Rational
@[expose] public section
set_option maxRecDepth 4096
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
namespace F4U.Light.Linking.Generated.DAG_E2_FULL_01
noncomputable section
def n00000_expression (x t : ℝ) : ℝ := x
def n00000_pair : RationalPair := ⟨[[0, 1]], [[1]]⟩
def n00001_expression (x t : ℝ) : ℝ := t
def n00001_pair : RationalPair := ⟨[[], [1]], [[1]]⟩
def n00002_expression (x t : ℝ) : ℝ := (29 : ℝ)/(20 : ℝ)
def n00002_pair : RationalPair := ⟨[[29]], [[20]]⟩
def n00003_expression (x t : ℝ) : ℝ := (8 : ℝ)/(5 : ℝ)
def n00003_pair : RationalPair := ⟨[[8]], [[5]]⟩
def n00004_expression (x t : ℝ) : ℝ := (195 : ℝ)/(128 : ℝ)
def n00004_pair : RationalPair := ⟨[[195]], [[128]]⟩
def n00005_expression (x t : ℝ) : ℝ := (1 : ℝ)/(1 : ℝ)
def n00005_pair : RationalPair := ⟨[[1]], [[1]]⟩
def n00006_expression (x t : ℝ) : ℝ := n00005_expression x t + n00000_expression x t
def n00006_pair : RationalPair := ⟨[[1, 1]], [[1]]⟩
def n00006_reduction : Reduction := ⟨rawAdd n00005_pair n00000_pair, n00006_pair, [[1]], 1⟩
theorem n00006_checked : checkReduction n00006_reduction = true := by decide
def n00007_expression (x t : ℝ) : ℝ := n00000_expression x t / n00006_expression x t
def n00007_pair : RationalPair := ⟨[[0, 1]], [[1, 1]]⟩
def n00007_reduction : Reduction := ⟨rawDiv n00000_pair n00006_pair, n00007_pair, [[1]], 1⟩
theorem n00007_checked : checkReduction n00007_reduction = true := by decide
def n00008_expression (x t : ℝ) : ℝ := n00005_expression x t + n00003_expression x t
def n00008_pair : RationalPair := ⟨[[13]], [[5]]⟩
def n00008_reduction : Reduction := ⟨rawAdd n00005_pair n00003_pair, n00008_pair, [[1]], 1⟩
theorem n00008_checked : checkReduction n00008_reduction = true := by decide
def n00009_expression (x t : ℝ) : ℝ := n00003_expression x t / n00008_expression x t
def n00009_pair : RationalPair := ⟨[[8]], [[13]]⟩
def n00009_reduction : Reduction := ⟨rawDiv n00003_pair n00008_pair, n00009_pair, [[5]], 1⟩
theorem n00009_checked : checkReduction n00009_reduction = true := by decide
def n00010_expression (x t : ℝ) : ℝ := (2 : ℝ)/(1 : ℝ)
def n00010_pair : RationalPair := ⟨[[2]], [[1]]⟩
def n00011_expression (x t : ℝ) : ℝ := n00009_expression x t / n00010_expression x t
def n00011_pair : RationalPair := ⟨[[4]], [[13]]⟩
def n00011_reduction : Reduction := ⟨rawDiv n00009_pair n00010_pair, n00011_pair, [[2]], 1⟩
theorem n00011_checked : checkReduction n00011_reduction = true := by decide
def n00012_expression (x t : ℝ) : ℝ := n00005_expression x t - n00011_expression x t
def n00012_pair : RationalPair := ⟨[[9]], [[13]]⟩
def n00012_reduction : Reduction := ⟨rawSub n00005_pair n00011_pair, n00012_pair, [[1]], 1⟩
theorem n00012_checked : checkReduction n00012_reduction = true := by decide
def n00013_expression (x t : ℝ) : ℝ := n00009_expression x t * n00012_expression x t
def n00013_pair : RationalPair := ⟨[[72]], [[169]]⟩
def n00013_reduction : Reduction := ⟨rawMul n00009_pair n00012_pair, n00013_pair, [[1]], 1⟩
theorem n00013_checked : checkReduction n00013_reduction = true := by decide
def n00014_expression (x t : ℝ) : ℝ := n00003_expression x t - n00002_expression x t
def n00014_pair : RationalPair := ⟨[[3]], [[20]]⟩
def n00014_reduction : Reduction := ⟨rawSub n00003_pair n00002_pair, n00014_pair, [[5]], 1⟩
theorem n00014_checked : checkReduction n00014_reduction = true := by decide
def n00015_expression (x t : ℝ) : ℝ := n00014_expression x t ^ 2
def n00015_pair : RationalPair := ⟨[[9]], [[400]]⟩
def n00015_reduction : Reduction := ⟨rawPow n00014_pair 2, n00015_pair, [[1]], 1⟩
theorem n00015_checked : checkReduction n00015_reduction = true := by decide
def n00016_expression (x t : ℝ) : ℝ := n00013_expression x t * n00015_expression x t
def n00016_pair : RationalPair := ⟨[[81]], [[8450]]⟩
def n00016_reduction : Reduction := ⟨rawMul n00013_pair n00015_pair, n00016_pair, [[8]], 1⟩
theorem n00016_checked : checkReduction n00016_reduction = true := by decide
def n00017_expression (x t : ℝ) : ℝ := n00002_expression x t ^ 2
def n00017_pair : RationalPair := ⟨[[841]], [[400]]⟩
def n00017_reduction : Reduction := ⟨rawPow n00002_pair 2, n00017_pair, [[1]], 1⟩
theorem n00017_checked : checkReduction n00017_reduction = true := by decide
def n00018_expression (x t : ℝ) : ℝ := (8 : ℝ)/(1 : ℝ)
def n00018_pair : RationalPair := ⟨[[8]], [[1]]⟩
def n00019_expression (x t : ℝ) : ℝ := n00018_expression x t * n00017_expression x t
def n00019_pair : RationalPair := ⟨[[841]], [[50]]⟩
def n00019_reduction : Reduction := ⟨rawMul n00018_pair n00017_pair, n00019_pair, [[8]], 1⟩
theorem n00019_checked : checkReduction n00019_reduction = true := by decide
def n00020_expression (x t : ℝ) : ℝ := n00016_expression x t / n00019_expression x t
def n00020_pair : RationalPair := ⟨[[81]], [[142129]]⟩
def n00020_reduction : Reduction := ⟨rawDiv n00016_pair n00019_pair, n00020_pair, [[50]], 1⟩
theorem n00020_checked : checkReduction n00020_reduction = true := by decide
def n00021_expression (x t : ℝ) : ℝ := n00003_expression x t - n00000_expression x t
def n00021_pair : RationalPair := ⟨[[8, -5]], [[5]]⟩
def n00021_reduction : Reduction := ⟨rawSub n00003_pair n00000_pair, n00021_pair, [[1]], 1⟩
theorem n00021_checked : checkReduction n00021_reduction = true := by decide
def n00022_expression (x t : ℝ) : ℝ := n00021_expression x t / n00014_expression x t
def n00022_pair : RationalPair := ⟨[[32, -20]], [[3]]⟩
def n00022_reduction : Reduction := ⟨rawDiv n00021_pair n00014_pair, n00022_pair, [[5]], 1⟩
theorem n00022_checked : checkReduction n00022_reduction = true := by decide
def n00023_expression (x t : ℝ) : ℝ := n00000_expression x t - n00002_expression x t
def n00023_pair : RationalPair := ⟨[[-29, 20]], [[20]]⟩
def n00023_reduction : Reduction := ⟨rawSub n00000_pair n00002_pair, n00023_pair, [[1]], 1⟩
theorem n00023_checked : checkReduction n00023_reduction = true := by decide
def n00024_expression (x t : ℝ) : ℝ := n00023_expression x t / n00014_expression x t
def n00024_pair : RationalPair := ⟨[[-29, 20]], [[3]]⟩
def n00024_reduction : Reduction := ⟨rawDiv n00023_pair n00014_pair, n00024_pair, [[20]], 1⟩
theorem n00024_checked : checkReduction n00024_reduction = true := by decide
def n00025_expression (x t : ℝ) : ℝ := (5922933 : ℝ)/(100000000 : ℝ)
def n00025_pair : RationalPair := ⟨[[5922933]], [[100000000]]⟩
def n00026_expression (x t : ℝ) : ℝ := n00022_expression x t * n00025_expression x t
def n00026_pair : RationalPair := ⟨[[15794488, -9871555]], [[25000000]]⟩
def n00026_reduction : Reduction := ⟨rawMul n00022_pair n00025_pair, n00026_pair, [[12]], 1⟩
theorem n00026_checked : checkReduction n00026_reduction = true := by decide
def n00027_expression (x t : ℝ) : ℝ := (1640021 : ℝ)/(20000000 : ℝ)
def n00027_pair : RationalPair := ⟨[[1640021]], [[20000000]]⟩
def n00028_expression (x t : ℝ) : ℝ := n00024_expression x t * n00027_expression x t
def n00028_pair : RationalPair := ⟨[[-47560609, 32800420]], [[60000000]]⟩
def n00028_reduction : Reduction := ⟨rawMul n00024_pair n00027_pair, n00028_pair, [[1]], 1⟩
theorem n00028_checked : checkReduction n00028_reduction = true := by decide
def n00029_expression (x t : ℝ) : ℝ := n00026_expression x t + n00028_expression x t
def n00029_pair : RationalPair := ⟨[[-48269189, 45543440]], [[300000000]]⟩
def n00029_reduction : Reduction := ⟨rawAdd n00026_pair n00028_pair, n00029_pair, [[5000000]], 1⟩
theorem n00029_checked : checkReduction n00029_reduction = true := by decide
def n00030_expression (x t : ℝ) : ℝ := n00029_expression x t + n00020_expression x t
def n00030_pair : RationalPair := ⟨[[-6836151563381, 6473043583760]], [[42638700000000]]⟩
def n00030_reduction : Reduction := ⟨rawAdd n00029_pair n00020_pair, n00030_pair, [[1]], 1⟩
theorem n00030_checked : checkReduction n00030_reduction = true := by decide
def n00031_expression (x t : ℝ) : ℝ := n00007_expression x t / n00010_expression x t
def n00031_pair : RationalPair := ⟨[[0, 1]], [[2, 2]]⟩
def n00031_reduction : Reduction := ⟨rawDiv n00007_pair n00010_pair, n00031_pair, [[1]], 1⟩
theorem n00031_checked : checkReduction n00031_reduction = true := by decide
def n00032_expression (x t : ℝ) : ℝ := n00007_expression x t * n00001_expression x t
def n00032_pair : RationalPair := ⟨[[], [0, 1]], [[1, 1]]⟩
def n00032_reduction : Reduction := ⟨rawMul n00007_pair n00001_pair, n00032_pair, [[1]], 1⟩
theorem n00032_checked : checkReduction n00032_reduction = true := by decide
def n00033_expression (x t : ℝ) : ℝ := n00032_expression x t / n00010_expression x t
def n00033_pair : RationalPair := ⟨[[], [0, 1]], [[2, 2]]⟩
def n00033_reduction : Reduction := ⟨rawDiv n00032_pair n00010_pair, n00033_pair, [[1]], 1⟩
theorem n00033_checked : checkReduction n00033_reduction = true := by decide
def n00034_expression (x t : ℝ) : ℝ := n00031_expression x t + n00033_expression x t
def n00034_pair : RationalPair := ⟨[[0, 1], [0, 1]], [[2, 2]]⟩
def n00034_reduction : Reduction := ⟨rawAdd n00031_pair n00033_pair, n00034_pair, [[2, 2]], 1⟩
theorem n00034_checked : checkReduction n00034_reduction = true := by decide
def n00035_expression (x t : ℝ) : ℝ := n00005_expression x t - n00034_expression x t
def n00035_pair : RationalPair := ⟨[[2, 1], [0, -1]], [[2, 2]]⟩
def n00035_reduction : Reduction := ⟨rawSub n00005_pair n00034_pair, n00035_pair, [[1]], 1⟩
theorem n00035_checked : checkReduction n00035_reduction = true := by decide
def n00036_expression (x t : ℝ) : ℝ := n00000_expression x t * n00035_expression x t
def n00036_pair : RationalPair := ⟨[[0, 2, 1], [0, 0, -1]], [[2, 2]]⟩
def n00036_reduction : Reduction := ⟨rawMul n00000_pair n00035_pair, n00036_pair, [[1]], 1⟩
theorem n00036_checked : checkReduction n00036_reduction = true := by decide
def n00037_expression (x t : ℝ) : ℝ := n00005_expression x t + n00036_expression x t
def n00037_pair : RationalPair := ⟨[[2, 4, 1], [0, 0, -1]], [[2, 2]]⟩
def n00037_reduction : Reduction := ⟨rawAdd n00005_pair n00036_pair, n00037_pair, [[1]], 1⟩
theorem n00037_checked : checkReduction n00037_reduction = true := by decide
def n00038_expression (x t : ℝ) : ℝ := n00036_expression x t / n00037_expression x t
def n00038_pair : RationalPair := ⟨[[0, -2, -1], [0, 0, 1]], [[-2, -4, -1], [0, 0, 1]]⟩
def n00038_reduction : Reduction := ⟨rawDiv n00036_pair n00037_pair, n00038_pair, [[-2, -2]], 1⟩
theorem n00038_checked : checkReduction n00038_reduction = true := by decide
def n00039_expression (x t : ℝ) : ℝ := n00005_expression x t - n00038_expression x t
def n00039_pair : RationalPair := ⟨[[-2, -2]], [[-2, -4, -1], [0, 0, 1]]⟩
def n00039_reduction : Reduction := ⟨rawSub n00005_pair n00038_pair, n00039_pair, [[1]], 1⟩
theorem n00039_checked : checkReduction n00039_reduction = true := by decide
def n00040_expression (x t : ℝ) : ℝ := n00000_expression x t * n00039_expression x t
def n00040_pair : RationalPair := ⟨[[0, -2, -2]], [[-2, -4, -1], [0, 0, 1]]⟩
def n00040_reduction : Reduction := ⟨rawMul n00000_pair n00039_pair, n00040_pair, [[1]], 1⟩
theorem n00040_checked : checkReduction n00040_reduction = true := by decide
def n00041_expression (x t : ℝ) : ℝ := n00005_expression x t + n00040_expression x t
def n00041_pair : RationalPair := ⟨[[-2, -6, -3], [0, 0, 1]], [[-2, -4, -1], [0, 0, 1]]⟩
def n00041_reduction : Reduction := ⟨rawAdd n00005_pair n00040_pair, n00041_pair, [[1]], 1⟩
theorem n00041_checked : checkReduction n00041_reduction = true := by decide
def n00042_expression (x t : ℝ) : ℝ := n00005_expression x t / n00041_expression x t
def n00042_pair : RationalPair := ⟨[[-2, -4, -1], [0, 0, 1]], [[-2, -6, -3], [0, 0, 1]]⟩
def n00042_reduction : Reduction := ⟨rawDiv n00005_pair n00041_pair, n00042_pair, [[1]], 1⟩
theorem n00042_checked : checkReduction n00042_reduction = true := by decide
def n00043_expression (x t : ℝ) : ℝ := (45775 : ℝ)/(1 : ℝ)
def n00043_pair : RationalPair := ⟨[[45775]], [[1]]⟩
def n00044_expression (x t : ℝ) : ℝ := n00000_expression x t - n00004_expression x t
def n00044_pair : RationalPair := ⟨[[-195, 128]], [[128]]⟩
def n00044_reduction : Reduction := ⟨rawSub n00000_pair n00004_pair, n00044_pair, [[1]], 1⟩
theorem n00044_checked : checkReduction n00044_reduction = true := by decide
def n00045_expression (x t : ℝ) : ℝ := (22238 : ℝ)/(1 : ℝ)
def n00045_pair : RationalPair := ⟨[[22238]], [[1]]⟩
def n00046_expression (x t : ℝ) : ℝ := n00045_expression x t * n00044_expression x t
def n00046_pair : RationalPair := ⟨[[-2168205, 1423232]], [[64]]⟩
def n00046_reduction : Reduction := ⟨rawMul n00045_pair n00044_pair, n00046_pair, [[2]], 1⟩
theorem n00046_checked : checkReduction n00046_reduction = true := by decide
def n00047_expression (x t : ℝ) : ℝ := n00043_expression x t + n00046_expression x t
def n00047_pair : RationalPair := ⟨[[761395, 1423232]], [[64]]⟩
def n00047_reduction : Reduction := ⟨rawAdd n00043_pair n00046_pair, n00047_pair, [[1]], 1⟩
theorem n00047_checked : checkReduction n00047_reduction = true := by decide
def n00048_expression (x t : ℝ) : ℝ := (65536 : ℝ)/(1 : ℝ)
def n00048_pair : RationalPair := ⟨[[65536]], [[1]]⟩
def n00049_expression (x t : ℝ) : ℝ := n00047_expression x t / n00048_expression x t
def n00049_pair : RationalPair := ⟨[[761395, 1423232]], [[4194304]]⟩
def n00049_reduction : Reduction := ⟨rawDiv n00047_pair n00048_pair, n00049_pair, [[1]], 1⟩
theorem n00049_checked : checkReduction n00049_reduction = true := by decide
def n00050_expression (x t : ℝ) : ℝ := (30825 : ℝ)/(1 : ℝ)
def n00050_pair : RationalPair := ⟨[[30825]], [[1]]⟩
def n00051_expression (x t : ℝ) : ℝ := (10297 : ℝ)/(1 : ℝ)
def n00051_pair : RationalPair := ⟨[[10297]], [[1]]⟩
def n00052_expression (x t : ℝ) : ℝ := n00051_expression x t * n00044_expression x t
def n00052_pair : RationalPair := ⟨[[-2007915, 1318016]], [[128]]⟩
def n00052_reduction : Reduction := ⟨rawMul n00051_pair n00044_pair, n00052_pair, [[1]], 1⟩
theorem n00052_checked : checkReduction n00052_reduction = true := by decide
def n00053_expression (x t : ℝ) : ℝ := n00050_expression x t + n00052_expression x t
def n00053_pair : RationalPair := ⟨[[1937685, 1318016]], [[128]]⟩
def n00053_reduction : Reduction := ⟨rawAdd n00050_pair n00052_pair, n00053_pair, [[1]], 1⟩
theorem n00053_checked : checkReduction n00053_reduction = true := by decide
def n00054_expression (x t : ℝ) : ℝ := n00053_expression x t / n00048_expression x t
def n00054_pair : RationalPair := ⟨[[1937685, 1318016]], [[8388608]]⟩
def n00054_reduction : Reduction := ⟨rawDiv n00053_pair n00048_pair, n00054_pair, [[1]], 1⟩
theorem n00054_checked : checkReduction n00054_reduction = true := by decide
def n00055_expression (x t : ℝ) : ℝ := (19913 : ℝ)/(1 : ℝ)
def n00055_pair : RationalPair := ⟨[[19913]], [[1]]⟩
def n00056_expression (x t : ℝ) : ℝ := (13978 : ℝ)/(1 : ℝ)
def n00056_pair : RationalPair := ⟨[[13978]], [[1]]⟩
def n00057_expression (x t : ℝ) : ℝ := n00056_expression x t * n00044_expression x t
def n00057_pair : RationalPair := ⟨[[-1362855, 894592]], [[64]]⟩
def n00057_reduction : Reduction := ⟨rawMul n00056_pair n00044_pair, n00057_pair, [[2]], 1⟩
theorem n00057_checked : checkReduction n00057_reduction = true := by decide
def n00058_expression (x t : ℝ) : ℝ := n00055_expression x t + n00057_expression x t
def n00058_pair : RationalPair := ⟨[[-88423, 894592]], [[64]]⟩
def n00058_reduction : Reduction := ⟨rawAdd n00055_pair n00057_pair, n00058_pair, [[1]], 1⟩
theorem n00058_checked : checkReduction n00058_reduction = true := by decide
def n00059_expression (x t : ℝ) : ℝ := n00058_expression x t / n00048_expression x t
def n00059_pair : RationalPair := ⟨[[-88423, 894592]], [[4194304]]⟩
def n00059_reduction : Reduction := ⟨rawDiv n00058_pair n00048_pair, n00059_pair, [[1]], 1⟩
theorem n00059_checked : checkReduction n00059_reduction = true := by decide
def n00060_expression (x t : ℝ) : ℝ := (3161 : ℝ)/(1 : ℝ)
def n00060_pair : RationalPair := ⟨[[3161]], [[1]]⟩
def n00061_expression (x t : ℝ) : ℝ := (4340 : ℝ)/(1 : ℝ)
def n00061_pair : RationalPair := ⟨[[4340]], [[1]]⟩
def n00062_expression (x t : ℝ) : ℝ := n00061_expression x t * n00044_expression x t
def n00062_pair : RationalPair := ⟨[[-211575, 138880]], [[32]]⟩
def n00062_reduction : Reduction := ⟨rawMul n00061_pair n00044_pair, n00062_pair, [[4]], 1⟩
theorem n00062_checked : checkReduction n00062_reduction = true := by decide
def n00063_expression (x t : ℝ) : ℝ := n00060_expression x t + n00062_expression x t
def n00063_pair : RationalPair := ⟨[[-110423, 138880]], [[32]]⟩
def n00063_reduction : Reduction := ⟨rawAdd n00060_pair n00062_pair, n00063_pair, [[1]], 1⟩
theorem n00063_checked : checkReduction n00063_reduction = true := by decide
def n00064_expression (x t : ℝ) : ℝ := n00063_expression x t / n00048_expression x t
def n00064_pair : RationalPair := ⟨[[-110423, 138880]], [[2097152]]⟩
def n00064_reduction : Reduction := ⟨rawDiv n00063_pair n00048_pair, n00064_pair, [[1]], 1⟩
theorem n00064_checked : checkReduction n00064_reduction = true := by decide
def n00065_expression (x t : ℝ) : ℝ := n00034_expression x t ^ 2
def n00065_pair : RationalPair := ⟨[[0, 0, 1], [0, 0, 2], [0, 0, 1]], [[4, 8, 4]]⟩
def n00065_reduction : Reduction := ⟨rawPow n00034_pair 2, n00065_pair, [[1]], 1⟩
theorem n00065_checked : checkReduction n00065_reduction = true := by decide
def n00066_expression (x t : ℝ) : ℝ := n00010_expression x t - n00034_expression x t
def n00066_pair : RationalPair := ⟨[[4, 3], [0, -1]], [[2, 2]]⟩
def n00066_reduction : Reduction := ⟨rawSub n00010_pair n00034_pair, n00066_pair, [[1]], 1⟩
theorem n00066_checked : checkReduction n00066_reduction = true := by decide
def n00067_expression (x t : ℝ) : ℝ := (6 : ℝ)/(1 : ℝ)
def n00067_pair : RationalPair := ⟨[[6]], [[1]]⟩
def n00068_expression (x t : ℝ) : ℝ := (12 : ℝ)/(1 : ℝ)
def n00068_pair : RationalPair := ⟨[[12]], [[1]]⟩
def n00069_expression (x t : ℝ) : ℝ := n00068_expression x t * n00034_expression x t
def n00069_pair : RationalPair := ⟨[[0, 6], [0, 6]], [[1, 1]]⟩
def n00069_reduction : Reduction := ⟨rawMul n00068_pair n00034_pair, n00069_pair, [[2]], 1⟩
theorem n00069_checked : checkReduction n00069_reduction = true := by decide
def n00070_expression (x t : ℝ) : ℝ := n00065_expression x t - n00069_expression x t
def n00070_pair : RationalPair := ⟨[[0, -24, -23], [0, -24, -22], [0, 0, 1]], [[4, 8, 4]]⟩
def n00070_reduction : Reduction := ⟨rawSub n00065_pair n00069_pair, n00070_pair, [[1, 1]], 1⟩
theorem n00070_checked : checkReduction n00070_reduction = true := by decide
def n00071_expression (x t : ℝ) : ℝ := n00070_expression x t + n00068_expression x t
def n00071_pair : RationalPair := ⟨[[48, 72, 25], [0, -24, -22], [0, 0, 1]], [[4, 8, 4]]⟩
def n00071_reduction : Reduction := ⟨rawAdd n00070_pair n00068_pair, n00071_pair, [[1]], 1⟩
theorem n00071_checked : checkReduction n00071_reduction = true := by decide
def n00072_expression (x t : ℝ) : ℝ := n00034_expression x t * n00071_expression x t
def n00072_pair : RationalPair := ⟨[[0, 48, 72, 25], [0, 48, 48, 3], [0, 0, -24, -21], [0, 0, 0, 1]], [[8, 24, 24, 8]]⟩
def n00072_reduction : Reduction := ⟨rawMul n00034_pair n00071_pair, n00072_pair, [[1]], 1⟩
theorem n00072_checked : checkReduction n00072_reduction = true := by decide
def n00073_expression (x t : ℝ) : ℝ := n00067_expression x t * n00035_expression x t
def n00073_pair : RationalPair := ⟨[[6, 3], [0, -3]], [[1, 1]]⟩
def n00073_reduction : Reduction := ⟨rawMul n00067_pair n00035_pair, n00073_pair, [[2]], 1⟩
theorem n00073_checked : checkReduction n00073_reduction = true := by decide
def n00074_expression (x t : ℝ) : ℝ := n00073_expression x t * n00066_expression x t
def n00074_pair : RationalPair := ⟨[[24, 30, 9], [0, -18, -12], [0, 0, 3]], [[2, 4, 2]]⟩
def n00074_reduction : Reduction := ⟨rawMul n00073_pair n00066_pair, n00074_pair, [[1]], 1⟩
theorem n00074_checked : checkReduction n00074_reduction = true := by decide
def n00075_expression (x t : ℝ) : ℝ := n00072_expression x t / n00074_expression x t
def n00075_pair : RationalPair := ⟨[[0, 48, 72, 25], [0, 48, 48, 3], [0, 0, -24, -21], [0, 0, 0, 1]], [[96, 216, 156, 36], [0, -72, -120, -48], [0, 0, 12, 12]]⟩
def n00075_reduction : Reduction := ⟨rawDiv n00072_pair n00074_pair, n00075_pair, [[2, 4, 2]], 1⟩
theorem n00075_checked : checkReduction n00075_reduction = true := by decide
def n00076_expression (x t : ℝ) : ℝ := n00038_expression x t / n00010_expression x t
def n00076_pair : RationalPair := ⟨[[0, -2, -1], [0, 0, 1]], [[-4, -8, -2], [0, 0, 2]]⟩
def n00076_reduction : Reduction := ⟨rawDiv n00038_pair n00010_pair, n00076_pair, [[1]], 1⟩
theorem n00076_checked : checkReduction n00076_reduction = true := by decide
def n00077_expression (x t : ℝ) : ℝ := n00005_expression x t - n00076_expression x t
def n00077_pair : RationalPair := ⟨[[-4, -6, -1], [0, 0, 1]], [[-4, -8, -2], [0, 0, 2]]⟩
def n00077_reduction : Reduction := ⟨rawSub n00005_pair n00076_pair, n00077_pair, [[1]], 1⟩
theorem n00077_checked : checkReduction n00077_reduction = true := by decide
def n00078_expression (x t : ℝ) : ℝ := n00038_expression x t * n00038_expression x t
def n00078_pair : RationalPair := ⟨[[0, 0, 4, 4, 1], [0, 0, 0, -4, -2], [0, 0, 0, 0, 1]], [[4, 16, 20, 8, 1], [0, 0, -4, -8, -2], [0, 0, 0, 0, 1]]⟩
def n00078_reduction : Reduction := ⟨rawMul n00038_pair n00038_pair, n00078_pair, [[1]], 1⟩
theorem n00078_checked : checkReduction n00078_reduction = true := by decide
def n00079_expression (x t : ℝ) : ℝ := n00078_expression x t / n00068_expression x t
def n00079_pair : RationalPair := ⟨[[0, 0, 4, 4, 1], [0, 0, 0, -4, -2], [0, 0, 0, 0, 1]], [[48, 192, 240, 96, 12], [0, 0, -48, -96, -24], [0, 0, 0, 0, 12]]⟩
def n00079_reduction : Reduction := ⟨rawDiv n00078_pair n00068_pair, n00079_pair, [[1]], 1⟩
theorem n00079_checked : checkReduction n00079_reduction = true := by decide
def n00080_expression (x t : ℝ) : ℝ := n00077_expression x t - n00079_expression x t
def n00080_pair : RationalPair := ⟨[[48, 168, 176, 56, 5], [0, 0, -36, -56, -10], [0, 0, 0, 0, 5]], [[48, 192, 240, 96, 12], [0, 0, -48, -96, -24], [0, 0, 0, 0, 12]]⟩
def n00080_reduction : Reduction := ⟨rawSub n00077_pair n00079_pair, n00080_pair, [[-4, -8, -2], [0, 0, 2]], 1⟩
theorem n00080_checked : checkReduction n00080_reduction = true := by decide
def n00081_expression (x t : ℝ) : ℝ := n00059_expression x t * n00080_expression x t
def n00081_pair : RationalPair := ⟨[[-4244304, 28085352, 134729008, 152496504, 49655037, 4472960], [0, 0, 3183228, -27253624, -49212922, -8945920], [0, 0, 0, 0, -442115, 4472960]], [[201326592, 805306368, 1006632960, 402653184, 50331648], [0, 0, -201326592, -402653184, -100663296], [0, 0, 0, 0, 50331648]]⟩
def n00081_reduction : Reduction := ⟨rawMul n00059_pair n00080_pair, n00081_pair, [[1]], 1⟩
theorem n00081_checked : checkReduction n00081_reduction = true := by decide
def n00082_expression (x t : ℝ) : ℝ := (3 : ℝ)/(4 : ℝ)
def n00082_pair : RationalPair := ⟨[[3]], [[4]]⟩
def n00083_expression (x t : ℝ) : ℝ := (6 : ℝ)/(7 : ℝ)
def n00083_pair : RationalPair := ⟨[[6]], [[7]]⟩
def n00084_expression (x t : ℝ) : ℝ := n00039_expression x t + n00081_expression x t
def n00084_pair : RationalPair := ⟨[[197082288, 632065128, 638045488, 253159800, 49655037, 4472960], [0, 0, -97480068, -127916920, -49212922, -8945920], [0, 0, 0, 0, -442115, 4472960]], [[201326592, 805306368, 1006632960, 402653184, 50331648], [0, 0, -201326592, -402653184, -100663296], [0, 0, 0, 0, 50331648]]⟩
def n00084_reduction : Reduction := ⟨rawAdd n00039_pair n00081_pair, n00084_pair, [[-2, -4, -1], [0, 0, 1]], 1⟩
theorem n00084_checked : checkReduction n00084_reduction = true := by decide
def n00085_expression (x t : ℝ) : ℝ := (10 : ℝ)/(1 : ℝ)
def n00085_pair : RationalPair := ⟨[[10]], [[1]]⟩
def n00086_expression (x t : ℝ) : ℝ := n00085_expression x t * n00064_expression x t
def n00086_pair : RationalPair := ⟨[[-552115, 694400]], [[1048576]]⟩
def n00086_reduction : Reduction := ⟨rawMul n00085_pair n00064_pair, n00086_pair, [[2]], 1⟩
theorem n00086_checked : checkReduction n00086_reduction = true := by decide
def n00087_expression (x t : ℝ) : ℝ := n00049_expression x t + n00054_expression x t
def n00087_pair : RationalPair := ⟨[[3460475, 4164480]], [[8388608]]⟩
def n00087_reduction : Reduction := ⟨rawAdd n00049_pair n00054_pair, n00087_pair, [[4194304]], 1⟩
theorem n00087_checked : checkReduction n00087_reduction = true := by decide
def n00088_expression (x t : ℝ) : ℝ := n00038_expression x t * n00087_expression x t
def n00088_pair : RationalPair := ⟨[[0, -6920950, -11789435, -4164480], [0, 0, 3460475, 4164480]], [[-16777216, -33554432, -8388608], [0, 0, 8388608]]⟩
def n00088_reduction : Reduction := ⟨rawMul n00038_pair n00087_pair, n00088_pair, [[1]], 1⟩
theorem n00088_checked : checkReduction n00088_reduction = true := by decide
def n00089_expression (x t : ℝ) : ℝ := n00086_expression x t + n00088_expression x t
def n00089_pair : RationalPair := ⟨[[8833840, -363670, -29593315, -9719680], [0, 0, -956445, 9719680]], [[-16777216, -33554432, -8388608], [0, 0, 8388608]]⟩
def n00089_reduction : Reduction := ⟨rawAdd n00086_pair n00088_pair, n00089_pair, [[1048576]], 1⟩
theorem n00089_checked : checkReduction n00089_reduction = true := by decide
def n00090_expression (x t : ℝ) : ℝ := n00059_expression x t - n00064_expression x t
def n00090_pair : RationalPair := ⟨[[132423, 616832]], [[4194304]]⟩
def n00090_reduction : Reduction := ⟨rawSub n00059_pair n00064_pair, n00090_pair, [[2097152]], 1⟩
theorem n00090_checked : checkReduction n00090_reduction = true := by decide
def n00091_expression (x t : ℝ) : ℝ := n00085_expression x t * n00030_expression x t
def n00091_pair : RationalPair := ⟨[[-6836151563381, 6473043583760]], [[4263870000000]]⟩
def n00091_reduction : Reduction := ⟨rawMul n00085_pair n00030_pair, n00091_pair, [[10]], 1⟩
theorem n00091_checked : checkReduction n00091_reduction = true := by decide
def n00092_expression (x t : ℝ) : ℝ := n00083_expression x t + n00091_expression x t
def n00092_pair : RationalPair := ⟨[[-22269840943667, 45311305086320]], [[29847090000000]]⟩
def n00092_reduction : Reduction := ⟨rawAdd n00083_pair n00091_pair, n00092_pair, [[1]], 1⟩
theorem n00092_checked : checkReduction n00092_reduction = true := by decide
def n00093_expression (x t : ℝ) : ℝ := n00090_expression x t * n00092_expression x t
def n00093_pair : RationalPair := ⟨[[-2949039147283215141, -7736491575518249584, 27949462939004938240]], [[125187768975360000000]]⟩
def n00093_reduction : Reduction := ⟨rawMul n00090_pair n00092_pair, n00093_pair, [[1]], 1⟩
theorem n00093_checked : checkReduction n00093_reduction = true := by decide
def n00094_expression (x t : ℝ) : ℝ := n00089_expression x t + n00093_expression x t
def n00094_pair : RationalPair := ⟨[[137730287057366430282, 21841894130019359732, -463641088530328663003, -249113442046101503376, -27949462939004938240], [0, 0, -17222589144808215141, 137315590290081750416, 27949462939004938240]], [[-250375537950720000000, -500751075901440000000, -125187768975360000000], [0, 0, 125187768975360000000]]⟩
def n00094_reduction : Reduction := ⟨rawAdd n00089_pair n00093_pair, n00094_pair, [[8388608]], 1⟩
theorem n00094_checked : checkReduction n00094_reduction = true := by decide
def n00095_expression (x t : ℝ) : ℝ := n00038_expression x t * n00084_expression x t
def n00095_pair : RationalPair := ⟨[[0, -394164576, -1461212544, -1908156104, -1144365088, -352469874, -58600957, -4472960], [0, 0, 197082288, 827025264, 991359396, 479502564, 116759799, 13418880], [0, 0, 0, 0, -97480068, -127032690, -57716727, -13418880], [0, 0, 0, 0, 0, 0, -442115, 4472960]], [[-402653184, -2415919104, -5435817984, -5637144576, -2717908992, -603979776, -50331648], [0, 0, 603979776, 2415919104, 3019898880, 1207959552, 150994944], [0, 0, 0, 0, -301989888, -603979776, -150994944], [0, 0, 0, 0, 0, 0, 50331648]]⟩
def n00095_reduction : Reduction := ⟨rawMul n00038_pair n00084_pair, n00095_pair, [[1]], 1⟩
theorem n00095_checked : checkReduction n00095_reduction = true := by decide
def n00096_expression (x t : ℝ) : ℝ := n00075_expression x t * n00092_expression x t
def n00096_pair : RationalPair := ⟨[[0, -1068952365296016, 571514096199336, 2705667942623365, 1132782627158000], [0, -1068952365296016, 1105990278847344, 2108133121312359, 135933915258960], [0, 0, 534476182648008, -619804662254673, -951537406812720], [0, 0, 0, -22269840943667, 45311305086320]], [[2865320640000000, 6446971440000000, 4656146040000000, 1074495240000000], [0, -2148990480000000, -3581650800000000, -1432660320000000], [0, 0, 358165080000000, 358165080000000]]⟩
def n00096_reduction : Reduction := ⟨rawMul n00075_pair n00092_pair, n00096_pair, [[1]], 1⟩
theorem n00096_checked : checkReduction n00096_reduction = true := by decide
def n00097_expression (x t : ℝ) : ℝ := n00010_expression x t + n00096_expression x t
def n00097_pair : RationalPair := ⟨[[5730641280000000, 11824990514703984, 9883806176199336, 4854658422623365, 1132782627158000], [0, -5366933325296016, -6057311321152656, -757187518687641, 135933915258960], [0, 0, 1250806342648008, 96525497745327, -951537406812720], [0, 0, 0, -22269840943667, 45311305086320]], [[2865320640000000, 6446971440000000, 4656146040000000, 1074495240000000], [0, -2148990480000000, -3581650800000000, -1432660320000000], [0, 0, 358165080000000, 358165080000000]]⟩
def n00097_reduction : Reduction := ⟨rawAdd n00010_pair n00096_pair, n00097_pair, [[1]], 1⟩
theorem n00097_checked : checkReduction n00097_reduction = true := by decide
def n00098_expression (x t : ℝ) : ℝ := n00095_expression x t * n00097_expression x t
def n00098_pair : RationalPair := ⟨[[0, 1129407895169648640000000, 5952634700381442649435392, 13078497090679600452030720, 16199626249141926245638320, 12876197062745669204058888, 6928470964124285539311328, 2495444670435251602559072, 572043136606411256494065, 77963056202545101556400, 5066891379972647680000], [0, 0, -1057727499292787110564608, -5144663475179767272686976, -9287937958405321901149296, -8433445650148817482599624, -4567910659146657532163508, -1753352597511712263659824, -502513013035812302063127, -95813994841247096402640, -9525755794348577638400], [0, 0, 0, 246511775853981395282304, 1332783562516334681742288, 1946005672954617653392728, 909978622171766333496516, -42339613845836979047472, -114376298308246695435314, -25518963906538945178720, -405351310397811814400], [0, 0, 0, 0, -4388991206573971470096, -127074621524079659948760, -152605280908185391699292, 20797647164179459790384, 89383662946007994333822, 44667781317065119513760, 9323080139149671731200], [0, 0, 0, 0, 0, 0, 2170865609537843329356, -2121259884759267381040, 852012725465860547649, -1178233856428556377680, -4661540069574835865600], [0, 0, 0, 0, 0, 0, 0, 0, 9845830728809335705, -119644915395623111120, 202675655198905907200]], [[576865239438458880000000, 4470705605648056320000000, 14277414676101857280000000, 24300448211345080320000000, 23867799281766236160000000, 13736603514128302080000000, 4506759683112960000000000, 775162665495429120000000, 54081116197355520000000], [0, -144216309859614720000000, -1874812028174991360000000, -7787680732419194880000000, -14998496225399930880000000, -14890333993005219840000000, -7679518500024483840000000, -1910866105639895040000000, -180270387324518400000000], [0, 0, 0, 216324464789422080000000, 1514271253525954560000000, 3569353669025464320000000, 3569353669025464320000000, 1514271253525954560000000, 216324464789422080000000], [0, 0, 0, 0, 0, -108162232394711040000000, -396594852113940480000000, -396594852113940480000000, -108162232394711040000000], [0, 0, 0, 0, 0, 0, 0, 18027038732451840000000, 18027038732451840000000]]⟩
def n00098_reduction : Reduction := ⟨rawMul n00095_pair n00097_pair, n00098_pair, [[-2, -1], [0, 1]], 1⟩
theorem n00098_checked : checkReduction n00098_reduction = true := by decide
def n00099_expression (x t : ℝ) : ℝ := n00094_expression x t - n00098_expression x t
def n00099_pair : RationalPair := ⟨[[-317330581380172255369728, -3004382462181203713198464, -9219731958439258143570048, -11367145555296405683609664, -2286985756027076578414704, 8507927648466539743905240, 9639202613591309730344960, 4754932714964277607462576, 1223258938518493169780895, 154420353321088792205392, 7007276609677485639680], [0, 79332645345043063842432, 1823983083806703964036992, 6806607816599422737095808, 7727902612213466655801456, -1882614583888731727543320, -10551149435842569880365612, -8661020692307578211965616, -3157911493075685037878217, -528541057477442001491760, -30721470837818533427200], [0, 0, 0, -335764632546433991045952, -1672883197034996787368976, -1576578034374324097182264, 1934320265922318037215324, 4077912268442558875661808, 2452985852990251751802482, 600877007638003942848608, 48702023268998345093120], [0, 0, 0, 0, 4388991206573971470096, 156827994207749957830584, 136170740381719984906556, -374729843612548686180944, -580164178806339526114206, -251852349918463396217504, -33471416118449938370560], [0, 0, 0, 0, 0, 0, -2170865609537843329356, -358792952093115599264, 16441379439453528531951, 24976401521417039544144, 8686262732791546972160], [0, 0, 0, 0, 0, 0, 0, 0, -9845830728809335705, 119644915395623111120, -202675655198905907200]], [[576865239438458880000000, 4470705605648056320000000, 14277414676101857280000000, 24300448211345080320000000, 23867799281766236160000000, 13736603514128302080000000, 4506759683112960000000000, 775162665495429120000000, 54081116197355520000000], [0, -144216309859614720000000, -1874812028174991360000000, -7787680732419194880000000, -14998496225399930880000000, -14890333993005219840000000, -7679518500024483840000000, -1910866105639895040000000, -180270387324518400000000], [0, 0, 0, 216324464789422080000000, 1514271253525954560000000, 3569353669025464320000000, 3569353669025464320000000, 1514271253525954560000000, 216324464789422080000000], [0, 0, 0, 0, 0, -108162232394711040000000, -396594852113940480000000, -396594852113940480000000, -108162232394711040000000], [0, 0, 0, 0, 0, 0, 0, 18027038732451840000000, 18027038732451840000000]]⟩
def n00099_reduction : Reduction := ⟨rawSub n00094_pair n00098_pair, n00099_pair, [[-250375537950720000000, -500751075901440000000, -125187768975360000000], [0, 0, 125187768975360000000]], 1⟩
theorem n00099_checked : checkReduction n00099_reduction = true := by decide
def n00100_expression (x t : ℝ) : ℝ := n00082_expression x t + n00091_expression x t
def n00100_pair : RationalPair := ⟨[[-3638249063381, 6473043583760]], [[4263870000000]]⟩
def n00100_reduction : Reduction := ⟨rawAdd n00082_pair n00091_pair, n00100_pair, [[4]], 1⟩
theorem n00100_checked : checkReduction n00100_reduction = true := by decide
def n00101_expression (x t : ℝ) : ℝ := n00090_expression x t * n00100_expression x t
def n00101_pair : RationalPair := ⟨[[-481787855720102163, -1387008595771178512, 3992780419857848320]], [[17883966996480000000]]⟩
def n00101_reduction : Reduction := ⟨rawMul n00090_pair n00100_pair, n00101_pair, [[1]], 1⟩
theorem n00101_checked : checkReduction n00101_reduction = true := by decide
def n00102_expression (x t : ℝ) : ℝ := n00089_expression x t + n00101_expression x t
def n00102_pair : RationalPair := ⟨[[19796748391840204326, 3925847812972765676, -65046762615435880429, -35305839064460214768, -3992780419857848320], [0, 0, -2520866426795102163, 19334717385028821488, 3992780419857848320]], [[-35767933992960000000, -71535867985920000000, -17883966996480000000], [0, 0, 17883966996480000000]]⟩
def n00102_reduction : Reduction := ⟨rawAdd n00089_pair n00101_pair, n00102_pair, [[8388608]], 1⟩
theorem n00102_checked : checkReduction n00102_reduction = true := by decide
def n00103_expression (x t : ℝ) : ℝ := n00075_expression x t * n00100_expression x t
def n00103_pair : RationalPair := ⟨[[0, -174635955042288, 48752159457048, 375102911446195, 161826089594000], [0, -174635955042288, 136070136978192, 299791344830337, 19419130751280], [0, 0, 87317977521144, -78949815679239, -135933915258960], [0, 0, 0, -3638249063381, 6473043583760]], [[409331520000000, 920995920000000, 665163720000000, 153499320000000], [0, -306998640000000, -511664400000000, -204665760000000], [0, 0, 51166440000000, 51166440000000]]⟩
def n00103_reduction : Reduction := ⟨rawMul n00075_pair n00100_pair, n00103_pair, [[1]], 1⟩
theorem n00103_checked : checkReduction n00103_reduction = true := by decide
def n00104_expression (x t : ℝ) : ℝ := n00010_expression x t + n00103_expression x t
def n00104_pair : RationalPair := ⟨[[818663040000000, 1667355884957712, 1379079599457048, 682101551446195, 161826089594000], [0, -788633235042288, -887258663021808, -109540175169663, 19419130751280], [0, 0, 189650857521144, 23383064320761, -135933915258960], [0, 0, 0, -3638249063381, 6473043583760]], [[409331520000000, 920995920000000, 665163720000000, 153499320000000], [0, -306998640000000, -511664400000000, -204665760000000], [0, 0, 51166440000000, 51166440000000]]⟩
def n00104_reduction : Reduction := ⟨rawAdd n00010_pair n00103_pair, n00104_pair, [[1]], 1⟩
theorem n00104_checked : checkReduction n00104_reduction = true := by decide
def n00105_expression (x t : ℝ) : ℝ := n00095_expression x t * n00104_expression x t
def n00105_pair : RationalPair := ⟨[[0, 161343985024235520000000, 846054671884199784205056, 1848013932506831607432960, 2277199728721680806519760, 1805699402351982923436984, 973078426064783385615904, 351869363366109234651296, 81006206136404734856295, 11086493421912157365200, 723841625710378240000], [0, 0, -155425642354975895794944, -753133862816503484669568, -1352832385708436003021328, -1219175579618911237514232, -653673366892820891737644, -248736983661361620522832, -71097391877502136366161, -13591671801832328057520, -1360822256335511091200], [0, 0, 0, 37376824921429067897472, 201356102730180605963184, 296002952474867759056104, 142921353306063286213788, -1708239815988031292496, -15692512898316964347902, -3641479389515163596960, -57907330056830259200], [0, 0, 0, 0, -717034449724984495728, -19511066607550079992680, -24420252964580640242756, 1000268172251677112912, 12078711316006694190546, 6287113311230102787680, 1331868591307095961600], [0, 0, 0, 0, 0, 0, 354656766099316189908, -249446603204266768720, 188999765288004006807, -121319969600193768240, -665934295653547980800], [0, 0, 0, 0, 0, 0, 0, 0, 1608524484656690815, -19135572194574730160, 28953665028415129600]], [[82409319919779840000000, 638672229378293760000000, 2039630668014551040000000, 3471492601620725760000000, 3409685611680890880000000, 1962371930589757440000000, 643822811873280000000000, 110737523642204160000000, 7725873742479360000000], [0, -20602329979944960000000, -267830289739284480000000, -1112525818917027840000000, -2142642317914275840000000, -2127190570429317120000000, -1097074071432069120000000, -272980872234270720000000, -25752912474931200000000], [0, 0, 0, 30903494969917440000000, 216324464789422080000000, 509907667003637760000000, 509907667003637760000000, 216324464789422080000000, 30903494969917440000000], [0, 0, 0, 0, 0, -15451747484958720000000, -56656407444848640000000, -56656407444848640000000, -15451747484958720000000], [0, 0, 0, 0, 0, 0, 0, 2575291247493120000000, 2575291247493120000000]]⟩
def n00105_reduction : Reduction := ⟨rawMul n00095_pair n00104_pair, n00105_pair, [[-2, -1], [0, 1]], 1⟩
theorem n00105_checked : checkReduction n00105_reduction = true := by decide
def n00106_expression (x t : ℝ) : ℝ := n00102_expression x t - n00105_expression x t
def n00106_pair : RationalPair := ⟨[[-45611708294799830767104, -432656461080423799028352, -1329745843403196557652864, -1647416462580406366229952, -355913579043290922630672, 1188811385635541749129320, 1360633351163406990049280, 673379601428961446780368, 173694506552357583182985, 21989400848180090315056, 1001039515668212234240], [0, 11402927073699957691776, 266121350605883743433856, 998538021948337328156544, 1154748099240940339400208, -213590252549834203934760, -1468963375098851195766516, -1220820745863084275995088, -447431952960451895054031, -75196121561319371641680, -4388781548259790489600], [0, 0, 0, -50231771056963004435136, -251160473707981958195568, -248361051670878725311752, 253647627992245852459332, 569452299105346405094544, 346266455570038623828926, 85348542989445500406944, 6957431895571192156160], [0, 0, 0, 0, 717034449724984495728, 23813817437809048261512, 22507585851633022129508, -50477629267956480882992, -81245216376522295873458, -35641437502004668031072, -4781630874064276910080], [0, 0, 0, 0, 0, 0, -354656766099316189908, -113558162254227942752, 2232194772697651575993, 3480479653503874220592, 1240894676113078138880], [0, 0, 0, 0, 0, 0, 0, 0, -1608524484656690815, 19135572194574730160, -28953665028415129600]], [[82409319919779840000000, 638672229378293760000000, 2039630668014551040000000, 3471492601620725760000000, 3409685611680890880000000, 1962371930589757440000000, 643822811873280000000000, 110737523642204160000000, 7725873742479360000000], [0, -20602329979944960000000, -267830289739284480000000, -1112525818917027840000000, -2142642317914275840000000, -2127190570429317120000000, -1097074071432069120000000, -272980872234270720000000, -25752912474931200000000], [0, 0, 0, 30903494969917440000000, 216324464789422080000000, 509907667003637760000000, 509907667003637760000000, 216324464789422080000000, 30903494969917440000000], [0, 0, 0, 0, 0, -15451747484958720000000, -56656407444848640000000, -56656407444848640000000, -15451747484958720000000], [0, 0, 0, 0, 0, 0, 0, 2575291247493120000000, 2575291247493120000000]]⟩
def n00106_reduction : Reduction := ⟨rawSub n00102_pair n00105_pair, n00106_pair, [[-35767933992960000000, -71535867985920000000, -17883966996480000000], [0, 0, 17883966996480000000]], 1⟩
theorem n00106_checked : checkReduction n00106_reduction = true := by decide
def n00107_expression (x t : ℝ) : ℝ := n00042_expression x t * n00039_expression x t
def n00107_pair : RationalPair := ⟨[[-2, -2]], [[-2, -6, -3], [0, 0, 1]]⟩
def n00107_reduction : Reduction := ⟨rawMul n00042_pair n00039_pair, n00107_pair, [[-2, -4, -1], [0, 0, 1]], 1⟩
theorem n00107_checked : checkReduction n00107_reduction = true := by decide
def n00108_expression (x t : ℝ) : ℝ := n00107_expression x t + n00081_expression x t
def n00108_pair : RationalPair := ⟨[[-394164576, -2043970800, -4049115872, -4016195400, -2324445786, -865028950, -175802871, -13418880], [0, 0, 392042424, 1271452784, 1393759872, 748753340, 250969323, 31310720], [0, 0, 0, 0, -96595838, -134210150, -74724337, -22364800], [0, 0, 0, 0, 0, 0, -442115, 4472960]], [[-402653184, -2818572288, -7449083904, -9261023232, -5536481280, -1509949440, -150994944], [0, 0, 603979776, 2818572288, 4227858432, 2214592512, 352321536], [0, 0, 0, 0, -301989888, -704643072, -251658240], [0, 0, 0, 0, 0, 0, 50331648]]⟩
def n00108_reduction : Reduction := ⟨rawAdd n00107_pair n00081_pair, n00108_pair, [[1]], 1⟩
theorem n00108_checked : checkReduction n00108_reduction = true := by decide
def n00109_expression (x t : ℝ) : ℝ := n00010_expression x t * n00090_expression x t
def n00109_pair : RationalPair := ⟨[[132423, 616832]], [[2097152]]⟩
def n00109_reduction : Reduction := ⟨rawMul n00010_pair n00090_pair, n00109_pair, [[2]], 1⟩
theorem n00109_checked : checkReduction n00109_reduction = true := by decide
def n00110_expression (x t : ℝ) : ℝ := n00109_expression x t * n00083_expression x t
def n00110_pair : RationalPair := ⟨[[397269, 1850496]], [[7340032]]⟩
def n00110_reduction : Reduction := ⟨rawMul n00109_pair n00083_pair, n00110_pair, [[2]], 1⟩
theorem n00110_checked : checkReduction n00110_reduction = true := by decide
def n00111_expression (x t : ℝ) : ℝ := n00010_expression x t * n00108_expression x t
def n00111_pair : RationalPair := ⟨[[-394164576, -2043970800, -4049115872, -4016195400, -2324445786, -865028950, -175802871, -13418880], [0, 0, 392042424, 1271452784, 1393759872, 748753340, 250969323, 31310720], [0, 0, 0, 0, -96595838, -134210150, -74724337, -22364800], [0, 0, 0, 0, 0, 0, -442115, 4472960]], [[-201326592, -1409286144, -3724541952, -4630511616, -2768240640, -754974720, -75497472], [0, 0, 301989888, 1409286144, 2113929216, 1107296256, 176160768], [0, 0, 0, 0, -150994944, -352321536, -125829120], [0, 0, 0, 0, 0, 0, 25165824]]⟩
def n00111_reduction : Reduction := ⟨rawMul n00010_pair n00108_pair, n00111_pair, [[2]], 1⟩
theorem n00111_checked : checkReduction n00111_reduction = true := by decide
def n00112_expression (x t : ℝ) : ℝ := n00075_expression x t * n00083_expression x t
def n00112_pair : RationalPair := ⟨[[0, 48, 72, 25], [0, 48, 48, 3], [0, 0, -24, -21], [0, 0, 0, 1]], [[112, 252, 182, 42], [0, -84, -140, -56], [0, 0, 14, 14]]⟩
def n00112_reduction : Reduction := ⟨rawMul n00075_pair n00083_pair, n00112_pair, [[6]], 1⟩
theorem n00112_checked : checkReduction n00112_reduction = true := by decide
def n00113_expression (x t : ℝ) : ℝ := n00005_expression x t - n00112_expression x t
def n00113_pair : RationalPair := ⟨[[112, 204, 110, 17], [0, -132, -188, -59], [0, 0, 38, 35], [0, 0, 0, -1]], [[112, 252, 182, 42], [0, -84, -140, -56], [0, 0, 14, 14]]⟩
def n00113_reduction : Reduction := ⟨rawSub n00005_pair n00112_pair, n00113_pair, [[1]], 1⟩
theorem n00113_checked : checkReduction n00113_reduction = true := by decide
def n00114_expression (x t : ℝ) : ℝ := n00111_expression x t * n00113_expression x t
def n00114_pair : RationalPair := ⟨[[-44146432512, -309334303104, -913829124224, -1507371108480, -1559792039152, -1081686646568, -520120185612, -172035463106, -36781259480, -4464725607, -228120960], [0, 52029724032, 387815837376, 1164384881792, 1870567994176, 1815481330816, 1143917686552, 483735050702, 132581759148, 20605776520, 1323996160], [0, 0, -14978253888, -143216250528, -477759858192, -775211497984, -711147328464, -404505981708, -147511885992, -31087065071, -2697194880], [0, 0, 0, 394164576, 16941582912, 78836457120, 137306158440, 120763723412, 62390809120, 19247364464, 2504857600], [0, 0, 0, 0, 0, -392042424, -4942094628, -9816240722, -8792946496, -4531015213, -1077983360], [0, 0, 0, 0, 0, 0, 0, 96595838, 117409780, 229222792, 178918400], [0, 0, 0, 0, 0, 0, 0, 0, 0, 442115, -4472960]], [[-22548578304, -208574349312, -808930246656, -1722147667968, -2213988532224, -1781337686016, -897010630656, -272696868864, -45449478144, -3170893824], [0, 16911433728, 180388626432, 755377373184, 1636181213184, 2015279185920, 1452974014464, 601765183488, 131415932928, 11626610688], [0, 0, -2818572288, -47915728896, -249443647488, -586263035904, -701824499712, -439697276928, -135996112896, -16206790656], [0, 0, 0, 0, 4227858432, 36641439744, 102877888512, 119789322240, 59894661120, 10569646080], [0, 0, 0, 0, 0, 0, -2113929216, -9160359936, -10217324544, -3170893824], [0, 0, 0, 0, 0, 0, 0, 0, 352321536, 352321536]]⟩
def n00114_reduction : Reduction := ⟨rawMul n00111_pair n00113_pair, n00114_pair, [[1]], 1⟩
theorem n00114_checked : checkReduction n00114_reduction = true := by decide
def n00115_expression (x t : ℝ) : ℝ := n00114_expression x t - n00049_expression x t
def n00115_pair : RationalPair := ⟨[[-40053172992, -263820357312, -696208958048, -920258196192, -573517446688, -7057593896, 247167117996, 181845482662, 64002068452, 11533030965, 847842432], [0, 48959779392, 349331289792, 966050326016, 1317232459984, 894449150944, 196323764872, -118534149250, -95468210496, -26097515444, -2621202944], [0, 0, -14466596448, -133561662144, -416219172384, -584144296960, -384810949872, -86540856972, 26375842512, 18001839577, 2802173568], [0, 0, 0, 394164576, 16174096752, 70750292544, 106197307128, 64109247716, 10870582600, -2995103896, -1081687040], [0, 0, 0, 0, 0, -392042424, -4558351548, -7436045114, -3829849588, -488407441, -2019968], [0, 0, 0, 0, 0, 0, 0, 96595838, 53452600, 45714124, 59366912], [0, 0, 0, 0, 0, 0, 0, 0, 0, 442115, -4472960]], [[-22548578304, -208574349312, -808930246656, -1722147667968, -2213988532224, -1781337686016, -897010630656, -272696868864, -45449478144, -3170893824], [0, 16911433728, 180388626432, 755377373184, 1636181213184, 2015279185920, 1452974014464, 601765183488, 131415932928, 11626610688], [0, 0, -2818572288, -47915728896, -249443647488, -586263035904, -701824499712, -439697276928, -135996112896, -16206790656], [0, 0, 0, 0, 4227858432, 36641439744, 102877888512, 119789322240, 59894661120, 10569646080], [0, 0, 0, 0, 0, 0, -2113929216, -9160359936, -10217324544, -3170893824], [0, 0, 0, 0, 0, 0, 0, 0, 352321536, 352321536]]⟩
def n00115_reduction : Reduction := ⟨rawSub n00114_pair n00049_pair, n00115_pair, [[4194304]], 1⟩
theorem n00115_checked : checkReduction n00115_reduction = true := by decide
def n00116_expression (x t : ℝ) : ℝ := n00115_expression x t - n00054_expression x t
def n00116_pair : RationalPair := ⟨[[-34844675712, -212098930464, -476582968304, -395360297520, 208475292728, 752275018072, 734250984048, 385773833554, 117346509910, 19406486583, 1346052480], [0, 45053406432, 305006191296, 763223051072, 820606171336, 171863321776, -455938942448, -485826835738, -220373179482, -49431185510, -4447973120], [0, 0, -13815534288, -122050752048, -351071663832, -409530843904, -130582969824, 125295330612, 126874718388, 43113122389, 5348580480], [0, 0, 0, 394164576, 15197503512, 61622204400, 76676444400, 20274957692, -21785756780, -14847221236, -2742387200], [0, 0, 0, 0, 0, -392042424, -4070054928, -4987953062, -30475786, 1849380977, 496190080], [0, 0, 0, 0, 0, 0, 0, 96595838, -27930170, -91025318, 4010240], [0, 0, 0, 0, 0, 0, 0, 0, 0, 442115, -4472960]], [[-22548578304, -208574349312, -808930246656, -1722147667968, -2213988532224, -1781337686016, -897010630656, -272696868864, -45449478144, -3170893824], [0, 16911433728, 180388626432, 755377373184, 1636181213184, 2015279185920, 1452974014464, 601765183488, 131415932928, 11626610688], [0, 0, -2818572288, -47915728896, -249443647488, -586263035904, -701824499712, -439697276928, -135996112896, -16206790656], [0, 0, 0, 0, 4227858432, 36641439744, 102877888512, 119789322240, 59894661120, 10569646080], [0, 0, 0, 0, 0, 0, -2113929216, -9160359936, -10217324544, -3170893824], [0, 0, 0, 0, 0, 0, 0, 0, 352321536, 352321536]]⟩
def n00116_reduction : Reduction := ⟨rawSub n00115_pair n00054_pair, n00116_pair, [[8388608]], 1⟩
theorem n00116_checked : checkReduction n00116_reduction = true := by decide
def n00117_expression (x t : ℝ) : ℝ := n00038_expression x t * n00116_expression x t
def n00117_pair : RationalPair := ⟨[[0, -34844675712, -212098930464, -476582968304, -395360297520, 208475292728, 752275018072, 734250984048, 385773833554, 117346509910, 19406486583, 1346052480], [0, 0, 45053406432, 305006191296, 763223051072, 820606171336, 171863321776, -455938942448, -485826835738, -220373179482, -49431185510, -4447973120], [0, 0, 0, -13815534288, -122050752048, -351071663832, -409530843904, -130582969824, 125295330612, 126874718388, 43113122389, 5348580480], [0, 0, 0, 0, 394164576, 15197503512, 61622204400, 76676444400, 20274957692, -21785756780, -14847221236, -2742387200], [0, 0, 0, 0, 0, 0, -392042424, -4070054928, -4987953062, -30475786, 1849380977, 496190080], [0, 0, 0, 0, 0, 0, 0, 0, 96595838, -27930170, -91025318, 4010240], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 442115, -4472960]], [[-22548578304, -242397216768, -1116154626048, -2886218022912, -4619639980032, -4760568594432, -3186395971584, -1364188987392, -357254037504, -51791265792, -3170893824], [0, 5637144576, 101468602368, 620085903360, 1888443432960, 3272362426368, 3392151748608, 2116747788288, 769470234624, 148327366656, 11626610688], [0, 0, 0, -11274289152, -121198608384, -481975861248, -939993858048, -978044583936, -545393737728, -151498260480, -16206790656], [0, 0, 0, 0, 0, 8455716864, 57780731904, 138110042112, 143747186688, 65531805696, 10569646080], [0, 0, 0, 0, 0, 0, 0, -2818572288, -10569646080, -10921967616, -3170893824], [0, 0, 0, 0, 0, 0, 0, 0, 0, 352321536, 352321536]]⟩
def n00117_reduction : Reduction := ⟨rawMul n00038_pair n00116_pair, n00117_pair, [[-2, -1], [0, 1]], 1⟩
theorem n00117_checked : checkReduction n00117_reduction = true := by decide
def n00118_expression (x t : ℝ) : ℝ := n00110_expression x t + n00117_expression x t
def n00118_pair : RationalPair := ⟨[[-1220410368, -53648810880, -333620023584, -914189319152, -1373036506800, -1213841616712, -620371515752, -142906362768, 22512172210, 24476038534, 6177766599, 546638208], [0, 305102592, 51966434016, 364148733120, 1021762321472, 1473813836872, 1180454335216, 513822704272, 89473106534, -18353970858, -11407088246, -1516787456], [0, 0, 0, -14425739472, -131452819632, -407713325400, -581917670464, -420500189280, -150798236172, -18824168556, 4041714997, 1262685312], [0, 0, 0, 0, 394164576, 15655157400, 66881277360, 98718562416, 62874006524, 18001174516, 2246074412, -77672960], [0, 0, 0, 0, 0, 0, -392042424, -4222606224, -6270610886, -3286326298, -1075777279, -303224192], [0, 0, 0, 0, 0, 0, 0, 0, 96595838, -8861258, 16867402, 92834048], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 442115, -4472960]], [[-22548578304, -242397216768, -1116154626048, -2886218022912, -4619639980032, -4760568594432, -3186395971584, -1364188987392, -357254037504, -51791265792, -3170893824], [0, 5637144576, 101468602368, 620085903360, 1888443432960, 3272362426368, 3392151748608, 2116747788288, 769470234624, 148327366656, 11626610688], [0, 0, 0, -11274289152, -121198608384, -481975861248, -939993858048, -978044583936, -545393737728, -151498260480, -16206790656], [0, 0, 0, 0, 0, 8455716864, 57780731904, 138110042112, 143747186688, 65531805696, 10569646080], [0, 0, 0, 0, 0, 0, 0, -2818572288, -10569646080, -10921967616, -3170893824], [0, 0, 0, 0, 0, 0, 0, 0, 0, 352321536, 352321536]]⟩
def n00118_reduction : Reduction := ⟨rawAdd n00110_pair n00117_pair, n00118_pair, [[7340032]], 1⟩
theorem n00118_checked : checkReduction n00118_reduction = true := by decide
def n00119_expression (x t : ℝ) : ℝ := n00118_expression x t / n00038_expression x t
def n00119_pair : RationalPair := ⟨[[-1220410368, -53648810880, -333620023584, -914189319152, -1373036506800, -1213841616712, -620371515752, -142906362768, 22512172210, 24476038534, 6177766599, 546638208], [0, 305102592, 51966434016, 364148733120, 1021762321472, 1473813836872, 1180454335216, 513822704272, 89473106534, -18353970858, -11407088246, -1516787456], [0, 0, 0, -14425739472, -131452819632, -407713325400, -581917670464, -420500189280, -150798236172, -18824168556, 4041714997, 1262685312], [0, 0, 0, 0, 394164576, 15655157400, 66881277360, 98718562416, 62874006524, 18001174516, 2246074412, -77672960], [0, 0, 0, 0, 0, 0, -392042424, -4222606224, -6270610886, -3286326298, -1075777279, -303224192], [0, 0, 0, 0, 0, 0, 0, 0, 96595838, -8861258, 16867402, 92834048], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 442115, -4472960]], [[0, -22548578304, -208574349312, -808930246656, -1722147667968, -2213988532224, -1781337686016, -897010630656, -272696868864, -45449478144, -3170893824], [0, 0, 16911433728, 180388626432, 755377373184, 1636181213184, 2015279185920, 1452974014464, 601765183488, 131415932928, 11626610688], [0, 0, 0, -2818572288, -47915728896, -249443647488, -586263035904, -701824499712, -439697276928, -135996112896, -16206790656], [0, 0, 0, 0, 0, 4227858432, 36641439744, 102877888512, 119789322240, 59894661120, 10569646080], [0, 0, 0, 0, 0, 0, 0, -2113929216, -9160359936, -10217324544, -3170893824], [0, 0, 0, 0, 0, 0, 0, 0, 0, 352321536, 352321536]]⟩
def n00119_reduction : Reduction := ⟨rawDiv n00118_pair n00038_pair, n00119_pair, [[-2, -4, -1], [0, 0, 1]], 1⟩
theorem n00119_checked : checkReduction n00119_reduction = true := by decide
def n00120_expression (x t : ℝ) : ℝ := n00109_expression x t * n00082_expression x t
def n00120_pair : RationalPair := ⟨[[397269, 1850496]], [[8388608]]⟩
def n00120_reduction : Reduction := ⟨rawMul n00109_pair n00082_pair, n00120_pair, [[1]], 1⟩
theorem n00120_checked : checkReduction n00120_reduction = true := by decide
def n00121_expression (x t : ℝ) : ℝ := n00075_expression x t * n00082_expression x t
def n00121_pair : RationalPair := ⟨[[0, 48, 72, 25], [0, 48, 48, 3], [0, 0, -24, -21], [0, 0, 0, 1]], [[128, 288, 208, 48], [0, -96, -160, -64], [0, 0, 16, 16]]⟩
def n00121_reduction : Reduction := ⟨rawMul n00075_pair n00082_pair, n00121_pair, [[3]], 1⟩
theorem n00121_checked : checkReduction n00121_reduction = true := by decide
def n00122_expression (x t : ℝ) : ℝ := n00005_expression x t - n00121_expression x t
def n00122_pair : RationalPair := ⟨[[128, 240, 136, 23], [0, -144, -208, -67], [0, 0, 40, 37], [0, 0, 0, -1]], [[128, 288, 208, 48], [0, -96, -160, -64], [0, 0, 16, 16]]⟩
def n00122_reduction : Reduction := ⟨rawSub n00005_pair n00121_pair, n00122_pair, [[1]], 1⟩
theorem n00122_checked : checkReduction n00122_reduction = true := by decide
def n00123_expression (x t : ℝ) : ℝ := n00111_expression x t * n00122_expression x t
def n00123_pair : RationalPair := ⟨[[-50453065728, -356227760640, -1062446205952, -1772906634528, -1859107043600, -1307922933696, -638606836584, -215016495958, -47025387506, -5868433713, -308634240], [0, 56759698944, 426499457280, 1291463776672, 2094361984016, 2053656950984, 1307753615656, 559106843662, 155323983086, 24600471746, 1619211520], [0, 0, -15766583040, -152797030368, -514589846832, -842257446632, -779399117208, -447138660692, -164531917916, -35129308379, -3108707200], [0, 0, 0, 394164576, 17725667760, 83322597592, 146171948472, 129458062804, 67376331556, 20970659516, 2773235200], [0, 0, 0, 0, 0, -392042424, -5135286304, -10272547318, -9255648690, -4811115767, -1158496640], [0, 0, 0, 0, 0, 0, 0, 96595838, 116525550, 237284482, 187864320], [0, 0, 0, 0, 0, 0, 0, 0, 0, 442115, -4472960]], [[-25769803776, -238370684928, -924491710464, -1968168763392, -2530272608256, -2035814498304, -1025155006464, -311653564416, -51942260736, -3623878656], [0, 19327352832, 206158430208, 863288426496, 1869921386496, 2303176212480, 1660541730816, 687731638272, 150189637632, 13287555072], [0, 0, -3221225472, -54760833024, -285078454272, -670014898176, -802085142528, -502511173632, -155424129024, -18522046464], [0, 0, 0, 0, 4831838208, 41875931136, 117574729728, 136902082560, 68451041280, 12079595520], [0, 0, 0, 0, 0, 0, -2415919104, -10468982784, -11676942336, -3623878656], [0, 0, 0, 0, 0, 0, 0, 0, 402653184, 402653184]]⟩
def n00123_reduction : Reduction := ⟨rawMul n00111_pair n00122_pair, n00123_pair, [[1]], 1⟩
theorem n00123_checked : checkReduction n00123_reduction = true := by decide
def n00124_expression (x t : ℝ) : ℝ := n00123_expression x t - n00049_expression x t
def n00124_pair : RationalPair := ⟨[[-45775054848, -304211822592, -813737444608, -1101920449056, -731936080784, -79775444928, 238292938968, 189418870634, 68155558702, 12414716655, 921038208], [0, 53251190784, 382517117184, 1064795712928, 1461978516368, 1001048745416, 224789133736, -129200813426, -105304553650, -28774719070, -2889587456], [0, 0, -15181831680, -141763215072, -444257634480, -623894931176, -406443255960, -83749946708, 34196914660, 20972296933, 3176285312], [0, 0, 0, 394164576, 16848540720, 74081266648, 110618975544, 64710090580, 8496072676, -4449304324, -1325672960], [0, 0, 0, 0, 0, -392042424, -4696722784, -7552323766, -3583537938, -190992599, 71175808], [0, 0, 0, 0, 0, 0, 0, 96595838, 43431630, 27560290, 51234048], [0, 0, 0, 0, 0, 0, 0, 0, 0, 442115, -4472960]], [[-25769803776, -238370684928, -924491710464, -1968168763392, -2530272608256, -2035814498304, -1025155006464, -311653564416, -51942260736, -3623878656], [0, 19327352832, 206158430208, 863288426496, 1869921386496, 2303176212480, 1660541730816, 687731638272, 150189637632, 13287555072], [0, 0, -3221225472, -54760833024, -285078454272, -670014898176, -802085142528, -502511173632, -155424129024, -18522046464], [0, 0, 0, 0, 4831838208, 41875931136, 117574729728, 136902082560, 68451041280, 12079595520], [0, 0, 0, 0, 0, 0, -2415919104, -10468982784, -11676942336, -3623878656], [0, 0, 0, 0, 0, 0, 0, 0, 402653184, 402653184]]⟩
def n00124_reduction : Reduction := ⟨rawSub n00123_pair n00049_pair, n00124_pair, [[4194304]], 1⟩
theorem n00124_checked : checkReduction n00124_reduction = true := by decide
def n00125_expression (x t : ℝ) : ℝ := n00124_expression x t - n00054_expression x t
def n00125_pair : RationalPair := ⟨[[-39822486528, -245101620480, -562736313472, -502037136288, 161769907120, 788033254464, 794960214456, 422479843082, 129120634654, 21412951647, 1490421120], [0, 48786764544, 331859861760, 832993112992, 894405615056, 175236369224, -520653960344, -548963883698, -248053089634, -55441770574, -4977324800], [0, 0, -14437760640, -128607889248, -369803338992, -424336699112, -115896993048, 158348553388, 149052772804, 49670905861, 6086464640], [0, 0, 0, 394164576, 15732434160, 63649165912, 76880846712, 14613759124, -28825458044, -17994581284, -3223616000], [0, 0, 0, 0, 0, -392042424, -4138669504, -4754504278, 758603550, 2480765593, 640558720], [0, 0, 0, 0, 0, 0, 0, 96595838, -49577250, -128713358, -12030720], [0, 0, 0, 0, 0, 0, 0, 0, 0, 442115, -4472960]], [[-25769803776, -238370684928, -924491710464, -1968168763392, -2530272608256, -2035814498304, -1025155006464, -311653564416, -51942260736, -3623878656], [0, 19327352832, 206158430208, 863288426496, 1869921386496, 2303176212480, 1660541730816, 687731638272, 150189637632, 13287555072], [0, 0, -3221225472, -54760833024, -285078454272, -670014898176, -802085142528, -502511173632, -155424129024, -18522046464], [0, 0, 0, 0, 4831838208, 41875931136, 117574729728, 136902082560, 68451041280, 12079595520], [0, 0, 0, 0, 0, 0, -2415919104, -10468982784, -11676942336, -3623878656], [0, 0, 0, 0, 0, 0, 0, 0, 402653184, 402653184]]⟩
def n00125_reduction : Reduction := ⟨rawSub n00124_pair n00054_pair, n00125_pair, [[8388608]], 1⟩
theorem n00125_checked : checkReduction n00125_reduction = true := by decide
def n00126_expression (x t : ℝ) : ℝ := n00038_expression x t * n00125_expression x t
def n00126_pair : RationalPair := ⟨[[0, -39822486528, -245101620480, -562736313472, -502037136288, 161769907120, 788033254464, 794960214456, 422479843082, 129120634654, 21412951647, 1490421120], [0, 0, 48786764544, 331859861760, 832993112992, 894405615056, 175236369224, -520653960344, -548963883698, -248053089634, -55441770574, -4977324800], [0, 0, 0, -14437760640, -128607889248, -369803338992, -424336699112, -115896993048, 158348553388, 149052772804, 49670905861, 6086464640], [0, 0, 0, 0, 394164576, 15732434160, 63649165912, 76880846712, 14613759124, -28825458044, -17994581284, -3223616000], [0, 0, 0, 0, 0, 0, -392042424, -4138669504, -4754504278, 758603550, 2480765593, 640558720], [0, 0, 0, 0, 0, 0, 0, 0, 96595838, -49577250, -128713358, -12030720], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 442115, -4472960]], [[-25769803776, -277025390592, -1275605286912, -3298534883328, -5279588548608, -5440649822208, -3641595396096, -1559073128448, -408290328576, -59190018048, -3623878656], [0, 6442450944, 115964116992, 708669603840, 2158221066240, 3739842772992, 3876744855552, 2419140329472, 879394553856, 169516990464, 13287555072], [0, 0, 0, -12884901888, -138512695296, -550829555712, -1074278694912, -1117765238784, -623307128832, -173140869120, -18522046464], [0, 0, 0, 0, 0, 9663676416, 66035122176, 157840048128, 164282499072, 74893492224, 12079595520], [0, 0, 0, 0, 0, 0, 0, -3221225472, -12079595520, -12482248704, -3623878656], [0, 0, 0, 0, 0, 0, 0, 0, 0, 402653184, 402653184]]⟩
def n00126_reduction : Reduction := ⟨rawMul n00038_pair n00125_pair, n00126_pair, [[-2, -1], [0, 1]], 1⟩
theorem n00126_checked : checkReduction n00126_reduction = true := by decide
def n00127_expression (x t : ℝ) : ℝ := n00120_expression x t + n00126_expression x t
def n00127_pair : RationalPair := ⟨[[-1220410368, -58626621696, -366622713600, -1000342664320, -1479713345568, -1260547002320, -584613279360, -82197132360, 59218181738, 36250163278, 8184231663, 691006848], [0, 305102592, 55699792128, 391002403584, 1091532383392, 1547613280592, 1183827382664, 449107686376, 26336058574, -46033881010, -17417673310, -2046139136], [0, 0, 0, -15047965824, -138009956832, -426445000560, -596723525672, -405814212504, -117745013396, 3353885860, 10599498469, 2000569472], [0, 0, 0, 0, 394164576, 16190088048, 68908238872, 98922964728, 57212807956, 10961473252, -901285636, -558901760], [0, 0, 0, 0, 0, 0, -392042424, -4291220800, -6037162102, -2497246962, -444392663, -158855552], [0, 0, 0, 0, 0, 0, 0, 0, 96595838, -30508338, -20820638, 76793088], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 442115, -4472960]], [[-25769803776, -277025390592, -1275605286912, -3298534883328, -5279588548608, -5440649822208, -3641595396096, -1559073128448, -408290328576, -59190018048, -3623878656], [0, 6442450944, 115964116992, 708669603840, 2158221066240, 3739842772992, 3876744855552, 2419140329472, 879394553856, 169516990464, 13287555072], [0, 0, 0, -12884901888, -138512695296, -550829555712, -1074278694912, -1117765238784, -623307128832, -173140869120, -18522046464], [0, 0, 0, 0, 0, 9663676416, 66035122176, 157840048128, 164282499072, 74893492224, 12079595520], [0, 0, 0, 0, 0, 0, 0, -3221225472, -12079595520, -12482248704, -3623878656], [0, 0, 0, 0, 0, 0, 0, 0, 0, 402653184, 402653184]]⟩
def n00127_reduction : Reduction := ⟨rawAdd n00120_pair n00126_pair, n00127_pair, [[8388608]], 1⟩
theorem n00127_checked : checkReduction n00127_reduction = true := by decide
def n00128_expression (x t : ℝ) : ℝ := n00127_expression x t / n00038_expression x t
def n00128_pair : RationalPair := ⟨[[-1220410368, -58626621696, -366622713600, -1000342664320, -1479713345568, -1260547002320, -584613279360, -82197132360, 59218181738, 36250163278, 8184231663, 691006848], [0, 305102592, 55699792128, 391002403584, 1091532383392, 1547613280592, 1183827382664, 449107686376, 26336058574, -46033881010, -17417673310, -2046139136], [0, 0, 0, -15047965824, -138009956832, -426445000560, -596723525672, -405814212504, -117745013396, 3353885860, 10599498469, 2000569472], [0, 0, 0, 0, 394164576, 16190088048, 68908238872, 98922964728, 57212807956, 10961473252, -901285636, -558901760], [0, 0, 0, 0, 0, 0, -392042424, -4291220800, -6037162102, -2497246962, -444392663, -158855552], [0, 0, 0, 0, 0, 0, 0, 0, 96595838, -30508338, -20820638, 76793088], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 442115, -4472960]], [[0, -25769803776, -238370684928, -924491710464, -1968168763392, -2530272608256, -2035814498304, -1025155006464, -311653564416, -51942260736, -3623878656], [0, 0, 19327352832, 206158430208, 863288426496, 1869921386496, 2303176212480, 1660541730816, 687731638272, 150189637632, 13287555072], [0, 0, 0, -3221225472, -54760833024, -285078454272, -670014898176, -802085142528, -502511173632, -155424129024, -18522046464], [0, 0, 0, 0, 0, 4831838208, 41875931136, 117574729728, 136902082560, 68451041280, 12079595520], [0, 0, 0, 0, 0, 0, 0, -2415919104, -10468982784, -11676942336, -3623878656], [0, 0, 0, 0, 0, 0, 0, 0, 0, 402653184, 402653184]]⟩
def n00128_reduction : Reduction := ⟨rawDiv n00127_pair n00038_pair, n00128_pair, [[-2, -4, -1], [0, 0, 1]], 1⟩
theorem n00128_checked : checkReduction n00128_reduction = true := by decide
def divisorExpression (i : Fin 19) (x t : ℝ) : ℝ :=
  match i.val with
  | 0 => n00006_expression x t
  | 1 => n00008_expression x t
  | 2 => n00010_expression x t
  | 3 => n00019_expression x t
  | 4 => n00014_expression x t
  | 5 => n00014_expression x t
  | 6 => n00010_expression x t
  | 7 => n00010_expression x t
  | 8 => n00037_expression x t
  | 9 => n00041_expression x t
  | 10 => n00048_expression x t
  | 11 => n00048_expression x t
  | 12 => n00048_expression x t
  | 13 => n00048_expression x t
  | 14 => n00074_expression x t
  | 15 => n00010_expression x t
  | 16 => n00068_expression x t
  | 17 => n00038_expression x t
  | 18 => n00038_expression x t
  | _ => 1
def DivisorsNonzero (x t : ℝ) : Prop := ∀ i : Fin 19, divisorExpression i x t ≠ 0
theorem n00000_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00000_pair.NonzeroDenominator x t ∧ n00000_pair.value x t = n00000_expression x t := by
  simpa [n00000_pair, n00000_expression, rationalX, Polynomial2.X, Polynomial2.const] using rationalX_sound x t
theorem n00001_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00001_pair.NonzeroDenominator x t ∧ n00001_pair.value x t = n00001_expression x t := by
  simpa [n00001_pair, n00001_expression, rationalT, Polynomial2.Y, Polynomial2.const] using rationalT_sound x t
theorem n00002_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00002_pair.NonzeroDenominator x t ∧ n00002_pair.value x t = n00002_expression x t := by
  simpa [n00002_pair, n00002_expression, rationalConst, Polynomial2.const] using rationalConst_sound 29 20 x t (by decide)
theorem n00003_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00003_pair.NonzeroDenominator x t ∧ n00003_pair.value x t = n00003_expression x t := by
  simpa [n00003_pair, n00003_expression, rationalConst, Polynomial2.const] using rationalConst_sound 8 5 x t (by decide)
theorem n00004_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00004_pair.NonzeroDenominator x t ∧ n00004_pair.value x t = n00004_expression x t := by
  simpa [n00004_pair, n00004_expression, rationalConst, Polynomial2.const] using rationalConst_sound 195 128 x t (by decide)
theorem n00005_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00005_pair.NonzeroDenominator x t ∧ n00005_pair.value x t = n00005_expression x t := by
  simpa [n00005_pair, n00005_expression, rationalConst, Polynomial2.const] using rationalConst_sound 1 1 x t (by decide)
theorem n00006_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00006_pair.NonzeroDenominator x t ∧ n00006_pair.value x t = n00006_expression x t := by
  have ha := n00005_sound x t hnz
  have hb := n00000_sound x t hnz
  have hraw := rawAdd_sound n00005_pair n00000_pair x t ha.1 hb.1
  have hred := checkReduction_sound n00006_checked x t hraw.1
  dsimp only [n00006_reduction] at hred
  refine ⟨hred.1, ?_⟩
  rw [← hred.2, hraw.2]
  simp only [n00006_expression, ha.2, hb.2]
theorem n00007_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00007_pair.NonzeroDenominator x t ∧ n00007_pair.value x t = n00007_expression x t := by
  have ha := n00000_sound x t hnz
  have hb := n00006_sound x t hnz
  have hd : n00006_pair.value x t ≠ 0 := by
    rw [hb.2]
    simpa only [divisorExpression] using hnz ⟨0, by decide⟩
  have hraw := rawDiv_sound n00000_pair n00006_pair x t ha.1 hb.1 hd
  have hred := checkReduction_sound n00007_checked x t hraw.1
  dsimp only [n00007_reduction] at hred
  refine ⟨hred.1, ?_⟩
  rw [← hred.2, hraw.2]
  simp only [n00007_expression, ha.2, hb.2]
theorem n00008_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00008_pair.NonzeroDenominator x t ∧ n00008_pair.value x t = n00008_expression x t := by
  have ha := n00005_sound x t hnz
  have hb := n00003_sound x t hnz
  have hraw := rawAdd_sound n00005_pair n00003_pair x t ha.1 hb.1
  have hred := checkReduction_sound n00008_checked x t hraw.1
  dsimp only [n00008_reduction] at hred
  refine ⟨hred.1, ?_⟩
  rw [← hred.2, hraw.2]
  simp only [n00008_expression, ha.2, hb.2]
theorem n00009_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00009_pair.NonzeroDenominator x t ∧ n00009_pair.value x t = n00009_expression x t := by
  have ha := n00003_sound x t hnz
  have hb := n00008_sound x t hnz
  have hd : n00008_pair.value x t ≠ 0 := by
    rw [hb.2]
    simpa only [divisorExpression] using hnz ⟨1, by decide⟩
  have hraw := rawDiv_sound n00003_pair n00008_pair x t ha.1 hb.1 hd
  have hred := checkReduction_sound n00009_checked x t hraw.1
  dsimp only [n00009_reduction] at hred
  refine ⟨hred.1, ?_⟩
  rw [← hred.2, hraw.2]
  simp only [n00009_expression, ha.2, hb.2]
theorem n00010_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00010_pair.NonzeroDenominator x t ∧ n00010_pair.value x t = n00010_expression x t := by
  simpa [n00010_pair, n00010_expression, rationalConst, Polynomial2.const] using rationalConst_sound 2 1 x t (by decide)
theorem n00011_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00011_pair.NonzeroDenominator x t ∧ n00011_pair.value x t = n00011_expression x t := by
  have ha := n00009_sound x t hnz
  have hb := n00010_sound x t hnz
  have hd : n00010_pair.value x t ≠ 0 := by
    rw [hb.2]
    simpa only [divisorExpression] using hnz ⟨2, by decide⟩
  have hraw := rawDiv_sound n00009_pair n00010_pair x t ha.1 hb.1 hd
  have hred := checkReduction_sound n00011_checked x t hraw.1
  dsimp only [n00011_reduction] at hred
  refine ⟨hred.1, ?_⟩
  rw [← hred.2, hraw.2]
  simp only [n00011_expression, ha.2, hb.2]
theorem n00012_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00012_pair.NonzeroDenominator x t ∧ n00012_pair.value x t = n00012_expression x t := by
  have ha := n00005_sound x t hnz
  have hb := n00011_sound x t hnz
  have hraw := rawSub_sound n00005_pair n00011_pair x t ha.1 hb.1
  have hred := checkReduction_sound n00012_checked x t hraw.1
  dsimp only [n00012_reduction] at hred
  refine ⟨hred.1, ?_⟩
  rw [← hred.2, hraw.2]
  simp only [n00012_expression, ha.2, hb.2]
theorem n00013_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00013_pair.NonzeroDenominator x t ∧ n00013_pair.value x t = n00013_expression x t := by
  have ha := n00009_sound x t hnz
  have hb := n00012_sound x t hnz
  have hraw := rawMul_sound n00009_pair n00012_pair x t ha.1 hb.1
  have hred := checkReduction_sound n00013_checked x t hraw.1
  dsimp only [n00013_reduction] at hred
  refine ⟨hred.1, ?_⟩
  rw [← hred.2, hraw.2]
  simp only [n00013_expression, ha.2, hb.2]
theorem n00014_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00014_pair.NonzeroDenominator x t ∧ n00014_pair.value x t = n00014_expression x t := by
  have ha := n00003_sound x t hnz
  have hb := n00002_sound x t hnz
  have hraw := rawSub_sound n00003_pair n00002_pair x t ha.1 hb.1
  have hred := checkReduction_sound n00014_checked x t hraw.1
  dsimp only [n00014_reduction] at hred
  refine ⟨hred.1, ?_⟩
  rw [← hred.2, hraw.2]
  simp only [n00014_expression, ha.2, hb.2]
theorem n00015_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00015_pair.NonzeroDenominator x t ∧ n00015_pair.value x t = n00015_expression x t := by
  have ha := n00014_sound x t hnz
  have hraw := rawPow_sound n00014_pair 2 x t ha.1
  have hred := checkReduction_sound n00015_checked x t hraw.1
  dsimp only [n00015_reduction] at hred
  refine ⟨hred.1, ?_⟩
  rw [← hred.2, hraw.2]
  simp only [n00015_expression, ha.2]
theorem n00016_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00016_pair.NonzeroDenominator x t ∧ n00016_pair.value x t = n00016_expression x t := by
  have ha := n00013_sound x t hnz
  have hb := n00015_sound x t hnz
  have hraw := rawMul_sound n00013_pair n00015_pair x t ha.1 hb.1
  have hred := checkReduction_sound n00016_checked x t hraw.1
  dsimp only [n00016_reduction] at hred
  refine ⟨hred.1, ?_⟩
  rw [← hred.2, hraw.2]
  simp only [n00016_expression, ha.2, hb.2]
theorem n00017_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00017_pair.NonzeroDenominator x t ∧ n00017_pair.value x t = n00017_expression x t := by
  have ha := n00002_sound x t hnz
  have hraw := rawPow_sound n00002_pair 2 x t ha.1
  have hred := checkReduction_sound n00017_checked x t hraw.1
  dsimp only [n00017_reduction] at hred
  refine ⟨hred.1, ?_⟩
  rw [← hred.2, hraw.2]
  simp only [n00017_expression, ha.2]
theorem n00018_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00018_pair.NonzeroDenominator x t ∧ n00018_pair.value x t = n00018_expression x t := by
  simpa [n00018_pair, n00018_expression, rationalConst, Polynomial2.const] using rationalConst_sound 8 1 x t (by decide)
theorem n00019_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00019_pair.NonzeroDenominator x t ∧ n00019_pair.value x t = n00019_expression x t := by
  have ha := n00018_sound x t hnz
  have hb := n00017_sound x t hnz
  have hraw := rawMul_sound n00018_pair n00017_pair x t ha.1 hb.1
  have hred := checkReduction_sound n00019_checked x t hraw.1
  dsimp only [n00019_reduction] at hred
  refine ⟨hred.1, ?_⟩
  rw [← hred.2, hraw.2]
  simp only [n00019_expression, ha.2, hb.2]
theorem n00020_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00020_pair.NonzeroDenominator x t ∧ n00020_pair.value x t = n00020_expression x t := by
  have ha := n00016_sound x t hnz
  have hb := n00019_sound x t hnz
  have hd : n00019_pair.value x t ≠ 0 := by
    rw [hb.2]
    simpa only [divisorExpression] using hnz ⟨3, by decide⟩
  have hraw := rawDiv_sound n00016_pair n00019_pair x t ha.1 hb.1 hd
  have hred := checkReduction_sound n00020_checked x t hraw.1
  dsimp only [n00020_reduction] at hred
  refine ⟨hred.1, ?_⟩
  rw [← hred.2, hraw.2]
  simp only [n00020_expression, ha.2, hb.2]
theorem n00021_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00021_pair.NonzeroDenominator x t ∧ n00021_pair.value x t = n00021_expression x t := by
  have ha := n00003_sound x t hnz
  have hb := n00000_sound x t hnz
  have hraw := rawSub_sound n00003_pair n00000_pair x t ha.1 hb.1
  have hred := checkReduction_sound n00021_checked x t hraw.1
  dsimp only [n00021_reduction] at hred
  refine ⟨hred.1, ?_⟩
  rw [← hred.2, hraw.2]
  simp only [n00021_expression, ha.2, hb.2]
theorem n00022_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00022_pair.NonzeroDenominator x t ∧ n00022_pair.value x t = n00022_expression x t := by
  have ha := n00021_sound x t hnz
  have hb := n00014_sound x t hnz
  have hd : n00014_pair.value x t ≠ 0 := by
    rw [hb.2]
    simpa only [divisorExpression] using hnz ⟨4, by decide⟩
  have hraw := rawDiv_sound n00021_pair n00014_pair x t ha.1 hb.1 hd
  have hred := checkReduction_sound n00022_checked x t hraw.1
  dsimp only [n00022_reduction] at hred
  refine ⟨hred.1, ?_⟩
  rw [← hred.2, hraw.2]
  simp only [n00022_expression, ha.2, hb.2]
theorem n00023_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00023_pair.NonzeroDenominator x t ∧ n00023_pair.value x t = n00023_expression x t := by
  have ha := n00000_sound x t hnz
  have hb := n00002_sound x t hnz
  have hraw := rawSub_sound n00000_pair n00002_pair x t ha.1 hb.1
  have hred := checkReduction_sound n00023_checked x t hraw.1
  dsimp only [n00023_reduction] at hred
  refine ⟨hred.1, ?_⟩
  rw [← hred.2, hraw.2]
  simp only [n00023_expression, ha.2, hb.2]
theorem n00024_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00024_pair.NonzeroDenominator x t ∧ n00024_pair.value x t = n00024_expression x t := by
  have ha := n00023_sound x t hnz
  have hb := n00014_sound x t hnz
  have hd : n00014_pair.value x t ≠ 0 := by
    rw [hb.2]
    simpa only [divisorExpression] using hnz ⟨5, by decide⟩
  have hraw := rawDiv_sound n00023_pair n00014_pair x t ha.1 hb.1 hd
  have hred := checkReduction_sound n00024_checked x t hraw.1
  dsimp only [n00024_reduction] at hred
  refine ⟨hred.1, ?_⟩
  rw [← hred.2, hraw.2]
  simp only [n00024_expression, ha.2, hb.2]
theorem n00025_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00025_pair.NonzeroDenominator x t ∧ n00025_pair.value x t = n00025_expression x t := by
  simpa [n00025_pair, n00025_expression, rationalConst, Polynomial2.const] using rationalConst_sound 5922933 100000000 x t (by decide)
theorem n00026_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00026_pair.NonzeroDenominator x t ∧ n00026_pair.value x t = n00026_expression x t := by
  have ha := n00022_sound x t hnz
  have hb := n00025_sound x t hnz
  have hraw := rawMul_sound n00022_pair n00025_pair x t ha.1 hb.1
  have hred := checkReduction_sound n00026_checked x t hraw.1
  dsimp only [n00026_reduction] at hred
  refine ⟨hred.1, ?_⟩
  rw [← hred.2, hraw.2]
  simp only [n00026_expression, ha.2, hb.2]
theorem n00027_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00027_pair.NonzeroDenominator x t ∧ n00027_pair.value x t = n00027_expression x t := by
  simpa [n00027_pair, n00027_expression, rationalConst, Polynomial2.const] using rationalConst_sound 1640021 20000000 x t (by decide)
theorem n00028_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00028_pair.NonzeroDenominator x t ∧ n00028_pair.value x t = n00028_expression x t := by
  have ha := n00024_sound x t hnz
  have hb := n00027_sound x t hnz
  have hraw := rawMul_sound n00024_pair n00027_pair x t ha.1 hb.1
  have hred := checkReduction_sound n00028_checked x t hraw.1
  dsimp only [n00028_reduction] at hred
  refine ⟨hred.1, ?_⟩
  rw [← hred.2, hraw.2]
  simp only [n00028_expression, ha.2, hb.2]
theorem n00029_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00029_pair.NonzeroDenominator x t ∧ n00029_pair.value x t = n00029_expression x t := by
  have ha := n00026_sound x t hnz
  have hb := n00028_sound x t hnz
  have hraw := rawAdd_sound n00026_pair n00028_pair x t ha.1 hb.1
  have hred := checkReduction_sound n00029_checked x t hraw.1
  dsimp only [n00029_reduction] at hred
  refine ⟨hred.1, ?_⟩
  rw [← hred.2, hraw.2]
  simp only [n00029_expression, ha.2, hb.2]
theorem n00030_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00030_pair.NonzeroDenominator x t ∧ n00030_pair.value x t = n00030_expression x t := by
  have ha := n00029_sound x t hnz
  have hb := n00020_sound x t hnz
  have hraw := rawAdd_sound n00029_pair n00020_pair x t ha.1 hb.1
  have hred := checkReduction_sound n00030_checked x t hraw.1
  dsimp only [n00030_reduction] at hred
  refine ⟨hred.1, ?_⟩
  rw [← hred.2, hraw.2]
  simp only [n00030_expression, ha.2, hb.2]
theorem n00031_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00031_pair.NonzeroDenominator x t ∧ n00031_pair.value x t = n00031_expression x t := by
  have ha := n00007_sound x t hnz
  have hb := n00010_sound x t hnz
  have hd : n00010_pair.value x t ≠ 0 := by
    rw [hb.2]
    simpa only [divisorExpression] using hnz ⟨6, by decide⟩
  have hraw := rawDiv_sound n00007_pair n00010_pair x t ha.1 hb.1 hd
  have hred := checkReduction_sound n00031_checked x t hraw.1
  dsimp only [n00031_reduction] at hred
  refine ⟨hred.1, ?_⟩
  rw [← hred.2, hraw.2]
  simp only [n00031_expression, ha.2, hb.2]
theorem n00032_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00032_pair.NonzeroDenominator x t ∧ n00032_pair.value x t = n00032_expression x t := by
  have ha := n00007_sound x t hnz
  have hb := n00001_sound x t hnz
  have hraw := rawMul_sound n00007_pair n00001_pair x t ha.1 hb.1
  have hred := checkReduction_sound n00032_checked x t hraw.1
  dsimp only [n00032_reduction] at hred
  refine ⟨hred.1, ?_⟩
  rw [← hred.2, hraw.2]
  simp only [n00032_expression, ha.2, hb.2]
theorem n00033_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00033_pair.NonzeroDenominator x t ∧ n00033_pair.value x t = n00033_expression x t := by
  have ha := n00032_sound x t hnz
  have hb := n00010_sound x t hnz
  have hd : n00010_pair.value x t ≠ 0 := by
    rw [hb.2]
    simpa only [divisorExpression] using hnz ⟨7, by decide⟩
  have hraw := rawDiv_sound n00032_pair n00010_pair x t ha.1 hb.1 hd
  have hred := checkReduction_sound n00033_checked x t hraw.1
  dsimp only [n00033_reduction] at hred
  refine ⟨hred.1, ?_⟩
  rw [← hred.2, hraw.2]
  simp only [n00033_expression, ha.2, hb.2]
theorem n00034_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00034_pair.NonzeroDenominator x t ∧ n00034_pair.value x t = n00034_expression x t := by
  have ha := n00031_sound x t hnz
  have hb := n00033_sound x t hnz
  have hraw := rawAdd_sound n00031_pair n00033_pair x t ha.1 hb.1
  have hred := checkReduction_sound n00034_checked x t hraw.1
  dsimp only [n00034_reduction] at hred
  refine ⟨hred.1, ?_⟩
  rw [← hred.2, hraw.2]
  simp only [n00034_expression, ha.2, hb.2]
theorem n00035_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00035_pair.NonzeroDenominator x t ∧ n00035_pair.value x t = n00035_expression x t := by
  have ha := n00005_sound x t hnz
  have hb := n00034_sound x t hnz
  have hraw := rawSub_sound n00005_pair n00034_pair x t ha.1 hb.1
  have hred := checkReduction_sound n00035_checked x t hraw.1
  dsimp only [n00035_reduction] at hred
  refine ⟨hred.1, ?_⟩
  rw [← hred.2, hraw.2]
  simp only [n00035_expression, ha.2, hb.2]
theorem n00036_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00036_pair.NonzeroDenominator x t ∧ n00036_pair.value x t = n00036_expression x t := by
  have ha := n00000_sound x t hnz
  have hb := n00035_sound x t hnz
  have hraw := rawMul_sound n00000_pair n00035_pair x t ha.1 hb.1
  have hred := checkReduction_sound n00036_checked x t hraw.1
  dsimp only [n00036_reduction] at hred
  refine ⟨hred.1, ?_⟩
  rw [← hred.2, hraw.2]
  simp only [n00036_expression, ha.2, hb.2]
theorem n00037_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00037_pair.NonzeroDenominator x t ∧ n00037_pair.value x t = n00037_expression x t := by
  have ha := n00005_sound x t hnz
  have hb := n00036_sound x t hnz
  have hraw := rawAdd_sound n00005_pair n00036_pair x t ha.1 hb.1
  have hred := checkReduction_sound n00037_checked x t hraw.1
  dsimp only [n00037_reduction] at hred
  refine ⟨hred.1, ?_⟩
  rw [← hred.2, hraw.2]
  simp only [n00037_expression, ha.2, hb.2]
theorem n00038_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00038_pair.NonzeroDenominator x t ∧ n00038_pair.value x t = n00038_expression x t := by
  have ha := n00036_sound x t hnz
  have hb := n00037_sound x t hnz
  have hd : n00037_pair.value x t ≠ 0 := by
    rw [hb.2]
    simpa only [divisorExpression] using hnz ⟨8, by decide⟩
  have hraw := rawDiv_sound n00036_pair n00037_pair x t ha.1 hb.1 hd
  have hred := checkReduction_sound n00038_checked x t hraw.1
  dsimp only [n00038_reduction] at hred
  refine ⟨hred.1, ?_⟩
  rw [← hred.2, hraw.2]
  simp only [n00038_expression, ha.2, hb.2]
theorem n00039_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00039_pair.NonzeroDenominator x t ∧ n00039_pair.value x t = n00039_expression x t := by
  have ha := n00005_sound x t hnz
  have hb := n00038_sound x t hnz
  have hraw := rawSub_sound n00005_pair n00038_pair x t ha.1 hb.1
  have hred := checkReduction_sound n00039_checked x t hraw.1
  dsimp only [n00039_reduction] at hred
  refine ⟨hred.1, ?_⟩
  rw [← hred.2, hraw.2]
  simp only [n00039_expression, ha.2, hb.2]
theorem n00040_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00040_pair.NonzeroDenominator x t ∧ n00040_pair.value x t = n00040_expression x t := by
  have ha := n00000_sound x t hnz
  have hb := n00039_sound x t hnz
  have hraw := rawMul_sound n00000_pair n00039_pair x t ha.1 hb.1
  have hred := checkReduction_sound n00040_checked x t hraw.1
  dsimp only [n00040_reduction] at hred
  refine ⟨hred.1, ?_⟩
  rw [← hred.2, hraw.2]
  simp only [n00040_expression, ha.2, hb.2]
theorem n00041_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00041_pair.NonzeroDenominator x t ∧ n00041_pair.value x t = n00041_expression x t := by
  have ha := n00005_sound x t hnz
  have hb := n00040_sound x t hnz
  have hraw := rawAdd_sound n00005_pair n00040_pair x t ha.1 hb.1
  have hred := checkReduction_sound n00041_checked x t hraw.1
  dsimp only [n00041_reduction] at hred
  refine ⟨hred.1, ?_⟩
  rw [← hred.2, hraw.2]
  simp only [n00041_expression, ha.2, hb.2]
theorem n00042_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00042_pair.NonzeroDenominator x t ∧ n00042_pair.value x t = n00042_expression x t := by
  have ha := n00005_sound x t hnz
  have hb := n00041_sound x t hnz
  have hd : n00041_pair.value x t ≠ 0 := by
    rw [hb.2]
    simpa only [divisorExpression] using hnz ⟨9, by decide⟩
  have hraw := rawDiv_sound n00005_pair n00041_pair x t ha.1 hb.1 hd
  have hred := checkReduction_sound n00042_checked x t hraw.1
  dsimp only [n00042_reduction] at hred
  refine ⟨hred.1, ?_⟩
  rw [← hred.2, hraw.2]
  simp only [n00042_expression, ha.2, hb.2]
theorem n00043_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00043_pair.NonzeroDenominator x t ∧ n00043_pair.value x t = n00043_expression x t := by
  simpa [n00043_pair, n00043_expression, rationalConst, Polynomial2.const] using rationalConst_sound 45775 1 x t (by decide)
theorem n00044_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00044_pair.NonzeroDenominator x t ∧ n00044_pair.value x t = n00044_expression x t := by
  have ha := n00000_sound x t hnz
  have hb := n00004_sound x t hnz
  have hraw := rawSub_sound n00000_pair n00004_pair x t ha.1 hb.1
  have hred := checkReduction_sound n00044_checked x t hraw.1
  dsimp only [n00044_reduction] at hred
  refine ⟨hred.1, ?_⟩
  rw [← hred.2, hraw.2]
  simp only [n00044_expression, ha.2, hb.2]
theorem n00045_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00045_pair.NonzeroDenominator x t ∧ n00045_pair.value x t = n00045_expression x t := by
  simpa [n00045_pair, n00045_expression, rationalConst, Polynomial2.const] using rationalConst_sound 22238 1 x t (by decide)
theorem n00046_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00046_pair.NonzeroDenominator x t ∧ n00046_pair.value x t = n00046_expression x t := by
  have ha := n00045_sound x t hnz
  have hb := n00044_sound x t hnz
  have hraw := rawMul_sound n00045_pair n00044_pair x t ha.1 hb.1
  have hred := checkReduction_sound n00046_checked x t hraw.1
  dsimp only [n00046_reduction] at hred
  refine ⟨hred.1, ?_⟩
  rw [← hred.2, hraw.2]
  simp only [n00046_expression, ha.2, hb.2]
theorem n00047_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00047_pair.NonzeroDenominator x t ∧ n00047_pair.value x t = n00047_expression x t := by
  have ha := n00043_sound x t hnz
  have hb := n00046_sound x t hnz
  have hraw := rawAdd_sound n00043_pair n00046_pair x t ha.1 hb.1
  have hred := checkReduction_sound n00047_checked x t hraw.1
  dsimp only [n00047_reduction] at hred
  refine ⟨hred.1, ?_⟩
  rw [← hred.2, hraw.2]
  simp only [n00047_expression, ha.2, hb.2]
theorem n00048_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00048_pair.NonzeroDenominator x t ∧ n00048_pair.value x t = n00048_expression x t := by
  simpa [n00048_pair, n00048_expression, rationalConst, Polynomial2.const] using rationalConst_sound 65536 1 x t (by decide)
theorem n00049_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00049_pair.NonzeroDenominator x t ∧ n00049_pair.value x t = n00049_expression x t := by
  have ha := n00047_sound x t hnz
  have hb := n00048_sound x t hnz
  have hd : n00048_pair.value x t ≠ 0 := by
    rw [hb.2]
    simpa only [divisorExpression] using hnz ⟨10, by decide⟩
  have hraw := rawDiv_sound n00047_pair n00048_pair x t ha.1 hb.1 hd
  have hred := checkReduction_sound n00049_checked x t hraw.1
  dsimp only [n00049_reduction] at hred
  refine ⟨hred.1, ?_⟩
  rw [← hred.2, hraw.2]
  simp only [n00049_expression, ha.2, hb.2]
theorem n00050_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00050_pair.NonzeroDenominator x t ∧ n00050_pair.value x t = n00050_expression x t := by
  simpa [n00050_pair, n00050_expression, rationalConst, Polynomial2.const] using rationalConst_sound 30825 1 x t (by decide)
theorem n00051_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00051_pair.NonzeroDenominator x t ∧ n00051_pair.value x t = n00051_expression x t := by
  simpa [n00051_pair, n00051_expression, rationalConst, Polynomial2.const] using rationalConst_sound 10297 1 x t (by decide)
theorem n00052_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00052_pair.NonzeroDenominator x t ∧ n00052_pair.value x t = n00052_expression x t := by
  have ha := n00051_sound x t hnz
  have hb := n00044_sound x t hnz
  have hraw := rawMul_sound n00051_pair n00044_pair x t ha.1 hb.1
  have hred := checkReduction_sound n00052_checked x t hraw.1
  dsimp only [n00052_reduction] at hred
  refine ⟨hred.1, ?_⟩
  rw [← hred.2, hraw.2]
  simp only [n00052_expression, ha.2, hb.2]
theorem n00053_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00053_pair.NonzeroDenominator x t ∧ n00053_pair.value x t = n00053_expression x t := by
  have ha := n00050_sound x t hnz
  have hb := n00052_sound x t hnz
  have hraw := rawAdd_sound n00050_pair n00052_pair x t ha.1 hb.1
  have hred := checkReduction_sound n00053_checked x t hraw.1
  dsimp only [n00053_reduction] at hred
  refine ⟨hred.1, ?_⟩
  rw [← hred.2, hraw.2]
  simp only [n00053_expression, ha.2, hb.2]
theorem n00054_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00054_pair.NonzeroDenominator x t ∧ n00054_pair.value x t = n00054_expression x t := by
  have ha := n00053_sound x t hnz
  have hb := n00048_sound x t hnz
  have hd : n00048_pair.value x t ≠ 0 := by
    rw [hb.2]
    simpa only [divisorExpression] using hnz ⟨11, by decide⟩
  have hraw := rawDiv_sound n00053_pair n00048_pair x t ha.1 hb.1 hd
  have hred := checkReduction_sound n00054_checked x t hraw.1
  dsimp only [n00054_reduction] at hred
  refine ⟨hred.1, ?_⟩
  rw [← hred.2, hraw.2]
  simp only [n00054_expression, ha.2, hb.2]
theorem n00055_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00055_pair.NonzeroDenominator x t ∧ n00055_pair.value x t = n00055_expression x t := by
  simpa [n00055_pair, n00055_expression, rationalConst, Polynomial2.const] using rationalConst_sound 19913 1 x t (by decide)
theorem n00056_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00056_pair.NonzeroDenominator x t ∧ n00056_pair.value x t = n00056_expression x t := by
  simpa [n00056_pair, n00056_expression, rationalConst, Polynomial2.const] using rationalConst_sound 13978 1 x t (by decide)
theorem n00057_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00057_pair.NonzeroDenominator x t ∧ n00057_pair.value x t = n00057_expression x t := by
  have ha := n00056_sound x t hnz
  have hb := n00044_sound x t hnz
  have hraw := rawMul_sound n00056_pair n00044_pair x t ha.1 hb.1
  have hred := checkReduction_sound n00057_checked x t hraw.1
  dsimp only [n00057_reduction] at hred
  refine ⟨hred.1, ?_⟩
  rw [← hred.2, hraw.2]
  simp only [n00057_expression, ha.2, hb.2]
theorem n00058_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00058_pair.NonzeroDenominator x t ∧ n00058_pair.value x t = n00058_expression x t := by
  have ha := n00055_sound x t hnz
  have hb := n00057_sound x t hnz
  have hraw := rawAdd_sound n00055_pair n00057_pair x t ha.1 hb.1
  have hred := checkReduction_sound n00058_checked x t hraw.1
  dsimp only [n00058_reduction] at hred
  refine ⟨hred.1, ?_⟩
  rw [← hred.2, hraw.2]
  simp only [n00058_expression, ha.2, hb.2]
theorem n00059_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00059_pair.NonzeroDenominator x t ∧ n00059_pair.value x t = n00059_expression x t := by
  have ha := n00058_sound x t hnz
  have hb := n00048_sound x t hnz
  have hd : n00048_pair.value x t ≠ 0 := by
    rw [hb.2]
    simpa only [divisorExpression] using hnz ⟨12, by decide⟩
  have hraw := rawDiv_sound n00058_pair n00048_pair x t ha.1 hb.1 hd
  have hred := checkReduction_sound n00059_checked x t hraw.1
  dsimp only [n00059_reduction] at hred
  refine ⟨hred.1, ?_⟩
  rw [← hred.2, hraw.2]
  simp only [n00059_expression, ha.2, hb.2]
theorem n00060_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00060_pair.NonzeroDenominator x t ∧ n00060_pair.value x t = n00060_expression x t := by
  simpa [n00060_pair, n00060_expression, rationalConst, Polynomial2.const] using rationalConst_sound 3161 1 x t (by decide)
theorem n00061_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00061_pair.NonzeroDenominator x t ∧ n00061_pair.value x t = n00061_expression x t := by
  simpa [n00061_pair, n00061_expression, rationalConst, Polynomial2.const] using rationalConst_sound 4340 1 x t (by decide)
theorem n00062_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00062_pair.NonzeroDenominator x t ∧ n00062_pair.value x t = n00062_expression x t := by
  have ha := n00061_sound x t hnz
  have hb := n00044_sound x t hnz
  have hraw := rawMul_sound n00061_pair n00044_pair x t ha.1 hb.1
  have hred := checkReduction_sound n00062_checked x t hraw.1
  dsimp only [n00062_reduction] at hred
  refine ⟨hred.1, ?_⟩
  rw [← hred.2, hraw.2]
  simp only [n00062_expression, ha.2, hb.2]
theorem n00063_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00063_pair.NonzeroDenominator x t ∧ n00063_pair.value x t = n00063_expression x t := by
  have ha := n00060_sound x t hnz
  have hb := n00062_sound x t hnz
  have hraw := rawAdd_sound n00060_pair n00062_pair x t ha.1 hb.1
  have hred := checkReduction_sound n00063_checked x t hraw.1
  dsimp only [n00063_reduction] at hred
  refine ⟨hred.1, ?_⟩
  rw [← hred.2, hraw.2]
  simp only [n00063_expression, ha.2, hb.2]
theorem n00064_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00064_pair.NonzeroDenominator x t ∧ n00064_pair.value x t = n00064_expression x t := by
  have ha := n00063_sound x t hnz
  have hb := n00048_sound x t hnz
  have hd : n00048_pair.value x t ≠ 0 := by
    rw [hb.2]
    simpa only [divisorExpression] using hnz ⟨13, by decide⟩
  have hraw := rawDiv_sound n00063_pair n00048_pair x t ha.1 hb.1 hd
  have hred := checkReduction_sound n00064_checked x t hraw.1
  dsimp only [n00064_reduction] at hred
  refine ⟨hred.1, ?_⟩
  rw [← hred.2, hraw.2]
  simp only [n00064_expression, ha.2, hb.2]
theorem n00065_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00065_pair.NonzeroDenominator x t ∧ n00065_pair.value x t = n00065_expression x t := by
  have ha := n00034_sound x t hnz
  have hraw := rawPow_sound n00034_pair 2 x t ha.1
  have hred := checkReduction_sound n00065_checked x t hraw.1
  dsimp only [n00065_reduction] at hred
  refine ⟨hred.1, ?_⟩
  rw [← hred.2, hraw.2]
  simp only [n00065_expression, ha.2]
theorem n00066_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00066_pair.NonzeroDenominator x t ∧ n00066_pair.value x t = n00066_expression x t := by
  have ha := n00010_sound x t hnz
  have hb := n00034_sound x t hnz
  have hraw := rawSub_sound n00010_pair n00034_pair x t ha.1 hb.1
  have hred := checkReduction_sound n00066_checked x t hraw.1
  dsimp only [n00066_reduction] at hred
  refine ⟨hred.1, ?_⟩
  rw [← hred.2, hraw.2]
  simp only [n00066_expression, ha.2, hb.2]
theorem n00067_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00067_pair.NonzeroDenominator x t ∧ n00067_pair.value x t = n00067_expression x t := by
  simpa [n00067_pair, n00067_expression, rationalConst, Polynomial2.const] using rationalConst_sound 6 1 x t (by decide)
theorem n00068_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00068_pair.NonzeroDenominator x t ∧ n00068_pair.value x t = n00068_expression x t := by
  simpa [n00068_pair, n00068_expression, rationalConst, Polynomial2.const] using rationalConst_sound 12 1 x t (by decide)
theorem n00069_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00069_pair.NonzeroDenominator x t ∧ n00069_pair.value x t = n00069_expression x t := by
  have ha := n00068_sound x t hnz
  have hb := n00034_sound x t hnz
  have hraw := rawMul_sound n00068_pair n00034_pair x t ha.1 hb.1
  have hred := checkReduction_sound n00069_checked x t hraw.1
  dsimp only [n00069_reduction] at hred
  refine ⟨hred.1, ?_⟩
  rw [← hred.2, hraw.2]
  simp only [n00069_expression, ha.2, hb.2]
theorem n00070_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00070_pair.NonzeroDenominator x t ∧ n00070_pair.value x t = n00070_expression x t := by
  have ha := n00065_sound x t hnz
  have hb := n00069_sound x t hnz
  have hraw := rawSub_sound n00065_pair n00069_pair x t ha.1 hb.1
  have hred := checkReduction_sound n00070_checked x t hraw.1
  dsimp only [n00070_reduction] at hred
  refine ⟨hred.1, ?_⟩
  rw [← hred.2, hraw.2]
  simp only [n00070_expression, ha.2, hb.2]
theorem n00071_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00071_pair.NonzeroDenominator x t ∧ n00071_pair.value x t = n00071_expression x t := by
  have ha := n00070_sound x t hnz
  have hb := n00068_sound x t hnz
  have hraw := rawAdd_sound n00070_pair n00068_pair x t ha.1 hb.1
  have hred := checkReduction_sound n00071_checked x t hraw.1
  dsimp only [n00071_reduction] at hred
  refine ⟨hred.1, ?_⟩
  rw [← hred.2, hraw.2]
  simp only [n00071_expression, ha.2, hb.2]
theorem n00072_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00072_pair.NonzeroDenominator x t ∧ n00072_pair.value x t = n00072_expression x t := by
  have ha := n00034_sound x t hnz
  have hb := n00071_sound x t hnz
  have hraw := rawMul_sound n00034_pair n00071_pair x t ha.1 hb.1
  have hred := checkReduction_sound n00072_checked x t hraw.1
  dsimp only [n00072_reduction] at hred
  refine ⟨hred.1, ?_⟩
  rw [← hred.2, hraw.2]
  simp only [n00072_expression, ha.2, hb.2]
theorem n00073_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00073_pair.NonzeroDenominator x t ∧ n00073_pair.value x t = n00073_expression x t := by
  have ha := n00067_sound x t hnz
  have hb := n00035_sound x t hnz
  have hraw := rawMul_sound n00067_pair n00035_pair x t ha.1 hb.1
  have hred := checkReduction_sound n00073_checked x t hraw.1
  dsimp only [n00073_reduction] at hred
  refine ⟨hred.1, ?_⟩
  rw [← hred.2, hraw.2]
  simp only [n00073_expression, ha.2, hb.2]
theorem n00074_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00074_pair.NonzeroDenominator x t ∧ n00074_pair.value x t = n00074_expression x t := by
  have ha := n00073_sound x t hnz
  have hb := n00066_sound x t hnz
  have hraw := rawMul_sound n00073_pair n00066_pair x t ha.1 hb.1
  have hred := checkReduction_sound n00074_checked x t hraw.1
  dsimp only [n00074_reduction] at hred
  refine ⟨hred.1, ?_⟩
  rw [← hred.2, hraw.2]
  simp only [n00074_expression, ha.2, hb.2]
theorem n00075_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00075_pair.NonzeroDenominator x t ∧ n00075_pair.value x t = n00075_expression x t := by
  have ha := n00072_sound x t hnz
  have hb := n00074_sound x t hnz
  have hd : n00074_pair.value x t ≠ 0 := by
    rw [hb.2]
    simpa only [divisorExpression] using hnz ⟨14, by decide⟩
  have hraw := rawDiv_sound n00072_pair n00074_pair x t ha.1 hb.1 hd
  have hred := checkReduction_sound n00075_checked x t hraw.1
  dsimp only [n00075_reduction] at hred
  refine ⟨hred.1, ?_⟩
  rw [← hred.2, hraw.2]
  simp only [n00075_expression, ha.2, hb.2]
theorem n00076_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00076_pair.NonzeroDenominator x t ∧ n00076_pair.value x t = n00076_expression x t := by
  have ha := n00038_sound x t hnz
  have hb := n00010_sound x t hnz
  have hd : n00010_pair.value x t ≠ 0 := by
    rw [hb.2]
    simpa only [divisorExpression] using hnz ⟨15, by decide⟩
  have hraw := rawDiv_sound n00038_pair n00010_pair x t ha.1 hb.1 hd
  have hred := checkReduction_sound n00076_checked x t hraw.1
  dsimp only [n00076_reduction] at hred
  refine ⟨hred.1, ?_⟩
  rw [← hred.2, hraw.2]
  simp only [n00076_expression, ha.2, hb.2]
theorem n00077_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00077_pair.NonzeroDenominator x t ∧ n00077_pair.value x t = n00077_expression x t := by
  have ha := n00005_sound x t hnz
  have hb := n00076_sound x t hnz
  have hraw := rawSub_sound n00005_pair n00076_pair x t ha.1 hb.1
  have hred := checkReduction_sound n00077_checked x t hraw.1
  dsimp only [n00077_reduction] at hred
  refine ⟨hred.1, ?_⟩
  rw [← hred.2, hraw.2]
  simp only [n00077_expression, ha.2, hb.2]
theorem n00078_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00078_pair.NonzeroDenominator x t ∧ n00078_pair.value x t = n00078_expression x t := by
  have ha := n00038_sound x t hnz
  have hb := n00038_sound x t hnz
  have hraw := rawMul_sound n00038_pair n00038_pair x t ha.1 hb.1
  have hred := checkReduction_sound n00078_checked x t hraw.1
  dsimp only [n00078_reduction] at hred
  refine ⟨hred.1, ?_⟩
  rw [← hred.2, hraw.2]
  simp only [n00078_expression, ha.2, hb.2]
theorem n00079_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00079_pair.NonzeroDenominator x t ∧ n00079_pair.value x t = n00079_expression x t := by
  have ha := n00078_sound x t hnz
  have hb := n00068_sound x t hnz
  have hd : n00068_pair.value x t ≠ 0 := by
    rw [hb.2]
    simpa only [divisorExpression] using hnz ⟨16, by decide⟩
  have hraw := rawDiv_sound n00078_pair n00068_pair x t ha.1 hb.1 hd
  have hred := checkReduction_sound n00079_checked x t hraw.1
  dsimp only [n00079_reduction] at hred
  refine ⟨hred.1, ?_⟩
  rw [← hred.2, hraw.2]
  simp only [n00079_expression, ha.2, hb.2]
theorem n00080_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00080_pair.NonzeroDenominator x t ∧ n00080_pair.value x t = n00080_expression x t := by
  have ha := n00077_sound x t hnz
  have hb := n00079_sound x t hnz
  have hraw := rawSub_sound n00077_pair n00079_pair x t ha.1 hb.1
  have hred := checkReduction_sound n00080_checked x t hraw.1
  dsimp only [n00080_reduction] at hred
  refine ⟨hred.1, ?_⟩
  rw [← hred.2, hraw.2]
  simp only [n00080_expression, ha.2, hb.2]
theorem n00081_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00081_pair.NonzeroDenominator x t ∧ n00081_pair.value x t = n00081_expression x t := by
  have ha := n00059_sound x t hnz
  have hb := n00080_sound x t hnz
  have hraw := rawMul_sound n00059_pair n00080_pair x t ha.1 hb.1
  have hred := checkReduction_sound n00081_checked x t hraw.1
  dsimp only [n00081_reduction] at hred
  refine ⟨hred.1, ?_⟩
  rw [← hred.2, hraw.2]
  simp only [n00081_expression, ha.2, hb.2]
theorem n00082_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00082_pair.NonzeroDenominator x t ∧ n00082_pair.value x t = n00082_expression x t := by
  simpa [n00082_pair, n00082_expression, rationalConst, Polynomial2.const] using rationalConst_sound 3 4 x t (by decide)
theorem n00083_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00083_pair.NonzeroDenominator x t ∧ n00083_pair.value x t = n00083_expression x t := by
  simpa [n00083_pair, n00083_expression, rationalConst, Polynomial2.const] using rationalConst_sound 6 7 x t (by decide)
theorem n00084_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00084_pair.NonzeroDenominator x t ∧ n00084_pair.value x t = n00084_expression x t := by
  have ha := n00039_sound x t hnz
  have hb := n00081_sound x t hnz
  have hraw := rawAdd_sound n00039_pair n00081_pair x t ha.1 hb.1
  have hred := checkReduction_sound n00084_checked x t hraw.1
  dsimp only [n00084_reduction] at hred
  refine ⟨hred.1, ?_⟩
  rw [← hred.2, hraw.2]
  simp only [n00084_expression, ha.2, hb.2]
theorem n00085_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00085_pair.NonzeroDenominator x t ∧ n00085_pair.value x t = n00085_expression x t := by
  simpa [n00085_pair, n00085_expression, rationalConst, Polynomial2.const] using rationalConst_sound 10 1 x t (by decide)
theorem n00086_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00086_pair.NonzeroDenominator x t ∧ n00086_pair.value x t = n00086_expression x t := by
  have ha := n00085_sound x t hnz
  have hb := n00064_sound x t hnz
  have hraw := rawMul_sound n00085_pair n00064_pair x t ha.1 hb.1
  have hred := checkReduction_sound n00086_checked x t hraw.1
  dsimp only [n00086_reduction] at hred
  refine ⟨hred.1, ?_⟩
  rw [← hred.2, hraw.2]
  simp only [n00086_expression, ha.2, hb.2]
theorem n00087_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00087_pair.NonzeroDenominator x t ∧ n00087_pair.value x t = n00087_expression x t := by
  have ha := n00049_sound x t hnz
  have hb := n00054_sound x t hnz
  have hraw := rawAdd_sound n00049_pair n00054_pair x t ha.1 hb.1
  have hred := checkReduction_sound n00087_checked x t hraw.1
  dsimp only [n00087_reduction] at hred
  refine ⟨hred.1, ?_⟩
  rw [← hred.2, hraw.2]
  simp only [n00087_expression, ha.2, hb.2]
theorem n00088_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00088_pair.NonzeroDenominator x t ∧ n00088_pair.value x t = n00088_expression x t := by
  have ha := n00038_sound x t hnz
  have hb := n00087_sound x t hnz
  have hraw := rawMul_sound n00038_pair n00087_pair x t ha.1 hb.1
  have hred := checkReduction_sound n00088_checked x t hraw.1
  dsimp only [n00088_reduction] at hred
  refine ⟨hred.1, ?_⟩
  rw [← hred.2, hraw.2]
  simp only [n00088_expression, ha.2, hb.2]
theorem n00089_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00089_pair.NonzeroDenominator x t ∧ n00089_pair.value x t = n00089_expression x t := by
  have ha := n00086_sound x t hnz
  have hb := n00088_sound x t hnz
  have hraw := rawAdd_sound n00086_pair n00088_pair x t ha.1 hb.1
  have hred := checkReduction_sound n00089_checked x t hraw.1
  dsimp only [n00089_reduction] at hred
  refine ⟨hred.1, ?_⟩
  rw [← hred.2, hraw.2]
  simp only [n00089_expression, ha.2, hb.2]
theorem n00090_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00090_pair.NonzeroDenominator x t ∧ n00090_pair.value x t = n00090_expression x t := by
  have ha := n00059_sound x t hnz
  have hb := n00064_sound x t hnz
  have hraw := rawSub_sound n00059_pair n00064_pair x t ha.1 hb.1
  have hred := checkReduction_sound n00090_checked x t hraw.1
  dsimp only [n00090_reduction] at hred
  refine ⟨hred.1, ?_⟩
  rw [← hred.2, hraw.2]
  simp only [n00090_expression, ha.2, hb.2]
theorem n00091_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00091_pair.NonzeroDenominator x t ∧ n00091_pair.value x t = n00091_expression x t := by
  have ha := n00085_sound x t hnz
  have hb := n00030_sound x t hnz
  have hraw := rawMul_sound n00085_pair n00030_pair x t ha.1 hb.1
  have hred := checkReduction_sound n00091_checked x t hraw.1
  dsimp only [n00091_reduction] at hred
  refine ⟨hred.1, ?_⟩
  rw [← hred.2, hraw.2]
  simp only [n00091_expression, ha.2, hb.2]
theorem n00092_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00092_pair.NonzeroDenominator x t ∧ n00092_pair.value x t = n00092_expression x t := by
  have ha := n00083_sound x t hnz
  have hb := n00091_sound x t hnz
  have hraw := rawAdd_sound n00083_pair n00091_pair x t ha.1 hb.1
  have hred := checkReduction_sound n00092_checked x t hraw.1
  dsimp only [n00092_reduction] at hred
  refine ⟨hred.1, ?_⟩
  rw [← hred.2, hraw.2]
  simp only [n00092_expression, ha.2, hb.2]
theorem n00093_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00093_pair.NonzeroDenominator x t ∧ n00093_pair.value x t = n00093_expression x t := by
  have ha := n00090_sound x t hnz
  have hb := n00092_sound x t hnz
  have hraw := rawMul_sound n00090_pair n00092_pair x t ha.1 hb.1
  have hred := checkReduction_sound n00093_checked x t hraw.1
  dsimp only [n00093_reduction] at hred
  refine ⟨hred.1, ?_⟩
  rw [← hred.2, hraw.2]
  simp only [n00093_expression, ha.2, hb.2]
theorem n00094_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00094_pair.NonzeroDenominator x t ∧ n00094_pair.value x t = n00094_expression x t := by
  have ha := n00089_sound x t hnz
  have hb := n00093_sound x t hnz
  have hraw := rawAdd_sound n00089_pair n00093_pair x t ha.1 hb.1
  have hred := checkReduction_sound n00094_checked x t hraw.1
  dsimp only [n00094_reduction] at hred
  refine ⟨hred.1, ?_⟩
  rw [← hred.2, hraw.2]
  simp only [n00094_expression, ha.2, hb.2]
theorem n00095_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00095_pair.NonzeroDenominator x t ∧ n00095_pair.value x t = n00095_expression x t := by
  have ha := n00038_sound x t hnz
  have hb := n00084_sound x t hnz
  have hraw := rawMul_sound n00038_pair n00084_pair x t ha.1 hb.1
  have hred := checkReduction_sound n00095_checked x t hraw.1
  dsimp only [n00095_reduction] at hred
  refine ⟨hred.1, ?_⟩
  rw [← hred.2, hraw.2]
  simp only [n00095_expression, ha.2, hb.2]
theorem n00096_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00096_pair.NonzeroDenominator x t ∧ n00096_pair.value x t = n00096_expression x t := by
  have ha := n00075_sound x t hnz
  have hb := n00092_sound x t hnz
  have hraw := rawMul_sound n00075_pair n00092_pair x t ha.1 hb.1
  have hred := checkReduction_sound n00096_checked x t hraw.1
  dsimp only [n00096_reduction] at hred
  refine ⟨hred.1, ?_⟩
  rw [← hred.2, hraw.2]
  simp only [n00096_expression, ha.2, hb.2]
theorem n00097_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00097_pair.NonzeroDenominator x t ∧ n00097_pair.value x t = n00097_expression x t := by
  have ha := n00010_sound x t hnz
  have hb := n00096_sound x t hnz
  have hraw := rawAdd_sound n00010_pair n00096_pair x t ha.1 hb.1
  have hred := checkReduction_sound n00097_checked x t hraw.1
  dsimp only [n00097_reduction] at hred
  refine ⟨hred.1, ?_⟩
  rw [← hred.2, hraw.2]
  simp only [n00097_expression, ha.2, hb.2]
theorem n00098_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00098_pair.NonzeroDenominator x t ∧ n00098_pair.value x t = n00098_expression x t := by
  have ha := n00095_sound x t hnz
  have hb := n00097_sound x t hnz
  have hraw := rawMul_sound n00095_pair n00097_pair x t ha.1 hb.1
  have hred := checkReduction_sound n00098_checked x t hraw.1
  dsimp only [n00098_reduction] at hred
  refine ⟨hred.1, ?_⟩
  rw [← hred.2, hraw.2]
  simp only [n00098_expression, ha.2, hb.2]
theorem n00099_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00099_pair.NonzeroDenominator x t ∧ n00099_pair.value x t = n00099_expression x t := by
  have ha := n00094_sound x t hnz
  have hb := n00098_sound x t hnz
  have hraw := rawSub_sound n00094_pair n00098_pair x t ha.1 hb.1
  have hred := checkReduction_sound n00099_checked x t hraw.1
  dsimp only [n00099_reduction] at hred
  refine ⟨hred.1, ?_⟩
  rw [← hred.2, hraw.2]
  simp only [n00099_expression, ha.2, hb.2]
theorem n00100_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00100_pair.NonzeroDenominator x t ∧ n00100_pair.value x t = n00100_expression x t := by
  have ha := n00082_sound x t hnz
  have hb := n00091_sound x t hnz
  have hraw := rawAdd_sound n00082_pair n00091_pair x t ha.1 hb.1
  have hred := checkReduction_sound n00100_checked x t hraw.1
  dsimp only [n00100_reduction] at hred
  refine ⟨hred.1, ?_⟩
  rw [← hred.2, hraw.2]
  simp only [n00100_expression, ha.2, hb.2]
theorem n00101_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00101_pair.NonzeroDenominator x t ∧ n00101_pair.value x t = n00101_expression x t := by
  have ha := n00090_sound x t hnz
  have hb := n00100_sound x t hnz
  have hraw := rawMul_sound n00090_pair n00100_pair x t ha.1 hb.1
  have hred := checkReduction_sound n00101_checked x t hraw.1
  dsimp only [n00101_reduction] at hred
  refine ⟨hred.1, ?_⟩
  rw [← hred.2, hraw.2]
  simp only [n00101_expression, ha.2, hb.2]
theorem n00102_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00102_pair.NonzeroDenominator x t ∧ n00102_pair.value x t = n00102_expression x t := by
  have ha := n00089_sound x t hnz
  have hb := n00101_sound x t hnz
  have hraw := rawAdd_sound n00089_pair n00101_pair x t ha.1 hb.1
  have hred := checkReduction_sound n00102_checked x t hraw.1
  dsimp only [n00102_reduction] at hred
  refine ⟨hred.1, ?_⟩
  rw [← hred.2, hraw.2]
  simp only [n00102_expression, ha.2, hb.2]
theorem n00103_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00103_pair.NonzeroDenominator x t ∧ n00103_pair.value x t = n00103_expression x t := by
  have ha := n00075_sound x t hnz
  have hb := n00100_sound x t hnz
  have hraw := rawMul_sound n00075_pair n00100_pair x t ha.1 hb.1
  have hred := checkReduction_sound n00103_checked x t hraw.1
  dsimp only [n00103_reduction] at hred
  refine ⟨hred.1, ?_⟩
  rw [← hred.2, hraw.2]
  simp only [n00103_expression, ha.2, hb.2]
theorem n00104_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00104_pair.NonzeroDenominator x t ∧ n00104_pair.value x t = n00104_expression x t := by
  have ha := n00010_sound x t hnz
  have hb := n00103_sound x t hnz
  have hraw := rawAdd_sound n00010_pair n00103_pair x t ha.1 hb.1
  have hred := checkReduction_sound n00104_checked x t hraw.1
  dsimp only [n00104_reduction] at hred
  refine ⟨hred.1, ?_⟩
  rw [← hred.2, hraw.2]
  simp only [n00104_expression, ha.2, hb.2]
theorem n00105_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00105_pair.NonzeroDenominator x t ∧ n00105_pair.value x t = n00105_expression x t := by
  have ha := n00095_sound x t hnz
  have hb := n00104_sound x t hnz
  have hraw := rawMul_sound n00095_pair n00104_pair x t ha.1 hb.1
  have hred := checkReduction_sound n00105_checked x t hraw.1
  dsimp only [n00105_reduction] at hred
  refine ⟨hred.1, ?_⟩
  rw [← hred.2, hraw.2]
  simp only [n00105_expression, ha.2, hb.2]
theorem n00106_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00106_pair.NonzeroDenominator x t ∧ n00106_pair.value x t = n00106_expression x t := by
  have ha := n00102_sound x t hnz
  have hb := n00105_sound x t hnz
  have hraw := rawSub_sound n00102_pair n00105_pair x t ha.1 hb.1
  have hred := checkReduction_sound n00106_checked x t hraw.1
  dsimp only [n00106_reduction] at hred
  refine ⟨hred.1, ?_⟩
  rw [← hred.2, hraw.2]
  simp only [n00106_expression, ha.2, hb.2]
theorem n00107_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00107_pair.NonzeroDenominator x t ∧ n00107_pair.value x t = n00107_expression x t := by
  have ha := n00042_sound x t hnz
  have hb := n00039_sound x t hnz
  have hraw := rawMul_sound n00042_pair n00039_pair x t ha.1 hb.1
  have hred := checkReduction_sound n00107_checked x t hraw.1
  dsimp only [n00107_reduction] at hred
  refine ⟨hred.1, ?_⟩
  rw [← hred.2, hraw.2]
  simp only [n00107_expression, ha.2, hb.2]
theorem n00108_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00108_pair.NonzeroDenominator x t ∧ n00108_pair.value x t = n00108_expression x t := by
  have ha := n00107_sound x t hnz
  have hb := n00081_sound x t hnz
  have hraw := rawAdd_sound n00107_pair n00081_pair x t ha.1 hb.1
  have hred := checkReduction_sound n00108_checked x t hraw.1
  dsimp only [n00108_reduction] at hred
  refine ⟨hred.1, ?_⟩
  rw [← hred.2, hraw.2]
  simp only [n00108_expression, ha.2, hb.2]
theorem n00109_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00109_pair.NonzeroDenominator x t ∧ n00109_pair.value x t = n00109_expression x t := by
  have ha := n00010_sound x t hnz
  have hb := n00090_sound x t hnz
  have hraw := rawMul_sound n00010_pair n00090_pair x t ha.1 hb.1
  have hred := checkReduction_sound n00109_checked x t hraw.1
  dsimp only [n00109_reduction] at hred
  refine ⟨hred.1, ?_⟩
  rw [← hred.2, hraw.2]
  simp only [n00109_expression, ha.2, hb.2]
theorem n00110_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00110_pair.NonzeroDenominator x t ∧ n00110_pair.value x t = n00110_expression x t := by
  have ha := n00109_sound x t hnz
  have hb := n00083_sound x t hnz
  have hraw := rawMul_sound n00109_pair n00083_pair x t ha.1 hb.1
  have hred := checkReduction_sound n00110_checked x t hraw.1
  dsimp only [n00110_reduction] at hred
  refine ⟨hred.1, ?_⟩
  rw [← hred.2, hraw.2]
  simp only [n00110_expression, ha.2, hb.2]
theorem n00111_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00111_pair.NonzeroDenominator x t ∧ n00111_pair.value x t = n00111_expression x t := by
  have ha := n00010_sound x t hnz
  have hb := n00108_sound x t hnz
  have hraw := rawMul_sound n00010_pair n00108_pair x t ha.1 hb.1
  have hred := checkReduction_sound n00111_checked x t hraw.1
  dsimp only [n00111_reduction] at hred
  refine ⟨hred.1, ?_⟩
  rw [← hred.2, hraw.2]
  simp only [n00111_expression, ha.2, hb.2]
theorem n00112_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00112_pair.NonzeroDenominator x t ∧ n00112_pair.value x t = n00112_expression x t := by
  have ha := n00075_sound x t hnz
  have hb := n00083_sound x t hnz
  have hraw := rawMul_sound n00075_pair n00083_pair x t ha.1 hb.1
  have hred := checkReduction_sound n00112_checked x t hraw.1
  dsimp only [n00112_reduction] at hred
  refine ⟨hred.1, ?_⟩
  rw [← hred.2, hraw.2]
  simp only [n00112_expression, ha.2, hb.2]
theorem n00113_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00113_pair.NonzeroDenominator x t ∧ n00113_pair.value x t = n00113_expression x t := by
  have ha := n00005_sound x t hnz
  have hb := n00112_sound x t hnz
  have hraw := rawSub_sound n00005_pair n00112_pair x t ha.1 hb.1
  have hred := checkReduction_sound n00113_checked x t hraw.1
  dsimp only [n00113_reduction] at hred
  refine ⟨hred.1, ?_⟩
  rw [← hred.2, hraw.2]
  simp only [n00113_expression, ha.2, hb.2]
theorem n00114_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00114_pair.NonzeroDenominator x t ∧ n00114_pair.value x t = n00114_expression x t := by
  have ha := n00111_sound x t hnz
  have hb := n00113_sound x t hnz
  have hraw := rawMul_sound n00111_pair n00113_pair x t ha.1 hb.1
  have hred := checkReduction_sound n00114_checked x t hraw.1
  dsimp only [n00114_reduction] at hred
  refine ⟨hred.1, ?_⟩
  rw [← hred.2, hraw.2]
  simp only [n00114_expression, ha.2, hb.2]
theorem n00115_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00115_pair.NonzeroDenominator x t ∧ n00115_pair.value x t = n00115_expression x t := by
  have ha := n00114_sound x t hnz
  have hb := n00049_sound x t hnz
  have hraw := rawSub_sound n00114_pair n00049_pair x t ha.1 hb.1
  have hred := checkReduction_sound n00115_checked x t hraw.1
  dsimp only [n00115_reduction] at hred
  refine ⟨hred.1, ?_⟩
  rw [← hred.2, hraw.2]
  simp only [n00115_expression, ha.2, hb.2]
theorem n00116_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00116_pair.NonzeroDenominator x t ∧ n00116_pair.value x t = n00116_expression x t := by
  have ha := n00115_sound x t hnz
  have hb := n00054_sound x t hnz
  have hraw := rawSub_sound n00115_pair n00054_pair x t ha.1 hb.1
  have hred := checkReduction_sound n00116_checked x t hraw.1
  dsimp only [n00116_reduction] at hred
  refine ⟨hred.1, ?_⟩
  rw [← hred.2, hraw.2]
  simp only [n00116_expression, ha.2, hb.2]
theorem n00117_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00117_pair.NonzeroDenominator x t ∧ n00117_pair.value x t = n00117_expression x t := by
  have ha := n00038_sound x t hnz
  have hb := n00116_sound x t hnz
  have hraw := rawMul_sound n00038_pair n00116_pair x t ha.1 hb.1
  have hred := checkReduction_sound n00117_checked x t hraw.1
  dsimp only [n00117_reduction] at hred
  refine ⟨hred.1, ?_⟩
  rw [← hred.2, hraw.2]
  simp only [n00117_expression, ha.2, hb.2]
theorem n00118_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00118_pair.NonzeroDenominator x t ∧ n00118_pair.value x t = n00118_expression x t := by
  have ha := n00110_sound x t hnz
  have hb := n00117_sound x t hnz
  have hraw := rawAdd_sound n00110_pair n00117_pair x t ha.1 hb.1
  have hred := checkReduction_sound n00118_checked x t hraw.1
  dsimp only [n00118_reduction] at hred
  refine ⟨hred.1, ?_⟩
  rw [← hred.2, hraw.2]
  simp only [n00118_expression, ha.2, hb.2]
theorem n00119_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00119_pair.NonzeroDenominator x t ∧ n00119_pair.value x t = n00119_expression x t := by
  have ha := n00118_sound x t hnz
  have hb := n00038_sound x t hnz
  have hd : n00038_pair.value x t ≠ 0 := by
    rw [hb.2]
    simpa only [divisorExpression] using hnz ⟨17, by decide⟩
  have hraw := rawDiv_sound n00118_pair n00038_pair x t ha.1 hb.1 hd
  have hred := checkReduction_sound n00119_checked x t hraw.1
  dsimp only [n00119_reduction] at hred
  refine ⟨hred.1, ?_⟩
  rw [← hred.2, hraw.2]
  simp only [n00119_expression, ha.2, hb.2]
theorem n00120_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00120_pair.NonzeroDenominator x t ∧ n00120_pair.value x t = n00120_expression x t := by
  have ha := n00109_sound x t hnz
  have hb := n00082_sound x t hnz
  have hraw := rawMul_sound n00109_pair n00082_pair x t ha.1 hb.1
  have hred := checkReduction_sound n00120_checked x t hraw.1
  dsimp only [n00120_reduction] at hred
  refine ⟨hred.1, ?_⟩
  rw [← hred.2, hraw.2]
  simp only [n00120_expression, ha.2, hb.2]
theorem n00121_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00121_pair.NonzeroDenominator x t ∧ n00121_pair.value x t = n00121_expression x t := by
  have ha := n00075_sound x t hnz
  have hb := n00082_sound x t hnz
  have hraw := rawMul_sound n00075_pair n00082_pair x t ha.1 hb.1
  have hred := checkReduction_sound n00121_checked x t hraw.1
  dsimp only [n00121_reduction] at hred
  refine ⟨hred.1, ?_⟩
  rw [← hred.2, hraw.2]
  simp only [n00121_expression, ha.2, hb.2]
theorem n00122_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00122_pair.NonzeroDenominator x t ∧ n00122_pair.value x t = n00122_expression x t := by
  have ha := n00005_sound x t hnz
  have hb := n00121_sound x t hnz
  have hraw := rawSub_sound n00005_pair n00121_pair x t ha.1 hb.1
  have hred := checkReduction_sound n00122_checked x t hraw.1
  dsimp only [n00122_reduction] at hred
  refine ⟨hred.1, ?_⟩
  rw [← hred.2, hraw.2]
  simp only [n00122_expression, ha.2, hb.2]
theorem n00123_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00123_pair.NonzeroDenominator x t ∧ n00123_pair.value x t = n00123_expression x t := by
  have ha := n00111_sound x t hnz
  have hb := n00122_sound x t hnz
  have hraw := rawMul_sound n00111_pair n00122_pair x t ha.1 hb.1
  have hred := checkReduction_sound n00123_checked x t hraw.1
  dsimp only [n00123_reduction] at hred
  refine ⟨hred.1, ?_⟩
  rw [← hred.2, hraw.2]
  simp only [n00123_expression, ha.2, hb.2]
theorem n00124_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00124_pair.NonzeroDenominator x t ∧ n00124_pair.value x t = n00124_expression x t := by
  have ha := n00123_sound x t hnz
  have hb := n00049_sound x t hnz
  have hraw := rawSub_sound n00123_pair n00049_pair x t ha.1 hb.1
  have hred := checkReduction_sound n00124_checked x t hraw.1
  dsimp only [n00124_reduction] at hred
  refine ⟨hred.1, ?_⟩
  rw [← hred.2, hraw.2]
  simp only [n00124_expression, ha.2, hb.2]
theorem n00125_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00125_pair.NonzeroDenominator x t ∧ n00125_pair.value x t = n00125_expression x t := by
  have ha := n00124_sound x t hnz
  have hb := n00054_sound x t hnz
  have hraw := rawSub_sound n00124_pair n00054_pair x t ha.1 hb.1
  have hred := checkReduction_sound n00125_checked x t hraw.1
  dsimp only [n00125_reduction] at hred
  refine ⟨hred.1, ?_⟩
  rw [← hred.2, hraw.2]
  simp only [n00125_expression, ha.2, hb.2]
theorem n00126_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00126_pair.NonzeroDenominator x t ∧ n00126_pair.value x t = n00126_expression x t := by
  have ha := n00038_sound x t hnz
  have hb := n00125_sound x t hnz
  have hraw := rawMul_sound n00038_pair n00125_pair x t ha.1 hb.1
  have hred := checkReduction_sound n00126_checked x t hraw.1
  dsimp only [n00126_reduction] at hred
  refine ⟨hred.1, ?_⟩
  rw [← hred.2, hraw.2]
  simp only [n00126_expression, ha.2, hb.2]
theorem n00127_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00127_pair.NonzeroDenominator x t ∧ n00127_pair.value x t = n00127_expression x t := by
  have ha := n00120_sound x t hnz
  have hb := n00126_sound x t hnz
  have hraw := rawAdd_sound n00120_pair n00126_pair x t ha.1 hb.1
  have hred := checkReduction_sound n00127_checked x t hraw.1
  dsimp only [n00127_reduction] at hred
  refine ⟨hred.1, ?_⟩
  rw [← hred.2, hraw.2]
  simp only [n00127_expression, ha.2, hb.2]
theorem n00128_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00128_pair.NonzeroDenominator x t ∧ n00128_pair.value x t = n00128_expression x t := by
  have ha := n00127_sound x t hnz
  have hb := n00038_sound x t hnz
  have hd : n00038_pair.value x t ≠ 0 := by
    rw [hb.2]
    simpa only [divisorExpression] using hnz ⟨18, by decide⟩
  have hraw := rawDiv_sound n00127_pair n00038_pair x t ha.1 hb.1 hd
  have hred := checkReduction_sound n00128_checked x t hraw.1
  dsimp only [n00128_reduction] at hred
  refine ⟨hred.1, ?_⟩
  rw [← hred.2, hraw.2]
  simp only [n00128_expression, ha.2, hb.2]
abbrev E2_guard_S_hi_pair := n00099_pair
abbrev E2_guard_S_hi_expression := n00099_expression
theorem E2_guard_S_hi_sound (x t : ℝ) (hnz : DivisorsNonzero x t) : n00099_pair.NonzeroDenominator x t ∧ n00099_pair.value x t = n00099_expression x t := n00099_sound x t hnz
#print axioms E2_guard_S_hi_sound
abbrev E2_guard_S_lo_pair := n00106_pair
abbrev E2_guard_S_lo_expression := n00106_expression
theorem E2_guard_S_lo_sound (x t : ℝ) (hnz : DivisorsNonzero x t) : n00106_pair.NonzeroDenominator x t ∧ n00106_pair.value x t = n00106_expression x t := n00106_sound x t hnz
#print axioms E2_guard_S_lo_sound
abbrev E2_guard_r_hi_pair := n00119_pair
abbrev E2_guard_r_hi_expression := n00119_expression
theorem E2_guard_r_hi_sound (x t : ℝ) (hnz : DivisorsNonzero x t) : n00119_pair.NonzeroDenominator x t ∧ n00119_pair.value x t = n00119_expression x t := n00119_sound x t hnz
#print axioms E2_guard_r_hi_sound
abbrev E2_guard_r_lo_pair := n00128_pair
abbrev E2_guard_r_lo_expression := n00128_expression
theorem E2_guard_r_lo_sound (x t : ℝ) (hnz : DivisorsNonzero x t) : n00128_pair.NonzeroDenominator x t ∧ n00128_pair.value x t = n00128_expression x t := n00128_sound x t hnz
#print axioms E2_guard_r_lo_sound
end
end F4U.Light.Linking.Generated.DAG_E2_FULL_01
