module
public import Erdos993Lean.F4U.Light.Linking.Rational
@[expose] public section
set_option maxRecDepth 4096
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
namespace F4U.Light.Linking.Generated.DAG_E1_FULL_01
noncomputable section
def n00000_expression (x t : ℝ) : ℝ := x
def n00000_pair : RationalPair := ⟨[[0, 1]], [[1]]⟩
def n00001_expression (x t : ℝ) : ℝ := t
def n00001_pair : RationalPair := ⟨[[], [1]], [[1]]⟩
def n00002_expression (x t : ℝ) : ℝ := (13 : ℝ)/(10 : ℝ)
def n00002_pair : RationalPair := ⟨[[13]], [[10]]⟩
def n00003_expression (x t : ℝ) : ℝ := (29 : ℝ)/(20 : ℝ)
def n00003_pair : RationalPair := ⟨[[29]], [[20]]⟩
def n00004_expression (x t : ℝ) : ℝ := (11 : ℝ)/(8 : ℝ)
def n00004_pair : RationalPair := ⟨[[11]], [[8]]⟩
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
def n00008_pair : RationalPair := ⟨[[49]], [[20]]⟩
def n00008_reduction : Reduction := ⟨rawAdd n00005_pair n00003_pair, n00008_pair, [[1]], 1⟩
theorem n00008_checked : checkReduction n00008_reduction = true := by decide
def n00009_expression (x t : ℝ) : ℝ := n00003_expression x t / n00008_expression x t
def n00009_pair : RationalPair := ⟨[[29]], [[49]]⟩
def n00009_reduction : Reduction := ⟨rawDiv n00003_pair n00008_pair, n00009_pair, [[20]], 1⟩
theorem n00009_checked : checkReduction n00009_reduction = true := by decide
def n00010_expression (x t : ℝ) : ℝ := (2 : ℝ)/(1 : ℝ)
def n00010_pair : RationalPair := ⟨[[2]], [[1]]⟩
def n00011_expression (x t : ℝ) : ℝ := n00009_expression x t / n00010_expression x t
def n00011_pair : RationalPair := ⟨[[29]], [[98]]⟩
def n00011_reduction : Reduction := ⟨rawDiv n00009_pair n00010_pair, n00011_pair, [[1]], 1⟩
theorem n00011_checked : checkReduction n00011_reduction = true := by decide
def n00012_expression (x t : ℝ) : ℝ := n00005_expression x t - n00011_expression x t
def n00012_pair : RationalPair := ⟨[[69]], [[98]]⟩
def n00012_reduction : Reduction := ⟨rawSub n00005_pair n00011_pair, n00012_pair, [[1]], 1⟩
theorem n00012_checked : checkReduction n00012_reduction = true := by decide
def n00013_expression (x t : ℝ) : ℝ := n00009_expression x t * n00012_expression x t
def n00013_pair : RationalPair := ⟨[[2001]], [[4802]]⟩
def n00013_reduction : Reduction := ⟨rawMul n00009_pair n00012_pair, n00013_pair, [[1]], 1⟩
theorem n00013_checked : checkReduction n00013_reduction = true := by decide
def n00014_expression (x t : ℝ) : ℝ := n00003_expression x t - n00002_expression x t
def n00014_pair : RationalPair := ⟨[[3]], [[20]]⟩
def n00014_reduction : Reduction := ⟨rawSub n00003_pair n00002_pair, n00014_pair, [[10]], 1⟩
theorem n00014_checked : checkReduction n00014_reduction = true := by decide
def n00015_expression (x t : ℝ) : ℝ := n00014_expression x t ^ 2
def n00015_pair : RationalPair := ⟨[[9]], [[400]]⟩
def n00015_reduction : Reduction := ⟨rawPow n00014_pair 2, n00015_pair, [[1]], 1⟩
theorem n00015_checked : checkReduction n00015_reduction = true := by decide
def n00016_expression (x t : ℝ) : ℝ := n00013_expression x t * n00015_expression x t
def n00016_pair : RationalPair := ⟨[[18009]], [[1920800]]⟩
def n00016_reduction : Reduction := ⟨rawMul n00013_pair n00015_pair, n00016_pair, [[1]], 1⟩
theorem n00016_checked : checkReduction n00016_reduction = true := by decide
def n00017_expression (x t : ℝ) : ℝ := n00002_expression x t ^ 2
def n00017_pair : RationalPair := ⟨[[169]], [[100]]⟩
def n00017_reduction : Reduction := ⟨rawPow n00002_pair 2, n00017_pair, [[1]], 1⟩
theorem n00017_checked : checkReduction n00017_reduction = true := by decide
def n00018_expression (x t : ℝ) : ℝ := (8 : ℝ)/(1 : ℝ)
def n00018_pair : RationalPair := ⟨[[8]], [[1]]⟩
def n00019_expression (x t : ℝ) : ℝ := n00018_expression x t * n00017_expression x t
def n00019_pair : RationalPair := ⟨[[338]], [[25]]⟩
def n00019_reduction : Reduction := ⟨rawMul n00018_pair n00017_pair, n00019_pair, [[4]], 1⟩
theorem n00019_checked : checkReduction n00019_reduction = true := by decide
def n00020_expression (x t : ℝ) : ℝ := n00016_expression x t / n00019_expression x t
def n00020_pair : RationalPair := ⟨[[18009]], [[25969216]]⟩
def n00020_reduction : Reduction := ⟨rawDiv n00016_pair n00019_pair, n00020_pair, [[25]], 1⟩
theorem n00020_checked : checkReduction n00020_reduction = true := by decide
def n00021_expression (x t : ℝ) : ℝ := n00003_expression x t - n00000_expression x t
def n00021_pair : RationalPair := ⟨[[29, -20]], [[20]]⟩
def n00021_reduction : Reduction := ⟨rawSub n00003_pair n00000_pair, n00021_pair, [[1]], 1⟩
theorem n00021_checked : checkReduction n00021_reduction = true := by decide
def n00022_expression (x t : ℝ) : ℝ := n00021_expression x t / n00014_expression x t
def n00022_pair : RationalPair := ⟨[[29, -20]], [[3]]⟩
def n00022_reduction : Reduction := ⟨rawDiv n00021_pair n00014_pair, n00022_pair, [[20]], 1⟩
theorem n00022_checked : checkReduction n00022_reduction = true := by decide
def n00023_expression (x t : ℝ) : ℝ := n00000_expression x t - n00002_expression x t
def n00023_pair : RationalPair := ⟨[[-13, 10]], [[10]]⟩
def n00023_reduction : Reduction := ⟨rawSub n00000_pair n00002_pair, n00023_pair, [[1]], 1⟩
theorem n00023_checked : checkReduction n00023_reduction = true := by decide
def n00024_expression (x t : ℝ) : ℝ := n00023_expression x t / n00014_expression x t
def n00024_pair : RationalPair := ⟨[[-26, 20]], [[3]]⟩
def n00024_reduction : Reduction := ⟨rawDiv n00023_pair n00014_pair, n00024_pair, [[10]], 1⟩
theorem n00024_checked : checkReduction n00024_reduction = true := by decide
def n00025_expression (x t : ℝ) : ℝ := (3500567 : ℝ)/(100000000 : ℝ)
def n00025_pair : RationalPair := ⟨[[3500567]], [[100000000]]⟩
def n00026_expression (x t : ℝ) : ℝ := n00022_expression x t * n00025_expression x t
def n00026_pair : RationalPair := ⟨[[101516443, -70011340]], [[300000000]]⟩
def n00026_reduction : Reduction := ⟨rawMul n00022_pair n00025_pair, n00026_pair, [[1]], 1⟩
theorem n00026_checked : checkReduction n00026_reduction = true := by decide
def n00027_expression (x t : ℝ) : ℝ := (5922933 : ℝ)/(100000000 : ℝ)
def n00027_pair : RationalPair := ⟨[[5922933]], [[100000000]]⟩
def n00028_expression (x t : ℝ) : ℝ := n00024_expression x t * n00027_expression x t
def n00028_pair : RationalPair := ⟨[[-25666043, 19743110]], [[50000000]]⟩
def n00028_reduction : Reduction := ⟨rawMul n00024_pair n00027_pair, n00028_pair, [[6]], 1⟩
theorem n00028_checked : checkReduction n00028_reduction = true := by decide
def n00029_expression (x t : ℝ) : ℝ := n00026_expression x t + n00028_expression x t
def n00029_pair : RationalPair := ⟨[[-10495963, 9689464]], [[60000000]]⟩
def n00029_reduction : Reduction := ⟨rawAdd n00026_pair n00028_pair, n00029_pair, [[250000000]], 1⟩
theorem n00029_checked : checkReduction n00029_reduction = true := by decide
def n00030_expression (x t : ℝ) : ℝ := n00029_expression x t + n00020_expression x t
def n00030_pair : RationalPair := ⟨[[-4242052973047, 3931684117816]], [[24346140000000]]⟩
def n00030_reduction : Reduction := ⟨rawAdd n00029_pair n00020_pair, n00030_pair, [[64]], 1⟩
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
def n00043_expression (x t : ℝ) : ℝ := (44917 : ℝ)/(1 : ℝ)
def n00043_pair : RationalPair := ⟨[[44917]], [[1]]⟩
def n00044_expression (x t : ℝ) : ℝ := n00000_expression x t - n00004_expression x t
def n00044_pair : RationalPair := ⟨[[-11, 8]], [[8]]⟩
def n00044_reduction : Reduction := ⟨rawSub n00000_pair n00004_pair, n00044_pair, [[1]], 1⟩
theorem n00044_checked : checkReduction n00044_reduction = true := by decide
def n00045_expression (x t : ℝ) : ℝ := (29958 : ℝ)/(1 : ℝ)
def n00045_pair : RationalPair := ⟨[[29958]], [[1]]⟩
def n00046_expression (x t : ℝ) : ℝ := n00045_expression x t * n00044_expression x t
def n00046_pair : RationalPair := ⟨[[-164769, 119832]], [[4]]⟩
def n00046_reduction : Reduction := ⟨rawMul n00045_pair n00044_pair, n00046_pair, [[2]], 1⟩
theorem n00046_checked : checkReduction n00046_reduction = true := by decide
def n00047_expression (x t : ℝ) : ℝ := n00043_expression x t + n00046_expression x t
def n00047_pair : RationalPair := ⟨[[14899, 119832]], [[4]]⟩
def n00047_reduction : Reduction := ⟨rawAdd n00043_pair n00046_pair, n00047_pair, [[1]], 1⟩
theorem n00047_checked : checkReduction n00047_reduction = true := by decide
def n00048_expression (x t : ℝ) : ℝ := (65536 : ℝ)/(1 : ℝ)
def n00048_pair : RationalPair := ⟨[[65536]], [[1]]⟩
def n00049_expression (x t : ℝ) : ℝ := n00047_expression x t / n00048_expression x t
def n00049_pair : RationalPair := ⟨[[14899, 119832]], [[262144]]⟩
def n00049_reduction : Reduction := ⟨rawDiv n00047_pair n00048_pair, n00049_pair, [[1]], 1⟩
theorem n00049_checked : checkReduction n00049_reduction = true := by decide
def n00050_expression (x t : ℝ) : ℝ := (28533 : ℝ)/(1 : ℝ)
def n00050_pair : RationalPair := ⟨[[28533]], [[1]]⟩
def n00051_expression (x t : ℝ) : ℝ := (57271 : ℝ)/(1 : ℝ)
def n00051_pair : RationalPair := ⟨[[57271]], [[1]]⟩
def n00052_expression (x t : ℝ) : ℝ := n00051_expression x t * n00044_expression x t
def n00052_pair : RationalPair := ⟨[[-629981, 458168]], [[8]]⟩
def n00052_reduction : Reduction := ⟨rawMul n00051_pair n00044_pair, n00052_pair, [[1]], 1⟩
theorem n00052_checked : checkReduction n00052_reduction = true := by decide
def n00053_expression (x t : ℝ) : ℝ := n00050_expression x t + n00052_expression x t
def n00053_pair : RationalPair := ⟨[[-401717, 458168]], [[8]]⟩
def n00053_reduction : Reduction := ⟨rawAdd n00050_pair n00052_pair, n00053_pair, [[1]], 1⟩
theorem n00053_checked : checkReduction n00053_reduction = true := by decide
def n00054_expression (x t : ℝ) : ℝ := n00053_expression x t / n00048_expression x t
def n00054_pair : RationalPair := ⟨[[-401717, 458168]], [[524288]]⟩
def n00054_reduction : Reduction := ⟨rawDiv n00053_pair n00048_pair, n00054_pair, [[1]], 1⟩
theorem n00054_checked : checkReduction n00054_reduction = true := by decide
def n00055_expression (x t : ℝ) : ℝ := (17821 : ℝ)/(1 : ℝ)
def n00055_pair : RationalPair := ⟨[[17821]], [[1]]⟩
def n00056_expression (x t : ℝ) : ℝ := (20483 : ℝ)/(1 : ℝ)
def n00056_pair : RationalPair := ⟨[[20483]], [[1]]⟩
def n00057_expression (x t : ℝ) : ℝ := n00056_expression x t * n00044_expression x t
def n00057_pair : RationalPair := ⟨[[-225313, 163864]], [[8]]⟩
def n00057_reduction : Reduction := ⟨rawMul n00056_pair n00044_pair, n00057_pair, [[1]], 1⟩
theorem n00057_checked : checkReduction n00057_reduction = true := by decide
def n00058_expression (x t : ℝ) : ℝ := n00055_expression x t + n00057_expression x t
def n00058_pair : RationalPair := ⟨[[-82745, 163864]], [[8]]⟩
def n00058_reduction : Reduction := ⟨rawAdd n00055_pair n00057_pair, n00058_pair, [[1]], 1⟩
theorem n00058_checked : checkReduction n00058_reduction = true := by decide
def n00059_expression (x t : ℝ) : ℝ := n00058_expression x t / n00048_expression x t
def n00059_pair : RationalPair := ⟨[[-82745, 163864]], [[524288]]⟩
def n00059_reduction : Reduction := ⟨rawDiv n00058_pair n00048_pair, n00059_pair, [[1]], 1⟩
theorem n00059_checked : checkReduction n00059_reduction = true := by decide
def n00060_expression (x t : ℝ) : ℝ := (3064 : ℝ)/(1 : ℝ)
def n00060_pair : RationalPair := ⟨[[3064]], [[1]]⟩
def n00061_expression (x t : ℝ) : ℝ := ((-4423) : ℝ)/(1 : ℝ)
def n00061_pair : RationalPair := ⟨[[-4423]], [[1]]⟩
def n00062_expression (x t : ℝ) : ℝ := n00061_expression x t * n00044_expression x t
def n00062_pair : RationalPair := ⟨[[48653, -35384]], [[8]]⟩
def n00062_reduction : Reduction := ⟨rawMul n00061_pair n00044_pair, n00062_pair, [[1]], 1⟩
theorem n00062_checked : checkReduction n00062_reduction = true := by decide
def n00063_expression (x t : ℝ) : ℝ := n00060_expression x t + n00062_expression x t
def n00063_pair : RationalPair := ⟨[[73165, -35384]], [[8]]⟩
def n00063_reduction : Reduction := ⟨rawAdd n00060_pair n00062_pair, n00063_pair, [[1]], 1⟩
theorem n00063_checked : checkReduction n00063_reduction = true := by decide
def n00064_expression (x t : ℝ) : ℝ := n00063_expression x t / n00048_expression x t
def n00064_pair : RationalPair := ⟨[[73165, -35384]], [[524288]]⟩
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
def n00081_pair : RationalPair := ⟨[[-3971760, -6035688, 12966032, 24206344, 8762659, 819320], [0, 0, 2978820, -1265384, -8348934, -1638640], [0, 0, 0, 0, -413725, 819320]], [[25165824, 100663296, 125829120, 50331648, 6291456], [0, 0, -25165824, -50331648, -12582912], [0, 0, 0, 0, 6291456]]⟩
def n00081_reduction : Reduction := ⟨rawMul n00059_pair n00080_pair, n00081_pair, [[1]], 1⟩
theorem n00081_checked : checkReduction n00081_reduction = true := by decide
def n00082_expression (x t : ℝ) : ℝ := (3 : ℝ)/(4 : ℝ)
def n00082_pair : RationalPair := ⟨[[3]], [[4]]⟩
def n00083_expression (x t : ℝ) : ℝ := (6 : ℝ)/(7 : ℝ)
def n00083_pair : RationalPair := ⟨[[6]], [[7]]⟩
def n00084_expression (x t : ℝ) : ℝ := n00039_expression x t + n00081_expression x t
def n00084_pair : RationalPair := ⟨[[21194064, 69461784, 75880592, 36789256, 8762659, 819320], [0, 0, -9604092, -13848296, -8348934, -1638640], [0, 0, 0, 0, -413725, 819320]], [[25165824, 100663296, 125829120, 50331648, 6291456], [0, 0, -25165824, -50331648, -12582912], [0, 0, 0, 0, 6291456]]⟩
def n00084_reduction : Reduction := ⟨rawAdd n00039_pair n00081_pair, n00084_pair, [[-2, -4, -1], [0, 0, 1]], 1⟩
theorem n00084_checked : checkReduction n00084_reduction = true := by decide
def n00085_expression (x t : ℝ) : ℝ := (10 : ℝ)/(1 : ℝ)
def n00085_pair : RationalPair := ⟨[[10]], [[1]]⟩
def n00086_expression (x t : ℝ) : ℝ := n00085_expression x t * n00064_expression x t
def n00086_pair : RationalPair := ⟨[[365825, -176920]], [[262144]]⟩
def n00086_reduction : Reduction := ⟨rawMul n00085_pair n00064_pair, n00086_pair, [[2]], 1⟩
theorem n00086_checked : checkReduction n00086_reduction = true := by decide
def n00087_expression (x t : ℝ) : ℝ := n00049_expression x t + n00054_expression x t
def n00087_pair : RationalPair := ⟨[[-371919, 697832]], [[524288]]⟩
def n00087_reduction : Reduction := ⟨rawAdd n00049_pair n00054_pair, n00087_pair, [[262144]], 1⟩
theorem n00087_checked : checkReduction n00087_reduction = true := by decide
def n00088_expression (x t : ℝ) : ℝ := n00038_expression x t * n00087_expression x t
def n00088_pair : RationalPair := ⟨[[0, 743838, -1023745, -697832], [0, 0, -371919, 697832]], [[-1048576, -2097152, -524288], [0, 0, 524288]]⟩
def n00088_reduction : Reduction := ⟨rawMul n00038_pair n00087_pair, n00088_pair, [[1]], 1⟩
theorem n00088_checked : checkReduction n00088_reduction = true := by decide
def n00089_expression (x t : ℝ) : ℝ := n00086_expression x t + n00088_expression x t
def n00089_pair : RationalPair := ⟨[[-1463300, -1475082, -340035, -343992], [0, 0, 359731, 343992]], [[-1048576, -2097152, -524288], [0, 0, 524288]]⟩
def n00089_reduction : Reduction := ⟨rawAdd n00086_pair n00088_pair, n00089_pair, [[262144]], 1⟩
theorem n00089_checked : checkReduction n00089_reduction = true := by decide
def n00090_expression (x t : ℝ) : ℝ := n00059_expression x t - n00064_expression x t
def n00090_pair : RationalPair := ⟨[[-77955, 99624]], [[262144]]⟩
def n00090_reduction : Reduction := ⟨rawSub n00059_pair n00064_pair, n00090_pair, [[1048576]], 1⟩
theorem n00090_checked : checkReduction n00090_reduction = true := by decide
def n00091_expression (x t : ℝ) : ℝ := n00085_expression x t * n00030_expression x t
def n00091_pair : RationalPair := ⟨[[-4242052973047, 3931684117816]], [[2434614000000]]⟩
def n00091_reduction : Reduction := ⟨rawMul n00085_pair n00030_pair, n00091_pair, [[10]], 1⟩
theorem n00091_checked : checkReduction n00091_reduction = true := by decide
def n00092_expression (x t : ℝ) : ℝ := n00083_expression x t + n00091_expression x t
def n00092_pair : RationalPair := ⟨[[-2155240973047, 3931684117816]], [[2434614000000]]⟩
def n00092_reduction : Reduction := ⟨rawAdd n00083_pair n00091_pair, n00092_pair, [[7]], 1⟩
theorem n00092_checked : checkReduction n00092_reduction = true := by decide
def n00093_expression (x t : ℝ) : ℝ := n00090_expression x t * n00092_expression x t
def n00093_pair : RationalPair := ⟨[[56003936684626295, -173736054034393536, 130563366184433728]], [[212739817472000000]]⟩
def n00093_reduction : Reduction := ⟨rawMul n00090_pair n00092_pair, n00093_pair, [[3]], 1⟩
theorem n00093_checked : checkReduction n00093_reduction = true := by decide
def n00094_expression (x t : ℝ) : ℝ := n00089_expression x t + n00093_expression x t
def n00094_pair : RationalPair := ⟨[[-705769651069252590, -475086186727718108, 239837885169080393, -488098700551341376, -130563366184433728], [0, 0, 201971624823626295, -34154764186393536, 130563366184433728]], [[-425479634944000000, -850959269888000000, -212739817472000000], [0, 0, 212739817472000000]]⟩
def n00094_reduction : Reduction := ⟨rawAdd n00089_pair n00093_pair, n00094_pair, [[524288]], 1⟩
theorem n00094_checked : checkReduction n00094_reduction = true := by decide
def n00095_expression (x t : ℝ) : ℝ := n00038_expression x t * n00084_expression x t
def n00095_pair : RationalPair := ⟨[[0, -42388128, -160117632, -221222968, -149459104, -54314574, -10401299, -819320], [0, 0, 21194064, 88669968, 113181276, 67335420, 20388873, 2457960], [0, 0, 0, 0, -9604092, -13020846, -9573849, -2457960], [0, 0, 0, 0, 0, 0, -413725, 819320]], [[-50331648, -301989888, -679477248, -704643072, -339738624, -75497472, -6291456], [0, 0, 75497472, 301989888, 377487360, 150994944, 18874368], [0, 0, 0, 0, -37748736, -75497472, -18874368], [0, 0, 0, 0, 0, 0, 6291456]]⟩
def n00095_reduction : Reduction := ⟨rawMul n00038_pair n00084_pair, n00095_pair, [[1]], 1⟩
theorem n00095_checked : checkReduction n00095_reduction = true := by decide
def n00096_expression (x t : ℝ) : ℝ := n00075_expression x t * n00092_expression x t
def n00096_pair : RationalPair := ⟨[[0, -103451566706256, 33543487595784, 229200232156577, 98292102945400], [0, -103451566706256, 85269270948912, 182255114736027, 11795052353448], [0, 0, 51725783353128, -49100358393597, -82565366474136], [0, 0, 0, -2155240973047, 3931684117816]], [[233722944000000, 525876624000000, 379799784000000, 87646104000000], [0, -175292208000000, -292153680000000, -116861472000000], [0, 0, 29215368000000, 29215368000000]]⟩
def n00096_reduction : Reduction := ⟨rawMul n00075_pair n00092_pair, n00096_pair, [[1]], 1⟩
theorem n00096_checked : checkReduction n00096_reduction = true := by decide
def n00097_expression (x t : ℝ) : ℝ := n00010_expression x t + n00096_expression x t
def n00097_pair : RationalPair := ⟨[[467445888000000, 948301681293744, 793143055595784, 404492440156577, 98292102945400], [0, -454035982706256, -499038089051088, -51467829263973, 11795052353448], [0, 0, 110156519353128, 9330377606403, -82565366474136], [0, 0, 0, -2155240973047, 3931684117816]], [[233722944000000, 525876624000000, 379799784000000, 87646104000000], [0, -175292208000000, -292153680000000, -116861472000000], [0, 0, 29215368000000, 29215368000000]]⟩
def n00097_reduction : Reduction := ⟨rawAdd n00010_pair n00096_pair, n00097_pair, [[1]], 1⟩
theorem n00097_checked : checkReduction n00097_reduction = true := by decide
def n00098_expression (x t : ℝ) : ℝ := n00095_expression x t * n00097_expression x t
def n00098_pair : RationalPair := ⟨[[0, 9907078066808832000000, 52567991828591405135616, 118150721943721186505472, 152820649684032951094032, 129347522463447627697560, 75392445586500221649184, 30066443559328374377248, 7810360627517403227523, 1192708926572522486240, 80532685785225128000], [0, 0, -9622867675779282864384, -46604187870129844062336, -85788313185760268061264, -82548469895997790653144, -48975652568623347252060, -20464710486397543363792, -6463870482905410420757, -1422264372562669599008, -151401449276223240640], [0, 0, 0, 2334664321187433432192, 12210020322854360451696, 18143989265778075157896, 10211930359849199822988, 1002130759996885486512, -1298912806136488746230, -439243610744772236736, -6442614862818010240], [0, 0, 0, 0, -45678315118180393008, -1124331864384186491400, -1317683022302830367444, -202421386443378479408, 623163780931293124122, 659681310696029891648, 148180141844814235520], [0, 0, 0, 0, 0, 0, 20699132587312908324, -53488347005733706960, 49940068157246092147, 12510214084569750496, -74090070922407117760], [0, 0, 0, 0, 0, 0, 0, 0, 891677071573870075, -3392468045680292640, 3221307431409005120]], [[5881830473465856000000, 45584186169360384000000, 145575304218279936000000, 247772108694749184000000, 243360735839649792000000, 140061088149405696000000, 45951800573952000000000, 7903709698719744000000, 551421606887424000000], [0, -1470457618366464000000, -19115949038764032000000, -79404711391789056000000, -152927592310112256000000, -151824749096337408000000, -78301868178014208000000, -19483563443355648000000, -1838072022958080000000], [0, 0, 0, 2205686427549696000000, 15439804992847872000000, 36393826054569984000000, 36393826054569984000000, 15439804992847872000000, 2205686427549696000000], [0, 0, 0, 0, 0, -1102843213774848000000, -4043758450507776000000, -4043758450507776000000, -1102843213774848000000], [0, 0, 0, 0, 0, 0, 0, 183807202295808000000, 183807202295808000000]]⟩
def n00098_reduction : Reduction := ⟨rawMul n00095_pair n00097_pair, n00098_pair, [[-2, -1], [0, 1]], 1⟩
theorem n00098_checked : checkReduction n00098_reduction = true := by decide
def n00099_expression (x t : ℝ) : ℝ := n00094_expression x t - n00098_expression x t
def n00099_pair : RationalPair := ⟨[[9756559656381347804160, 52760731402707892998912, 106276275676306268983296, 87422006879504909548416, 8987961307229016808560, -10367092086572260251480, 30085603511058747634976, 40164719837801458594496, 18178024975693556727645, 3569452105140427331104, 257887559364827094976], [0, -2439139914095336951040, -16763345153971553378304, -41465536142860547650944, -45950549564867341385136, -27289709098552553083752, -35041027857628309420260, -54043245304296568862576, -36783722905025902829611, -10240153793502068795104, -976666034557284169280], [0, 0, 0, 802489528298355994368, 5352523748343877352976, 14102278740957418003512, 17562883129230928967988, 20688307234165460225232, 20803384384758475620470, 9560893879861706298816, 1360123595463026902144], [0, 0, 0, 0, 45678315118180393008, -183467049530100221880, -2376593298087386157292, -2946463904933406249616, -3013421342423495806938, -2964371477587482102848, -825020632144918681472], [0, 0, 0, 0, 0, 0, -20699132587312908324, 227991830853346825840, 95053699433323011629, 70786818041736975392, 186896819305757858752], [0, 0, 0, 0, 0, 0, 0, 0, -891677071573870075, 3392468045680292640, -3221307431409005120]], [[5881830473465856000000, 45584186169360384000000, 145575304218279936000000, 247772108694749184000000, 243360735839649792000000, 140061088149405696000000, 45951800573952000000000, 7903709698719744000000, 551421606887424000000], [0, -1470457618366464000000, -19115949038764032000000, -79404711391789056000000, -152927592310112256000000, -151824749096337408000000, -78301868178014208000000, -19483563443355648000000, -1838072022958080000000], [0, 0, 0, 2205686427549696000000, 15439804992847872000000, 36393826054569984000000, 36393826054569984000000, 15439804992847872000000, 2205686427549696000000], [0, 0, 0, 0, 0, -1102843213774848000000, -4043758450507776000000, -4043758450507776000000, -1102843213774848000000], [0, 0, 0, 0, 0, 0, 0, 183807202295808000000, 183807202295808000000]]⟩
def n00099_reduction : Reduction := ⟨rawSub n00094_pair n00098_pair, n00099_pair, [[-425479634944000000, -850959269888000000, -212739817472000000], [0, 0, 212739817472000000]], 1⟩
theorem n00099_checked : checkReduction n00099_reduction = true := by decide
def n00100_expression (x t : ℝ) : ℝ := n00082_expression x t + n00091_expression x t
def n00100_pair : RationalPair := ⟨[[-2416092473047, 3931684117816]], [[2434614000000]]⟩
def n00100_reduction : Reduction := ⟨rawAdd n00082_pair n00091_pair, n00100_pair, [[4]], 1⟩
theorem n00100_checked : checkReduction n00100_reduction = true := by decide
def n00101_expression (x t : ℝ) : ℝ := n00090_expression x t * n00100_expression x t
def n00101_pair : RationalPair := ⟨[[62782162912126295, -182398410646393536, 130563366184433728]], [[212739817472000000]]⟩
def n00101_reduction : Reduction := ⟨rawMul n00090_pair n00100_pair, n00101_pair, [[3]], 1⟩
theorem n00101_checked : checkReduction n00101_reduction = true := by decide
def n00102_expression (x t : ℝ) : ℝ := n00089_expression x t + n00101_expression x t
def n00102_pair : RationalPair := ⟨[[-719326103524252590, -484874378413718108, 267709085389580393, -479436343939341376, -130563366184433728], [0, 0, 208749851051126295, -42817120798393536, 130563366184433728]], [[-425479634944000000, -850959269888000000, -212739817472000000], [0, 0, 212739817472000000]]⟩
def n00102_reduction : Reduction := ⟨rawAdd n00089_pair n00101_pair, n00102_pair, [[524288]], 1⟩
theorem n00102_checked : checkReduction n00102_reduction = true := by decide
def n00103_expression (x t : ℝ) : ℝ := n00075_expression x t * n00100_expression x t
def n00103_pair : RationalPair := ⟨[[0, -115972438706256, 14762179595784, 222678944656577, 98292102945400], [0, -115972438706256, 72748398948912, 181472560236027, 11795052353448], [0, 0, 57986219353128, -43622476893597, -82565366474136], [0, 0, 0, -2416092473047, 3931684117816]], [[233722944000000, 525876624000000, 379799784000000, 87646104000000], [0, -175292208000000, -292153680000000, -116861472000000], [0, 0, 29215368000000, 29215368000000]]⟩
def n00103_reduction : Reduction := ⟨rawMul n00075_pair n00100_pair, n00103_pair, [[1]], 1⟩
theorem n00103_checked : checkReduction n00103_reduction = true := by decide
def n00104_expression (x t : ℝ) : ℝ := n00010_expression x t + n00103_expression x t
def n00104_pair : RationalPair := ⟨[[467445888000000, 935780809293744, 774361747595784, 397971152656577, 98292102945400], [0, -466556854706256, -511558961051088, -52250383763973, 11795052353448], [0, 0, 116416955353128, 14808259106403, -82565366474136], [0, 0, 0, -2416092473047, 3931684117816]], [[233722944000000, 525876624000000, 379799784000000, 87646104000000], [0, -175292208000000, -292153680000000, -116861472000000], [0, 0, 29215368000000, 29215368000000]]⟩
def n00104_reduction : Reduction := ⟨rawAdd n00010_pair n00103_pair, n00104_pair, [[1]], 1⟩
theorem n00104_checked : checkReduction n00104_reduction = true := by decide
def n00105_expression (x t : ℝ) : ℝ := n00095_expression x t * n00104_expression x t
def n00105_pair : RationalPair := ⟨[[0, 9907078066808832000000, 52302623666087597135616, 116882947593609826505472, 150427762760145855094032, 127008771864795159697560, 74096939950652525649184, 29651697445616262377248, 7737828907643380727523, 1187365905298022486240, 80532685785225128000], [0, 0, -9888235838283090864384, -47739278138989300062336, -87504460375380404061264, -83659782121166026653144, -49178126872915425252060, -20345844994576831363792, -6395764740511220920757, -1412219492566609599008, -151401449276223240640], [0, 0, 0, 2467348402439337432192, 12881231553735824451696, 19293182625409119157896, 11148536632416437822988, 1391917888499293486512, -1231421882119699746230, -438816169042812236736, -6442614862818010240], [0, 0, 0, 0, -51206818503676393008, -1202576878237374491400, -1471602839486872367444, -345223613573850479408, 554950117750266124122, 649850151550949891648, 148180141844814235520], [0, 0, 0, 0, 0, 0, 23204374391650908324, -52466097105789706960, 54980864014479592147, 17425793657109750496, -74090070922407117760], [0, 0, 0, 0, 0, 0, 0, 0, 999597858411370075, -3606188896660292640, 3221307431409005120]], [[5881830473465856000000, 45584186169360384000000, 145575304218279936000000, 247772108694749184000000, 243360735839649792000000, 140061088149405696000000, 45951800573952000000000, 7903709698719744000000, 551421606887424000000], [0, -1470457618366464000000, -19115949038764032000000, -79404711391789056000000, -152927592310112256000000, -151824749096337408000000, -78301868178014208000000, -19483563443355648000000, -1838072022958080000000], [0, 0, 0, 2205686427549696000000, 15439804992847872000000, 36393826054569984000000, 36393826054569984000000, 15439804992847872000000, 2205686427549696000000], [0, 0, 0, 0, 0, -1102843213774848000000, -4043758450507776000000, -4043758450507776000000, -1102843213774848000000], [0, 0, 0, 0, 0, 0, 0, 183807202295808000000, 183807202295808000000]]⟩
def n00105_reduction : Reduction := ⟨rawMul n00095_pair n00104_pair, n00105_pair, [[-2, -1], [0, 1]], 1⟩
theorem n00105_checked : checkReduction n00105_reduction = true := by decide
def n00106_expression (x t : ℝ) : ℝ := n00102_expression x t - n00105_expression x t
def n00106_pair : RationalPair := ⟨[[9943964055119267804160, 53973618657318196998912, 109323802231607132983296, 90656644845138893548416, 9045901028886288808560, -13474955816277904251480, 27142187614117227634976, 38960221584125650594496, 17946301985100235227645, 3552342298076623331104, 257887559364827094976], [0, -2485991013779816951040, -17047167078463841378304, -42082040541235139650944, -45873709461717349385136, -24788855189983901083752, -31151362542388423420260, -51594586242897472862576, -36117059254072284329611, -10175355912370448795104, -976666034557284169280], [0, 0, 0, 740082096573171994368, 5083437750796237352976, 13483970905044742003512, 16303954903526506967988, 19308569982022028225232, 20177490916795894620470, 9470655124806530298816, 1360123595463026902144], [0, 0, 0, 0, 51206818503676393008, -140360360440272221880, -2306608348359056157292, -2767848127454358249616, -2815691929524932806938, -2909634661765794102848, -825020632144918681472], [0, 0, 0, 0, 0, 0, -23204374391650908324, 232825968413962825840, 88385014923881511629, 58386962356428975392, 186896819305757858752], [0, 0, 0, 0, 0, 0, 0, 0, -999597858411370075, 3606188896660292640, -3221307431409005120]], [[5881830473465856000000, 45584186169360384000000, 145575304218279936000000, 247772108694749184000000, 243360735839649792000000, 140061088149405696000000, 45951800573952000000000, 7903709698719744000000, 551421606887424000000], [0, -1470457618366464000000, -19115949038764032000000, -79404711391789056000000, -152927592310112256000000, -151824749096337408000000, -78301868178014208000000, -19483563443355648000000, -1838072022958080000000], [0, 0, 0, 2205686427549696000000, 15439804992847872000000, 36393826054569984000000, 36393826054569984000000, 15439804992847872000000, 2205686427549696000000], [0, 0, 0, 0, 0, -1102843213774848000000, -4043758450507776000000, -4043758450507776000000, -1102843213774848000000], [0, 0, 0, 0, 0, 0, 0, 183807202295808000000, 183807202295808000000]]⟩
def n00106_reduction : Reduction := ⟨rawSub n00102_pair n00105_pair, n00106_pair, [[-425479634944000000, -850959269888000000, -212739817472000000], [0, 0, 212739817472000000]], 1⟩
theorem n00106_checked : checkReduction n00106_reduction = true := by decide
def n00107_expression (x t : ℝ) : ℝ := n00042_expression x t * n00039_expression x t
def n00107_pair : RationalPair := ⟨[[-2, -2]], [[-2, -6, -3], [0, 0, 1]]⟩
def n00107_reduction : Reduction := ⟨rawMul n00042_pair n00039_pair, n00107_pair, [[-2, -4, -1], [0, 0, 1]], 1⟩
theorem n00107_checked : checkReduction n00107_reduction = true := by decide
def n00108_expression (x t : ℝ) : ℝ := n00107_expression x t + n00081_expression x t
def n00108_pair : RationalPair := ⟨[[-42388128, -215756304, -430787488, -460423352, -314907686, -139416538, -31203897, -2457960], [0, 0, 40402248, 129617104, 154148864, 106539204, 43641301, 5735240], [0, 0, 0, 0, -8776642, -13004586, -12023679, -4096600], [0, 0, 0, 0, 0, 0, -413725, 819320]], [[-50331648, -352321536, -931135488, -1157627904, -692060160, -188743680, -18874368], [0, 0, 75497472, 352321536, 528482304, 276824064, 44040192], [0, 0, 0, 0, -37748736, -88080384, -31457280], [0, 0, 0, 0, 0, 0, 6291456]]⟩
def n00108_reduction : Reduction := ⟨rawAdd n00107_pair n00081_pair, n00108_pair, [[1]], 1⟩
theorem n00108_checked : checkReduction n00108_reduction = true := by decide
def n00109_expression (x t : ℝ) : ℝ := n00010_expression x t * n00090_expression x t
def n00109_pair : RationalPair := ⟨[[-77955, 99624]], [[131072]]⟩
def n00109_reduction : Reduction := ⟨rawMul n00010_pair n00090_pair, n00109_pair, [[2]], 1⟩
theorem n00109_checked : checkReduction n00109_reduction = true := by decide
def n00110_expression (x t : ℝ) : ℝ := n00109_expression x t * n00083_expression x t
def n00110_pair : RationalPair := ⟨[[-233865, 298872]], [[458752]]⟩
def n00110_reduction : Reduction := ⟨rawMul n00109_pair n00083_pair, n00110_pair, [[2]], 1⟩
theorem n00110_checked : checkReduction n00110_reduction = true := by decide
def n00111_expression (x t : ℝ) : ℝ := n00010_expression x t * n00108_expression x t
def n00111_pair : RationalPair := ⟨[[-42388128, -215756304, -430787488, -460423352, -314907686, -139416538, -31203897, -2457960], [0, 0, 40402248, 129617104, 154148864, 106539204, 43641301, 5735240], [0, 0, 0, 0, -8776642, -13004586, -12023679, -4096600], [0, 0, 0, 0, 0, 0, -413725, 819320]], [[-25165824, -176160768, -465567744, -578813952, -346030080, -94371840, -9437184], [0, 0, 37748736, 176160768, 264241152, 138412032, 22020096], [0, 0, 0, 0, -18874368, -44040192, -15728640], [0, 0, 0, 0, 0, 0, 3145728]]⟩
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
def n00114_pair : RationalPair := ⟨[[-4747470336, -32811884160, -96925178752, -163901854592, -180250505488, -137825776216, -74402852660, -27330136350, -6303933656, -800841849, -41785320], [0, 5595232896, 40973851968, 122686207360, 202644361408, 211867345280, 150552294888, 72793792434, 22198057636, 3675904920, 242518720], [0, 0, -1610748864, -15015420768, -49609459440, -82919996288, -83736898096, -55695759604, -23692145272, -5493629297, -494049960], [0, 0, 0, 42388128, 1751041728, 7928832864, 14174955672, 14315781292, 9216763072, 3339238288, 458819200], [0, 0, 0, 0, 0, -40402248, -463129500, -900893902, -1048969456, -749763251, -197456120], [0, 0, 0, 0, 0, 0, 0, 8776642, -2716964, 28677464, 32772800], [0, 0, 0, 0, 0, 0, 0, 0, 0, 413725, -819320]], [[-2818572288, -26071793664, -101116280832, -215268458496, -276748566528, -222667210752, -112126328832, -34087108608, -5681184768, -396361728], [0, 2113929216, 22548578304, 94422171648, 204522651648, 251909898240, 181621751808, 75220647936, 16426991616, 1453326336], [0, 0, -352321536, -5989466112, -31180455936, -73282879488, -87728062464, -54962159616, -16999514112, -2025848832], [0, 0, 0, 0, 528482304, 4580179968, 12859736064, 14973665280, 7486832640, 1321205760], [0, 0, 0, 0, 0, 0, -264241152, -1145044992, -1277165568, -396361728], [0, 0, 0, 0, 0, 0, 0, 0, 44040192, 44040192]]⟩
def n00114_reduction : Reduction := ⟨rawMul n00111_pair n00113_pair, n00114_pair, [[1]], 1⟩
theorem n00114_checked : checkReduction n00114_reduction = true := by decide
def n00115_expression (x t : ℝ) : ℝ := n00114_expression x t - n00049_expression x t
def n00115_pair : RationalPair := ⟨[[-4587276288, -30041655552, -79260205888, -105444476480, -66117331312, 1337633960, 33756126268, 25862712114, 9600952096, 1818684543, 139400664], [0, 5475087360, 38725974336, 107012237440, 147857753056, 104058034496, 25076032200, -14504830446, -13120646708, -3915847584, -421829888], [0, 0, -1590724608, -14513954208, -45099391248, -64501653632, -45251583088, -12469477876, 2398481528, 2392375711, 432011736], [0, 0, 0, 42388128, 1721005344, 7426936224, 11350365624, 7586271820, 1946443792, -158254592, -145134080], [0, 0, 0, 0, 0, -40402248, -448111308, -715024414, -452955352, -143414459, -16270136], [0, 0, 0, 0, 0, 0, 0, 8776642, -5219996, 6042656, 12641024], [0, 0, 0, 0, 0, 0, 0, 0, 0, 413725, -819320]], [[-2818572288, -26071793664, -101116280832, -215268458496, -276748566528, -222667210752, -112126328832, -34087108608, -5681184768, -396361728], [0, 2113929216, 22548578304, 94422171648, 204522651648, 251909898240, 181621751808, 75220647936, 16426991616, 1453326336], [0, 0, -352321536, -5989466112, -31180455936, -73282879488, -87728062464, -54962159616, -16999514112, -2025848832], [0, 0, 0, 0, 528482304, 4580179968, 12859736064, 14973665280, 7486832640, 1321205760], [0, 0, 0, 0, 0, 0, -264241152, -1145044992, -1277165568, -396361728], [0, 0, 0, 0, 0, 0, 0, 0, 44040192, 44040192]]⟩
def n00115_reduction : Reduction := ⟨rawSub n00114_pair n00049_pair, n00115_pair, [[262144]], 1⟩
theorem n00115_checked : checkReduction n00115_reduction = true := by decide
def n00116_expression (x t : ℝ) : ℝ := n00115_expression x t - n00054_expression x t
def n00116_pair : RationalPair := ⟨[[-6746906880, -47555127360, -133953175072, -182022149792, -90045944608, 72573545000, 142429104052, 97730320794, 35036197372, 6479694939, 485775672], [0, 7094810304, 54155685696, 159654972928, 222051723760, 118345514528, -55903332168, -115586414910, -66268328960, -17157607836, -1691871584], [0, 0, -1860678432, -18795280320, -63756193440, -93403881728, -48429194896, 22082060684, 37403877296, 15695780455, 2202372888], [0, 0, 0, 42388128, 2125936080, 10474502592, 17201124552, 7821364636, -5402315528, -5688566792, -1299717440], [0, 0, 0, 0, 0, -40402248, -650576676, -1361457670, -430899052, 668984737, 330104872], [0, 0, 0, 0, 0, 0, 0, 8776642, 28524232, 1300772, -25845088], [0, 0, 0, 0, 0, 0, 0, 0, 0, 413725, -819320]], [[-2818572288, -26071793664, -101116280832, -215268458496, -276748566528, -222667210752, -112126328832, -34087108608, -5681184768, -396361728], [0, 2113929216, 22548578304, 94422171648, 204522651648, 251909898240, 181621751808, 75220647936, 16426991616, 1453326336], [0, 0, -352321536, -5989466112, -31180455936, -73282879488, -87728062464, -54962159616, -16999514112, -2025848832], [0, 0, 0, 0, 528482304, 4580179968, 12859736064, 14973665280, 7486832640, 1321205760], [0, 0, 0, 0, 0, 0, -264241152, -1145044992, -1277165568, -396361728], [0, 0, 0, 0, 0, 0, 0, 0, 44040192, 44040192]]⟩
def n00116_reduction : Reduction := ⟨rawSub n00115_pair n00054_pair, n00116_pair, [[524288]], 1⟩
theorem n00116_checked : checkReduction n00116_reduction = true := by decide
def n00117_expression (x t : ℝ) : ℝ := n00038_expression x t * n00116_expression x t
def n00117_pair : RationalPair := ⟨[[0, -6746906880, -47555127360, -133953175072, -182022149792, -90045944608, 72573545000, 142429104052, 97730320794, 35036197372, 6479694939, 485775672], [0, 0, 7094810304, 54155685696, 159654972928, 222051723760, 118345514528, -55903332168, -115586414910, -66268328960, -17157607836, -1691871584], [0, 0, 0, -1860678432, -18795280320, -63756193440, -93403881728, -48429194896, 22082060684, 37403877296, 15695780455, 2202372888], [0, 0, 0, 0, 42388128, 2125936080, 10474502592, 17201124552, 7821364636, -5402315528, -5688566792, -1299717440], [0, 0, 0, 0, 0, 0, -40402248, -650576676, -1361457670, -430899052, 668984737, 330104872], [0, 0, 0, 0, 0, 0, 0, 0, 8776642, 28524232, 1300772, -25845088], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 413725, -819320]], [[-2818572288, -30299652096, -139519328256, -360777252864, -577454997504, -595071074304, -398299496448, -170523623424, -44656754688, -6473908224, -396361728], [0, 704643072, 12683575296, 77510737920, 236055429120, 409045303296, 424018968576, 264593473536, 96183779328, 18540920832, 1453326336], [0, 0, 0, -1409286144, -15149826048, -60246982656, -117499232256, -122255572992, -68174217216, -18937282560, -2025848832], [0, 0, 0, 0, 0, 1056964608, 7222591488, 17263755264, 17968398336, 8191475712, 1321205760], [0, 0, 0, 0, 0, 0, 0, -352321536, -1321205760, -1365245952, -396361728], [0, 0, 0, 0, 0, 0, 0, 0, 0, 44040192, 44040192]]⟩
def n00117_reduction : Reduction := ⟨rawMul n00038_pair n00116_pair, n00117_pair, [[-2, -1], [0, 1]], 1⟩
theorem n00117_checked : checkReduction n00117_reduction = true := by decide
def n00118_expression (x t : ℝ) : ℝ := n00110_expression x t + n00117_expression x t
def n00118_pair : RationalPair := ⟨[[1436866560, 6863139072, 3829869504, -40929599008, -122686618016, -162893219872, -112061661784, -30128312396, 9401366490, 9243104284, 2464072635, 227550264], [0, -359216640, 1087978176, 22905068352, 89814811648, 167314040560, 168675522464, 85454622648, 7760319426, -13057517792, -5819281404, -745045088], [0, 0, 0, -1142245152, -11990257344, -42913119648, -72754769024, -62654595472, -22811921908, 2643054320, 4391092135, 882554136], [0, 0, 0, 0, 42388128, 1587111120, 7481133120, 13105757640, 9908491420, 2128009528, -1025439560, -438966080], [0, 0, 0, 0, 0, 0, -40402248, -470968356, -917460166, -595668172, -18398975, 71879464], [0, 0, 0, 0, 0, 0, 0, 0, 8776642, 6073192, 7541444, 2846624], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 413725, -819320]], [[-2818572288, -30299652096, -139519328256, -360777252864, -577454997504, -595071074304, -398299496448, -170523623424, -44656754688, -6473908224, -396361728], [0, 704643072, 12683575296, 77510737920, 236055429120, 409045303296, 424018968576, 264593473536, 96183779328, 18540920832, 1453326336], [0, 0, 0, -1409286144, -15149826048, -60246982656, -117499232256, -122255572992, -68174217216, -18937282560, -2025848832], [0, 0, 0, 0, 0, 1056964608, 7222591488, 17263755264, 17968398336, 8191475712, 1321205760], [0, 0, 0, 0, 0, 0, 0, -352321536, -1321205760, -1365245952, -396361728], [0, 0, 0, 0, 0, 0, 0, 0, 0, 44040192, 44040192]]⟩
def n00118_reduction : Reduction := ⟨rawAdd n00110_pair n00117_pair, n00118_pair, [[458752]], 1⟩
theorem n00118_checked : checkReduction n00118_reduction = true := by decide
def n00119_expression (x t : ℝ) : ℝ := n00118_expression x t / n00038_expression x t
def n00119_pair : RationalPair := ⟨[[1436866560, 6863139072, 3829869504, -40929599008, -122686618016, -162893219872, -112061661784, -30128312396, 9401366490, 9243104284, 2464072635, 227550264], [0, -359216640, 1087978176, 22905068352, 89814811648, 167314040560, 168675522464, 85454622648, 7760319426, -13057517792, -5819281404, -745045088], [0, 0, 0, -1142245152, -11990257344, -42913119648, -72754769024, -62654595472, -22811921908, 2643054320, 4391092135, 882554136], [0, 0, 0, 0, 42388128, 1587111120, 7481133120, 13105757640, 9908491420, 2128009528, -1025439560, -438966080], [0, 0, 0, 0, 0, 0, -40402248, -470968356, -917460166, -595668172, -18398975, 71879464], [0, 0, 0, 0, 0, 0, 0, 0, 8776642, 6073192, 7541444, 2846624], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 413725, -819320]], [[0, -2818572288, -26071793664, -101116280832, -215268458496, -276748566528, -222667210752, -112126328832, -34087108608, -5681184768, -396361728], [0, 0, 2113929216, 22548578304, 94422171648, 204522651648, 251909898240, 181621751808, 75220647936, 16426991616, 1453326336], [0, 0, 0, -352321536, -5989466112, -31180455936, -73282879488, -87728062464, -54962159616, -16999514112, -2025848832], [0, 0, 0, 0, 0, 528482304, 4580179968, 12859736064, 14973665280, 7486832640, 1321205760], [0, 0, 0, 0, 0, 0, 0, -264241152, -1145044992, -1277165568, -396361728], [0, 0, 0, 0, 0, 0, 0, 0, 0, 44040192, 44040192]]⟩
def n00119_reduction : Reduction := ⟨rawDiv n00118_pair n00038_pair, n00119_pair, [[-2, -4, -1], [0, 0, 1]], 1⟩
theorem n00119_checked : checkReduction n00119_reduction = true := by decide
def n00120_expression (x t : ℝ) : ℝ := n00109_expression x t * n00082_expression x t
def n00120_pair : RationalPair := ⟨[[-233865, 298872]], [[524288]]⟩
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
def n00123_pair : RationalPair := ⟨[[-5425680384, -37789957632, -112687096832, -192640970464, -214359281648, -165948849600, -90871250328, -34007080106, -8040220766, -1051972191, -56533080], [0, 6103890432, 45057126144, 136038242912, 226694297840, 239167449016, 171526079128, 83833594610, 25947341090, 4385659342, 296593840], [0, 0, -1695525120, -16016536608, -53406423504, -89991796888, -91574681384, -61381255788, -26365469444, -6203441893, -569427400], [0, 0, 0, 42388128, 1831846224, 8374191272, 15067455880, 15309961452, 9929532220, 3634932772, 507978400], [0, 0, 0, 0, 0, -40402248, -480682784, -939491658, -1100583326, -795080409, -212203880], [0, 0, 0, 0, 0, 0, 0, 8776642, -3544414, 29488654, 34411440], [0, 0, 0, 0, 0, 0, 0, 0, 0, 413725, -819320]], [[-3221225472, -29796335616, -115561463808, -246021095424, -316284076032, -254476812288, -128144375808, -38956695552, -6492782592, -452984832], [0, 2415919104, 25769803776, 107911053312, 233740173312, 287897026560, 207567716352, 85966454784, 18773704704, 1660944384], [0, 0, -402653184, -6845104128, -35634806784, -83751862272, -100260642816, -62813896704, -19428016128, -2315255808], [0, 0, 0, 0, 603979776, 5234491392, 14696841216, 17112760320, 8556380160, 1509949440], [0, 0, 0, 0, 0, 0, -301989888, -1308622848, -1459617792, -452984832], [0, 0, 0, 0, 0, 0, 0, 0, 50331648, 50331648]]⟩
def n00123_reduction : Reduction := ⟨rawMul n00111_pair n00122_pair, n00123_pair, [[1]], 1⟩
theorem n00123_checked : checkReduction n00123_reduction = true := by decide
def n00124_expression (x t : ℝ) : ℝ := n00123_expression x t - n00049_expression x t
def n00124_pair : RationalPair := ⟨[[-5242601472, -34623982080, -92498556416, -125832538336, -83921368304, -6904952256, 32739011304, 26784746710, 10136791522, 1941772257, 150536616], [0, 5966581248, 42488123136, 118125134432, 164081031152, 115956808120, 28124636056, -15936260110, -14416892446, -4290629234, -462661712], [0, 0, -1672640256, -15443431968, -48252059856, -68942262424, -47591464232, -11979790956, 3452389756, 2809135259, 488928824], [0, 0, 0, 42388128, 1797518928, 7800595112, 11839352968, 7619093484, 1620595900, -362201948, -182253920], [0, 0, 0, 0, 0, -40402248, -463519136, -727069386, -419424350, -102110361, -5134184], [0, 0, 0, 0, 0, 0, 0, 8776642, -6405022, 3620302, 11403696], [0, 0, 0, 0, 0, 0, 0, 0, 0, 413725, -819320]], [[-3221225472, -29796335616, -115561463808, -246021095424, -316284076032, -254476812288, -128144375808, -38956695552, -6492782592, -452984832], [0, 2415919104, 25769803776, 107911053312, 233740173312, 287897026560, 207567716352, 85966454784, 18773704704, 1660944384], [0, 0, -402653184, -6845104128, -35634806784, -83751862272, -100260642816, -62813896704, -19428016128, -2315255808], [0, 0, 0, 0, 603979776, 5234491392, 14696841216, 17112760320, 8556380160, 1509949440], [0, 0, 0, 0, 0, 0, -301989888, -1308622848, -1459617792, -452984832], [0, 0, 0, 0, 0, 0, 0, 0, 50331648, 50331648]]⟩
def n00124_reduction : Reduction := ⟨rawSub n00123_pair n00049_pair, n00124_pair, [[262144]], 1⟩
theorem n00124_checked : checkReduction n00124_reduction = true := by decide
def n00125_expression (x t : ℝ) : ℝ := n00124_expression x t - n00054_expression x t
def n00125_pair : RationalPair := ⟨[[-7710750720, -54639378432, -155004806912, -213349879264, -111268354928, 74507517504, 156936700200, 108919156630, 39205643266, 7268641281, 546393768], [0, 7817693184, 60122078976, 178288260704, 248874140528, 132285356728, -64423208936, -131458070926, -75157100734, -19424069522, -1914137936], [0, 0, -1981158912, -20336376096, -69574119504, -101973380248, -51223020584, 27507681684, 43458556348, 18013026395, 2512198712], [0, 0, 0, 42388128, 2260296912, 11283528104, 18525934600, 7887770988, -6777986180, -6682558748, -1501777760], [0, 0, 0, 0, 0, -40402248, -694908128, -1465850250, -394217150, 826345863, 390722968], [0, 0, 0, 0, 0, 0, 0, 8776642, 32159810, -1798994, -32580432], [0, 0, 0, 0, 0, 0, 0, 0, 0, 413725, -819320]], [[-3221225472, -29796335616, -115561463808, -246021095424, -316284076032, -254476812288, -128144375808, -38956695552, -6492782592, -452984832], [0, 2415919104, 25769803776, 107911053312, 233740173312, 287897026560, 207567716352, 85966454784, 18773704704, 1660944384], [0, 0, -402653184, -6845104128, -35634806784, -83751862272, -100260642816, -62813896704, -19428016128, -2315255808], [0, 0, 0, 0, 603979776, 5234491392, 14696841216, 17112760320, 8556380160, 1509949440], [0, 0, 0, 0, 0, 0, -301989888, -1308622848, -1459617792, -452984832], [0, 0, 0, 0, 0, 0, 0, 0, 50331648, 50331648]]⟩
def n00125_reduction : Reduction := ⟨rawSub n00124_pair n00054_pair, n00125_pair, [[524288]], 1⟩
theorem n00125_checked : checkReduction n00125_reduction = true := by decide
def n00126_expression (x t : ℝ) : ℝ := n00038_expression x t * n00125_expression x t
def n00126_pair : RationalPair := ⟨[[0, -7710750720, -54639378432, -155004806912, -213349879264, -111268354928, 74507517504, 156936700200, 108919156630, 39205643266, 7268641281, 546393768], [0, 0, 7817693184, 60122078976, 178288260704, 248874140528, 132285356728, -64423208936, -131458070926, -75157100734, -19424069522, -1914137936], [0, 0, 0, -1981158912, -20336376096, -69574119504, -101973380248, -51223020584, 27507681684, 43458556348, 18013026395, 2512198712], [0, 0, 0, 0, 42388128, 2260296912, 11283528104, 18525934600, 7887770988, -6777986180, -6682558748, -1501777760], [0, 0, 0, 0, 0, 0, -40402248, -694908128, -1465850250, -394217150, 826345863, 390722968], [0, 0, 0, 0, 0, 0, 0, 0, 8776642, 32159810, -1798994, -32580432], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 413725, -819320]], [[-3221225472, -34628173824, -159450660864, -412316860416, -659948568576, -680081227776, -455199424512, -194884141056, -51036291072, -7398752256, -452984832], [0, 805306368, 14495514624, 88583700480, 269777633280, 467480346624, 484593106944, 302392541184, 109924319232, 21189623808, 1660944384], [0, 0, 0, -1610612736, -17314086912, -68853694464, -134284836864, -139720654848, -77913391104, -21642608640, -2315255808], [0, 0, 0, 0, 0, 1207959552, 8254390272, 19730006016, 20535312384, 9361686528, 1509949440], [0, 0, 0, 0, 0, 0, 0, -402653184, -1509949440, -1560281088, -452984832], [0, 0, 0, 0, 0, 0, 0, 0, 0, 50331648, 50331648]]⟩
def n00126_reduction : Reduction := ⟨rawMul n00038_pair n00125_pair, n00126_pair, [[-2, -1], [0, 1]], 1⟩
theorem n00126_checked : checkReduction n00126_reduction = true := by decide
def n00127_expression (x t : ℝ) : ℝ := n00120_expression x t + n00126_expression x t
def n00127_pair : RationalPair := ⟨[[1436866560, 5899295232, -3254381568, -61981230848, -154014347488, -184115630192, -110127689280, -15620716248, 20590202326, 13412550178, 3253018977, 288168360], [0, -359216640, 1810861056, 28871461632, 108448099424, 194136457328, 182615364664, 76934745880, -8111336590, -21946289566, -8085743090, -967311440], [0, 0, 0, -1262725632, -13531353120, -48731045712, -81324267544, -65448421160, -17386300908, 8697733372, 6708338075, 1192379960], [0, 0, 0, 0, 42388128, 1721471952, 8290158632, 14430567688, 9974897772, 752338876, -2019431516, -641026400], [0, 0, 0, 0, 0, 0, -40402248, -515299808, -1021852746, -558986270, 138962151, 132497560], [0, 0, 0, 0, 0, 0, 0, 0, 8776642, 9708770, 4441678, -3888720], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 413725, -819320]], [[-3221225472, -34628173824, -159450660864, -412316860416, -659948568576, -680081227776, -455199424512, -194884141056, -51036291072, -7398752256, -452984832], [0, 805306368, 14495514624, 88583700480, 269777633280, 467480346624, 484593106944, 302392541184, 109924319232, 21189623808, 1660944384], [0, 0, 0, -1610612736, -17314086912, -68853694464, -134284836864, -139720654848, -77913391104, -21642608640, -2315255808], [0, 0, 0, 0, 0, 1207959552, 8254390272, 19730006016, 20535312384, 9361686528, 1509949440], [0, 0, 0, 0, 0, 0, 0, -402653184, -1509949440, -1560281088, -452984832], [0, 0, 0, 0, 0, 0, 0, 0, 0, 50331648, 50331648]]⟩
def n00127_reduction : Reduction := ⟨rawAdd n00120_pair n00126_pair, n00127_pair, [[524288]], 1⟩
theorem n00127_checked : checkReduction n00127_reduction = true := by decide
def n00128_expression (x t : ℝ) : ℝ := n00127_expression x t / n00038_expression x t
def n00128_pair : RationalPair := ⟨[[1436866560, 5899295232, -3254381568, -61981230848, -154014347488, -184115630192, -110127689280, -15620716248, 20590202326, 13412550178, 3253018977, 288168360], [0, -359216640, 1810861056, 28871461632, 108448099424, 194136457328, 182615364664, 76934745880, -8111336590, -21946289566, -8085743090, -967311440], [0, 0, 0, -1262725632, -13531353120, -48731045712, -81324267544, -65448421160, -17386300908, 8697733372, 6708338075, 1192379960], [0, 0, 0, 0, 42388128, 1721471952, 8290158632, 14430567688, 9974897772, 752338876, -2019431516, -641026400], [0, 0, 0, 0, 0, 0, -40402248, -515299808, -1021852746, -558986270, 138962151, 132497560], [0, 0, 0, 0, 0, 0, 0, 0, 8776642, 9708770, 4441678, -3888720], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 413725, -819320]], [[0, -3221225472, -29796335616, -115561463808, -246021095424, -316284076032, -254476812288, -128144375808, -38956695552, -6492782592, -452984832], [0, 0, 2415919104, 25769803776, 107911053312, 233740173312, 287897026560, 207567716352, 85966454784, 18773704704, 1660944384], [0, 0, 0, -402653184, -6845104128, -35634806784, -83751862272, -100260642816, -62813896704, -19428016128, -2315255808], [0, 0, 0, 0, 0, 603979776, 5234491392, 14696841216, 17112760320, 8556380160, 1509949440], [0, 0, 0, 0, 0, 0, 0, -301989888, -1308622848, -1459617792, -452984832], [0, 0, 0, 0, 0, 0, 0, 0, 0, 50331648, 50331648]]⟩
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
  simpa [n00002_pair, n00002_expression, rationalConst, Polynomial2.const] using rationalConst_sound 13 10 x t (by decide)
theorem n00003_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00003_pair.NonzeroDenominator x t ∧ n00003_pair.value x t = n00003_expression x t := by
  simpa [n00003_pair, n00003_expression, rationalConst, Polynomial2.const] using rationalConst_sound 29 20 x t (by decide)
theorem n00004_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00004_pair.NonzeroDenominator x t ∧ n00004_pair.value x t = n00004_expression x t := by
  simpa [n00004_pair, n00004_expression, rationalConst, Polynomial2.const] using rationalConst_sound 11 8 x t (by decide)
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
  simpa [n00025_pair, n00025_expression, rationalConst, Polynomial2.const] using rationalConst_sound 3500567 100000000 x t (by decide)
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
  simpa [n00027_pair, n00027_expression, rationalConst, Polynomial2.const] using rationalConst_sound 5922933 100000000 x t (by decide)
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
  simpa [n00043_pair, n00043_expression, rationalConst, Polynomial2.const] using rationalConst_sound 44917 1 x t (by decide)
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
  simpa [n00045_pair, n00045_expression, rationalConst, Polynomial2.const] using rationalConst_sound 29958 1 x t (by decide)
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
  simpa [n00050_pair, n00050_expression, rationalConst, Polynomial2.const] using rationalConst_sound 28533 1 x t (by decide)
theorem n00051_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00051_pair.NonzeroDenominator x t ∧ n00051_pair.value x t = n00051_expression x t := by
  simpa [n00051_pair, n00051_expression, rationalConst, Polynomial2.const] using rationalConst_sound 57271 1 x t (by decide)
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
  simpa [n00055_pair, n00055_expression, rationalConst, Polynomial2.const] using rationalConst_sound 17821 1 x t (by decide)
theorem n00056_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00056_pair.NonzeroDenominator x t ∧ n00056_pair.value x t = n00056_expression x t := by
  simpa [n00056_pair, n00056_expression, rationalConst, Polynomial2.const] using rationalConst_sound 20483 1 x t (by decide)
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
  simpa [n00060_pair, n00060_expression, rationalConst, Polynomial2.const] using rationalConst_sound 3064 1 x t (by decide)
theorem n00061_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00061_pair.NonzeroDenominator x t ∧ n00061_pair.value x t = n00061_expression x t := by
  simpa [n00061_pair, n00061_expression, rationalConst, Polynomial2.const] using rationalConst_sound (-4423) 1 x t (by decide)
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
abbrev E1_guard_S_hi_pair := n00099_pair
abbrev E1_guard_S_hi_expression := n00099_expression
theorem E1_guard_S_hi_sound (x t : ℝ) (hnz : DivisorsNonzero x t) : n00099_pair.NonzeroDenominator x t ∧ n00099_pair.value x t = n00099_expression x t := n00099_sound x t hnz
#print axioms E1_guard_S_hi_sound
abbrev E1_guard_S_lo_pair := n00106_pair
abbrev E1_guard_S_lo_expression := n00106_expression
theorem E1_guard_S_lo_sound (x t : ℝ) (hnz : DivisorsNonzero x t) : n00106_pair.NonzeroDenominator x t ∧ n00106_pair.value x t = n00106_expression x t := n00106_sound x t hnz
#print axioms E1_guard_S_lo_sound
abbrev E1_guard_r_hi_pair := n00119_pair
abbrev E1_guard_r_hi_expression := n00119_expression
theorem E1_guard_r_hi_sound (x t : ℝ) (hnz : DivisorsNonzero x t) : n00119_pair.NonzeroDenominator x t ∧ n00119_pair.value x t = n00119_expression x t := n00119_sound x t hnz
#print axioms E1_guard_r_hi_sound
abbrev E1_guard_r_lo_pair := n00128_pair
abbrev E1_guard_r_lo_expression := n00128_expression
theorem E1_guard_r_lo_sound (x t : ℝ) (hnz : DivisorsNonzero x t) : n00128_pair.NonzeroDenominator x t ∧ n00128_pair.value x t = n00128_expression x t := n00128_sound x t hnz
#print axioms E1_guard_r_lo_sound
end
end F4U.Light.Linking.Generated.DAG_E1_FULL_01
