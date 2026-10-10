module
public import Erdos993Lean.F4U.Light.Linking.Rational
@[expose] public section
set_option maxRecDepth 4096
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
namespace F4U.Light.Linking.Generated.DAG_D_FULL_01
noncomputable section
def n00000_expression (x t : ℝ) : ℝ := x
def n00000_pair : RationalPair := ⟨[[0, 1]], [[1]]⟩
def n00001_expression (x t : ℝ) : ℝ := t
def n00001_pair : RationalPair := ⟨[[], [1]], [[1]]⟩
def n00002_expression (x t : ℝ) : ℝ := (4 : ℝ)/(5 : ℝ)
def n00002_pair : RationalPair := ⟨[[4]], [[5]]⟩
def n00003_expression (x t : ℝ) : ℝ := (13 : ℝ)/(10 : ℝ)
def n00003_pair : RationalPair := ⟨[[13]], [[10]]⟩
def n00004_expression (x t : ℝ) : ℝ := (269 : ℝ)/(256 : ℝ)
def n00004_pair : RationalPair := ⟨[[269]], [[256]]⟩
def n00005_expression (x t : ℝ) : ℝ := (1 : ℝ)/(1 : ℝ)
def n00005_pair : RationalPair := ⟨[[1]], [[1]]⟩
def n00006_expression (x t : ℝ) : ℝ := n00005_expression x t - n00000_expression x t
def n00006_pair : RationalPair := ⟨[[1, -1]], [[1]]⟩
def n00006_reduction : Reduction := ⟨rawSub n00005_pair n00000_pair, n00006_pair, [[1]], 1⟩
theorem n00006_checked : checkReduction n00006_reduction = true := by decide
def n00007_expression (x t : ℝ) : ℝ := n00000_expression x t / n00006_expression x t
def n00007_pair : RationalPair := ⟨[[0, -1]], [[-1, 1]]⟩
def n00007_reduction : Reduction := ⟨rawDiv n00000_pair n00006_pair, n00007_pair, [[-1]], 1⟩
theorem n00007_checked : checkReduction n00007_reduction = true := by decide
def n00008_expression (x t : ℝ) : ℝ := n00005_expression x t + n00007_expression x t
def n00008_pair : RationalPair := ⟨[[-1]], [[-1, 1]]⟩
def n00008_reduction : Reduction := ⟨rawAdd n00005_pair n00007_pair, n00008_pair, [[1]], 1⟩
theorem n00008_checked : checkReduction n00008_reduction = true := by decide
def n00009_expression (x t : ℝ) : ℝ := n00007_expression x t / n00008_expression x t
def n00009_pair : RationalPair := ⟨[[0, 1]], [[1]]⟩
def n00009_reduction : Reduction := ⟨rawDiv n00007_pair n00008_pair, n00009_pair, [[1, -1]], 1⟩
theorem n00009_checked : checkReduction n00009_reduction = true := by decide
def n00010_expression (x t : ℝ) : ℝ := n00005_expression x t + n00002_expression x t
def n00010_pair : RationalPair := ⟨[[9]], [[5]]⟩
def n00010_reduction : Reduction := ⟨rawAdd n00005_pair n00002_pair, n00010_pair, [[1]], 1⟩
theorem n00010_checked : checkReduction n00010_reduction = true := by decide
def n00011_expression (x t : ℝ) : ℝ := n00002_expression x t / n00010_expression x t
def n00011_pair : RationalPair := ⟨[[4]], [[9]]⟩
def n00011_reduction : Reduction := ⟨rawDiv n00002_pair n00010_pair, n00011_pair, [[5]], 1⟩
theorem n00011_checked : checkReduction n00011_reduction = true := by decide
def n00012_expression (x t : ℝ) : ℝ := n00005_expression x t + n00003_expression x t
def n00012_pair : RationalPair := ⟨[[23]], [[10]]⟩
def n00012_reduction : Reduction := ⟨rawAdd n00005_pair n00003_pair, n00012_pair, [[1]], 1⟩
theorem n00012_checked : checkReduction n00012_reduction = true := by decide
def n00013_expression (x t : ℝ) : ℝ := n00003_expression x t / n00012_expression x t
def n00013_pair : RationalPair := ⟨[[13]], [[23]]⟩
def n00013_reduction : Reduction := ⟨rawDiv n00003_pair n00012_pair, n00013_pair, [[10]], 1⟩
theorem n00013_checked : checkReduction n00013_reduction = true := by decide
def n00014_expression (x t : ℝ) : ℝ := n00009_expression x t - n00011_expression x t
def n00014_pair : RationalPair := ⟨[[-4, 9]], [[9]]⟩
def n00014_reduction : Reduction := ⟨rawSub n00009_pair n00011_pair, n00014_pair, [[1]], 1⟩
theorem n00014_checked : checkReduction n00014_reduction = true := by decide
def n00015_expression (x t : ℝ) : ℝ := n00013_expression x t - n00011_expression x t
def n00015_pair : RationalPair := ⟨[[25]], [[207]]⟩
def n00015_reduction : Reduction := ⟨rawSub n00013_pair n00011_pair, n00015_pair, [[1]], 1⟩
theorem n00015_checked : checkReduction n00015_reduction = true := by decide
def n00016_expression (x t : ℝ) : ℝ := n00014_expression x t / n00015_expression x t
def n00016_pair : RationalPair := ⟨[[-92, 207]], [[25]]⟩
def n00016_reduction : Reduction := ⟨rawDiv n00014_pair n00015_pair, n00016_pair, [[9]], 1⟩
theorem n00016_checked : checkReduction n00016_reduction = true := by decide
def n00017_expression (x t : ℝ) : ℝ := (2 : ℝ)/(1 : ℝ)
def n00017_pair : RationalPair := ⟨[[2]], [[1]]⟩
def n00018_expression (x t : ℝ) : ℝ := n00013_expression x t / n00017_expression x t
def n00018_pair : RationalPair := ⟨[[13]], [[46]]⟩
def n00018_reduction : Reduction := ⟨rawDiv n00013_pair n00017_pair, n00018_pair, [[1]], 1⟩
theorem n00018_checked : checkReduction n00018_reduction = true := by decide
def n00019_expression (x t : ℝ) : ℝ := n00005_expression x t - n00018_expression x t
def n00019_pair : RationalPair := ⟨[[33]], [[46]]⟩
def n00019_reduction : Reduction := ⟨rawSub n00005_pair n00018_pair, n00019_pair, [[1]], 1⟩
theorem n00019_checked : checkReduction n00019_reduction = true := by decide
def n00020_expression (x t : ℝ) : ℝ := n00013_expression x t * n00019_expression x t
def n00020_pair : RationalPair := ⟨[[429]], [[1058]]⟩
def n00020_reduction : Reduction := ⟨rawMul n00013_pair n00019_pair, n00020_pair, [[1]], 1⟩
theorem n00020_checked : checkReduction n00020_reduction = true := by decide
def n00021_expression (x t : ℝ) : ℝ := (729 : ℝ)/(800 : ℝ)
def n00021_pair : RationalPair := ⟨[[729]], [[800]]⟩
def n00022_expression (x t : ℝ) : ℝ := n00020_expression x t * n00021_expression x t
def n00022_pair : RationalPair := ⟨[[312741]], [[846400]]⟩
def n00022_reduction : Reduction := ⟨rawMul n00020_pair n00021_pair, n00022_pair, [[1]], 1⟩
theorem n00022_checked : checkReduction n00022_reduction = true := by decide
def n00023_expression (x t : ℝ) : ℝ := n00022_expression x t * n00014_expression x t
def n00023_pair : RationalPair := ⟨[[-138996, 312741]], [[846400]]⟩
def n00023_reduction : Reduction := ⟨rawMul n00022_pair n00014_pair, n00023_pair, [[9]], 1⟩
theorem n00023_checked : checkReduction n00023_reduction = true := by decide
def n00024_expression (x t : ℝ) : ℝ := n00013_expression x t - n00009_expression x t
def n00024_pair : RationalPair := ⟨[[13, -23]], [[23]]⟩
def n00024_reduction : Reduction := ⟨rawSub n00013_pair n00009_pair, n00024_pair, [[1]], 1⟩
theorem n00024_checked : checkReduction n00024_reduction = true := by decide
def n00025_expression (x t : ℝ) : ℝ := n00023_expression x t * n00024_expression x t
def n00025_pair : RationalPair := ⟨[[-1806948, 7262541, -7193043]], [[19467200]]⟩
def n00025_reduction : Reduction := ⟨rawMul n00023_pair n00024_pair, n00025_pair, [[1]], 1⟩
theorem n00025_checked : checkReduction n00025_reduction = true := by decide
def n00026_expression (x t : ℝ) : ℝ := n00005_expression x t - n00016_expression x t
def n00026_pair : RationalPair := ⟨[[117, -207]], [[25]]⟩
def n00026_reduction : Reduction := ⟨rawSub n00005_pair n00016_pair, n00026_pair, [[1]], 1⟩
theorem n00026_checked : checkReduction n00026_reduction = true := by decide
def n00027_expression (x t : ℝ) : ℝ := ((-60258643) : ℝ)/(1000000000 : ℝ)
def n00027_pair : RationalPair := ⟨[[-60258643]], [[1000000000]]⟩
def n00028_expression (x t : ℝ) : ℝ := n00026_expression x t * n00027_expression x t
def n00028_pair : RationalPair := ⟨[[-7050261231, 12473539101]], [[25000000000]]⟩
def n00028_reduction : Reduction := ⟨rawMul n00026_pair n00027_pair, n00028_pair, [[1]], 1⟩
theorem n00028_checked : checkReduction n00028_reduction = true := by decide
def n00029_expression (x t : ℝ) : ℝ := (174865111 : ℝ)/(5000000000 : ℝ)
def n00029_pair : RationalPair := ⟨[[174865111]], [[5000000000]]⟩
def n00030_expression (x t : ℝ) : ℝ := n00016_expression x t * n00029_expression x t
def n00030_pair : RationalPair := ⟨[[-16087590212, 36197077977]], [[125000000000]]⟩
def n00030_reduction : Reduction := ⟨rawMul n00016_pair n00029_pair, n00030_pair, [[1]], 1⟩
theorem n00030_checked : checkReduction n00030_reduction = true := by decide
def n00031_expression (x t : ℝ) : ℝ := n00028_expression x t + n00030_expression x t
def n00031_pair : RationalPair := ⟨[[-51338896367, 98564773482]], [[125000000000]]⟩
def n00031_reduction : Reduction := ⟨rawAdd n00028_pair n00030_pair, n00031_pair, [[25000000000]], 1⟩
theorem n00031_checked : checkReduction n00031_reduction = true := by decide
def n00032_expression (x t : ℝ) : ℝ := n00031_expression x t + n00025_expression x t
def n00032_pair : RationalPair := ⟨[[-765808164597289, 1766623614580494, -561956484375000]], [[1520875000000000]]⟩
def n00032_reduction : Reduction := ⟨rawAdd n00031_pair n00025_pair, n00032_pair, [[1600]], 1⟩
theorem n00032_checked : checkReduction n00032_reduction = true := by decide
def n00033_expression (x t : ℝ) : ℝ := n00009_expression x t / n00017_expression x t
def n00033_pair : RationalPair := ⟨[[0, 1]], [[2]]⟩
def n00033_reduction : Reduction := ⟨rawDiv n00009_pair n00017_pair, n00033_pair, [[1]], 1⟩
theorem n00033_checked : checkReduction n00033_reduction = true := by decide
def n00034_expression (x t : ℝ) : ℝ := n00009_expression x t * n00001_expression x t
def n00034_pair : RationalPair := ⟨[[], [0, 1]], [[1]]⟩
def n00034_reduction : Reduction := ⟨rawMul n00009_pair n00001_pair, n00034_pair, [[1]], 1⟩
theorem n00034_checked : checkReduction n00034_reduction = true := by decide
def n00035_expression (x t : ℝ) : ℝ := n00034_expression x t / n00017_expression x t
def n00035_pair : RationalPair := ⟨[[], [0, 1]], [[2]]⟩
def n00035_reduction : Reduction := ⟨rawDiv n00034_pair n00017_pair, n00035_pair, [[1]], 1⟩
theorem n00035_checked : checkReduction n00035_reduction = true := by decide
def n00036_expression (x t : ℝ) : ℝ := n00033_expression x t + n00035_expression x t
def n00036_pair : RationalPair := ⟨[[0, 1], [0, 1]], [[2]]⟩
def n00036_reduction : Reduction := ⟨rawAdd n00033_pair n00035_pair, n00036_pair, [[2]], 1⟩
theorem n00036_checked : checkReduction n00036_reduction = true := by decide
def n00037_expression (x t : ℝ) : ℝ := n00005_expression x t - n00036_expression x t
def n00037_pair : RationalPair := ⟨[[2, -1], [0, -1]], [[2]]⟩
def n00037_reduction : Reduction := ⟨rawSub n00005_pair n00036_pair, n00037_pair, [[1]], 1⟩
theorem n00037_checked : checkReduction n00037_reduction = true := by decide
def n00038_expression (x t : ℝ) : ℝ := n00007_expression x t * n00037_expression x t
def n00038_pair : RationalPair := ⟨[[0, -2, 1], [0, 0, 1]], [[-2, 2]]⟩
def n00038_reduction : Reduction := ⟨rawMul n00007_pair n00037_pair, n00038_pair, [[1]], 1⟩
theorem n00038_checked : checkReduction n00038_reduction = true := by decide
def n00039_expression (x t : ℝ) : ℝ := n00005_expression x t + n00038_expression x t
def n00039_pair : RationalPair := ⟨[[-2, 0, 1], [0, 0, 1]], [[-2, 2]]⟩
def n00039_reduction : Reduction := ⟨rawAdd n00005_pair n00038_pair, n00039_pair, [[1]], 1⟩
theorem n00039_checked : checkReduction n00039_reduction = true := by decide
def n00040_expression (x t : ℝ) : ℝ := n00038_expression x t / n00039_expression x t
def n00040_pair : RationalPair := ⟨[[0, -2, 1], [0, 0, 1]], [[-2, 0, 1], [0, 0, 1]]⟩
def n00040_reduction : Reduction := ⟨rawDiv n00038_pair n00039_pair, n00040_pair, [[-2, 2]], 1⟩
theorem n00040_checked : checkReduction n00040_reduction = true := by decide
def n00041_expression (x t : ℝ) : ℝ := n00005_expression x t - n00040_expression x t
def n00041_pair : RationalPair := ⟨[[-2, 2]], [[-2, 0, 1], [0, 0, 1]]⟩
def n00041_reduction : Reduction := ⟨rawSub n00005_pair n00040_pair, n00041_pair, [[1]], 1⟩
theorem n00041_checked : checkReduction n00041_reduction = true := by decide
def n00042_expression (x t : ℝ) : ℝ := n00007_expression x t * n00041_expression x t
def n00042_pair : RationalPair := ⟨[[0, -2]], [[-2, 0, 1], [0, 0, 1]]⟩
def n00042_reduction : Reduction := ⟨rawMul n00007_pair n00041_pair, n00042_pair, [[-1, 1]], 1⟩
theorem n00042_checked : checkReduction n00042_reduction = true := by decide
def n00043_expression (x t : ℝ) : ℝ := n00005_expression x t + n00042_expression x t
def n00043_pair : RationalPair := ⟨[[-2, -2, 1], [0, 0, 1]], [[-2, 0, 1], [0, 0, 1]]⟩
def n00043_reduction : Reduction := ⟨rawAdd n00005_pair n00042_pair, n00043_pair, [[1]], 1⟩
theorem n00043_checked : checkReduction n00043_reduction = true := by decide
def n00044_expression (x t : ℝ) : ℝ := n00005_expression x t / n00043_expression x t
def n00044_pair : RationalPair := ⟨[[-2, 0, 1], [0, 0, 1]], [[-2, -2, 1], [0, 0, 1]]⟩
def n00044_reduction : Reduction := ⟨rawDiv n00005_pair n00043_pair, n00044_pair, [[1]], 1⟩
theorem n00044_checked : checkReduction n00044_reduction = true := by decide
def n00045_expression (x t : ℝ) : ℝ := (46809 : ℝ)/(1 : ℝ)
def n00045_pair : RationalPair := ⟨[[46809]], [[1]]⟩
def n00046_expression (x t : ℝ) : ℝ := n00007_expression x t - n00004_expression x t
def n00046_pair : RationalPair := ⟨[[269, -525]], [[-256, 256]]⟩
def n00046_reduction : Reduction := ⟨rawSub n00007_pair n00004_pair, n00046_pair, [[1]], 1⟩
theorem n00046_checked : checkReduction n00046_reduction = true := by decide
def n00047_expression (x t : ℝ) : ℝ := (3327 : ℝ)/(1 : ℝ)
def n00047_pair : RationalPair := ⟨[[3327]], [[1]]⟩
def n00048_expression (x t : ℝ) : ℝ := n00047_expression x t * n00046_expression x t
def n00048_pair : RationalPair := ⟨[[894963, -1746675]], [[-256, 256]]⟩
def n00048_reduction : Reduction := ⟨rawMul n00047_pair n00046_pair, n00048_pair, [[1]], 1⟩
theorem n00048_checked : checkReduction n00048_reduction = true := by decide
def n00049_expression (x t : ℝ) : ℝ := n00045_expression x t + n00048_expression x t
def n00049_pair : RationalPair := ⟨[[-11088141, 10236429]], [[-256, 256]]⟩
def n00049_reduction : Reduction := ⟨rawAdd n00045_pair n00048_pair, n00049_pair, [[1]], 1⟩
theorem n00049_checked : checkReduction n00049_reduction = true := by decide
def n00050_expression (x t : ℝ) : ℝ := (65536 : ℝ)/(1 : ℝ)
def n00050_pair : RationalPair := ⟨[[65536]], [[1]]⟩
def n00051_expression (x t : ℝ) : ℝ := n00049_expression x t / n00050_expression x t
def n00051_pair : RationalPair := ⟨[[-11088141, 10236429]], [[-16777216, 16777216]]⟩
def n00051_reduction : Reduction := ⟨rawDiv n00049_pair n00050_pair, n00051_pair, [[1]], 1⟩
theorem n00051_checked : checkReduction n00051_reduction = true := by decide
def n00052_expression (x t : ℝ) : ℝ := (35136 : ℝ)/(1 : ℝ)
def n00052_pair : RationalPair := ⟨[[35136]], [[1]]⟩
def n00053_expression (x t : ℝ) : ℝ := (3086 : ℝ)/(1 : ℝ)
def n00053_pair : RationalPair := ⟨[[3086]], [[1]]⟩
def n00054_expression (x t : ℝ) : ℝ := n00053_expression x t * n00046_expression x t
def n00054_pair : RationalPair := ⟨[[415067, -810075]], [[-128, 128]]⟩
def n00054_reduction : Reduction := ⟨rawMul n00053_pair n00046_pair, n00054_pair, [[2]], 1⟩
theorem n00054_checked : checkReduction n00054_reduction = true := by decide
def n00055_expression (x t : ℝ) : ℝ := n00052_expression x t + n00054_expression x t
def n00055_pair : RationalPair := ⟨[[-4082341, 3687333]], [[-128, 128]]⟩
def n00055_reduction : Reduction := ⟨rawAdd n00052_pair n00054_pair, n00055_pair, [[1]], 1⟩
theorem n00055_checked : checkReduction n00055_reduction = true := by decide
def n00056_expression (x t : ℝ) : ℝ := n00055_expression x t / n00050_expression x t
def n00056_pair : RationalPair := ⟨[[-4082341, 3687333]], [[-8388608, 8388608]]⟩
def n00056_reduction : Reduction := ⟨rawDiv n00055_pair n00050_pair, n00056_pair, [[1]], 1⟩
theorem n00056_checked : checkReduction n00056_reduction = true := by decide
def n00057_expression (x t : ℝ) : ℝ := (14520 : ℝ)/(1 : ℝ)
def n00057_pair : RationalPair := ⟨[[14520]], [[1]]⟩
def n00058_expression (x t : ℝ) : ℝ := (13694 : ℝ)/(1 : ℝ)
def n00058_pair : RationalPair := ⟨[[13694]], [[1]]⟩
def n00059_expression (x t : ℝ) : ℝ := n00058_expression x t * n00046_expression x t
def n00059_pair : RationalPair := ⟨[[1841843, -3594675]], [[-128, 128]]⟩
def n00059_reduction : Reduction := ⟨rawMul n00058_pair n00046_pair, n00059_pair, [[2]], 1⟩
theorem n00059_checked : checkReduction n00059_reduction = true := by decide
def n00060_expression (x t : ℝ) : ℝ := n00057_expression x t + n00059_expression x t
def n00060_pair : RationalPair := ⟨[[-16717, -1736115]], [[-128, 128]]⟩
def n00060_reduction : Reduction := ⟨rawAdd n00057_pair n00059_pair, n00060_pair, [[1]], 1⟩
theorem n00060_checked : checkReduction n00060_reduction = true := by decide
def n00061_expression (x t : ℝ) : ℝ := n00060_expression x t / n00050_expression x t
def n00061_pair : RationalPair := ⟨[[-16717, -1736115]], [[-8388608, 8388608]]⟩
def n00061_reduction : Reduction := ⟨rawDiv n00060_pair n00050_pair, n00061_pair, [[1]], 1⟩
theorem n00061_checked : checkReduction n00061_reduction = true := by decide
def n00062_expression (x t : ℝ) : ℝ := (1835 : ℝ)/(1 : ℝ)
def n00062_pair : RationalPair := ⟨[[1835]], [[1]]⟩
def n00063_expression (x t : ℝ) : ℝ := (1340 : ℝ)/(1 : ℝ)
def n00063_pair : RationalPair := ⟨[[1340]], [[1]]⟩
def n00064_expression (x t : ℝ) : ℝ := n00063_expression x t * n00046_expression x t
def n00064_pair : RationalPair := ⟨[[90115, -175875]], [[-64, 64]]⟩
def n00064_reduction : Reduction := ⟨rawMul n00063_pair n00046_pair, n00064_pair, [[4]], 1⟩
theorem n00064_checked : checkReduction n00064_reduction = true := by decide
def n00065_expression (x t : ℝ) : ℝ := n00062_expression x t + n00064_expression x t
def n00065_pair : RationalPair := ⟨[[-27325, -58435]], [[-64, 64]]⟩
def n00065_reduction : Reduction := ⟨rawAdd n00062_pair n00064_pair, n00065_pair, [[1]], 1⟩
theorem n00065_checked : checkReduction n00065_reduction = true := by decide
def n00066_expression (x t : ℝ) : ℝ := n00065_expression x t / n00050_expression x t
def n00066_pair : RationalPair := ⟨[[-27325, -58435]], [[-4194304, 4194304]]⟩
def n00066_reduction : Reduction := ⟨rawDiv n00065_pair n00050_pair, n00066_pair, [[1]], 1⟩
theorem n00066_checked : checkReduction n00066_reduction = true := by decide
def n00067_expression (x t : ℝ) : ℝ := n00036_expression x t ^ 2
def n00067_pair : RationalPair := ⟨[[0, 0, 1], [0, 0, 2], [0, 0, 1]], [[4]]⟩
def n00067_reduction : Reduction := ⟨rawPow n00036_pair 2, n00067_pair, [[1]], 1⟩
theorem n00067_checked : checkReduction n00067_reduction = true := by decide
def n00068_expression (x t : ℝ) : ℝ := n00017_expression x t - n00036_expression x t
def n00068_pair : RationalPair := ⟨[[4, -1], [0, -1]], [[2]]⟩
def n00068_reduction : Reduction := ⟨rawSub n00017_pair n00036_pair, n00068_pair, [[1]], 1⟩
theorem n00068_checked : checkReduction n00068_reduction = true := by decide
def n00069_expression (x t : ℝ) : ℝ := (6 : ℝ)/(1 : ℝ)
def n00069_pair : RationalPair := ⟨[[6]], [[1]]⟩
def n00070_expression (x t : ℝ) : ℝ := (12 : ℝ)/(1 : ℝ)
def n00070_pair : RationalPair := ⟨[[12]], [[1]]⟩
def n00071_expression (x t : ℝ) : ℝ := n00070_expression x t * n00036_expression x t
def n00071_pair : RationalPair := ⟨[[0, 6], [0, 6]], [[1]]⟩
def n00071_reduction : Reduction := ⟨rawMul n00070_pair n00036_pair, n00071_pair, [[2]], 1⟩
theorem n00071_checked : checkReduction n00071_reduction = true := by decide
def n00072_expression (x t : ℝ) : ℝ := n00067_expression x t - n00071_expression x t
def n00072_pair : RationalPair := ⟨[[0, -24, 1], [0, -24, 2], [0, 0, 1]], [[4]]⟩
def n00072_reduction : Reduction := ⟨rawSub n00067_pair n00071_pair, n00072_pair, [[1]], 1⟩
theorem n00072_checked : checkReduction n00072_reduction = true := by decide
def n00073_expression (x t : ℝ) : ℝ := n00072_expression x t + n00070_expression x t
def n00073_pair : RationalPair := ⟨[[48, -24, 1], [0, -24, 2], [0, 0, 1]], [[4]]⟩
def n00073_reduction : Reduction := ⟨rawAdd n00072_pair n00070_pair, n00073_pair, [[1]], 1⟩
theorem n00073_checked : checkReduction n00073_reduction = true := by decide
def n00074_expression (x t : ℝ) : ℝ := n00036_expression x t * n00073_expression x t
def n00074_pair : RationalPair := ⟨[[0, 48, -24, 1], [0, 48, -48, 3], [0, 0, -24, 3], [0, 0, 0, 1]], [[8]]⟩
def n00074_reduction : Reduction := ⟨rawMul n00036_pair n00073_pair, n00074_pair, [[1]], 1⟩
theorem n00074_checked : checkReduction n00074_reduction = true := by decide
def n00075_expression (x t : ℝ) : ℝ := n00069_expression x t * n00037_expression x t
def n00075_pair : RationalPair := ⟨[[6, -3], [0, -3]], [[1]]⟩
def n00075_reduction : Reduction := ⟨rawMul n00069_pair n00037_pair, n00075_pair, [[2]], 1⟩
theorem n00075_checked : checkReduction n00075_reduction = true := by decide
def n00076_expression (x t : ℝ) : ℝ := n00075_expression x t * n00068_expression x t
def n00076_pair : RationalPair := ⟨[[24, -18, 3], [0, -18, 6], [0, 0, 3]], [[2]]⟩
def n00076_reduction : Reduction := ⟨rawMul n00075_pair n00068_pair, n00076_pair, [[1]], 1⟩
theorem n00076_checked : checkReduction n00076_reduction = true := by decide
def n00077_expression (x t : ℝ) : ℝ := n00074_expression x t / n00076_expression x t
def n00077_pair : RationalPair := ⟨[[0, 48, -24, 1], [0, 48, -48, 3], [0, 0, -24, 3], [0, 0, 0, 1]], [[96, -72, 12], [0, -72, 24], [0, 0, 12]]⟩
def n00077_reduction : Reduction := ⟨rawDiv n00074_pair n00076_pair, n00077_pair, [[2]], 1⟩
theorem n00077_checked : checkReduction n00077_reduction = true := by decide
def n00078_expression (x t : ℝ) : ℝ := n00040_expression x t / n00017_expression x t
def n00078_pair : RationalPair := ⟨[[0, -2, 1], [0, 0, 1]], [[-4, 0, 2], [0, 0, 2]]⟩
def n00078_reduction : Reduction := ⟨rawDiv n00040_pair n00017_pair, n00078_pair, [[1]], 1⟩
theorem n00078_checked : checkReduction n00078_reduction = true := by decide
def n00079_expression (x t : ℝ) : ℝ := n00005_expression x t - n00078_expression x t
def n00079_pair : RationalPair := ⟨[[-4, 2, 1], [0, 0, 1]], [[-4, 0, 2], [0, 0, 2]]⟩
def n00079_reduction : Reduction := ⟨rawSub n00005_pair n00078_pair, n00079_pair, [[1]], 1⟩
theorem n00079_checked : checkReduction n00079_reduction = true := by decide
def n00080_expression (x t : ℝ) : ℝ := n00040_expression x t * n00040_expression x t
def n00080_pair : RationalPair := ⟨[[0, 0, 4, -4, 1], [0, 0, 0, -4, 2], [0, 0, 0, 0, 1]], [[4, 0, -4, 0, 1], [0, 0, -4, 0, 2], [0, 0, 0, 0, 1]]⟩
def n00080_reduction : Reduction := ⟨rawMul n00040_pair n00040_pair, n00080_pair, [[1]], 1⟩
theorem n00080_checked : checkReduction n00080_reduction = true := by decide
def n00081_expression (x t : ℝ) : ℝ := n00080_expression x t / n00070_expression x t
def n00081_pair : RationalPair := ⟨[[0, 0, 4, -4, 1], [0, 0, 0, -4, 2], [0, 0, 0, 0, 1]], [[48, 0, -48, 0, 12], [0, 0, -48, 0, 24], [0, 0, 0, 0, 12]]⟩
def n00081_reduction : Reduction := ⟨rawDiv n00080_pair n00070_pair, n00081_pair, [[1]], 1⟩
theorem n00081_checked : checkReduction n00081_reduction = true := by decide
def n00082_expression (x t : ℝ) : ℝ := n00079_expression x t - n00081_expression x t
def n00082_pair : RationalPair := ⟨[[48, -24, -40, 16, 5], [0, 0, -36, 16, 10], [0, 0, 0, 0, 5]], [[48, 0, -48, 0, 12], [0, 0, -48, 0, 24], [0, 0, 0, 0, 12]]⟩
def n00082_reduction : Reduction := ⟨rawSub n00079_pair n00081_pair, n00082_pair, [[-4, 0, 2], [0, 0, 2]], 1⟩
theorem n00082_checked : checkReduction n00082_reduction = true := by decide
def n00083_expression (x t : ℝ) : ℝ := n00061_expression x t * n00082_expression x t
def n00083_pair : RationalPair := ⟨[[-802416, -82932312, 42335440, 69177128, -27861425, -8680575], [0, 0, 601812, 62232668, -27945010, -17361150], [0, 0, 0, 0, -83585, -8680575]], [[-402653184, 402653184, 402653184, -402653184, -100663296, 100663296], [0, 0, 402653184, -402653184, -201326592, 201326592], [0, 0, 0, 0, -100663296, 100663296]]⟩
def n00083_reduction : Reduction := ⟨rawMul n00061_pair n00082_pair, n00083_pair, [[1]], 1⟩
theorem n00083_checked : checkReduction n00083_reduction = true := by decide
def n00084_expression (x t : ℝ) : ℝ := (9 : ℝ)/(10 : ℝ)
def n00084_pair : RationalPair := ⟨[[9]], [[10]]⟩
def n00085_expression (x t : ℝ) : ℝ := n00044_expression x t * n00041_expression x t
def n00085_pair : RationalPair := ⟨[[-2, 2]], [[-2, -2, 1], [0, 0, 1]]⟩
def n00085_reduction : Reduction := ⟨rawMul n00044_pair n00041_pair, n00085_pair, [[-2, 0, 1], [0, 0, 1]], 1⟩
theorem n00085_checked : checkReduction n00085_reduction = true := by decide
def n00086_expression (x t : ℝ) : ℝ := n00085_expression x t + n00083_expression x t
def n00086_pair : RationalPair := ⟨[[806911200, -1443143280, 80391328, 1304655288, -644275742, -260392056, 190826317, -8680575], [0, 0, -807312408, 1402011464, -428291248, -583284252, 381569049, -26041725], [0, 0, 0, 0, 202095574, -322892196, 190659147, -26041725], [0, 0, 0, 0, 0, 0, -83585, -8680575]], [[805306368, 0, -2013265920, 402653184, 1409286144, -402653184, -301989888, 100663296], [0, 0, -1207959552, 402653184, 2013265920, -805306368, -704643072, 301989888], [0, 0, 0, 0, 603979776, -402653184, -503316480, 301989888], [0, 0, 0, 0, 0, 0, -100663296, 100663296]]⟩
def n00086_reduction : Reduction := ⟨rawAdd n00085_pair n00083_pair, n00086_pair, [[1]], 1⟩
theorem n00086_checked : checkReduction n00086_reduction = true := by decide
def n00087_expression (x t : ℝ) : ℝ := n00061_expression x t - n00066_expression x t
def n00087_pair : RationalPair := ⟨[[37933, -1619245]], [[-8388608, 8388608]]⟩
def n00087_reduction : Reduction := ⟨rawSub n00061_pair n00066_pair, n00087_pair, [[-4194304, 4194304]], 1⟩
theorem n00087_checked : checkReduction n00087_reduction = true := by decide
def n00088_expression (x t : ℝ) : ℝ := n00017_expression x t * n00087_expression x t
def n00088_pair : RationalPair := ⟨[[37933, -1619245]], [[-4194304, 4194304]]⟩
def n00088_reduction : Reduction := ⟨rawMul n00017_pair n00087_pair, n00088_pair, [[2]], 1⟩
theorem n00088_checked : checkReduction n00088_reduction = true := by decide
def n00089_expression (x t : ℝ) : ℝ := n00088_expression x t * n00002_expression x t
def n00089_pair : RationalPair := ⟨[[37933, -1619245]], [[-5242880, 5242880]]⟩
def n00089_reduction : Reduction := ⟨rawMul n00088_pair n00002_pair, n00089_pair, [[4]], 1⟩
theorem n00089_checked : checkReduction n00089_reduction = true := by decide
def n00090_expression (x t : ℝ) : ℝ := n00017_expression x t * n00086_expression x t
def n00090_pair : RationalPair := ⟨[[806911200, -1443143280, 80391328, 1304655288, -644275742, -260392056, 190826317, -8680575], [0, 0, -807312408, 1402011464, -428291248, -583284252, 381569049, -26041725], [0, 0, 0, 0, 202095574, -322892196, 190659147, -26041725], [0, 0, 0, 0, 0, 0, -83585, -8680575]], [[402653184, 0, -1006632960, 201326592, 704643072, -201326592, -150994944, 50331648], [0, 0, -603979776, 201326592, 1006632960, -402653184, -352321536, 150994944], [0, 0, 0, 0, 301989888, -201326592, -251658240, 150994944], [0, 0, 0, 0, 0, 0, -50331648, 50331648]]⟩
def n00090_reduction : Reduction := ⟨rawMul n00017_pair n00086_pair, n00090_pair, [[2]], 1⟩
theorem n00090_checked : checkReduction n00090_reduction = true := by decide
def n00091_expression (x t : ℝ) : ℝ := n00077_expression x t * n00002_expression x t
def n00091_pair : RationalPair := ⟨[[0, 48, -24, 1], [0, 48, -48, 3], [0, 0, -24, 3], [0, 0, 0, 1]], [[120, -90, 15], [0, -90, 30], [0, 0, 15]]⟩
def n00091_reduction : Reduction := ⟨rawMul n00077_pair n00002_pair, n00091_pair, [[4]], 1⟩
theorem n00091_checked : checkReduction n00091_reduction = true := by decide
def n00092_expression (x t : ℝ) : ℝ := n00005_expression x t - n00091_expression x t
def n00092_pair : RationalPair := ⟨[[120, -138, 39, -1], [0, -138, 78, -3], [0, 0, 39, -3], [0, 0, 0, -1]], [[120, -90, 15], [0, -90, 30], [0, 0, 15]]⟩
def n00092_reduction : Reduction := ⟨rawSub n00005_pair n00091_pair, n00092_pair, [[1]], 1⟩
theorem n00092_checked : checkReduction n00092_reduction = true := by decide
def n00093_expression (x t : ℝ) : ℝ := n00090_expression x t * n00092_expression x t
def n00093_pair : RationalPair := ⟨[[96829344000, -284530939200, 240270268800, 88375132176, -252777113712, 108464170580, 32401852542, -36886715188, 8900537769, -529368742, 8680575], [0, -111353745600, 165215357280, 153570575280, -445800192024, 235027832364, 89942772508, -122813115230, 35921783457, -2646760125, 52083450], [0, 0, 31469536800, 52705790784, -224731789344, 154887153156, 89159703312, -147321150136, 54681756138, -5293269495, 130208625], [0, 0, 0, -806911200, -30042040632, 29130803780, 38098499268, -73951910908, 37519945362, -5292851570, 173611500], [0, 0, 0, 0, 0, 807312408, 6479715922, -12759256388, 10179067293, -2646007860, 130208625], [0, 0, 0, 0, 0, 0, 0, -202095574, 319632381, -528950817, 52083450], [0, 0, 0, 0, 0, 0, 0, 0, 0, 83585, 8680575]], [[48318382080, -36238786560, -114756157440, 114756157440, 51338280960, -84557168640, 10569646080, 16609443840, -6794772480, 754974720], [0, -36238786560, -60397977600, 169114337280, 45298483200, -193273528320, 48318382080, 51338280960, -27934064640, 3774873600], [0, 0, 6039797760, 54358179840, -15099494400, -132875550720, 69457674240, 54358179840, -43788533760, 7549747200], [0, 0, 0, 0, -9059696640, -24159191040, 36238786560, 21139292160, -31708938240, 7549747200], [0, 0, 0, 0, 0, 0, 4529848320, 1509949440, -9814671360, 3774873600], [0, 0, 0, 0, 0, 0, 0, 0, -754974720, 754974720]]⟩
def n00093_reduction : Reduction := ⟨rawMul n00090_pair n00092_pair, n00093_pair, [[1]], 1⟩
theorem n00093_checked : checkReduction n00093_reduction = true := by decide
def n00094_expression (x t : ℝ) : ℝ := n00093_expression x t - n00051_expression x t
def n00094_pair : RationalPair := ⟨[[64895497920, -263033485200, 315499920600, 17744725176, -287320057812, 161128929860, 26489480832, -47327396218, 13084618554, -990008047, 8680575], [0, -87403361040, 206972362800, 46707975120, -479417568564, 356784198444, 61841630428, -155363053250, 53157072942, -4949956650, 52083450], [0, 0, 27477806040, 16473597624, -217818625644, 240405607476, 47700736212, -182326878016, 81782106228, -9899662545, 130208625], [0, 0, 0, -806911200, -24054444492, 45557651300, 15834504468, -88076276728, 57250066572, -9899244620, 173611500], [0, 0, 0, 0, 0, 807312408, 3485917852, -13987151318, 16359013458, -4949204385, 130208625], [0, 0, 0, 0, 0, 0, 0, -202095574, 818598726, -989590122, 52083450], [0, 0, 0, 0, 0, 0, 0, 0, 0, 83585, 8680575]], [[48318382080, -36238786560, -114756157440, 114756157440, 51338280960, -84557168640, 10569646080, 16609443840, -6794772480, 754974720], [0, -36238786560, -60397977600, 169114337280, 45298483200, -193273528320, 48318382080, 51338280960, -27934064640, 3774873600], [0, 0, 6039797760, 54358179840, -15099494400, -132875550720, 69457674240, 54358179840, -43788533760, 7549747200], [0, 0, 0, 0, -9059696640, -24159191040, 36238786560, 21139292160, -31708938240, 7549747200], [0, 0, 0, 0, 0, 0, 4529848320, 1509949440, -9814671360, 3774873600], [0, 0, 0, 0, 0, 0, 0, 0, -754974720, 754974720]]⟩
def n00094_reduction : Reduction := ⟨rawSub n00093_pair n00051_pair, n00094_pair, [[-16777216, 16777216]], 1⟩
theorem n00094_checked : checkReduction n00094_reduction = true := by decide
def n00095_expression (x t : ℝ) : ℝ := n00094_expression x t - n00056_expression x t
def n00095_pair : RationalPair := ⟨[[41381213760, -247673018160, 370777533960, -33266801784, -312872796252, 199292666660, 22341151332, -54912721318, 16106909004, -1321868017, 8680575], [0, -69767647920, 238071652560, -31041527280, -504875079084, 445295422764, 41882418268, -179067154250, 65613645432, -6609256500, 52083450], [0, 0, 24538520520, -10264377816, -213314469444, 302936845716, 18022836252, -207927230416, 101385491688, -13218262245, 130208625], [0, 0, 0, -806911200, -19645516212, 57741402020, -236976972, -98505978928, 71543692512, -13217844320, 173611500], [0, 0, 0, 0, 0, 807312408, 1281453712, -14935277018, 20850946668, -6608504235, 130208625], [0, 0, 0, 0, 0, 0, 0, -202095574, 1186009416, -1321450092, 52083450], [0, 0, 0, 0, 0, 0, 0, 0, 0, 83585, 8680575]], [[48318382080, -36238786560, -114756157440, 114756157440, 51338280960, -84557168640, 10569646080, 16609443840, -6794772480, 754974720], [0, -36238786560, -60397977600, 169114337280, 45298483200, -193273528320, 48318382080, 51338280960, -27934064640, 3774873600], [0, 0, 6039797760, 54358179840, -15099494400, -132875550720, 69457674240, 54358179840, -43788533760, 7549747200], [0, 0, 0, 0, -9059696640, -24159191040, 36238786560, 21139292160, -31708938240, 7549747200], [0, 0, 0, 0, 0, 0, 4529848320, 1509949440, -9814671360, 3774873600], [0, 0, 0, 0, 0, 0, 0, 0, -754974720, 754974720]]⟩
def n00095_reduction : Reduction := ⟨rawSub n00094_pair n00056_pair, n00095_pair, [[-8388608, 8388608]], 1⟩
theorem n00095_checked : checkReduction n00095_reduction = true := by decide
def n00096_expression (x t : ℝ) : ℝ := n00040_expression x t * n00095_expression x t
def n00096_pair : RationalPair := ⟨[[0, 41381213760, -247673018160, 370777533960, -33266801784, -312872796252, 199292666660, 22341151332, -54912721318, 16106909004, -1321868017, 8680575], [0, 0, -69767647920, 238071652560, -31041527280, -504875079084, 445295422764, 41882418268, -179067154250, 65613645432, -6609256500, 52083450], [0, 0, 0, 24538520520, -10264377816, -213314469444, 302936845716, 18022836252, -207927230416, 101385491688, -13218262245, 130208625], [0, 0, 0, 0, -806911200, -19645516212, 57741402020, -236976972, -98505978928, 71543692512, -13217844320, 173611500], [0, 0, 0, 0, 0, 0, 807312408, 1281453712, -14935277018, 20850946668, -6608504235, 130208625], [0, 0, 0, 0, 0, 0, 0, 0, -202095574, 1186009416, -1321450092, 52083450], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 83585, 8680575]], [[48318382080, -12079595520, -144955146240, 60397977600, 138915348480, -72477573120, -51338280960, 33218887680, 4529848320, -5284823040, 754974720], [0, -12079595520, -96636764160, 84557168640, 205353123840, -163074539520, -117776056320, 105696460800, 12079595520, -21894266880, 3774873600], [0, 0, 0, 24159191040, 66437775360, -108716359680, -81537269760, 117776056320, 9059696640, -34728837120, 7549747200], [0, 0, 0, 0, 0, -18119393280, -15099494400, 51338280960, 0, -25669140480, 7549747200], [0, 0, 0, 0, 0, 0, 0, 6039797760, -1509949440, -8304721920, 3774873600], [0, 0, 0, 0, 0, 0, 0, 0, 0, -754974720, 754974720]]⟩
def n00096_reduction : Reduction := ⟨rawMul n00040_pair n00095_pair, n00096_pair, [[-2, 1], [0, 1]], 1⟩
theorem n00096_checked : checkReduction n00096_reduction = true := by decide
def n00097_expression (x t : ℝ) : ℝ := n00089_expression x t + n00096_expression x t
def n00097_pair : RationalPair := ⟨[[-349590528, 56041982784, -235694218032, 337550460168, -48845245944, -285023339100, 205129120868, 12081615012, -54945495430, 17511399036, -1555039297, 8680575], [0, 87397632, -72711809712, 204669783504, -39813972720, -449045068332, 451612563948, 11060110492, -177332880458, 71237067912, -7775112900, 52083450], [0, 0, 0, 24363725256, -3458379096, -185202819396, 298061765460, -12886869156, -202527764368, 109834281288, -15549975045, 130208625], [0, 0, 0, 0, -806911200, -19514419764, 52385634788, -10627609740, -93040964656, 77194426752, -15549557120, 173611500], [0, 0, 0, 0, 0, 0, 807312408, 1237754896, -13102680890, 22277286108, -7774360635, 130208625], [0, 0, 0, 0, 0, 0, 0, 0, -202095574, 1191471768, -1554621372, 52083450], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 83585, 8680575]], [[48318382080, -12079595520, -144955146240, 60397977600, 138915348480, -72477573120, -51338280960, 33218887680, 4529848320, -5284823040, 754974720], [0, -12079595520, -96636764160, 84557168640, 205353123840, -163074539520, -117776056320, 105696460800, 12079595520, -21894266880, 3774873600], [0, 0, 0, 24159191040, 66437775360, -108716359680, -81537269760, 117776056320, 9059696640, -34728837120, 7549747200], [0, 0, 0, 0, 0, -18119393280, -15099494400, 51338280960, 0, -25669140480, 7549747200], [0, 0, 0, 0, 0, 0, 0, 6039797760, -1509949440, -8304721920, 3774873600], [0, 0, 0, 0, 0, 0, 0, 0, 0, -754974720, 754974720]]⟩
def n00097_reduction : Reduction := ⟨rawAdd n00089_pair n00096_pair, n00097_pair, [[-5242880, 5242880]], 1⟩
theorem n00097_checked : checkReduction n00097_reduction = true := by decide
def n00098_expression (x t : ℝ) : ℝ := n00005_expression x t * n00041_expression x t
def n00098_pair : RationalPair := ⟨[[-2, 2]], [[-2, 0, 1], [0, 0, 1]]⟩
def n00098_reduction : Reduction := ⟨rawMul n00005_pair n00041_pair, n00098_pair, [[1]], 1⟩
theorem n00098_checked : checkReduction n00098_reduction = true := by decide
def n00099_expression (x t : ℝ) : ℝ := n00098_expression x t + n00083_expression x t
def n00099_pair : RationalPair := ⟨[[-403455600, 722374056, -158991152, -333476056, 173465167, -8680575], [0, 0, 201928404, -340420516, 173381582, -17361150], [0, 0, 0, 0, -83585, -8680575]], [[-402653184, 402653184, 402653184, -402653184, -100663296, 100663296], [0, 0, 402653184, -402653184, -201326592, 201326592], [0, 0, 0, 0, -100663296, 100663296]]⟩
def n00099_reduction : Reduction := ⟨rawAdd n00098_pair n00083_pair, n00099_pair, [[-2, 0, 1], [0, 0, 1]], 1⟩
theorem n00099_checked : checkReduction n00099_reduction = true := by decide
def n00100_expression (x t : ℝ) : ℝ := n00017_expression x t * n00099_expression x t
def n00100_pair : RationalPair := ⟨[[-403455600, 722374056, -158991152, -333476056, 173465167, -8680575], [0, 0, 201928404, -340420516, 173381582, -17361150], [0, 0, 0, 0, -83585, -8680575]], [[-201326592, 201326592, 201326592, -201326592, -50331648, 50331648], [0, 0, 201326592, -201326592, -100663296, 100663296], [0, 0, 0, 0, -50331648, 50331648]]⟩
def n00100_reduction : Reduction := ⟨rawMul n00017_pair n00099_pair, n00100_pair, [[2]], 1⟩
theorem n00100_checked : checkReduction n00100_reduction = true := by decide
def n00101_expression (x t : ℝ) : ℝ := n00100_expression x t * n00092_expression x t
def n00101_pair : RationalPair := ⟨[[-48414672000, 142361759520, -134501326368, 10499696040, 59912486784, -37826437078, 8296536919, -512007592, 8680575], [0, 55676872800, -106925748048, 10779740472, 107110292508, -88960676802, 25226771458, -2047946783, 43402875], [0, 0, -15734768400, 1516835232, 54350639424, -64643970774, 25901092860, -3071711212, 86805750], [0, 0, 0, 403455600, 7152833700, -13711659454, 9308019022, -2047528858, 86805750], [0, 0, 0, 0, 0, -201928404, 337160701, -511673252, 43402875], [0, 0, 0, 0, 0, 0, 0, 83585, 8680575]], [[-24159191040, 42278584320, 3019898880, -39258685440, 15099494400, 7549747200, -5284823040, 754974720], [0, 18119393280, 0, -54358179840, 33218887680, 16609443840, -16609443840, 3019898880], [0, 0, -3019898880, -15099494400, 21139292160, 10569646080, -18119393280, 4529848320], [0, 0, 0, 0, 3019898880, 1509949440, -7549747200, 3019898880], [0, 0, 0, 0, 0, 0, -754974720, 754974720]]⟩
def n00101_reduction : Reduction := ⟨rawMul n00100_pair n00092_pair, n00101_pair, [[1]], 1⟩
theorem n00101_checked : checkReduction n00101_reduction = true := by decide
def n00102_expression (x t : ℝ) : ℝ := n00101_expression x t - n00051_expression x t
def n00102_pair : RationalPair := ⟨[[-32447748960, 115646109480, -137417040708, 35372788860, 50853008844, -42662792368, 11559339094, -972646897, 8680575], [0, 43701680520, -107845597008, 45785468352, 86995471248, -99784628232, 35514144328, -3890504003, 43402875], [0, 0, -13738903020, 11649470292, 41299430724, -71782807764, 37186398420, -5835547042, 86805750], [0, 0, 0, 403455600, 5156968320, -14862900304, 14067720232, -3890086078, 86805750], [0, 0, 0, 0, 0, -201928404, 836127046, -972312557, 43402875], [0, 0, 0, 0, 0, 0, 0, 83585, 8680575]], [[-24159191040, 42278584320, 3019898880, -39258685440, 15099494400, 7549747200, -5284823040, 754974720], [0, 18119393280, 0, -54358179840, 33218887680, 16609443840, -16609443840, 3019898880], [0, 0, -3019898880, -15099494400, 21139292160, 10569646080, -18119393280, 4529848320], [0, 0, 0, 0, 3019898880, 1509949440, -7549747200, 3019898880], [0, 0, 0, 0, 0, 0, -754974720, 754974720]]⟩
def n00102_reduction : Reduction := ⟨rawSub n00101_pair n00051_pair, n00102_pair, [[-16777216, 16777216]], 1⟩
theorem n00102_checked : checkReduction n00102_reduction = true := by decide
def n00103_expression (x t : ℝ) : ℝ := n00102_expression x t - n00056_expression x t
def n00103_pair : RationalPair := ⟨[[-20690606880, 96208733880, -139739900748, 53482724580, 44358012324, -46194696388, 13917909604, -1304506867, 8680575], [0, 34883823960, -108698814288, 71385820752, 72535835448, -107725460532, 42957266548, -5217943883, 43402875], [0, 0, -12269260260, 19139886972, 31865148684, -77068760304, 45364342020, -7826706862, 86805750], [0, 0, 0, 403455600, 3687325560, -15739924564, 17528522812, -5217525958, 86805750], [0, 0, 0, 0, 0, -201928404, 1203537736, -1304172527, 43402875], [0, 0, 0, 0, 0, 0, 0, 83585, 8680575]], [[-24159191040, 42278584320, 3019898880, -39258685440, 15099494400, 7549747200, -5284823040, 754974720], [0, 18119393280, 0, -54358179840, 33218887680, 16609443840, -16609443840, 3019898880], [0, 0, -3019898880, -15099494400, 21139292160, 10569646080, -18119393280, 4529848320], [0, 0, 0, 0, 3019898880, 1509949440, -7549747200, 3019898880], [0, 0, 0, 0, 0, 0, -754974720, 754974720]]⟩
def n00103_reduction : Reduction := ⟨rawSub n00102_pair n00056_pair, n00103_pair, [[-8388608, 8388608]], 1⟩
theorem n00103_checked : checkReduction n00103_reduction = true := by decide
def n00104_expression (x t : ℝ) : ℝ := n00040_expression x t * n00103_expression x t
def n00104_pair : RationalPair := ⟨[[0, -20690606880, 96208733880, -139739900748, 53482724580, 44358012324, -46194696388, 13917909604, -1304506867, 8680575], [0, 0, 34883823960, -108698814288, 71385820752, 72535835448, -107725460532, 42957266548, -5217943883, 43402875], [0, 0, 0, -12269260260, 19139886972, 31865148684, -77068760304, 45364342020, -7826706862, 86805750], [0, 0, 0, 0, 403455600, 3687325560, -15739924564, 17528522812, -5217525958, 86805750], [0, 0, 0, 0, 0, 0, -201928404, 1203537736, -1304172527, 43402875], [0, 0, 0, 0, 0, 0, 0, 0, 83585, 8680575]], [[-24159191040, 30198988800, 30198988800, -45298483200, -9059696640, 22649241600, -1509949440, -3774873600, 754974720], [0, 6039797760, 30198988800, -54358179840, -18119393280, 49828331520, -4529848320, -12079595520, 3019898880], [0, 0, 0, -9059696640, -9059696640, 31708938240, -4529848320, -13589544960, 4529848320], [0, 0, 0, 0, 0, 4529848320, -1509949440, -6039797760, 3019898880], [0, 0, 0, 0, 0, 0, 0, -754974720, 754974720]]⟩
def n00104_reduction : Reduction := ⟨rawMul n00040_pair n00103_pair, n00104_pair, [[-2, 1], [0, 1]], 1⟩
theorem n00104_checked : checkReduction n00104_reduction = true := by decide
def n00105_expression (x t : ℝ) : ℝ := n00089_expression x t + n00104_expression x t
def n00105_pair : RationalPair := ⟨[[174795264, -28195786656, 97811911224, -128482131084, 50815765668, 38729127492, -44817518116, 14856057076, -1537678147, 8680575], [0, -43698816, 36487001304, -97375496400, 66051902928, 61245291672, -103593925716, 45777171316, -6150629003, 43402875], [0, 0, 0, -12203712036, 16472928060, 26170715628, -72937225488, 48195171492, -9225734542, 86805750], [0, 0, 0, 0, 403455600, 3654551448, -14362746292, 18483057340, -6150211078, 86805750], [0, 0, 0, 0, 0, 0, -201928404, 1209000088, -1537343807, 43402875], [0, 0, 0, 0, 0, 0, 0, 0, 83585, 8680575]], [[-24159191040, 30198988800, 30198988800, -45298483200, -9059696640, 22649241600, -1509949440, -3774873600, 754974720], [0, 6039797760, 30198988800, -54358179840, -18119393280, 49828331520, -4529848320, -12079595520, 3019898880], [0, 0, 0, -9059696640, -9059696640, 31708938240, -4529848320, -13589544960, 4529848320], [0, 0, 0, 0, 0, 4529848320, -1509949440, -6039797760, 3019898880], [0, 0, 0, 0, 0, 0, 0, -754974720, 754974720]]⟩
def n00105_reduction : Reduction := ⟨rawAdd n00089_pair n00104_pair, n00105_pair, [[-5242880, 5242880]], 1⟩
theorem n00105_checked : checkReduction n00105_reduction = true := by decide
def n00106_expression (x t : ℝ) : ℝ := n00088_expression x t * n00084_expression x t
def n00106_pair : RationalPair := ⟨[[341397, -14573205]], [[-41943040, 41943040]]⟩
def n00106_reduction : Reduction := ⟨rawMul n00088_pair n00084_pair, n00106_pair, [[1]], 1⟩
theorem n00106_checked : checkReduction n00106_reduction = true := by decide
def n00107_expression (x t : ℝ) : ℝ := n00077_expression x t * n00084_expression x t
def n00107_pair : RationalPair := ⟨[[0, 144, -72, 3], [0, 144, -144, 9], [0, 0, -72, 9], [0, 0, 0, 3]], [[320, -240, 40], [0, -240, 80], [0, 0, 40]]⟩
def n00107_reduction : Reduction := ⟨rawMul n00077_pair n00084_pair, n00107_pair, [[3]], 1⟩
theorem n00107_checked : checkReduction n00107_reduction = true := by decide
def n00108_expression (x t : ℝ) : ℝ := n00005_expression x t - n00107_expression x t
def n00108_pair : RationalPair := ⟨[[320, -384, 112, -3], [0, -384, 224, -9], [0, 0, 112, -9], [0, 0, 0, -3]], [[320, -240, 40], [0, -240, 80], [0, 0, 40]]⟩
def n00108_reduction : Reduction := ⟨rawSub n00005_pair n00107_pair, n00108_pair, [[1]], 1⟩
theorem n00108_checked : checkReduction n00108_reduction = true := by decide
def n00109_expression (x t : ℝ) : ℝ := n00090_expression x t * n00108_expression x t
def n00109_pair : RationalPair := ⟨[[258211584000, -771659750400, 670266298880, 222566641248, -693822609456, 309956645280, 84982121976, -103286172774, 25487064472, -1544703351, 26041725], [0, -309853900800, 476575157760, 397255067680, -1235836274832, 676181247272, 237839479984, -344705473890, 102907572956, -7723266000, 156250350], [0, 0, 90374054400, 141113716512, -632547679632, 450247886008, 239161263936, -415005671748, 156759647104, -15445779735, 390625875], [0, 0, 0, -2420733600, -86089559856, 86445221240, 104732575824, -209645899644, 107704148296, -15444525960, 520834500], [0, 0, 0, 0, 0, 2421937224, 18428669896, -36665815734, 29324324744, -7721009205, 390625875], [0, 0, 0, 0, 0, 0, 0, -606286722, 959315068, -1543449576, 156250350], [0, 0, 0, 0, 0, 0, 0, 0, 0, 250755, 26041725]], [[128849018880, -96636764160, -306016419840, 306016419840, 136902082560, -225485783040, 28185722880, 44291850240, -18119393280, 2013265920], [0, -96636764160, -161061273600, 450971566080, 120795955200, -515396075520, 128849018880, 136902082560, -74490839040, 10066329600], [0, 0, 16106127360, 144955146240, -40265318400, -354334801920, 185220464640, 144955146240, -116769423360, 20132659200], [0, 0, 0, 0, -24159191040, -64424509440, 96636764160, 56371445760, -84557168640, 20132659200], [0, 0, 0, 0, 0, 0, 12079595520, 4026531840, -26172456960, 10066329600], [0, 0, 0, 0, 0, 0, 0, 0, -2013265920, 2013265920]]⟩
def n00109_reduction : Reduction := ⟨rawMul n00090_pair n00108_pair, n00109_pair, [[1]], 1⟩
theorem n00109_checked : checkReduction n00109_reduction = true := by decide
def n00110_expression (x t : ℝ) : ℝ := n00109_expression x t - n00051_expression x t
def n00110_pair : RationalPair := ⟨[[173054661120, -714333206400, 870878703680, 34218889248, -785937127056, 450396003360, 69215797416, -131127988854, 36644613232, -2773074831, 26041725], [0, -245986208640, 587927172480, 112288133920, -1325482612272, 1000864890152, 162903101104, -431505308610, 148868344916, -13865123400, 156250350], [0, 0, 79729439040, 44494534752, -614112576432, 678297097528, 128604018336, -508354279428, 229027247344, -27729494535, 390625875], [0, 0, 0, -2420733600, -70122636816, 130250147960, 45361923024, -247310875164, 160317804856, -27728240760, 520834500], [0, 0, 0, 0, 0, 2421937224, 10445208376, -39940202214, 45804181184, -13862866605, 390625875], [0, 0, 0, 0, 0, 0, 0, -606286722, 2289891988, -2771821056, 156250350], [0, 0, 0, 0, 0, 0, 0, 0, 0, 250755, 26041725]], [[128849018880, -96636764160, -306016419840, 306016419840, 136902082560, -225485783040, 28185722880, 44291850240, -18119393280, 2013265920], [0, -96636764160, -161061273600, 450971566080, 120795955200, -515396075520, 128849018880, 136902082560, -74490839040, 10066329600], [0, 0, 16106127360, 144955146240, -40265318400, -354334801920, 185220464640, 144955146240, -116769423360, 20132659200], [0, 0, 0, 0, -24159191040, -64424509440, 96636764160, 56371445760, -84557168640, 20132659200], [0, 0, 0, 0, 0, 0, 12079595520, 4026531840, -26172456960, 10066329600], [0, 0, 0, 0, 0, 0, 0, 0, -2013265920, 2013265920]]⟩
def n00110_reduction : Reduction := ⟨rawSub n00109_pair n00051_pair, n00110_pair, [[-16777216, 16777216]], 1⟩
theorem n00110_checked : checkReduction n00110_reduction = true := by decide
def n00111_expression (x t : ℝ) : ℝ := n00110_expression x t - n00056_expression x t
def n00111_pair : RationalPair := ⟨[[110349903360, -673371960960, 1018285672640, -101811849312, -854077762896, 552165968160, 58153585416, -151355522454, 44704054432, -3658034751, 26041725], [0, -198957640320, 670858611840, -95043872480, -1393369306992, 1236894821672, 109678535344, -494716244610, 182085871556, -18289923000, 156250350], [0, 0, 71891344320, -26806733088, -602101493232, 845047066168, 49462951776, -576621885828, 281302941904, -36579093735, 390625875], [0, 0, 0, -2420733600, -58365494736, 162740149880, 2504639184, -275123414364, 198434140696, -36577839960, 520834500], [0, 0, 0, 0, 0, 2421937224, 4566637336, -42468537414, 57782669744, -18287666205, 390625875], [0, 0, 0, 0, 0, 0, 0, -606286722, 3269653828, -3656780976, 156250350], [0, 0, 0, 0, 0, 0, 0, 0, 0, 250755, 26041725]], [[128849018880, -96636764160, -306016419840, 306016419840, 136902082560, -225485783040, 28185722880, 44291850240, -18119393280, 2013265920], [0, -96636764160, -161061273600, 450971566080, 120795955200, -515396075520, 128849018880, 136902082560, -74490839040, 10066329600], [0, 0, 16106127360, 144955146240, -40265318400, -354334801920, 185220464640, 144955146240, -116769423360, 20132659200], [0, 0, 0, 0, -24159191040, -64424509440, 96636764160, 56371445760, -84557168640, 20132659200], [0, 0, 0, 0, 0, 0, 12079595520, 4026531840, -26172456960, 10066329600], [0, 0, 0, 0, 0, 0, 0, 0, -2013265920, 2013265920]]⟩
def n00111_reduction : Reduction := ⟨rawSub n00110_pair n00056_pair, n00111_pair, [[-8388608, 8388608]], 1⟩
theorem n00111_checked : checkReduction n00111_reduction = true := by decide
def n00112_expression (x t : ℝ) : ℝ := n00040_expression x t * n00111_expression x t
def n00112_pair : RationalPair := ⟨[[0, 110349903360, -673371960960, 1018285672640, -101811849312, -854077762896, 552165968160, 58153585416, -151355522454, 44704054432, -3658034751, 26041725], [0, 0, -198957640320, 670858611840, -95043872480, -1393369306992, 1236894821672, 109678535344, -494716244610, 182085871556, -18289923000, 156250350], [0, 0, 0, 71891344320, -26806733088, -602101493232, 845047066168, 49462951776, -576621885828, 281302941904, -36579093735, 390625875], [0, 0, 0, 0, -2420733600, -58365494736, 162740149880, 2504639184, -275123414364, 198434140696, -36577839960, 520834500], [0, 0, 0, 0, 0, 0, 2421937224, 4566637336, -42468537414, 57782669744, -18287666205, 390625875], [0, 0, 0, 0, 0, 0, 0, 0, -606286722, 3269653828, -3656780976, 156250350], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 250755, 26041725]], [[128849018880, -32212254720, -386547056640, 161061273600, 370440929280, -193273528320, -136902082560, 88583700480, 12079595520, -14092861440, 2013265920], [0, -32212254720, -257698037760, 225485783040, 547608330240, -434865438720, -314069483520, 281857228800, 32212254720, -58384711680, 10066329600], [0, 0, 0, 64424509440, 177167400960, -289910292480, -217432719360, 314069483520, 24159191040, -92610232320, 20132659200], [0, 0, 0, 0, 0, -48318382080, -40265318400, 136902082560, 0, -68451041280, 20132659200], [0, 0, 0, 0, 0, 0, 0, 16106127360, -4026531840, -22145925120, 10066329600], [0, 0, 0, 0, 0, 0, 0, 0, 0, -2013265920, 2013265920]]⟩
def n00112_reduction : Reduction := ⟨rawMul n00040_pair n00111_pair, n00112_pair, [[-2, 1], [0, 1]], 1⟩
theorem n00112_checked : checkReduction n00112_reduction = true := by decide
def n00113_expression (x t : ℝ) : ℝ := n00106_expression x t + n00112_expression x t
def n00113_pair : RationalPair := ⟨[[-1048771584, 154332210432, -637435560576, 918604451264, -148547181792, -770529391440, 569675330784, 27374976456, -151453844790, 48917524528, -4357548591, 26041725], [0, 262192896, -207790125696, 570653004672, -121361208800, -1225879274736, 1255846245224, 17211612016, -489513423234, 198956138996, -21787492200, 156250350], [0, 0, 0, 71366958528, -6388736928, -517766543088, 830421825400, -43266164448, -560423487684, 306649310704, -43574232135, 390625875], [0, 0, 0, 0, -2420733600, -57972205392, 146672848184, -28667259120, -258728371548, 215386343416, -43572978360, 520834500], [0, 0, 0, 0, 0, 0, 2421937224, 4435540888, -36970749030, 62061688064, -21785235405, 390625875], [0, 0, 0, 0, 0, 0, 0, 0, -606286722, 3286040884, -4356294816, 156250350], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 250755, 26041725]], [[128849018880, -32212254720, -386547056640, 161061273600, 370440929280, -193273528320, -136902082560, 88583700480, 12079595520, -14092861440, 2013265920], [0, -32212254720, -257698037760, 225485783040, 547608330240, -434865438720, -314069483520, 281857228800, 32212254720, -58384711680, 10066329600], [0, 0, 0, 64424509440, 177167400960, -289910292480, -217432719360, 314069483520, 24159191040, -92610232320, 20132659200], [0, 0, 0, 0, 0, -48318382080, -40265318400, 136902082560, 0, -68451041280, 20132659200], [0, 0, 0, 0, 0, 0, 0, 16106127360, -4026531840, -22145925120, 10066329600], [0, 0, 0, 0, 0, 0, 0, 0, 0, -2013265920, 2013265920]]⟩
def n00113_reduction : Reduction := ⟨rawAdd n00106_pair n00112_pair, n00113_pair, [[-41943040, 41943040]], 1⟩
theorem n00113_checked : checkReduction n00113_reduction = true := by decide
def n00114_expression (x t : ℝ) : ℝ := n00100_expression x t * n00108_expression x t
def n00114_pair : RationalPair := ⟨[[-129105792000, 386086648320, -373455833344, 36456525520, 163589527752, -106260752944, 23761867672, -1492619901, 26041725], [0, 154926950400, -303148602624, 40020419056, 294758986584, -250745318796, 72297503044, -5970228849, 130208625], [0, 0, -45187027200, 6996487536, 151618317912, -183314163972, 74321303100, -8954716386, 260417250], [0, 0, 0, 1210366800, 20448859080, -39435383332, 26797567756, -5968975074, 260417250], [0, 0, 0, 0, 0, -605785212, 1011900028, -1491616881, 130208625], [0, 0, 0, 0, 0, 0, 0, 250755, 26041725]], [[-64424509440, 112742891520, 8053063680, -104689827840, 40265318400, 20132659200, -14092861440, 2013265920], [0, 48318382080, 0, -144955146240, 88583700480, 44291850240, -44291850240, 8053063680], [0, 0, -8053063680, -40265318400, 56371445760, 28185722880, -48318382080, 12079595520], [0, 0, 0, 0, 8053063680, 4026531840, -20132659200, 8053063680], [0, 0, 0, 0, 0, 0, -2013265920, 2013265920]]⟩
def n00114_reduction : Reduction := ⟨rawMul n00100_pair n00108_pair, n00114_pair, [[1]], 1⟩
theorem n00114_checked : checkReduction n00114_reduction = true := by decide
def n00115_expression (x t : ℝ) : ℝ := n00114_expression x t - n00051_expression x t
def n00115_pair : RationalPair := ⟨[[-86527330560, 314844914880, -381231071584, 102784773040, 139430919912, -119157700384, 32462673472, -2720991381, 26041725], [0, 122993104320, -305601533184, 133369026736, 241119463224, -279609189276, 99730497364, -10883714769, 130208625], [0, 0, -39864719520, 34016847696, 116815094712, -202351062612, 104415451260, -16324945266, 260417250], [0, 0, 0, 1210366800, 15126551400, -42505358932, 39490104316, -10882460994, 260417250], [0, 0, 0, 0, 0, -605785212, 2342476948, -2719988361, 130208625], [0, 0, 0, 0, 0, 0, 0, 250755, 26041725]], [[-64424509440, 112742891520, 8053063680, -104689827840, 40265318400, 20132659200, -14092861440, 2013265920], [0, 48318382080, 0, -144955146240, 88583700480, 44291850240, -44291850240, 8053063680], [0, 0, -8053063680, -40265318400, 56371445760, 28185722880, -48318382080, 12079595520], [0, 0, 0, 0, 8053063680, 4026531840, -20132659200, 8053063680], [0, 0, 0, 0, 0, 0, -2013265920, 2013265920]]⟩
def n00115_reduction : Reduction := ⟨rawSub n00114_pair n00051_pair, n00115_pair, [[-16777216, 16777216]], 1⟩
theorem n00115_checked : checkReduction n00115_reduction = true := by decide
def n00116_expression (x t : ℝ) : ℝ := n00115_expression x t - n00056_expression x t
def n00116_pair : RationalPair := ⟨[[-55174951680, 263011913280, -387425365024, 151077934960, 122110929192, -128576111104, 38752194832, -3605951301, 26041725], [0, 99478820160, -307876779264, 201636633136, 202560434424, -300784742076, 119578823284, -14423554449, 130208625], [0, 0, -35945672160, 53991292176, 91657009272, -216446936052, 126223300860, -21634704786, 260417250], [0, 0, 0, 1210366800, 11207504040, -44844090292, 48718911196, -14422300674, 260417250], [0, 0, 0, 0, 0, -605785212, 3322238788, -3604948281, 130208625], [0, 0, 0, 0, 0, 0, 0, 250755, 26041725]], [[-64424509440, 112742891520, 8053063680, -104689827840, 40265318400, 20132659200, -14092861440, 2013265920], [0, 48318382080, 0, -144955146240, 88583700480, 44291850240, -44291850240, 8053063680], [0, 0, -8053063680, -40265318400, 56371445760, 28185722880, -48318382080, 12079595520], [0, 0, 0, 0, 8053063680, 4026531840, -20132659200, 8053063680], [0, 0, 0, 0, 0, 0, -2013265920, 2013265920]]⟩
def n00116_reduction : Reduction := ⟨rawSub n00115_pair n00056_pair, n00116_pair, [[-8388608, 8388608]], 1⟩
theorem n00116_checked : checkReduction n00116_reduction = true := by decide
def n00117_expression (x t : ℝ) : ℝ := n00040_expression x t * n00116_expression x t
def n00117_pair : RationalPair := ⟨[[0, -55174951680, 263011913280, -387425365024, 151077934960, 122110929192, -128576111104, 38752194832, -3605951301, 26041725], [0, 0, 99478820160, -307876779264, 201636633136, 202560434424, -300784742076, 119578823284, -14423554449, 130208625], [0, 0, 0, -35945672160, 53991292176, 91657009272, -216446936052, 126223300860, -21634704786, 260417250], [0, 0, 0, 0, 1210366800, 11207504040, -44844090292, 48718911196, -14422300674, 260417250], [0, 0, 0, 0, 0, 0, -605785212, 3322238788, -3604948281, 130208625], [0, 0, 0, 0, 0, 0, 0, 0, 250755, 26041725]], [[-64424509440, 80530636800, 80530636800, -120795955200, -24159191040, 60397977600, -4026531840, -10066329600, 2013265920], [0, 16106127360, 80530636800, -144955146240, -48318382080, 132875550720, -12079595520, -32212254720, 8053063680], [0, 0, 0, -24159191040, -24159191040, 84557168640, -12079595520, -36238786560, 12079595520], [0, 0, 0, 0, 0, 12079595520, -4026531840, -16106127360, 8053063680], [0, 0, 0, 0, 0, 0, 0, -2013265920, 2013265920]]⟩
def n00117_reduction : Reduction := ⟨rawMul n00040_pair n00116_pair, n00117_pair, [[-2, 1], [0, 1]], 1⟩
theorem n00117_checked : checkReduction n00117_reduction = true := by decide
def n00118_expression (x t : ℝ) : ℝ := n00106_expression x t + n00117_expression x t
def n00118_pair : RationalPair := ⟨[[524385792, -77690491008, 267821445312, -353652056032, 143077058224, 105224274696, -124444576288, 41566637248, -4305465141, 26041725], [0, -131096448, 104288352192, -273906825600, 185634879664, 168688803096, -288390137628, 128038537588, -17221609809, 130208625], [0, 0, 0, -35749027488, 45990415440, 74573710104, -204052331604, 134715789276, -25831787826, 260417250], [0, 0, 0, 0, 1210366800, 11109181704, -40712555476, 51582514780, -17220356034, 260417250], [0, 0, 0, 0, 0, 0, -605785212, 3338625844, -4304462121, 130208625], [0, 0, 0, 0, 0, 0, 0, 0, 250755, 26041725]], [[-64424509440, 80530636800, 80530636800, -120795955200, -24159191040, 60397977600, -4026531840, -10066329600, 2013265920], [0, 16106127360, 80530636800, -144955146240, -48318382080, 132875550720, -12079595520, -32212254720, 8053063680], [0, 0, 0, -24159191040, -24159191040, 84557168640, -12079595520, -36238786560, 12079595520], [0, 0, 0, 0, 0, 12079595520, -4026531840, -16106127360, 8053063680], [0, 0, 0, 0, 0, 0, 0, -2013265920, 2013265920]]⟩
def n00118_reduction : Reduction := ⟨rawAdd n00106_pair n00117_pair, n00118_pair, [[-41943040, 41943040]], 1⟩
theorem n00118_checked : checkReduction n00118_reduction = true := by decide
def n00119_expression (x t : ℝ) : ℝ := n00041_expression x t + n00083_expression x t
def n00119_pair : RationalPair := ⟨[[-403455600, 722374056, -158991152, -333476056, 173465167, -8680575], [0, 0, 201928404, -340420516, 173381582, -17361150], [0, 0, 0, 0, -83585, -8680575]], [[-402653184, 402653184, 402653184, -402653184, -100663296, 100663296], [0, 0, 402653184, -402653184, -201326592, 201326592], [0, 0, 0, 0, -100663296, 100663296]]⟩
def n00119_reduction : Reduction := ⟨rawAdd n00041_pair n00083_pair, n00119_pair, [[-2, 0, 1], [0, 0, 1]], 1⟩
theorem n00119_checked : checkReduction n00119_reduction = true := by decide
def n00120_expression (x t : ℝ) : ℝ := (10 : ℝ)/(1 : ℝ)
def n00120_pair : RationalPair := ⟨[[10]], [[1]]⟩
def n00121_expression (x t : ℝ) : ℝ := n00120_expression x t * n00066_expression x t
def n00121_pair : RationalPair := ⟨[[-136625, -292175]], [[-2097152, 2097152]]⟩
def n00121_reduction : Reduction := ⟨rawMul n00120_pair n00066_pair, n00121_pair, [[2]], 1⟩
theorem n00121_checked : checkReduction n00121_reduction = true := by decide
def n00122_expression (x t : ℝ) : ℝ := n00051_expression x t + n00056_expression x t
def n00122_pair : RationalPair := ⟨[[-19252823, 17611095]], [[-16777216, 16777216]]⟩
def n00122_reduction : Reduction := ⟨rawAdd n00051_pair n00056_pair, n00122_pair, [[-8388608, 8388608]], 1⟩
theorem n00122_checked : checkReduction n00122_reduction = true := by decide
def n00123_expression (x t : ℝ) : ℝ := n00040_expression x t * n00122_expression x t
def n00123_pair : RationalPair := ⟨[[0, 38505646, -54475013, 17611095], [0, 0, -19252823, 17611095]], [[33554432, -33554432, -16777216, 16777216], [0, 0, -16777216, 16777216]]⟩
def n00123_reduction : Reduction := ⟨rawMul n00040_pair n00122_pair, n00123_pair, [[1]], 1⟩
theorem n00123_checked : checkReduction n00123_reduction = true := by decide
def n00124_expression (x t : ℝ) : ℝ := n00121_expression x t + n00123_expression x t
def n00124_pair : RationalPair := ⟨[[2186000, 43180446, -55568013, 15273695], [0, 0, -20345823, 15273695]], [[33554432, -33554432, -16777216, 16777216], [0, 0, -16777216, 16777216]]⟩
def n00124_reduction : Reduction := ⟨rawAdd n00121_pair n00123_pair, n00124_pair, [[-2097152, 2097152]], 1⟩
theorem n00124_checked : checkReduction n00124_reduction = true := by decide
def n00125_expression (x t : ℝ) : ℝ := n00120_expression x t * n00032_expression x t
def n00125_pair : RationalPair := ⟨[[-765808164597289, 1766623614580494, -561956484375000]], [[152087500000000]]⟩
def n00125_reduction : Reduction := ⟨rawMul n00120_pair n00032_pair, n00125_pair, [[10]], 1⟩
theorem n00125_checked : checkReduction n00125_reduction = true := by decide
def n00126_expression (x t : ℝ) : ℝ := n00002_expression x t + n00125_expression x t
def n00126_pair : RationalPair := ⟨[[-644138164597289, 1766623614580494, -561956484375000]], [[152087500000000]]⟩
def n00126_reduction : Reduction := ⟨rawAdd n00002_pair n00125_pair, n00126_pair, [[5]], 1⟩
theorem n00126_checked : checkReduction n00126_reduction = true := by decide
def n00127_expression (x t : ℝ) : ℝ := n00087_expression x t * n00126_expression x t
def n00127_pair : RationalPair := ⟨[[-24434092997668963637, 1110030835905219105707, -2881913150113188882030, 909945227541796875000]], [[-1275802419200000000000, 1275802419200000000000]]⟩
def n00127_reduction : Reduction := ⟨rawMul n00087_pair n00126_pair, n00127_pair, [[1]], 1⟩
theorem n00127_checked : checkReduction n00127_reduction = true := by decide
def n00128_expression (x t : ℝ) : ℝ := n00124_expression x t + n00127_expression x t
def n00128_pair : RationalPair := ⟨[[215099823495337927274, 1063541368702061788586, 1513792118659958800423, 451609424977875355707, -2881913150113188882030, 909945227541796875000], [0, 0, -1571606770753918963637, 2271499880061469105707, -2881913150113188882030, 909945227541796875000]], [[2551604838400000000000, -2551604838400000000000, -1275802419200000000000, 1275802419200000000000], [0, 0, -1275802419200000000000, 1275802419200000000000]]⟩
def n00128_reduction : Reduction := ⟨rawAdd n00124_pair n00127_pair, n00128_pair, [[-16777216, 16777216]], 1⟩
theorem n00128_checked : checkReduction n00128_reduction = true := by decide
def n00129_expression (x t : ℝ) : ℝ := n00040_expression x t * n00119_expression x t
def n00129_pair : RationalPair := ⟨[[0, 806911200, -1848203712, 1040356360, 507960960, -680406390, 190826317, -8680575], [0, 0, -403455600, 318517248, 723778284, -1020659736, 381569049, -26041725], [0, 0, 0, 0, 201928404, -340253346, 190659147, -26041725], [0, 0, 0, 0, 0, 0, -83585, -8680575]], [[805306368, -805306368, -1207959552, 1207959552, 603979776, -603979776, -100663296, 100663296], [0, 0, -1207959552, 1207959552, 1207959552, -1207959552, -301989888, 301989888], [0, 0, 0, 0, 603979776, -603979776, -301989888, 301989888], [0, 0, 0, 0, 0, 0, -100663296, 100663296]]⟩
def n00129_reduction : Reduction := ⟨rawMul n00040_pair n00119_pair, n00129_pair, [[1]], 1⟩
theorem n00129_checked : checkReduction n00129_reduction = true := by decide
def n00130_expression (x t : ℝ) : ℝ := n00077_expression x t * n00126_expression x t
def n00130_pair : RationalPair := ⟨[[0, -30918631900669872, 100257249450198648, -70017016164529145, 15253579239580494, -561956484375000], [0, -30918631900669872, 115716565400533584, -113704259243655579, 32273782093741482, -1685869453125000], [0, 0, 15459315950334936, -44331381243723723, 18786826468741482, -1685869453125000], [0, 0, 0, -644138164597289, 1766623614580494, -561956484375000]], [[14600400000000000, -10950300000000000, 1825050000000000], [0, -10950300000000000, 3650100000000000], [0, 0, 1825050000000000]]⟩
def n00130_reduction : Reduction := ⟨rawMul n00077_pair n00126_pair, n00130_pair, [[1]], 1⟩
theorem n00130_checked : checkReduction n00130_reduction = true := by decide
def n00131_expression (x t : ℝ) : ℝ := n00017_expression x t + n00130_expression x t
def n00131_pair : RationalPair := ⟨[[29200800000000000, -52819231900669872, 103907349450198648, -70017016164529145, 15253579239580494, -561956484375000], [0, -52819231900669872, 123016765400533584, -113704259243655579, 32273782093741482, -1685869453125000], [0, 0, 19109415950334936, -44331381243723723, 18786826468741482, -1685869453125000], [0, 0, 0, -644138164597289, 1766623614580494, -561956484375000]], [[14600400000000000, -10950300000000000, 1825050000000000], [0, -10950300000000000, 3650100000000000], [0, 0, 1825050000000000]]⟩
def n00131_reduction : Reduction := ⟨rawAdd n00017_pair n00130_pair, n00131_pair, [[1]], 1⟩
theorem n00131_checked : checkReduction n00131_reduction = true := by decide
def n00132_expression (x t : ℝ) : ℝ := n00129_expression x t * n00131_expression x t
def n00132_pair : RationalPair := ⟨[[0, -11781226284480000000000000, 42404115232468703609683200, -84719913631052650201669632, 101968753649017024795910832, -50573696326676250760706184, -21688789246995766569532208, 39000678511959994291493648, -18044846277649536726306479, 3441151662286971609510873, -229889714016463712329050, 4878105409353515625000], [0, 0, 21310214898023903609683200, -81890574738099802006511232, 122530275839910216194217360, -53077196848010312951229816, -67289014419262273115079780, 99214181751373966354418420, -50535798216004249250049979, 11199159583241594901913677, -934847193716245436645250, 24390527046767578125000], [0, 0, 0, -7709800877891951804841600, 21024187128141689390174928, 177170453909933484797928, -59317442959863997838624172, 81813420791945018425263036, -47925892151963712027909998, 12956012602416279450045978, -1440491634700344623290500, 48781054093535156250000], [0, 0, 0, 0, 259881149680497991868400, 2680670975243995675321560, -13847287579130111163573356, 22174329625327289953245404, -16423720926224335346494910, 6084596930668985033764602, -1011288881968198373290500, 48781054093535156250000], [0, 0, 0, 0, 0, 0, -130069791532619870496756, 574412072796243590907140, -988726872326847977927347, 892036075620653277491613, -291043064618026061645250, 24390527046767578125000], [0, 0, 0, 0, 0, 0, 0, 0, 53840288487864401065, 5443826413324401370185, -15288337650390587329050, 4878105409353515625000]], [[-5878897547673600000000000, 7348621934592000000000000, 7348621934592000000000000, -11022932901888000000000000, -2204586580377600000000000, 5511466450944000000000000, -367431096729600000000000, -918577741824000000000000, 183715548364800000000000], [0, 1469724386918400000000000, 7348621934592000000000000, -13227519482265600000000000, -4409173160755200000000000, 12125226192076800000000000, -1102293290188800000000000, -2939448773836800000000000, 734862193459200000000000], [0, 0, 0, -2204586580377600000000000, -2204586580377600000000000, 7716053031321600000000000, -1102293290188800000000000, -3306879870566400000000000, 1102293290188800000000000], [0, 0, 0, 0, 0, 1102293290188800000000000, -367431096729600000000000, -1469724386918400000000000, 734862193459200000000000], [0, 0, 0, 0, 0, 0, 0, -183715548364800000000000, 183715548364800000000000]]⟩
def n00132_reduction : Reduction := ⟨rawMul n00129_pair n00131_pair, n00132_pair, [[-2, 1], [0, 1]], 1⟩
theorem n00132_checked : checkReduction n00132_reduction = true := by decide
def n00133_expression (x t : ℝ) : ℝ := n00128_expression x t - n00132_expression x t
def n00133_pair : RationalPair := ⟨[[-495589993333258584439296, 9454724469323764285207680, -44783702452155602511192960, 86877851591407997365956672, -92317419007682138566987248, 46404138948966583586464104, 14594068468156758808960592, -35286323696938719633070688, 19245731558247472573577567, -4380275606967345808523193, 360921826782482462329050, -4878105409353515625000], [0, 123897498333314646109824, -16581043076501228142798720, 78826342091654977201633536, -115928036594182655288961552, 51963843379897464587328024, 52849584387716205609660612, -91442199387683156709913268, 54465550040526908343085051, -14431526910899016697962957, 1458975644780320436645250, -24390527046767578125000], [0, 0, 0, 6680657879604379835676864, -24073282523749014713842704, 3815253330224471310124728, 51722745233288886109500684, -77638831884615787442285340, 52509835941944074223388686, -17018370917306299644119898, 2226684311296457123290500, -48781054093535156250000], [0, 0, 0, 0, -259881149680497991868400, -1744451100706409690739192, 13597299105262059179297420, -22283679641656158287113628, 18605894155008825847431422, -8268707356198256829813882, 1535417333032273373290500, -48781054093535156250000], [0, 0, 0, 0, 0, 0, 130069791532619870496756, -800723447784807921670868, 1315822855055699529149155, -1307031569236952476503933, 422075177384044811645250, -24390527046767578125000], [0, 0, 0, 0, 0, 0, 0, 0, -53840288487864401065, -5443826413324401370185, 15288337650390587329050, -4878105409353515625000]], [[-5878897547673600000000000, 7348621934592000000000000, 7348621934592000000000000, -11022932901888000000000000, -2204586580377600000000000, 5511466450944000000000000, -367431096729600000000000, -918577741824000000000000, 183715548364800000000000], [0, 1469724386918400000000000, 7348621934592000000000000, -13227519482265600000000000, -4409173160755200000000000, 12125226192076800000000000, -1102293290188800000000000, -2939448773836800000000000, 734862193459200000000000], [0, 0, 0, -2204586580377600000000000, -2204586580377600000000000, 7716053031321600000000000, -1102293290188800000000000, -3306879870566400000000000, 1102293290188800000000000], [0, 0, 0, 0, 0, 1102293290188800000000000, -367431096729600000000000, -1469724386918400000000000, 734862193459200000000000], [0, 0, 0, 0, 0, 0, 0, -183715548364800000000000, 183715548364800000000000]]⟩
def n00133_reduction : Reduction := ⟨rawSub n00128_pair n00132_pair, n00133_pair, [[2551604838400000000000, -2551604838400000000000, -1275802419200000000000, 1275802419200000000000], [0, 0, -1275802419200000000000, 1275802419200000000000]], 1⟩
theorem n00133_checked : checkReduction n00133_reduction = true := by decide
def n00134_expression (x t : ℝ) : ℝ := n00084_expression x t + n00125_expression x t
def n00134_pair : RationalPair := ⟨[[-628929414597289, 1766623614580494, -561956484375000]], [[152087500000000]]⟩
def n00134_reduction : Reduction := ⟨rawAdd n00084_pair n00125_pair, n00134_pair, [[10]], 1⟩
theorem n00134_checked : checkReduction n00134_reduction = true := by decide
def n00135_expression (x t : ℝ) : ℝ := n00087_expression x t * n00134_expression x t
def n00135_pair : RationalPair := ⟨[[-23857179483918963637, 1085404143511469105707, -2881913150113188882030, 909945227541796875000]], [[-1275802419200000000000, 1275802419200000000000]]⟩
def n00135_reduction : Reduction := ⟨rawMul n00087_pair n00134_pair, n00135_pair, [[1]], 1⟩
theorem n00135_checked : checkReduction n00135_reduction = true := by decide
def n00136_expression (x t : ℝ) : ℝ := n00124_expression x t + n00135_expression x t
def n00136_pair : RationalPair := ⟨[[213945996467837927274, 1112794753489561788586, 1514369032173708800423, 426982732584125355707, -2881913150113188882030, 909945227541796875000], [0, 0, -1571029857240168963637, 2246873187667719105707, -2881913150113188882030, 909945227541796875000]], [[2551604838400000000000, -2551604838400000000000, -1275802419200000000000, 1275802419200000000000], [0, 0, -1275802419200000000000, 1275802419200000000000]]⟩
def n00136_reduction : Reduction := ⟨rawAdd n00124_pair n00135_pair, n00136_pair, [[-16777216, 16777216]], 1⟩
theorem n00136_checked : checkReduction n00136_reduction = true := by decide
def n00137_expression (x t : ℝ) : ℝ := n00077_expression x t * n00134_expression x t
def n00137_pair : RationalPair := ⟨[[0, -30188611900669872, 99892239450198648, -70001807414529145, 15253579239580494, -561956484375000], [0, -30188611900669872, 114986545400533584, -113658632993655579, 32273782093741482, -1685869453125000], [0, 0, 15094305950334936, -44285754993723723, 18786826468741482, -1685869453125000], [0, 0, 0, -628929414597289, 1766623614580494, -561956484375000]], [[14600400000000000, -10950300000000000, 1825050000000000], [0, -10950300000000000, 3650100000000000], [0, 0, 1825050000000000]]⟩
def n00137_reduction : Reduction := ⟨rawMul n00077_pair n00134_pair, n00137_pair, [[1]], 1⟩
theorem n00137_checked : checkReduction n00137_reduction = true := by decide
def n00138_expression (x t : ℝ) : ℝ := n00017_expression x t + n00137_expression x t
def n00138_pair : RationalPair := ⟨[[29200800000000000, -52089211900669872, 103542339450198648, -70001807414529145, 15253579239580494, -561956484375000], [0, -52089211900669872, 122286745400533584, -113658632993655579, 32273782093741482, -1685869453125000], [0, 0, 18744405950334936, -44285754993723723, 18786826468741482, -1685869453125000], [0, 0, 0, -628929414597289, 1766623614580494, -561956484375000]], [[14600400000000000, -10950300000000000, 1825050000000000], [0, -10950300000000000, 3650100000000000], [0, 0, 1825050000000000]]⟩
def n00138_reduction : Reduction := ⟨rawAdd n00017_pair n00137_pair, n00138_pair, [[1]], 1⟩
theorem n00138_checked : checkReduction n00138_reduction = true := by decide
def n00139_expression (x t : ℝ) : ℝ := n00129_expression x t * n00138_expression x t
def n00139_pair : RationalPair := ⟨[[0, -11781226284480000000000000, 42109584575356703609683200, -84045300794135530201669632, 101582877118696924795910832, -50748120750261660760706184, -21442852167264846569532208, 38925953244025134291493648, -18039039592610175476306479, 3441019641591940359510873, -229889714016463712329050, 4878105409353515625000], [0, 0, 21015684240911903609683200, -81068696572626682006511232, 122015865218184636194217360, -53493834770190182951229816, -66672291364045618115079780, 98984859086407521354418420, -50512572747070173000049979, 11198499479766438651913677, -934847193716245436645250, 24390527046767578125000], [0, 0, 0, -7562535549335951804841600, 20889516981379709390174928, -127762525004376515202072, -58818737010009112838624172, 81573804404654843425263036, -47891057126621019527909998, 12954692395465966950045978, -1440491634700344623290500, 48781054093535156250000], [0, 0, 0, 0, 253745094323997991868400, 2617951494924145675321560, -13716296526146626163573356, 22084163773906834953245404, -16400501813407102846494910, 6083276723718672533764602, -1011288881968198373290500, 48781054093535156250000], [0, 0, 0, 0, 0, 0, -126998712918284870496756, 569265211634378590907140, -982925272180961727927347, 891375972145497027491613, -291043064618026061645250, 24390527046767578125000], [0, 0, 0, 0, 0, 0, 0, 0, 52569065119114401065, 5311805718293151370185, -15288337650390587329050, 4878105409353515625000]], [[-5878897547673600000000000, 7348621934592000000000000, 7348621934592000000000000, -11022932901888000000000000, -2204586580377600000000000, 5511466450944000000000000, -367431096729600000000000, -918577741824000000000000, 183715548364800000000000], [0, 1469724386918400000000000, 7348621934592000000000000, -13227519482265600000000000, -4409173160755200000000000, 12125226192076800000000000, -1102293290188800000000000, -2939448773836800000000000, 734862193459200000000000], [0, 0, 0, -2204586580377600000000000, -2204586580377600000000000, 7716053031321600000000000, -1102293290188800000000000, -3306879870566400000000000, 1102293290188800000000000], [0, 0, 0, 0, 0, 1102293290188800000000000, -367431096729600000000000, -1469724386918400000000000, 734862193459200000000000], [0, 0, 0, 0, 0, 0, 0, -183715548364800000000000, 183715548364800000000000]]⟩
def n00139_reduction : Reduction := ⟨rawMul n00129_pair n00138_pair, n00139_pair, [[-2, 1], [0, 1]], 1⟩
theorem n00139_checked : checkReduction n00139_reduction = true := by decide
def n00140_expression (x t : ℝ) : ℝ := n00136_expression x t - n00139_expression x t
def n00140_pair : RationalPair := ⟨[[-492931575861898584439296, 9340580066405524285207680, -44464789471613042511192960, 86374455358868237365956672, -91972103588714918566987248, 46492955070363313586464104, 14369076548470118808960592, -35197330378639079633070688, 19236378629503411323577567, -4380143586272314558523193, 360921826782482462329050, -4878105409353515625000], [0, 123232893965474646109824, -16262130095958668142798720, 78176677437110977201633536, -115494748195162835288961552, 52208766244424094587328024, 52295696812632390609660612, -91169989496076391709913268, 54428139596774032093085051, -14430866807423860447962957, 1458975644780320436645250, -24390527046767578125000], [0, 0, 0, 6534389457600139835676864, -23979173488339914713842704, 4033581100398341310124728, 51286874763566841109500684, -77356162119593332442285340, 52453723454373181723388686, -17017050710355987144119898, 2226684311296457123290500, -48781054093535156250000], [0, 0, 0, 0, -253745094323997991868400, -1682230073662439690739192, 13487253212322854179297420, -22178996513232983287113628, 18568490067372793347431422, -8267387149247944329813882, 1535417333032273373290500, -48781054093535156250000], [0, 0, 0, 0, 0, 0, 126998712918284870496756, -795493511076962921670868, 1306475011205113279149155, -1306371465761796226503933, 422075177384044811645250, -24390527046767578125000], [0, 0, 0, 0, 0, 0, 0, 0, -52569065119114401065, -5311805718293151370185, 15288337650390587329050, -4878105409353515625000]], [[-5878897547673600000000000, 7348621934592000000000000, 7348621934592000000000000, -11022932901888000000000000, -2204586580377600000000000, 5511466450944000000000000, -367431096729600000000000, -918577741824000000000000, 183715548364800000000000], [0, 1469724386918400000000000, 7348621934592000000000000, -13227519482265600000000000, -4409173160755200000000000, 12125226192076800000000000, -1102293290188800000000000, -2939448773836800000000000, 734862193459200000000000], [0, 0, 0, -2204586580377600000000000, -2204586580377600000000000, 7716053031321600000000000, -1102293290188800000000000, -3306879870566400000000000, 1102293290188800000000000], [0, 0, 0, 0, 0, 1102293290188800000000000, -367431096729600000000000, -1469724386918400000000000, 734862193459200000000000], [0, 0, 0, 0, 0, 0, 0, -183715548364800000000000, 183715548364800000000000]]⟩
def n00140_reduction : Reduction := ⟨rawSub n00136_pair n00139_pair, n00140_pair, [[2551604838400000000000, -2551604838400000000000, -1275802419200000000000, 1275802419200000000000], [0, 0, -1275802419200000000000, 1275802419200000000000]], 1⟩
theorem n00140_checked : checkReduction n00140_reduction = true := by decide
def divisorExpression (i : Fin 17) (x t : ℝ) : ℝ :=
  match i.val with
  | 0 => n00006_expression x t
  | 1 => n00008_expression x t
  | 2 => n00010_expression x t
  | 3 => n00012_expression x t
  | 4 => n00015_expression x t
  | 5 => n00017_expression x t
  | 6 => n00017_expression x t
  | 7 => n00017_expression x t
  | 8 => n00039_expression x t
  | 9 => n00043_expression x t
  | 10 => n00050_expression x t
  | 11 => n00050_expression x t
  | 12 => n00050_expression x t
  | 13 => n00050_expression x t
  | 14 => n00076_expression x t
  | 15 => n00017_expression x t
  | 16 => n00070_expression x t
  | _ => 1
def DivisorsNonzero (x t : ℝ) : Prop := ∀ i : Fin 17, divisorExpression i x t ≠ 0
theorem n00000_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00000_pair.NonzeroDenominator x t ∧ n00000_pair.value x t = n00000_expression x t := by
  simpa [n00000_pair, n00000_expression, rationalX, Polynomial2.X, Polynomial2.const] using rationalX_sound x t
theorem n00001_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00001_pair.NonzeroDenominator x t ∧ n00001_pair.value x t = n00001_expression x t := by
  simpa [n00001_pair, n00001_expression, rationalT, Polynomial2.Y, Polynomial2.const] using rationalT_sound x t
theorem n00002_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00002_pair.NonzeroDenominator x t ∧ n00002_pair.value x t = n00002_expression x t := by
  simpa [n00002_pair, n00002_expression, rationalConst, Polynomial2.const] using rationalConst_sound 4 5 x t (by decide)
theorem n00003_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00003_pair.NonzeroDenominator x t ∧ n00003_pair.value x t = n00003_expression x t := by
  simpa [n00003_pair, n00003_expression, rationalConst, Polynomial2.const] using rationalConst_sound 13 10 x t (by decide)
theorem n00004_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00004_pair.NonzeroDenominator x t ∧ n00004_pair.value x t = n00004_expression x t := by
  simpa [n00004_pair, n00004_expression, rationalConst, Polynomial2.const] using rationalConst_sound 269 256 x t (by decide)
theorem n00005_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00005_pair.NonzeroDenominator x t ∧ n00005_pair.value x t = n00005_expression x t := by
  simpa [n00005_pair, n00005_expression, rationalConst, Polynomial2.const] using rationalConst_sound 1 1 x t (by decide)
theorem n00006_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00006_pair.NonzeroDenominator x t ∧ n00006_pair.value x t = n00006_expression x t := by
  have ha := n00005_sound x t hnz
  have hb := n00000_sound x t hnz
  have hraw := rawSub_sound n00005_pair n00000_pair x t ha.1 hb.1
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
  have hb := n00007_sound x t hnz
  have hraw := rawAdd_sound n00005_pair n00007_pair x t ha.1 hb.1
  have hred := checkReduction_sound n00008_checked x t hraw.1
  dsimp only [n00008_reduction] at hred
  refine ⟨hred.1, ?_⟩
  rw [← hred.2, hraw.2]
  simp only [n00008_expression, ha.2, hb.2]
theorem n00009_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00009_pair.NonzeroDenominator x t ∧ n00009_pair.value x t = n00009_expression x t := by
  have ha := n00007_sound x t hnz
  have hb := n00008_sound x t hnz
  have hd : n00008_pair.value x t ≠ 0 := by
    rw [hb.2]
    simpa only [divisorExpression] using hnz ⟨1, by decide⟩
  have hraw := rawDiv_sound n00007_pair n00008_pair x t ha.1 hb.1 hd
  have hred := checkReduction_sound n00009_checked x t hraw.1
  dsimp only [n00009_reduction] at hred
  refine ⟨hred.1, ?_⟩
  rw [← hred.2, hraw.2]
  simp only [n00009_expression, ha.2, hb.2]
theorem n00010_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00010_pair.NonzeroDenominator x t ∧ n00010_pair.value x t = n00010_expression x t := by
  have ha := n00005_sound x t hnz
  have hb := n00002_sound x t hnz
  have hraw := rawAdd_sound n00005_pair n00002_pair x t ha.1 hb.1
  have hred := checkReduction_sound n00010_checked x t hraw.1
  dsimp only [n00010_reduction] at hred
  refine ⟨hred.1, ?_⟩
  rw [← hred.2, hraw.2]
  simp only [n00010_expression, ha.2, hb.2]
theorem n00011_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00011_pair.NonzeroDenominator x t ∧ n00011_pair.value x t = n00011_expression x t := by
  have ha := n00002_sound x t hnz
  have hb := n00010_sound x t hnz
  have hd : n00010_pair.value x t ≠ 0 := by
    rw [hb.2]
    simpa only [divisorExpression] using hnz ⟨2, by decide⟩
  have hraw := rawDiv_sound n00002_pair n00010_pair x t ha.1 hb.1 hd
  have hred := checkReduction_sound n00011_checked x t hraw.1
  dsimp only [n00011_reduction] at hred
  refine ⟨hred.1, ?_⟩
  rw [← hred.2, hraw.2]
  simp only [n00011_expression, ha.2, hb.2]
theorem n00012_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00012_pair.NonzeroDenominator x t ∧ n00012_pair.value x t = n00012_expression x t := by
  have ha := n00005_sound x t hnz
  have hb := n00003_sound x t hnz
  have hraw := rawAdd_sound n00005_pair n00003_pair x t ha.1 hb.1
  have hred := checkReduction_sound n00012_checked x t hraw.1
  dsimp only [n00012_reduction] at hred
  refine ⟨hred.1, ?_⟩
  rw [← hred.2, hraw.2]
  simp only [n00012_expression, ha.2, hb.2]
theorem n00013_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00013_pair.NonzeroDenominator x t ∧ n00013_pair.value x t = n00013_expression x t := by
  have ha := n00003_sound x t hnz
  have hb := n00012_sound x t hnz
  have hd : n00012_pair.value x t ≠ 0 := by
    rw [hb.2]
    simpa only [divisorExpression] using hnz ⟨3, by decide⟩
  have hraw := rawDiv_sound n00003_pair n00012_pair x t ha.1 hb.1 hd
  have hred := checkReduction_sound n00013_checked x t hraw.1
  dsimp only [n00013_reduction] at hred
  refine ⟨hred.1, ?_⟩
  rw [← hred.2, hraw.2]
  simp only [n00013_expression, ha.2, hb.2]
theorem n00014_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00014_pair.NonzeroDenominator x t ∧ n00014_pair.value x t = n00014_expression x t := by
  have ha := n00009_sound x t hnz
  have hb := n00011_sound x t hnz
  have hraw := rawSub_sound n00009_pair n00011_pair x t ha.1 hb.1
  have hred := checkReduction_sound n00014_checked x t hraw.1
  dsimp only [n00014_reduction] at hred
  refine ⟨hred.1, ?_⟩
  rw [← hred.2, hraw.2]
  simp only [n00014_expression, ha.2, hb.2]
theorem n00015_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00015_pair.NonzeroDenominator x t ∧ n00015_pair.value x t = n00015_expression x t := by
  have ha := n00013_sound x t hnz
  have hb := n00011_sound x t hnz
  have hraw := rawSub_sound n00013_pair n00011_pair x t ha.1 hb.1
  have hred := checkReduction_sound n00015_checked x t hraw.1
  dsimp only [n00015_reduction] at hred
  refine ⟨hred.1, ?_⟩
  rw [← hred.2, hraw.2]
  simp only [n00015_expression, ha.2, hb.2]
theorem n00016_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00016_pair.NonzeroDenominator x t ∧ n00016_pair.value x t = n00016_expression x t := by
  have ha := n00014_sound x t hnz
  have hb := n00015_sound x t hnz
  have hd : n00015_pair.value x t ≠ 0 := by
    rw [hb.2]
    simpa only [divisorExpression] using hnz ⟨4, by decide⟩
  have hraw := rawDiv_sound n00014_pair n00015_pair x t ha.1 hb.1 hd
  have hred := checkReduction_sound n00016_checked x t hraw.1
  dsimp only [n00016_reduction] at hred
  refine ⟨hred.1, ?_⟩
  rw [← hred.2, hraw.2]
  simp only [n00016_expression, ha.2, hb.2]
theorem n00017_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00017_pair.NonzeroDenominator x t ∧ n00017_pair.value x t = n00017_expression x t := by
  simpa [n00017_pair, n00017_expression, rationalConst, Polynomial2.const] using rationalConst_sound 2 1 x t (by decide)
theorem n00018_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00018_pair.NonzeroDenominator x t ∧ n00018_pair.value x t = n00018_expression x t := by
  have ha := n00013_sound x t hnz
  have hb := n00017_sound x t hnz
  have hd : n00017_pair.value x t ≠ 0 := by
    rw [hb.2]
    simpa only [divisorExpression] using hnz ⟨5, by decide⟩
  have hraw := rawDiv_sound n00013_pair n00017_pair x t ha.1 hb.1 hd
  have hred := checkReduction_sound n00018_checked x t hraw.1
  dsimp only [n00018_reduction] at hred
  refine ⟨hred.1, ?_⟩
  rw [← hred.2, hraw.2]
  simp only [n00018_expression, ha.2, hb.2]
theorem n00019_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00019_pair.NonzeroDenominator x t ∧ n00019_pair.value x t = n00019_expression x t := by
  have ha := n00005_sound x t hnz
  have hb := n00018_sound x t hnz
  have hraw := rawSub_sound n00005_pair n00018_pair x t ha.1 hb.1
  have hred := checkReduction_sound n00019_checked x t hraw.1
  dsimp only [n00019_reduction] at hred
  refine ⟨hred.1, ?_⟩
  rw [← hred.2, hraw.2]
  simp only [n00019_expression, ha.2, hb.2]
theorem n00020_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00020_pair.NonzeroDenominator x t ∧ n00020_pair.value x t = n00020_expression x t := by
  have ha := n00013_sound x t hnz
  have hb := n00019_sound x t hnz
  have hraw := rawMul_sound n00013_pair n00019_pair x t ha.1 hb.1
  have hred := checkReduction_sound n00020_checked x t hraw.1
  dsimp only [n00020_reduction] at hred
  refine ⟨hred.1, ?_⟩
  rw [← hred.2, hraw.2]
  simp only [n00020_expression, ha.2, hb.2]
theorem n00021_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00021_pair.NonzeroDenominator x t ∧ n00021_pair.value x t = n00021_expression x t := by
  simpa [n00021_pair, n00021_expression, rationalConst, Polynomial2.const] using rationalConst_sound 729 800 x t (by decide)
theorem n00022_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00022_pair.NonzeroDenominator x t ∧ n00022_pair.value x t = n00022_expression x t := by
  have ha := n00020_sound x t hnz
  have hb := n00021_sound x t hnz
  have hraw := rawMul_sound n00020_pair n00021_pair x t ha.1 hb.1
  have hred := checkReduction_sound n00022_checked x t hraw.1
  dsimp only [n00022_reduction] at hred
  refine ⟨hred.1, ?_⟩
  rw [← hred.2, hraw.2]
  simp only [n00022_expression, ha.2, hb.2]
theorem n00023_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00023_pair.NonzeroDenominator x t ∧ n00023_pair.value x t = n00023_expression x t := by
  have ha := n00022_sound x t hnz
  have hb := n00014_sound x t hnz
  have hraw := rawMul_sound n00022_pair n00014_pair x t ha.1 hb.1
  have hred := checkReduction_sound n00023_checked x t hraw.1
  dsimp only [n00023_reduction] at hred
  refine ⟨hred.1, ?_⟩
  rw [← hred.2, hraw.2]
  simp only [n00023_expression, ha.2, hb.2]
theorem n00024_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00024_pair.NonzeroDenominator x t ∧ n00024_pair.value x t = n00024_expression x t := by
  have ha := n00013_sound x t hnz
  have hb := n00009_sound x t hnz
  have hraw := rawSub_sound n00013_pair n00009_pair x t ha.1 hb.1
  have hred := checkReduction_sound n00024_checked x t hraw.1
  dsimp only [n00024_reduction] at hred
  refine ⟨hred.1, ?_⟩
  rw [← hred.2, hraw.2]
  simp only [n00024_expression, ha.2, hb.2]
theorem n00025_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00025_pair.NonzeroDenominator x t ∧ n00025_pair.value x t = n00025_expression x t := by
  have ha := n00023_sound x t hnz
  have hb := n00024_sound x t hnz
  have hraw := rawMul_sound n00023_pair n00024_pair x t ha.1 hb.1
  have hred := checkReduction_sound n00025_checked x t hraw.1
  dsimp only [n00025_reduction] at hred
  refine ⟨hred.1, ?_⟩
  rw [← hred.2, hraw.2]
  simp only [n00025_expression, ha.2, hb.2]
theorem n00026_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00026_pair.NonzeroDenominator x t ∧ n00026_pair.value x t = n00026_expression x t := by
  have ha := n00005_sound x t hnz
  have hb := n00016_sound x t hnz
  have hraw := rawSub_sound n00005_pair n00016_pair x t ha.1 hb.1
  have hred := checkReduction_sound n00026_checked x t hraw.1
  dsimp only [n00026_reduction] at hred
  refine ⟨hred.1, ?_⟩
  rw [← hred.2, hraw.2]
  simp only [n00026_expression, ha.2, hb.2]
theorem n00027_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00027_pair.NonzeroDenominator x t ∧ n00027_pair.value x t = n00027_expression x t := by
  simpa [n00027_pair, n00027_expression, rationalConst, Polynomial2.const] using rationalConst_sound (-60258643) 1000000000 x t (by decide)
theorem n00028_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00028_pair.NonzeroDenominator x t ∧ n00028_pair.value x t = n00028_expression x t := by
  have ha := n00026_sound x t hnz
  have hb := n00027_sound x t hnz
  have hraw := rawMul_sound n00026_pair n00027_pair x t ha.1 hb.1
  have hred := checkReduction_sound n00028_checked x t hraw.1
  dsimp only [n00028_reduction] at hred
  refine ⟨hred.1, ?_⟩
  rw [← hred.2, hraw.2]
  simp only [n00028_expression, ha.2, hb.2]
theorem n00029_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00029_pair.NonzeroDenominator x t ∧ n00029_pair.value x t = n00029_expression x t := by
  simpa [n00029_pair, n00029_expression, rationalConst, Polynomial2.const] using rationalConst_sound 174865111 5000000000 x t (by decide)
theorem n00030_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00030_pair.NonzeroDenominator x t ∧ n00030_pair.value x t = n00030_expression x t := by
  have ha := n00016_sound x t hnz
  have hb := n00029_sound x t hnz
  have hraw := rawMul_sound n00016_pair n00029_pair x t ha.1 hb.1
  have hred := checkReduction_sound n00030_checked x t hraw.1
  dsimp only [n00030_reduction] at hred
  refine ⟨hred.1, ?_⟩
  rw [← hred.2, hraw.2]
  simp only [n00030_expression, ha.2, hb.2]
theorem n00031_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00031_pair.NonzeroDenominator x t ∧ n00031_pair.value x t = n00031_expression x t := by
  have ha := n00028_sound x t hnz
  have hb := n00030_sound x t hnz
  have hraw := rawAdd_sound n00028_pair n00030_pair x t ha.1 hb.1
  have hred := checkReduction_sound n00031_checked x t hraw.1
  dsimp only [n00031_reduction] at hred
  refine ⟨hred.1, ?_⟩
  rw [← hred.2, hraw.2]
  simp only [n00031_expression, ha.2, hb.2]
theorem n00032_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00032_pair.NonzeroDenominator x t ∧ n00032_pair.value x t = n00032_expression x t := by
  have ha := n00031_sound x t hnz
  have hb := n00025_sound x t hnz
  have hraw := rawAdd_sound n00031_pair n00025_pair x t ha.1 hb.1
  have hred := checkReduction_sound n00032_checked x t hraw.1
  dsimp only [n00032_reduction] at hred
  refine ⟨hred.1, ?_⟩
  rw [← hred.2, hraw.2]
  simp only [n00032_expression, ha.2, hb.2]
theorem n00033_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00033_pair.NonzeroDenominator x t ∧ n00033_pair.value x t = n00033_expression x t := by
  have ha := n00009_sound x t hnz
  have hb := n00017_sound x t hnz
  have hd : n00017_pair.value x t ≠ 0 := by
    rw [hb.2]
    simpa only [divisorExpression] using hnz ⟨6, by decide⟩
  have hraw := rawDiv_sound n00009_pair n00017_pair x t ha.1 hb.1 hd
  have hred := checkReduction_sound n00033_checked x t hraw.1
  dsimp only [n00033_reduction] at hred
  refine ⟨hred.1, ?_⟩
  rw [← hred.2, hraw.2]
  simp only [n00033_expression, ha.2, hb.2]
theorem n00034_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00034_pair.NonzeroDenominator x t ∧ n00034_pair.value x t = n00034_expression x t := by
  have ha := n00009_sound x t hnz
  have hb := n00001_sound x t hnz
  have hraw := rawMul_sound n00009_pair n00001_pair x t ha.1 hb.1
  have hred := checkReduction_sound n00034_checked x t hraw.1
  dsimp only [n00034_reduction] at hred
  refine ⟨hred.1, ?_⟩
  rw [← hred.2, hraw.2]
  simp only [n00034_expression, ha.2, hb.2]
theorem n00035_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00035_pair.NonzeroDenominator x t ∧ n00035_pair.value x t = n00035_expression x t := by
  have ha := n00034_sound x t hnz
  have hb := n00017_sound x t hnz
  have hd : n00017_pair.value x t ≠ 0 := by
    rw [hb.2]
    simpa only [divisorExpression] using hnz ⟨7, by decide⟩
  have hraw := rawDiv_sound n00034_pair n00017_pair x t ha.1 hb.1 hd
  have hred := checkReduction_sound n00035_checked x t hraw.1
  dsimp only [n00035_reduction] at hred
  refine ⟨hred.1, ?_⟩
  rw [← hred.2, hraw.2]
  simp only [n00035_expression, ha.2, hb.2]
theorem n00036_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00036_pair.NonzeroDenominator x t ∧ n00036_pair.value x t = n00036_expression x t := by
  have ha := n00033_sound x t hnz
  have hb := n00035_sound x t hnz
  have hraw := rawAdd_sound n00033_pair n00035_pair x t ha.1 hb.1
  have hred := checkReduction_sound n00036_checked x t hraw.1
  dsimp only [n00036_reduction] at hred
  refine ⟨hred.1, ?_⟩
  rw [← hred.2, hraw.2]
  simp only [n00036_expression, ha.2, hb.2]
theorem n00037_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00037_pair.NonzeroDenominator x t ∧ n00037_pair.value x t = n00037_expression x t := by
  have ha := n00005_sound x t hnz
  have hb := n00036_sound x t hnz
  have hraw := rawSub_sound n00005_pair n00036_pair x t ha.1 hb.1
  have hred := checkReduction_sound n00037_checked x t hraw.1
  dsimp only [n00037_reduction] at hred
  refine ⟨hred.1, ?_⟩
  rw [← hred.2, hraw.2]
  simp only [n00037_expression, ha.2, hb.2]
theorem n00038_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00038_pair.NonzeroDenominator x t ∧ n00038_pair.value x t = n00038_expression x t := by
  have ha := n00007_sound x t hnz
  have hb := n00037_sound x t hnz
  have hraw := rawMul_sound n00007_pair n00037_pair x t ha.1 hb.1
  have hred := checkReduction_sound n00038_checked x t hraw.1
  dsimp only [n00038_reduction] at hred
  refine ⟨hred.1, ?_⟩
  rw [← hred.2, hraw.2]
  simp only [n00038_expression, ha.2, hb.2]
theorem n00039_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00039_pair.NonzeroDenominator x t ∧ n00039_pair.value x t = n00039_expression x t := by
  have ha := n00005_sound x t hnz
  have hb := n00038_sound x t hnz
  have hraw := rawAdd_sound n00005_pair n00038_pair x t ha.1 hb.1
  have hred := checkReduction_sound n00039_checked x t hraw.1
  dsimp only [n00039_reduction] at hred
  refine ⟨hred.1, ?_⟩
  rw [← hred.2, hraw.2]
  simp only [n00039_expression, ha.2, hb.2]
theorem n00040_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00040_pair.NonzeroDenominator x t ∧ n00040_pair.value x t = n00040_expression x t := by
  have ha := n00038_sound x t hnz
  have hb := n00039_sound x t hnz
  have hd : n00039_pair.value x t ≠ 0 := by
    rw [hb.2]
    simpa only [divisorExpression] using hnz ⟨8, by decide⟩
  have hraw := rawDiv_sound n00038_pair n00039_pair x t ha.1 hb.1 hd
  have hred := checkReduction_sound n00040_checked x t hraw.1
  dsimp only [n00040_reduction] at hred
  refine ⟨hred.1, ?_⟩
  rw [← hred.2, hraw.2]
  simp only [n00040_expression, ha.2, hb.2]
theorem n00041_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00041_pair.NonzeroDenominator x t ∧ n00041_pair.value x t = n00041_expression x t := by
  have ha := n00005_sound x t hnz
  have hb := n00040_sound x t hnz
  have hraw := rawSub_sound n00005_pair n00040_pair x t ha.1 hb.1
  have hred := checkReduction_sound n00041_checked x t hraw.1
  dsimp only [n00041_reduction] at hred
  refine ⟨hred.1, ?_⟩
  rw [← hred.2, hraw.2]
  simp only [n00041_expression, ha.2, hb.2]
theorem n00042_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00042_pair.NonzeroDenominator x t ∧ n00042_pair.value x t = n00042_expression x t := by
  have ha := n00007_sound x t hnz
  have hb := n00041_sound x t hnz
  have hraw := rawMul_sound n00007_pair n00041_pair x t ha.1 hb.1
  have hred := checkReduction_sound n00042_checked x t hraw.1
  dsimp only [n00042_reduction] at hred
  refine ⟨hred.1, ?_⟩
  rw [← hred.2, hraw.2]
  simp only [n00042_expression, ha.2, hb.2]
theorem n00043_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00043_pair.NonzeroDenominator x t ∧ n00043_pair.value x t = n00043_expression x t := by
  have ha := n00005_sound x t hnz
  have hb := n00042_sound x t hnz
  have hraw := rawAdd_sound n00005_pair n00042_pair x t ha.1 hb.1
  have hred := checkReduction_sound n00043_checked x t hraw.1
  dsimp only [n00043_reduction] at hred
  refine ⟨hred.1, ?_⟩
  rw [← hred.2, hraw.2]
  simp only [n00043_expression, ha.2, hb.2]
theorem n00044_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00044_pair.NonzeroDenominator x t ∧ n00044_pair.value x t = n00044_expression x t := by
  have ha := n00005_sound x t hnz
  have hb := n00043_sound x t hnz
  have hd : n00043_pair.value x t ≠ 0 := by
    rw [hb.2]
    simpa only [divisorExpression] using hnz ⟨9, by decide⟩
  have hraw := rawDiv_sound n00005_pair n00043_pair x t ha.1 hb.1 hd
  have hred := checkReduction_sound n00044_checked x t hraw.1
  dsimp only [n00044_reduction] at hred
  refine ⟨hred.1, ?_⟩
  rw [← hred.2, hraw.2]
  simp only [n00044_expression, ha.2, hb.2]
theorem n00045_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00045_pair.NonzeroDenominator x t ∧ n00045_pair.value x t = n00045_expression x t := by
  simpa [n00045_pair, n00045_expression, rationalConst, Polynomial2.const] using rationalConst_sound 46809 1 x t (by decide)
theorem n00046_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00046_pair.NonzeroDenominator x t ∧ n00046_pair.value x t = n00046_expression x t := by
  have ha := n00007_sound x t hnz
  have hb := n00004_sound x t hnz
  have hraw := rawSub_sound n00007_pair n00004_pair x t ha.1 hb.1
  have hred := checkReduction_sound n00046_checked x t hraw.1
  dsimp only [n00046_reduction] at hred
  refine ⟨hred.1, ?_⟩
  rw [← hred.2, hraw.2]
  simp only [n00046_expression, ha.2, hb.2]
theorem n00047_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00047_pair.NonzeroDenominator x t ∧ n00047_pair.value x t = n00047_expression x t := by
  simpa [n00047_pair, n00047_expression, rationalConst, Polynomial2.const] using rationalConst_sound 3327 1 x t (by decide)
theorem n00048_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00048_pair.NonzeroDenominator x t ∧ n00048_pair.value x t = n00048_expression x t := by
  have ha := n00047_sound x t hnz
  have hb := n00046_sound x t hnz
  have hraw := rawMul_sound n00047_pair n00046_pair x t ha.1 hb.1
  have hred := checkReduction_sound n00048_checked x t hraw.1
  dsimp only [n00048_reduction] at hred
  refine ⟨hred.1, ?_⟩
  rw [← hred.2, hraw.2]
  simp only [n00048_expression, ha.2, hb.2]
theorem n00049_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00049_pair.NonzeroDenominator x t ∧ n00049_pair.value x t = n00049_expression x t := by
  have ha := n00045_sound x t hnz
  have hb := n00048_sound x t hnz
  have hraw := rawAdd_sound n00045_pair n00048_pair x t ha.1 hb.1
  have hred := checkReduction_sound n00049_checked x t hraw.1
  dsimp only [n00049_reduction] at hred
  refine ⟨hred.1, ?_⟩
  rw [← hred.2, hraw.2]
  simp only [n00049_expression, ha.2, hb.2]
theorem n00050_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00050_pair.NonzeroDenominator x t ∧ n00050_pair.value x t = n00050_expression x t := by
  simpa [n00050_pair, n00050_expression, rationalConst, Polynomial2.const] using rationalConst_sound 65536 1 x t (by decide)
theorem n00051_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00051_pair.NonzeroDenominator x t ∧ n00051_pair.value x t = n00051_expression x t := by
  have ha := n00049_sound x t hnz
  have hb := n00050_sound x t hnz
  have hd : n00050_pair.value x t ≠ 0 := by
    rw [hb.2]
    simpa only [divisorExpression] using hnz ⟨10, by decide⟩
  have hraw := rawDiv_sound n00049_pair n00050_pair x t ha.1 hb.1 hd
  have hred := checkReduction_sound n00051_checked x t hraw.1
  dsimp only [n00051_reduction] at hred
  refine ⟨hred.1, ?_⟩
  rw [← hred.2, hraw.2]
  simp only [n00051_expression, ha.2, hb.2]
theorem n00052_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00052_pair.NonzeroDenominator x t ∧ n00052_pair.value x t = n00052_expression x t := by
  simpa [n00052_pair, n00052_expression, rationalConst, Polynomial2.const] using rationalConst_sound 35136 1 x t (by decide)
theorem n00053_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00053_pair.NonzeroDenominator x t ∧ n00053_pair.value x t = n00053_expression x t := by
  simpa [n00053_pair, n00053_expression, rationalConst, Polynomial2.const] using rationalConst_sound 3086 1 x t (by decide)
theorem n00054_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00054_pair.NonzeroDenominator x t ∧ n00054_pair.value x t = n00054_expression x t := by
  have ha := n00053_sound x t hnz
  have hb := n00046_sound x t hnz
  have hraw := rawMul_sound n00053_pair n00046_pair x t ha.1 hb.1
  have hred := checkReduction_sound n00054_checked x t hraw.1
  dsimp only [n00054_reduction] at hred
  refine ⟨hred.1, ?_⟩
  rw [← hred.2, hraw.2]
  simp only [n00054_expression, ha.2, hb.2]
theorem n00055_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00055_pair.NonzeroDenominator x t ∧ n00055_pair.value x t = n00055_expression x t := by
  have ha := n00052_sound x t hnz
  have hb := n00054_sound x t hnz
  have hraw := rawAdd_sound n00052_pair n00054_pair x t ha.1 hb.1
  have hred := checkReduction_sound n00055_checked x t hraw.1
  dsimp only [n00055_reduction] at hred
  refine ⟨hred.1, ?_⟩
  rw [← hred.2, hraw.2]
  simp only [n00055_expression, ha.2, hb.2]
theorem n00056_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00056_pair.NonzeroDenominator x t ∧ n00056_pair.value x t = n00056_expression x t := by
  have ha := n00055_sound x t hnz
  have hb := n00050_sound x t hnz
  have hd : n00050_pair.value x t ≠ 0 := by
    rw [hb.2]
    simpa only [divisorExpression] using hnz ⟨11, by decide⟩
  have hraw := rawDiv_sound n00055_pair n00050_pair x t ha.1 hb.1 hd
  have hred := checkReduction_sound n00056_checked x t hraw.1
  dsimp only [n00056_reduction] at hred
  refine ⟨hred.1, ?_⟩
  rw [← hred.2, hraw.2]
  simp only [n00056_expression, ha.2, hb.2]
theorem n00057_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00057_pair.NonzeroDenominator x t ∧ n00057_pair.value x t = n00057_expression x t := by
  simpa [n00057_pair, n00057_expression, rationalConst, Polynomial2.const] using rationalConst_sound 14520 1 x t (by decide)
theorem n00058_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00058_pair.NonzeroDenominator x t ∧ n00058_pair.value x t = n00058_expression x t := by
  simpa [n00058_pair, n00058_expression, rationalConst, Polynomial2.const] using rationalConst_sound 13694 1 x t (by decide)
theorem n00059_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00059_pair.NonzeroDenominator x t ∧ n00059_pair.value x t = n00059_expression x t := by
  have ha := n00058_sound x t hnz
  have hb := n00046_sound x t hnz
  have hraw := rawMul_sound n00058_pair n00046_pair x t ha.1 hb.1
  have hred := checkReduction_sound n00059_checked x t hraw.1
  dsimp only [n00059_reduction] at hred
  refine ⟨hred.1, ?_⟩
  rw [← hred.2, hraw.2]
  simp only [n00059_expression, ha.2, hb.2]
theorem n00060_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00060_pair.NonzeroDenominator x t ∧ n00060_pair.value x t = n00060_expression x t := by
  have ha := n00057_sound x t hnz
  have hb := n00059_sound x t hnz
  have hraw := rawAdd_sound n00057_pair n00059_pair x t ha.1 hb.1
  have hred := checkReduction_sound n00060_checked x t hraw.1
  dsimp only [n00060_reduction] at hred
  refine ⟨hred.1, ?_⟩
  rw [← hred.2, hraw.2]
  simp only [n00060_expression, ha.2, hb.2]
theorem n00061_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00061_pair.NonzeroDenominator x t ∧ n00061_pair.value x t = n00061_expression x t := by
  have ha := n00060_sound x t hnz
  have hb := n00050_sound x t hnz
  have hd : n00050_pair.value x t ≠ 0 := by
    rw [hb.2]
    simpa only [divisorExpression] using hnz ⟨12, by decide⟩
  have hraw := rawDiv_sound n00060_pair n00050_pair x t ha.1 hb.1 hd
  have hred := checkReduction_sound n00061_checked x t hraw.1
  dsimp only [n00061_reduction] at hred
  refine ⟨hred.1, ?_⟩
  rw [← hred.2, hraw.2]
  simp only [n00061_expression, ha.2, hb.2]
theorem n00062_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00062_pair.NonzeroDenominator x t ∧ n00062_pair.value x t = n00062_expression x t := by
  simpa [n00062_pair, n00062_expression, rationalConst, Polynomial2.const] using rationalConst_sound 1835 1 x t (by decide)
theorem n00063_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00063_pair.NonzeroDenominator x t ∧ n00063_pair.value x t = n00063_expression x t := by
  simpa [n00063_pair, n00063_expression, rationalConst, Polynomial2.const] using rationalConst_sound 1340 1 x t (by decide)
theorem n00064_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00064_pair.NonzeroDenominator x t ∧ n00064_pair.value x t = n00064_expression x t := by
  have ha := n00063_sound x t hnz
  have hb := n00046_sound x t hnz
  have hraw := rawMul_sound n00063_pair n00046_pair x t ha.1 hb.1
  have hred := checkReduction_sound n00064_checked x t hraw.1
  dsimp only [n00064_reduction] at hred
  refine ⟨hred.1, ?_⟩
  rw [← hred.2, hraw.2]
  simp only [n00064_expression, ha.2, hb.2]
theorem n00065_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00065_pair.NonzeroDenominator x t ∧ n00065_pair.value x t = n00065_expression x t := by
  have ha := n00062_sound x t hnz
  have hb := n00064_sound x t hnz
  have hraw := rawAdd_sound n00062_pair n00064_pair x t ha.1 hb.1
  have hred := checkReduction_sound n00065_checked x t hraw.1
  dsimp only [n00065_reduction] at hred
  refine ⟨hred.1, ?_⟩
  rw [← hred.2, hraw.2]
  simp only [n00065_expression, ha.2, hb.2]
theorem n00066_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00066_pair.NonzeroDenominator x t ∧ n00066_pair.value x t = n00066_expression x t := by
  have ha := n00065_sound x t hnz
  have hb := n00050_sound x t hnz
  have hd : n00050_pair.value x t ≠ 0 := by
    rw [hb.2]
    simpa only [divisorExpression] using hnz ⟨13, by decide⟩
  have hraw := rawDiv_sound n00065_pair n00050_pair x t ha.1 hb.1 hd
  have hred := checkReduction_sound n00066_checked x t hraw.1
  dsimp only [n00066_reduction] at hred
  refine ⟨hred.1, ?_⟩
  rw [← hred.2, hraw.2]
  simp only [n00066_expression, ha.2, hb.2]
theorem n00067_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00067_pair.NonzeroDenominator x t ∧ n00067_pair.value x t = n00067_expression x t := by
  have ha := n00036_sound x t hnz
  have hraw := rawPow_sound n00036_pair 2 x t ha.1
  have hred := checkReduction_sound n00067_checked x t hraw.1
  dsimp only [n00067_reduction] at hred
  refine ⟨hred.1, ?_⟩
  rw [← hred.2, hraw.2]
  simp only [n00067_expression, ha.2]
theorem n00068_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00068_pair.NonzeroDenominator x t ∧ n00068_pair.value x t = n00068_expression x t := by
  have ha := n00017_sound x t hnz
  have hb := n00036_sound x t hnz
  have hraw := rawSub_sound n00017_pair n00036_pair x t ha.1 hb.1
  have hred := checkReduction_sound n00068_checked x t hraw.1
  dsimp only [n00068_reduction] at hred
  refine ⟨hred.1, ?_⟩
  rw [← hred.2, hraw.2]
  simp only [n00068_expression, ha.2, hb.2]
theorem n00069_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00069_pair.NonzeroDenominator x t ∧ n00069_pair.value x t = n00069_expression x t := by
  simpa [n00069_pair, n00069_expression, rationalConst, Polynomial2.const] using rationalConst_sound 6 1 x t (by decide)
theorem n00070_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00070_pair.NonzeroDenominator x t ∧ n00070_pair.value x t = n00070_expression x t := by
  simpa [n00070_pair, n00070_expression, rationalConst, Polynomial2.const] using rationalConst_sound 12 1 x t (by decide)
theorem n00071_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00071_pair.NonzeroDenominator x t ∧ n00071_pair.value x t = n00071_expression x t := by
  have ha := n00070_sound x t hnz
  have hb := n00036_sound x t hnz
  have hraw := rawMul_sound n00070_pair n00036_pair x t ha.1 hb.1
  have hred := checkReduction_sound n00071_checked x t hraw.1
  dsimp only [n00071_reduction] at hred
  refine ⟨hred.1, ?_⟩
  rw [← hred.2, hraw.2]
  simp only [n00071_expression, ha.2, hb.2]
theorem n00072_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00072_pair.NonzeroDenominator x t ∧ n00072_pair.value x t = n00072_expression x t := by
  have ha := n00067_sound x t hnz
  have hb := n00071_sound x t hnz
  have hraw := rawSub_sound n00067_pair n00071_pair x t ha.1 hb.1
  have hred := checkReduction_sound n00072_checked x t hraw.1
  dsimp only [n00072_reduction] at hred
  refine ⟨hred.1, ?_⟩
  rw [← hred.2, hraw.2]
  simp only [n00072_expression, ha.2, hb.2]
theorem n00073_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00073_pair.NonzeroDenominator x t ∧ n00073_pair.value x t = n00073_expression x t := by
  have ha := n00072_sound x t hnz
  have hb := n00070_sound x t hnz
  have hraw := rawAdd_sound n00072_pair n00070_pair x t ha.1 hb.1
  have hred := checkReduction_sound n00073_checked x t hraw.1
  dsimp only [n00073_reduction] at hred
  refine ⟨hred.1, ?_⟩
  rw [← hred.2, hraw.2]
  simp only [n00073_expression, ha.2, hb.2]
theorem n00074_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00074_pair.NonzeroDenominator x t ∧ n00074_pair.value x t = n00074_expression x t := by
  have ha := n00036_sound x t hnz
  have hb := n00073_sound x t hnz
  have hraw := rawMul_sound n00036_pair n00073_pair x t ha.1 hb.1
  have hred := checkReduction_sound n00074_checked x t hraw.1
  dsimp only [n00074_reduction] at hred
  refine ⟨hred.1, ?_⟩
  rw [← hred.2, hraw.2]
  simp only [n00074_expression, ha.2, hb.2]
theorem n00075_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00075_pair.NonzeroDenominator x t ∧ n00075_pair.value x t = n00075_expression x t := by
  have ha := n00069_sound x t hnz
  have hb := n00037_sound x t hnz
  have hraw := rawMul_sound n00069_pair n00037_pair x t ha.1 hb.1
  have hred := checkReduction_sound n00075_checked x t hraw.1
  dsimp only [n00075_reduction] at hred
  refine ⟨hred.1, ?_⟩
  rw [← hred.2, hraw.2]
  simp only [n00075_expression, ha.2, hb.2]
theorem n00076_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00076_pair.NonzeroDenominator x t ∧ n00076_pair.value x t = n00076_expression x t := by
  have ha := n00075_sound x t hnz
  have hb := n00068_sound x t hnz
  have hraw := rawMul_sound n00075_pair n00068_pair x t ha.1 hb.1
  have hred := checkReduction_sound n00076_checked x t hraw.1
  dsimp only [n00076_reduction] at hred
  refine ⟨hred.1, ?_⟩
  rw [← hred.2, hraw.2]
  simp only [n00076_expression, ha.2, hb.2]
theorem n00077_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00077_pair.NonzeroDenominator x t ∧ n00077_pair.value x t = n00077_expression x t := by
  have ha := n00074_sound x t hnz
  have hb := n00076_sound x t hnz
  have hd : n00076_pair.value x t ≠ 0 := by
    rw [hb.2]
    simpa only [divisorExpression] using hnz ⟨14, by decide⟩
  have hraw := rawDiv_sound n00074_pair n00076_pair x t ha.1 hb.1 hd
  have hred := checkReduction_sound n00077_checked x t hraw.1
  dsimp only [n00077_reduction] at hred
  refine ⟨hred.1, ?_⟩
  rw [← hred.2, hraw.2]
  simp only [n00077_expression, ha.2, hb.2]
theorem n00078_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00078_pair.NonzeroDenominator x t ∧ n00078_pair.value x t = n00078_expression x t := by
  have ha := n00040_sound x t hnz
  have hb := n00017_sound x t hnz
  have hd : n00017_pair.value x t ≠ 0 := by
    rw [hb.2]
    simpa only [divisorExpression] using hnz ⟨15, by decide⟩
  have hraw := rawDiv_sound n00040_pair n00017_pair x t ha.1 hb.1 hd
  have hred := checkReduction_sound n00078_checked x t hraw.1
  dsimp only [n00078_reduction] at hred
  refine ⟨hred.1, ?_⟩
  rw [← hred.2, hraw.2]
  simp only [n00078_expression, ha.2, hb.2]
theorem n00079_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00079_pair.NonzeroDenominator x t ∧ n00079_pair.value x t = n00079_expression x t := by
  have ha := n00005_sound x t hnz
  have hb := n00078_sound x t hnz
  have hraw := rawSub_sound n00005_pair n00078_pair x t ha.1 hb.1
  have hred := checkReduction_sound n00079_checked x t hraw.1
  dsimp only [n00079_reduction] at hred
  refine ⟨hred.1, ?_⟩
  rw [← hred.2, hraw.2]
  simp only [n00079_expression, ha.2, hb.2]
theorem n00080_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00080_pair.NonzeroDenominator x t ∧ n00080_pair.value x t = n00080_expression x t := by
  have ha := n00040_sound x t hnz
  have hb := n00040_sound x t hnz
  have hraw := rawMul_sound n00040_pair n00040_pair x t ha.1 hb.1
  have hred := checkReduction_sound n00080_checked x t hraw.1
  dsimp only [n00080_reduction] at hred
  refine ⟨hred.1, ?_⟩
  rw [← hred.2, hraw.2]
  simp only [n00080_expression, ha.2, hb.2]
theorem n00081_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00081_pair.NonzeroDenominator x t ∧ n00081_pair.value x t = n00081_expression x t := by
  have ha := n00080_sound x t hnz
  have hb := n00070_sound x t hnz
  have hd : n00070_pair.value x t ≠ 0 := by
    rw [hb.2]
    simpa only [divisorExpression] using hnz ⟨16, by decide⟩
  have hraw := rawDiv_sound n00080_pair n00070_pair x t ha.1 hb.1 hd
  have hred := checkReduction_sound n00081_checked x t hraw.1
  dsimp only [n00081_reduction] at hred
  refine ⟨hred.1, ?_⟩
  rw [← hred.2, hraw.2]
  simp only [n00081_expression, ha.2, hb.2]
theorem n00082_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00082_pair.NonzeroDenominator x t ∧ n00082_pair.value x t = n00082_expression x t := by
  have ha := n00079_sound x t hnz
  have hb := n00081_sound x t hnz
  have hraw := rawSub_sound n00079_pair n00081_pair x t ha.1 hb.1
  have hred := checkReduction_sound n00082_checked x t hraw.1
  dsimp only [n00082_reduction] at hred
  refine ⟨hred.1, ?_⟩
  rw [← hred.2, hraw.2]
  simp only [n00082_expression, ha.2, hb.2]
theorem n00083_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00083_pair.NonzeroDenominator x t ∧ n00083_pair.value x t = n00083_expression x t := by
  have ha := n00061_sound x t hnz
  have hb := n00082_sound x t hnz
  have hraw := rawMul_sound n00061_pair n00082_pair x t ha.1 hb.1
  have hred := checkReduction_sound n00083_checked x t hraw.1
  dsimp only [n00083_reduction] at hred
  refine ⟨hred.1, ?_⟩
  rw [← hred.2, hraw.2]
  simp only [n00083_expression, ha.2, hb.2]
theorem n00084_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00084_pair.NonzeroDenominator x t ∧ n00084_pair.value x t = n00084_expression x t := by
  simpa [n00084_pair, n00084_expression, rationalConst, Polynomial2.const] using rationalConst_sound 9 10 x t (by decide)
theorem n00085_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00085_pair.NonzeroDenominator x t ∧ n00085_pair.value x t = n00085_expression x t := by
  have ha := n00044_sound x t hnz
  have hb := n00041_sound x t hnz
  have hraw := rawMul_sound n00044_pair n00041_pair x t ha.1 hb.1
  have hred := checkReduction_sound n00085_checked x t hraw.1
  dsimp only [n00085_reduction] at hred
  refine ⟨hred.1, ?_⟩
  rw [← hred.2, hraw.2]
  simp only [n00085_expression, ha.2, hb.2]
theorem n00086_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00086_pair.NonzeroDenominator x t ∧ n00086_pair.value x t = n00086_expression x t := by
  have ha := n00085_sound x t hnz
  have hb := n00083_sound x t hnz
  have hraw := rawAdd_sound n00085_pair n00083_pair x t ha.1 hb.1
  have hred := checkReduction_sound n00086_checked x t hraw.1
  dsimp only [n00086_reduction] at hred
  refine ⟨hred.1, ?_⟩
  rw [← hred.2, hraw.2]
  simp only [n00086_expression, ha.2, hb.2]
theorem n00087_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00087_pair.NonzeroDenominator x t ∧ n00087_pair.value x t = n00087_expression x t := by
  have ha := n00061_sound x t hnz
  have hb := n00066_sound x t hnz
  have hraw := rawSub_sound n00061_pair n00066_pair x t ha.1 hb.1
  have hred := checkReduction_sound n00087_checked x t hraw.1
  dsimp only [n00087_reduction] at hred
  refine ⟨hred.1, ?_⟩
  rw [← hred.2, hraw.2]
  simp only [n00087_expression, ha.2, hb.2]
theorem n00088_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00088_pair.NonzeroDenominator x t ∧ n00088_pair.value x t = n00088_expression x t := by
  have ha := n00017_sound x t hnz
  have hb := n00087_sound x t hnz
  have hraw := rawMul_sound n00017_pair n00087_pair x t ha.1 hb.1
  have hred := checkReduction_sound n00088_checked x t hraw.1
  dsimp only [n00088_reduction] at hred
  refine ⟨hred.1, ?_⟩
  rw [← hred.2, hraw.2]
  simp only [n00088_expression, ha.2, hb.2]
theorem n00089_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00089_pair.NonzeroDenominator x t ∧ n00089_pair.value x t = n00089_expression x t := by
  have ha := n00088_sound x t hnz
  have hb := n00002_sound x t hnz
  have hraw := rawMul_sound n00088_pair n00002_pair x t ha.1 hb.1
  have hred := checkReduction_sound n00089_checked x t hraw.1
  dsimp only [n00089_reduction] at hred
  refine ⟨hred.1, ?_⟩
  rw [← hred.2, hraw.2]
  simp only [n00089_expression, ha.2, hb.2]
theorem n00090_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00090_pair.NonzeroDenominator x t ∧ n00090_pair.value x t = n00090_expression x t := by
  have ha := n00017_sound x t hnz
  have hb := n00086_sound x t hnz
  have hraw := rawMul_sound n00017_pair n00086_pair x t ha.1 hb.1
  have hred := checkReduction_sound n00090_checked x t hraw.1
  dsimp only [n00090_reduction] at hred
  refine ⟨hred.1, ?_⟩
  rw [← hred.2, hraw.2]
  simp only [n00090_expression, ha.2, hb.2]
theorem n00091_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00091_pair.NonzeroDenominator x t ∧ n00091_pair.value x t = n00091_expression x t := by
  have ha := n00077_sound x t hnz
  have hb := n00002_sound x t hnz
  have hraw := rawMul_sound n00077_pair n00002_pair x t ha.1 hb.1
  have hred := checkReduction_sound n00091_checked x t hraw.1
  dsimp only [n00091_reduction] at hred
  refine ⟨hred.1, ?_⟩
  rw [← hred.2, hraw.2]
  simp only [n00091_expression, ha.2, hb.2]
theorem n00092_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00092_pair.NonzeroDenominator x t ∧ n00092_pair.value x t = n00092_expression x t := by
  have ha := n00005_sound x t hnz
  have hb := n00091_sound x t hnz
  have hraw := rawSub_sound n00005_pair n00091_pair x t ha.1 hb.1
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
  have ha := n00093_sound x t hnz
  have hb := n00051_sound x t hnz
  have hraw := rawSub_sound n00093_pair n00051_pair x t ha.1 hb.1
  have hred := checkReduction_sound n00094_checked x t hraw.1
  dsimp only [n00094_reduction] at hred
  refine ⟨hred.1, ?_⟩
  rw [← hred.2, hraw.2]
  simp only [n00094_expression, ha.2, hb.2]
theorem n00095_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00095_pair.NonzeroDenominator x t ∧ n00095_pair.value x t = n00095_expression x t := by
  have ha := n00094_sound x t hnz
  have hb := n00056_sound x t hnz
  have hraw := rawSub_sound n00094_pair n00056_pair x t ha.1 hb.1
  have hred := checkReduction_sound n00095_checked x t hraw.1
  dsimp only [n00095_reduction] at hred
  refine ⟨hred.1, ?_⟩
  rw [← hred.2, hraw.2]
  simp only [n00095_expression, ha.2, hb.2]
theorem n00096_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00096_pair.NonzeroDenominator x t ∧ n00096_pair.value x t = n00096_expression x t := by
  have ha := n00040_sound x t hnz
  have hb := n00095_sound x t hnz
  have hraw := rawMul_sound n00040_pair n00095_pair x t ha.1 hb.1
  have hred := checkReduction_sound n00096_checked x t hraw.1
  dsimp only [n00096_reduction] at hred
  refine ⟨hred.1, ?_⟩
  rw [← hred.2, hraw.2]
  simp only [n00096_expression, ha.2, hb.2]
theorem n00097_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00097_pair.NonzeroDenominator x t ∧ n00097_pair.value x t = n00097_expression x t := by
  have ha := n00089_sound x t hnz
  have hb := n00096_sound x t hnz
  have hraw := rawAdd_sound n00089_pair n00096_pair x t ha.1 hb.1
  have hred := checkReduction_sound n00097_checked x t hraw.1
  dsimp only [n00097_reduction] at hred
  refine ⟨hred.1, ?_⟩
  rw [← hred.2, hraw.2]
  simp only [n00097_expression, ha.2, hb.2]
theorem n00098_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00098_pair.NonzeroDenominator x t ∧ n00098_pair.value x t = n00098_expression x t := by
  have ha := n00005_sound x t hnz
  have hb := n00041_sound x t hnz
  have hraw := rawMul_sound n00005_pair n00041_pair x t ha.1 hb.1
  have hred := checkReduction_sound n00098_checked x t hraw.1
  dsimp only [n00098_reduction] at hred
  refine ⟨hred.1, ?_⟩
  rw [← hred.2, hraw.2]
  simp only [n00098_expression, ha.2, hb.2]
theorem n00099_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00099_pair.NonzeroDenominator x t ∧ n00099_pair.value x t = n00099_expression x t := by
  have ha := n00098_sound x t hnz
  have hb := n00083_sound x t hnz
  have hraw := rawAdd_sound n00098_pair n00083_pair x t ha.1 hb.1
  have hred := checkReduction_sound n00099_checked x t hraw.1
  dsimp only [n00099_reduction] at hred
  refine ⟨hred.1, ?_⟩
  rw [← hred.2, hraw.2]
  simp only [n00099_expression, ha.2, hb.2]
theorem n00100_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00100_pair.NonzeroDenominator x t ∧ n00100_pair.value x t = n00100_expression x t := by
  have ha := n00017_sound x t hnz
  have hb := n00099_sound x t hnz
  have hraw := rawMul_sound n00017_pair n00099_pair x t ha.1 hb.1
  have hred := checkReduction_sound n00100_checked x t hraw.1
  dsimp only [n00100_reduction] at hred
  refine ⟨hred.1, ?_⟩
  rw [← hred.2, hraw.2]
  simp only [n00100_expression, ha.2, hb.2]
theorem n00101_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00101_pair.NonzeroDenominator x t ∧ n00101_pair.value x t = n00101_expression x t := by
  have ha := n00100_sound x t hnz
  have hb := n00092_sound x t hnz
  have hraw := rawMul_sound n00100_pair n00092_pair x t ha.1 hb.1
  have hred := checkReduction_sound n00101_checked x t hraw.1
  dsimp only [n00101_reduction] at hred
  refine ⟨hred.1, ?_⟩
  rw [← hred.2, hraw.2]
  simp only [n00101_expression, ha.2, hb.2]
theorem n00102_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00102_pair.NonzeroDenominator x t ∧ n00102_pair.value x t = n00102_expression x t := by
  have ha := n00101_sound x t hnz
  have hb := n00051_sound x t hnz
  have hraw := rawSub_sound n00101_pair n00051_pair x t ha.1 hb.1
  have hred := checkReduction_sound n00102_checked x t hraw.1
  dsimp only [n00102_reduction] at hred
  refine ⟨hred.1, ?_⟩
  rw [← hred.2, hraw.2]
  simp only [n00102_expression, ha.2, hb.2]
theorem n00103_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00103_pair.NonzeroDenominator x t ∧ n00103_pair.value x t = n00103_expression x t := by
  have ha := n00102_sound x t hnz
  have hb := n00056_sound x t hnz
  have hraw := rawSub_sound n00102_pair n00056_pair x t ha.1 hb.1
  have hred := checkReduction_sound n00103_checked x t hraw.1
  dsimp only [n00103_reduction] at hred
  refine ⟨hred.1, ?_⟩
  rw [← hred.2, hraw.2]
  simp only [n00103_expression, ha.2, hb.2]
theorem n00104_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00104_pair.NonzeroDenominator x t ∧ n00104_pair.value x t = n00104_expression x t := by
  have ha := n00040_sound x t hnz
  have hb := n00103_sound x t hnz
  have hraw := rawMul_sound n00040_pair n00103_pair x t ha.1 hb.1
  have hred := checkReduction_sound n00104_checked x t hraw.1
  dsimp only [n00104_reduction] at hred
  refine ⟨hred.1, ?_⟩
  rw [← hred.2, hraw.2]
  simp only [n00104_expression, ha.2, hb.2]
theorem n00105_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00105_pair.NonzeroDenominator x t ∧ n00105_pair.value x t = n00105_expression x t := by
  have ha := n00089_sound x t hnz
  have hb := n00104_sound x t hnz
  have hraw := rawAdd_sound n00089_pair n00104_pair x t ha.1 hb.1
  have hred := checkReduction_sound n00105_checked x t hraw.1
  dsimp only [n00105_reduction] at hred
  refine ⟨hred.1, ?_⟩
  rw [← hred.2, hraw.2]
  simp only [n00105_expression, ha.2, hb.2]
theorem n00106_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00106_pair.NonzeroDenominator x t ∧ n00106_pair.value x t = n00106_expression x t := by
  have ha := n00088_sound x t hnz
  have hb := n00084_sound x t hnz
  have hraw := rawMul_sound n00088_pair n00084_pair x t ha.1 hb.1
  have hred := checkReduction_sound n00106_checked x t hraw.1
  dsimp only [n00106_reduction] at hred
  refine ⟨hred.1, ?_⟩
  rw [← hred.2, hraw.2]
  simp only [n00106_expression, ha.2, hb.2]
theorem n00107_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00107_pair.NonzeroDenominator x t ∧ n00107_pair.value x t = n00107_expression x t := by
  have ha := n00077_sound x t hnz
  have hb := n00084_sound x t hnz
  have hraw := rawMul_sound n00077_pair n00084_pair x t ha.1 hb.1
  have hred := checkReduction_sound n00107_checked x t hraw.1
  dsimp only [n00107_reduction] at hred
  refine ⟨hred.1, ?_⟩
  rw [← hred.2, hraw.2]
  simp only [n00107_expression, ha.2, hb.2]
theorem n00108_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00108_pair.NonzeroDenominator x t ∧ n00108_pair.value x t = n00108_expression x t := by
  have ha := n00005_sound x t hnz
  have hb := n00107_sound x t hnz
  have hraw := rawSub_sound n00005_pair n00107_pair x t ha.1 hb.1
  have hred := checkReduction_sound n00108_checked x t hraw.1
  dsimp only [n00108_reduction] at hred
  refine ⟨hred.1, ?_⟩
  rw [← hred.2, hraw.2]
  simp only [n00108_expression, ha.2, hb.2]
theorem n00109_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00109_pair.NonzeroDenominator x t ∧ n00109_pair.value x t = n00109_expression x t := by
  have ha := n00090_sound x t hnz
  have hb := n00108_sound x t hnz
  have hraw := rawMul_sound n00090_pair n00108_pair x t ha.1 hb.1
  have hred := checkReduction_sound n00109_checked x t hraw.1
  dsimp only [n00109_reduction] at hred
  refine ⟨hred.1, ?_⟩
  rw [← hred.2, hraw.2]
  simp only [n00109_expression, ha.2, hb.2]
theorem n00110_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00110_pair.NonzeroDenominator x t ∧ n00110_pair.value x t = n00110_expression x t := by
  have ha := n00109_sound x t hnz
  have hb := n00051_sound x t hnz
  have hraw := rawSub_sound n00109_pair n00051_pair x t ha.1 hb.1
  have hred := checkReduction_sound n00110_checked x t hraw.1
  dsimp only [n00110_reduction] at hred
  refine ⟨hred.1, ?_⟩
  rw [← hred.2, hraw.2]
  simp only [n00110_expression, ha.2, hb.2]
theorem n00111_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00111_pair.NonzeroDenominator x t ∧ n00111_pair.value x t = n00111_expression x t := by
  have ha := n00110_sound x t hnz
  have hb := n00056_sound x t hnz
  have hraw := rawSub_sound n00110_pair n00056_pair x t ha.1 hb.1
  have hred := checkReduction_sound n00111_checked x t hraw.1
  dsimp only [n00111_reduction] at hred
  refine ⟨hred.1, ?_⟩
  rw [← hred.2, hraw.2]
  simp only [n00111_expression, ha.2, hb.2]
theorem n00112_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00112_pair.NonzeroDenominator x t ∧ n00112_pair.value x t = n00112_expression x t := by
  have ha := n00040_sound x t hnz
  have hb := n00111_sound x t hnz
  have hraw := rawMul_sound n00040_pair n00111_pair x t ha.1 hb.1
  have hred := checkReduction_sound n00112_checked x t hraw.1
  dsimp only [n00112_reduction] at hred
  refine ⟨hred.1, ?_⟩
  rw [← hred.2, hraw.2]
  simp only [n00112_expression, ha.2, hb.2]
theorem n00113_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00113_pair.NonzeroDenominator x t ∧ n00113_pair.value x t = n00113_expression x t := by
  have ha := n00106_sound x t hnz
  have hb := n00112_sound x t hnz
  have hraw := rawAdd_sound n00106_pair n00112_pair x t ha.1 hb.1
  have hred := checkReduction_sound n00113_checked x t hraw.1
  dsimp only [n00113_reduction] at hred
  refine ⟨hred.1, ?_⟩
  rw [← hred.2, hraw.2]
  simp only [n00113_expression, ha.2, hb.2]
theorem n00114_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00114_pair.NonzeroDenominator x t ∧ n00114_pair.value x t = n00114_expression x t := by
  have ha := n00100_sound x t hnz
  have hb := n00108_sound x t hnz
  have hraw := rawMul_sound n00100_pair n00108_pair x t ha.1 hb.1
  have hred := checkReduction_sound n00114_checked x t hraw.1
  dsimp only [n00114_reduction] at hred
  refine ⟨hred.1, ?_⟩
  rw [← hred.2, hraw.2]
  simp only [n00114_expression, ha.2, hb.2]
theorem n00115_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00115_pair.NonzeroDenominator x t ∧ n00115_pair.value x t = n00115_expression x t := by
  have ha := n00114_sound x t hnz
  have hb := n00051_sound x t hnz
  have hraw := rawSub_sound n00114_pair n00051_pair x t ha.1 hb.1
  have hred := checkReduction_sound n00115_checked x t hraw.1
  dsimp only [n00115_reduction] at hred
  refine ⟨hred.1, ?_⟩
  rw [← hred.2, hraw.2]
  simp only [n00115_expression, ha.2, hb.2]
theorem n00116_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00116_pair.NonzeroDenominator x t ∧ n00116_pair.value x t = n00116_expression x t := by
  have ha := n00115_sound x t hnz
  have hb := n00056_sound x t hnz
  have hraw := rawSub_sound n00115_pair n00056_pair x t ha.1 hb.1
  have hred := checkReduction_sound n00116_checked x t hraw.1
  dsimp only [n00116_reduction] at hred
  refine ⟨hred.1, ?_⟩
  rw [← hred.2, hraw.2]
  simp only [n00116_expression, ha.2, hb.2]
theorem n00117_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00117_pair.NonzeroDenominator x t ∧ n00117_pair.value x t = n00117_expression x t := by
  have ha := n00040_sound x t hnz
  have hb := n00116_sound x t hnz
  have hraw := rawMul_sound n00040_pair n00116_pair x t ha.1 hb.1
  have hred := checkReduction_sound n00117_checked x t hraw.1
  dsimp only [n00117_reduction] at hred
  refine ⟨hred.1, ?_⟩
  rw [← hred.2, hraw.2]
  simp only [n00117_expression, ha.2, hb.2]
theorem n00118_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00118_pair.NonzeroDenominator x t ∧ n00118_pair.value x t = n00118_expression x t := by
  have ha := n00106_sound x t hnz
  have hb := n00117_sound x t hnz
  have hraw := rawAdd_sound n00106_pair n00117_pair x t ha.1 hb.1
  have hred := checkReduction_sound n00118_checked x t hraw.1
  dsimp only [n00118_reduction] at hred
  refine ⟨hred.1, ?_⟩
  rw [← hred.2, hraw.2]
  simp only [n00118_expression, ha.2, hb.2]
theorem n00119_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00119_pair.NonzeroDenominator x t ∧ n00119_pair.value x t = n00119_expression x t := by
  have ha := n00041_sound x t hnz
  have hb := n00083_sound x t hnz
  have hraw := rawAdd_sound n00041_pair n00083_pair x t ha.1 hb.1
  have hred := checkReduction_sound n00119_checked x t hraw.1
  dsimp only [n00119_reduction] at hred
  refine ⟨hred.1, ?_⟩
  rw [← hred.2, hraw.2]
  simp only [n00119_expression, ha.2, hb.2]
theorem n00120_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00120_pair.NonzeroDenominator x t ∧ n00120_pair.value x t = n00120_expression x t := by
  simpa [n00120_pair, n00120_expression, rationalConst, Polynomial2.const] using rationalConst_sound 10 1 x t (by decide)
theorem n00121_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00121_pair.NonzeroDenominator x t ∧ n00121_pair.value x t = n00121_expression x t := by
  have ha := n00120_sound x t hnz
  have hb := n00066_sound x t hnz
  have hraw := rawMul_sound n00120_pair n00066_pair x t ha.1 hb.1
  have hred := checkReduction_sound n00121_checked x t hraw.1
  dsimp only [n00121_reduction] at hred
  refine ⟨hred.1, ?_⟩
  rw [← hred.2, hraw.2]
  simp only [n00121_expression, ha.2, hb.2]
theorem n00122_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00122_pair.NonzeroDenominator x t ∧ n00122_pair.value x t = n00122_expression x t := by
  have ha := n00051_sound x t hnz
  have hb := n00056_sound x t hnz
  have hraw := rawAdd_sound n00051_pair n00056_pair x t ha.1 hb.1
  have hred := checkReduction_sound n00122_checked x t hraw.1
  dsimp only [n00122_reduction] at hred
  refine ⟨hred.1, ?_⟩
  rw [← hred.2, hraw.2]
  simp only [n00122_expression, ha.2, hb.2]
theorem n00123_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00123_pair.NonzeroDenominator x t ∧ n00123_pair.value x t = n00123_expression x t := by
  have ha := n00040_sound x t hnz
  have hb := n00122_sound x t hnz
  have hraw := rawMul_sound n00040_pair n00122_pair x t ha.1 hb.1
  have hred := checkReduction_sound n00123_checked x t hraw.1
  dsimp only [n00123_reduction] at hred
  refine ⟨hred.1, ?_⟩
  rw [← hred.2, hraw.2]
  simp only [n00123_expression, ha.2, hb.2]
theorem n00124_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00124_pair.NonzeroDenominator x t ∧ n00124_pair.value x t = n00124_expression x t := by
  have ha := n00121_sound x t hnz
  have hb := n00123_sound x t hnz
  have hraw := rawAdd_sound n00121_pair n00123_pair x t ha.1 hb.1
  have hred := checkReduction_sound n00124_checked x t hraw.1
  dsimp only [n00124_reduction] at hred
  refine ⟨hred.1, ?_⟩
  rw [← hred.2, hraw.2]
  simp only [n00124_expression, ha.2, hb.2]
theorem n00125_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00125_pair.NonzeroDenominator x t ∧ n00125_pair.value x t = n00125_expression x t := by
  have ha := n00120_sound x t hnz
  have hb := n00032_sound x t hnz
  have hraw := rawMul_sound n00120_pair n00032_pair x t ha.1 hb.1
  have hred := checkReduction_sound n00125_checked x t hraw.1
  dsimp only [n00125_reduction] at hred
  refine ⟨hred.1, ?_⟩
  rw [← hred.2, hraw.2]
  simp only [n00125_expression, ha.2, hb.2]
theorem n00126_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00126_pair.NonzeroDenominator x t ∧ n00126_pair.value x t = n00126_expression x t := by
  have ha := n00002_sound x t hnz
  have hb := n00125_sound x t hnz
  have hraw := rawAdd_sound n00002_pair n00125_pair x t ha.1 hb.1
  have hred := checkReduction_sound n00126_checked x t hraw.1
  dsimp only [n00126_reduction] at hred
  refine ⟨hred.1, ?_⟩
  rw [← hred.2, hraw.2]
  simp only [n00126_expression, ha.2, hb.2]
theorem n00127_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00127_pair.NonzeroDenominator x t ∧ n00127_pair.value x t = n00127_expression x t := by
  have ha := n00087_sound x t hnz
  have hb := n00126_sound x t hnz
  have hraw := rawMul_sound n00087_pair n00126_pair x t ha.1 hb.1
  have hred := checkReduction_sound n00127_checked x t hraw.1
  dsimp only [n00127_reduction] at hred
  refine ⟨hred.1, ?_⟩
  rw [← hred.2, hraw.2]
  simp only [n00127_expression, ha.2, hb.2]
theorem n00128_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00128_pair.NonzeroDenominator x t ∧ n00128_pair.value x t = n00128_expression x t := by
  have ha := n00124_sound x t hnz
  have hb := n00127_sound x t hnz
  have hraw := rawAdd_sound n00124_pair n00127_pair x t ha.1 hb.1
  have hred := checkReduction_sound n00128_checked x t hraw.1
  dsimp only [n00128_reduction] at hred
  refine ⟨hred.1, ?_⟩
  rw [← hred.2, hraw.2]
  simp only [n00128_expression, ha.2, hb.2]
theorem n00129_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00129_pair.NonzeroDenominator x t ∧ n00129_pair.value x t = n00129_expression x t := by
  have ha := n00040_sound x t hnz
  have hb := n00119_sound x t hnz
  have hraw := rawMul_sound n00040_pair n00119_pair x t ha.1 hb.1
  have hred := checkReduction_sound n00129_checked x t hraw.1
  dsimp only [n00129_reduction] at hred
  refine ⟨hred.1, ?_⟩
  rw [← hred.2, hraw.2]
  simp only [n00129_expression, ha.2, hb.2]
theorem n00130_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00130_pair.NonzeroDenominator x t ∧ n00130_pair.value x t = n00130_expression x t := by
  have ha := n00077_sound x t hnz
  have hb := n00126_sound x t hnz
  have hraw := rawMul_sound n00077_pair n00126_pair x t ha.1 hb.1
  have hred := checkReduction_sound n00130_checked x t hraw.1
  dsimp only [n00130_reduction] at hred
  refine ⟨hred.1, ?_⟩
  rw [← hred.2, hraw.2]
  simp only [n00130_expression, ha.2, hb.2]
theorem n00131_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00131_pair.NonzeroDenominator x t ∧ n00131_pair.value x t = n00131_expression x t := by
  have ha := n00017_sound x t hnz
  have hb := n00130_sound x t hnz
  have hraw := rawAdd_sound n00017_pair n00130_pair x t ha.1 hb.1
  have hred := checkReduction_sound n00131_checked x t hraw.1
  dsimp only [n00131_reduction] at hred
  refine ⟨hred.1, ?_⟩
  rw [← hred.2, hraw.2]
  simp only [n00131_expression, ha.2, hb.2]
theorem n00132_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00132_pair.NonzeroDenominator x t ∧ n00132_pair.value x t = n00132_expression x t := by
  have ha := n00129_sound x t hnz
  have hb := n00131_sound x t hnz
  have hraw := rawMul_sound n00129_pair n00131_pair x t ha.1 hb.1
  have hred := checkReduction_sound n00132_checked x t hraw.1
  dsimp only [n00132_reduction] at hred
  refine ⟨hred.1, ?_⟩
  rw [← hred.2, hraw.2]
  simp only [n00132_expression, ha.2, hb.2]
theorem n00133_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00133_pair.NonzeroDenominator x t ∧ n00133_pair.value x t = n00133_expression x t := by
  have ha := n00128_sound x t hnz
  have hb := n00132_sound x t hnz
  have hraw := rawSub_sound n00128_pair n00132_pair x t ha.1 hb.1
  have hred := checkReduction_sound n00133_checked x t hraw.1
  dsimp only [n00133_reduction] at hred
  refine ⟨hred.1, ?_⟩
  rw [← hred.2, hraw.2]
  simp only [n00133_expression, ha.2, hb.2]
theorem n00134_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00134_pair.NonzeroDenominator x t ∧ n00134_pair.value x t = n00134_expression x t := by
  have ha := n00084_sound x t hnz
  have hb := n00125_sound x t hnz
  have hraw := rawAdd_sound n00084_pair n00125_pair x t ha.1 hb.1
  have hred := checkReduction_sound n00134_checked x t hraw.1
  dsimp only [n00134_reduction] at hred
  refine ⟨hred.1, ?_⟩
  rw [← hred.2, hraw.2]
  simp only [n00134_expression, ha.2, hb.2]
theorem n00135_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00135_pair.NonzeroDenominator x t ∧ n00135_pair.value x t = n00135_expression x t := by
  have ha := n00087_sound x t hnz
  have hb := n00134_sound x t hnz
  have hraw := rawMul_sound n00087_pair n00134_pair x t ha.1 hb.1
  have hred := checkReduction_sound n00135_checked x t hraw.1
  dsimp only [n00135_reduction] at hred
  refine ⟨hred.1, ?_⟩
  rw [← hred.2, hraw.2]
  simp only [n00135_expression, ha.2, hb.2]
theorem n00136_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00136_pair.NonzeroDenominator x t ∧ n00136_pair.value x t = n00136_expression x t := by
  have ha := n00124_sound x t hnz
  have hb := n00135_sound x t hnz
  have hraw := rawAdd_sound n00124_pair n00135_pair x t ha.1 hb.1
  have hred := checkReduction_sound n00136_checked x t hraw.1
  dsimp only [n00136_reduction] at hred
  refine ⟨hred.1, ?_⟩
  rw [← hred.2, hraw.2]
  simp only [n00136_expression, ha.2, hb.2]
theorem n00137_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00137_pair.NonzeroDenominator x t ∧ n00137_pair.value x t = n00137_expression x t := by
  have ha := n00077_sound x t hnz
  have hb := n00134_sound x t hnz
  have hraw := rawMul_sound n00077_pair n00134_pair x t ha.1 hb.1
  have hred := checkReduction_sound n00137_checked x t hraw.1
  dsimp only [n00137_reduction] at hred
  refine ⟨hred.1, ?_⟩
  rw [← hred.2, hraw.2]
  simp only [n00137_expression, ha.2, hb.2]
theorem n00138_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00138_pair.NonzeroDenominator x t ∧ n00138_pair.value x t = n00138_expression x t := by
  have ha := n00017_sound x t hnz
  have hb := n00137_sound x t hnz
  have hraw := rawAdd_sound n00017_pair n00137_pair x t ha.1 hb.1
  have hred := checkReduction_sound n00138_checked x t hraw.1
  dsimp only [n00138_reduction] at hred
  refine ⟨hred.1, ?_⟩
  rw [← hred.2, hraw.2]
  simp only [n00138_expression, ha.2, hb.2]
theorem n00139_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00139_pair.NonzeroDenominator x t ∧ n00139_pair.value x t = n00139_expression x t := by
  have ha := n00129_sound x t hnz
  have hb := n00138_sound x t hnz
  have hraw := rawMul_sound n00129_pair n00138_pair x t ha.1 hb.1
  have hred := checkReduction_sound n00139_checked x t hraw.1
  dsimp only [n00139_reduction] at hred
  refine ⟨hred.1, ?_⟩
  rw [← hred.2, hraw.2]
  simp only [n00139_expression, ha.2, hb.2]
theorem n00140_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00140_pair.NonzeroDenominator x t ∧ n00140_pair.value x t = n00140_expression x t := by
  have ha := n00136_sound x t hnz
  have hb := n00139_sound x t hnz
  have hraw := rawSub_sound n00136_pair n00139_pair x t ha.1 hb.1
  have hred := checkReduction_sound n00140_checked x t hraw.1
  dsimp only [n00140_reduction] at hred
  refine ⟨hred.1, ?_⟩
  rw [← hred.2, hraw.2]
  simp only [n00140_expression, ha.2, hb.2]
abbrev D_mono_r0_lo_pair := n00097_pair
abbrev D_mono_r0_lo_expression := n00097_expression
theorem D_mono_r0_lo_sound (x t : ℝ) (hnz : DivisorsNonzero x t) : n00097_pair.NonzeroDenominator x t ∧ n00097_pair.value x t = n00097_expression x t := n00097_sound x t hnz
#print axioms D_mono_r0_lo_sound
abbrev D_mono_r0_hi_pair := n00105_pair
abbrev D_mono_r0_hi_expression := n00105_expression
theorem D_mono_r0_hi_sound (x t : ℝ) (hnz : DivisorsNonzero x t) : n00105_pair.NonzeroDenominator x t ∧ n00105_pair.value x t = n00105_expression x t := n00105_sound x t hnz
#print axioms D_mono_r0_hi_sound
abbrev D_mono_r1_lo_pair := n00113_pair
abbrev D_mono_r1_lo_expression := n00113_expression
theorem D_mono_r1_lo_sound (x t : ℝ) (hnz : DivisorsNonzero x t) : n00113_pair.NonzeroDenominator x t ∧ n00113_pair.value x t = n00113_expression x t := n00113_sound x t hnz
#print axioms D_mono_r1_lo_sound
abbrev D_mono_r1_hi_pair := n00118_pair
abbrev D_mono_r1_hi_expression := n00118_expression
theorem D_mono_r1_hi_sound (x t : ℝ) (hnz : DivisorsNonzero x t) : n00118_pair.NonzeroDenominator x t ∧ n00118_pair.value x t = n00118_expression x t := n00118_sound x t hnz
#print axioms D_mono_r1_hi_sound
abbrev D_mono_s0_pair := n00133_pair
abbrev D_mono_s0_expression := n00133_expression
theorem D_mono_s0_sound (x t : ℝ) (hnz : DivisorsNonzero x t) : n00133_pair.NonzeroDenominator x t ∧ n00133_pair.value x t = n00133_expression x t := n00133_sound x t hnz
#print axioms D_mono_s0_sound
abbrev D_mono_s1_pair := n00140_pair
abbrev D_mono_s1_expression := n00140_expression
theorem D_mono_s1_sound (x t : ℝ) (hnz : DivisorsNonzero x t) : n00140_pair.NonzeroDenominator x t ∧ n00140_pair.value x t = n00140_expression x t := n00140_sound x t hnz
#print axioms D_mono_s1_sound
end
end F4U.Light.Linking.Generated.DAG_D_FULL_01
