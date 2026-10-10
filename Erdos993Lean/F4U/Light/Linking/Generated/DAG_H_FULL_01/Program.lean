module
public import Erdos993Lean.F4U.Light.Linking.Rational
@[expose] public section
set_option maxRecDepth 4096
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
namespace F4U.Light.Linking.Generated.DAG_H_FULL_01
noncomputable section
def n00000_expression (x t : ℝ) : ℝ := x
def n00000_pair : RationalPair := ⟨[[0, 1]], [[1]]⟩
def n00001_expression (x t : ℝ) : ℝ := t
def n00001_pair : RationalPair := ⟨[[], [1]], [[1]]⟩
def n00002_expression (x t : ℝ) : ℝ := (7 : ℝ)/(4 : ℝ)
def n00002_pair : RationalPair := ⟨[[7]], [[4]]⟩
def n00003_expression (x t : ℝ) : ℝ := (7 : ℝ)/(3 : ℝ)
def n00003_pair : RationalPair := ⟨[[7]], [[3]]⟩
def n00004_expression (x t : ℝ) : ℝ := (2 : ℝ)/(1 : ℝ)
def n00004_pair : RationalPair := ⟨[[2]], [[1]]⟩
def n00005_expression (x t : ℝ) : ℝ := (523 : ℝ)/(256 : ℝ)
def n00005_pair : RationalPair := ⟨[[523]], [[256]]⟩
def n00006_expression (x t : ℝ) : ℝ := (1 : ℝ)/(1 : ℝ)
def n00006_pair : RationalPair := ⟨[[1]], [[1]]⟩
def n00007_expression (x t : ℝ) : ℝ := n00006_expression x t - n00000_expression x t
def n00007_pair : RationalPair := ⟨[[1, -1]], [[1]]⟩
def n00007_reduction : Reduction := ⟨rawSub n00006_pair n00000_pair, n00007_pair, [[1]], 1⟩
theorem n00007_checked : checkReduction n00007_reduction = true := by decide
def n00008_expression (x t : ℝ) : ℝ := n00000_expression x t / n00007_expression x t
def n00008_pair : RationalPair := ⟨[[0, -1]], [[-1, 1]]⟩
def n00008_reduction : Reduction := ⟨rawDiv n00000_pair n00007_pair, n00008_pair, [[-1]], 1⟩
theorem n00008_checked : checkReduction n00008_reduction = true := by decide
def n00009_expression (x t : ℝ) : ℝ := n00006_expression x t + n00008_expression x t
def n00009_pair : RationalPair := ⟨[[-1]], [[-1, 1]]⟩
def n00009_reduction : Reduction := ⟨rawAdd n00006_pair n00008_pair, n00009_pair, [[1]], 1⟩
theorem n00009_checked : checkReduction n00009_reduction = true := by decide
def n00010_expression (x t : ℝ) : ℝ := n00008_expression x t / n00009_expression x t
def n00010_pair : RationalPair := ⟨[[0, 1]], [[1]]⟩
def n00010_reduction : Reduction := ⟨rawDiv n00008_pair n00009_pair, n00010_pair, [[1, -1]], 1⟩
theorem n00010_checked : checkReduction n00010_reduction = true := by decide
def n00011_expression (x t : ℝ) : ℝ := n00006_expression x t + n00002_expression x t
def n00011_pair : RationalPair := ⟨[[11]], [[4]]⟩
def n00011_reduction : Reduction := ⟨rawAdd n00006_pair n00002_pair, n00011_pair, [[1]], 1⟩
theorem n00011_checked : checkReduction n00011_reduction = true := by decide
def n00012_expression (x t : ℝ) : ℝ := n00002_expression x t / n00011_expression x t
def n00012_pair : RationalPair := ⟨[[7]], [[11]]⟩
def n00012_reduction : Reduction := ⟨rawDiv n00002_pair n00011_pair, n00012_pair, [[4]], 1⟩
theorem n00012_checked : checkReduction n00012_reduction = true := by decide
def n00013_expression (x t : ℝ) : ℝ := n00006_expression x t + n00003_expression x t
def n00013_pair : RationalPair := ⟨[[10]], [[3]]⟩
def n00013_reduction : Reduction := ⟨rawAdd n00006_pair n00003_pair, n00013_pair, [[1]], 1⟩
theorem n00013_checked : checkReduction n00013_reduction = true := by decide
def n00014_expression (x t : ℝ) : ℝ := n00003_expression x t / n00013_expression x t
def n00014_pair : RationalPair := ⟨[[7]], [[10]]⟩
def n00014_reduction : Reduction := ⟨rawDiv n00003_pair n00013_pair, n00014_pair, [[3]], 1⟩
theorem n00014_checked : checkReduction n00014_reduction = true := by decide
def n00015_expression (x t : ℝ) : ℝ := n00010_expression x t - n00012_expression x t
def n00015_pair : RationalPair := ⟨[[-7, 11]], [[11]]⟩
def n00015_reduction : Reduction := ⟨rawSub n00010_pair n00012_pair, n00015_pair, [[1]], 1⟩
theorem n00015_checked : checkReduction n00015_reduction = true := by decide
def n00016_expression (x t : ℝ) : ℝ := n00014_expression x t - n00012_expression x t
def n00016_pair : RationalPair := ⟨[[7]], [[110]]⟩
def n00016_reduction : Reduction := ⟨rawSub n00014_pair n00012_pair, n00016_pair, [[1]], 1⟩
theorem n00016_checked : checkReduction n00016_reduction = true := by decide
def n00017_expression (x t : ℝ) : ℝ := n00015_expression x t / n00016_expression x t
def n00017_pair : RationalPair := ⟨[[-70, 110]], [[7]]⟩
def n00017_reduction : Reduction := ⟨rawDiv n00015_pair n00016_pair, n00017_pair, [[11]], 1⟩
theorem n00017_checked : checkReduction n00017_reduction = true := by decide
def n00018_expression (x t : ℝ) : ℝ := (0 : ℝ)/(1 : ℝ)
def n00018_pair : RationalPair := ⟨[], [[1]]⟩
def n00019_expression (x t : ℝ) : ℝ := n00006_expression x t - n00017_expression x t
def n00019_pair : RationalPair := ⟨[[77, -110]], [[7]]⟩
def n00019_reduction : Reduction := ⟨rawSub n00006_pair n00017_pair, n00019_pair, [[1]], 1⟩
theorem n00019_checked : checkReduction n00019_reduction = true := by decide
def n00020_expression (x t : ℝ) : ℝ := (516659173 : ℝ)/(5000000000 : ℝ)
def n00020_pair : RationalPair := ⟨[[516659173]], [[5000000000]]⟩
def n00021_expression (x t : ℝ) : ℝ := n00019_expression x t * n00020_expression x t
def n00021_pair : RationalPair := ⟨[[39782756321, -56832509030]], [[35000000000]]⟩
def n00021_reduction : Reduction := ⟨rawMul n00019_pair n00020_pair, n00021_pair, [[1]], 1⟩
theorem n00021_checked : checkReduction n00021_reduction = true := by decide
def n00022_expression (x t : ℝ) : ℝ := (1762035691 : ℝ)/(10000000000 : ℝ)
def n00022_pair : RationalPair := ⟨[[1762035691]], [[10000000000]]⟩
def n00023_expression (x t : ℝ) : ℝ := n00017_expression x t * n00022_expression x t
def n00023_pair : RationalPair := ⟨[[-12334249837, 19382392601]], [[7000000000]]⟩
def n00023_reduction : Reduction := ⟨rawMul n00017_pair n00022_pair, n00023_pair, [[10]], 1⟩
theorem n00023_checked : checkReduction n00023_reduction = true := by decide
def n00024_expression (x t : ℝ) : ℝ := n00021_expression x t + n00023_expression x t
def n00024_pair : RationalPair := ⟨[[-21888492864, 40079453975]], [[35000000000]]⟩
def n00024_reduction : Reduction := ⟨rawAdd n00021_pair n00023_pair, n00024_pair, [[7000000000]], 1⟩
theorem n00024_checked : checkReduction n00024_reduction = true := by decide
def n00025_expression (x t : ℝ) : ℝ := n00024_expression x t + n00018_expression x t
def n00025_pair : RationalPair := ⟨[[-21888492864, 40079453975]], [[35000000000]]⟩
def n00025_reduction : Reduction := ⟨rawAdd n00024_pair n00018_pair, n00025_pair, [[1]], 1⟩
theorem n00025_checked : checkReduction n00025_reduction = true := by decide
def n00026_expression (x t : ℝ) : ℝ := n00010_expression x t / n00004_expression x t
def n00026_pair : RationalPair := ⟨[[0, 1]], [[2]]⟩
def n00026_reduction : Reduction := ⟨rawDiv n00010_pair n00004_pair, n00026_pair, [[1]], 1⟩
theorem n00026_checked : checkReduction n00026_reduction = true := by decide
def n00027_expression (x t : ℝ) : ℝ := n00010_expression x t * n00001_expression x t
def n00027_pair : RationalPair := ⟨[[], [0, 1]], [[1]]⟩
def n00027_reduction : Reduction := ⟨rawMul n00010_pair n00001_pair, n00027_pair, [[1]], 1⟩
theorem n00027_checked : checkReduction n00027_reduction = true := by decide
def n00028_expression (x t : ℝ) : ℝ := n00027_expression x t / n00004_expression x t
def n00028_pair : RationalPair := ⟨[[], [0, 1]], [[2]]⟩
def n00028_reduction : Reduction := ⟨rawDiv n00027_pair n00004_pair, n00028_pair, [[1]], 1⟩
theorem n00028_checked : checkReduction n00028_reduction = true := by decide
def n00029_expression (x t : ℝ) : ℝ := n00026_expression x t + n00028_expression x t
def n00029_pair : RationalPair := ⟨[[0, 1], [0, 1]], [[2]]⟩
def n00029_reduction : Reduction := ⟨rawAdd n00026_pair n00028_pair, n00029_pair, [[2]], 1⟩
theorem n00029_checked : checkReduction n00029_reduction = true := by decide
def n00030_expression (x t : ℝ) : ℝ := n00006_expression x t - n00029_expression x t
def n00030_pair : RationalPair := ⟨[[2, -1], [0, -1]], [[2]]⟩
def n00030_reduction : Reduction := ⟨rawSub n00006_pair n00029_pair, n00030_pair, [[1]], 1⟩
theorem n00030_checked : checkReduction n00030_reduction = true := by decide
def n00031_expression (x t : ℝ) : ℝ := n00008_expression x t * n00030_expression x t
def n00031_pair : RationalPair := ⟨[[0, -2, 1], [0, 0, 1]], [[-2, 2]]⟩
def n00031_reduction : Reduction := ⟨rawMul n00008_pair n00030_pair, n00031_pair, [[1]], 1⟩
theorem n00031_checked : checkReduction n00031_reduction = true := by decide
def n00032_expression (x t : ℝ) : ℝ := n00006_expression x t + n00031_expression x t
def n00032_pair : RationalPair := ⟨[[-2, 0, 1], [0, 0, 1]], [[-2, 2]]⟩
def n00032_reduction : Reduction := ⟨rawAdd n00006_pair n00031_pair, n00032_pair, [[1]], 1⟩
theorem n00032_checked : checkReduction n00032_reduction = true := by decide
def n00033_expression (x t : ℝ) : ℝ := n00031_expression x t / n00032_expression x t
def n00033_pair : RationalPair := ⟨[[0, -2, 1], [0, 0, 1]], [[-2, 0, 1], [0, 0, 1]]⟩
def n00033_reduction : Reduction := ⟨rawDiv n00031_pair n00032_pair, n00033_pair, [[-2, 2]], 1⟩
theorem n00033_checked : checkReduction n00033_reduction = true := by decide
def n00034_expression (x t : ℝ) : ℝ := n00006_expression x t - n00033_expression x t
def n00034_pair : RationalPair := ⟨[[-2, 2]], [[-2, 0, 1], [0, 0, 1]]⟩
def n00034_reduction : Reduction := ⟨rawSub n00006_pair n00033_pair, n00034_pair, [[1]], 1⟩
theorem n00034_checked : checkReduction n00034_reduction = true := by decide
def n00035_expression (x t : ℝ) : ℝ := n00008_expression x t * n00034_expression x t
def n00035_pair : RationalPair := ⟨[[0, -2]], [[-2, 0, 1], [0, 0, 1]]⟩
def n00035_reduction : Reduction := ⟨rawMul n00008_pair n00034_pair, n00035_pair, [[-1, 1]], 1⟩
theorem n00035_checked : checkReduction n00035_reduction = true := by decide
def n00036_expression (x t : ℝ) : ℝ := n00006_expression x t + n00035_expression x t
def n00036_pair : RationalPair := ⟨[[-2, -2, 1], [0, 0, 1]], [[-2, 0, 1], [0, 0, 1]]⟩
def n00036_reduction : Reduction := ⟨rawAdd n00006_pair n00035_pair, n00036_pair, [[1]], 1⟩
theorem n00036_checked : checkReduction n00036_reduction = true := by decide
def n00037_expression (x t : ℝ) : ℝ := n00006_expression x t / n00036_expression x t
def n00037_pair : RationalPair := ⟨[[-2, 0, 1], [0, 0, 1]], [[-2, -2, 1], [0, 0, 1]]⟩
def n00037_reduction : Reduction := ⟨rawDiv n00006_pair n00036_pair, n00037_pair, [[1]], 1⟩
theorem n00037_checked : checkReduction n00037_reduction = true := by decide
def n00038_expression (x t : ℝ) : ℝ := (51799 : ℝ)/(1 : ℝ)
def n00038_pair : RationalPair := ⟨[[51799]], [[1]]⟩
def n00039_expression (x t : ℝ) : ℝ := n00008_expression x t - n00005_expression x t
def n00039_pair : RationalPair := ⟨[[523, -779]], [[-256, 256]]⟩
def n00039_reduction : Reduction := ⟨rawSub n00008_pair n00005_pair, n00039_pair, [[1]], 1⟩
theorem n00039_checked : checkReduction n00039_reduction = true := by decide
def n00040_expression (x t : ℝ) : ℝ := (8158 : ℝ)/(1 : ℝ)
def n00040_pair : RationalPair := ⟨[[8158]], [[1]]⟩
def n00041_expression (x t : ℝ) : ℝ := n00040_expression x t * n00039_expression x t
def n00041_pair : RationalPair := ⟨[[2133317, -3177541]], [[-128, 128]]⟩
def n00041_reduction : Reduction := ⟨rawMul n00040_pair n00039_pair, n00041_pair, [[2]], 1⟩
theorem n00041_checked : checkReduction n00041_reduction = true := by decide
def n00042_expression (x t : ℝ) : ℝ := n00038_expression x t + n00041_expression x t
def n00042_pair : RationalPair := ⟨[[-4496955, 3452731]], [[-128, 128]]⟩
def n00042_reduction : Reduction := ⟨rawAdd n00038_pair n00041_pair, n00042_pair, [[1]], 1⟩
theorem n00042_checked : checkReduction n00042_reduction = true := by decide
def n00043_expression (x t : ℝ) : ℝ := (65536 : ℝ)/(1 : ℝ)
def n00043_pair : RationalPair := ⟨[[65536]], [[1]]⟩
def n00044_expression (x t : ℝ) : ℝ := n00042_expression x t / n00043_expression x t
def n00044_pair : RationalPair := ⟨[[-4496955, 3452731]], [[-8388608, 8388608]]⟩
def n00044_reduction : Reduction := ⟨rawDiv n00042_pair n00043_pair, n00044_pair, [[1]], 1⟩
theorem n00044_checked : checkReduction n00044_reduction = true := by decide
def n00045_expression (x t : ℝ) : ℝ := (20496 : ℝ)/(1 : ℝ)
def n00045_pair : RationalPair := ⟨[[20496]], [[1]]⟩
def n00046_expression (x t : ℝ) : ℝ := (41265 : ℝ)/(1 : ℝ)
def n00046_pair : RationalPair := ⟨[[41265]], [[1]]⟩
def n00047_expression (x t : ℝ) : ℝ := n00046_expression x t * n00039_expression x t
def n00047_pair : RationalPair := ⟨[[21581595, -32145435]], [[-256, 256]]⟩
def n00047_reduction : Reduction := ⟨rawMul n00046_pair n00039_pair, n00047_pair, [[1]], 1⟩
theorem n00047_checked : checkReduction n00047_reduction = true := by decide
def n00048_expression (x t : ℝ) : ℝ := n00045_expression x t + n00047_expression x t
def n00048_pair : RationalPair := ⟨[[16334619, -26898459]], [[-256, 256]]⟩
def n00048_reduction : Reduction := ⟨rawAdd n00045_pair n00047_pair, n00048_pair, [[1]], 1⟩
theorem n00048_checked : checkReduction n00048_reduction = true := by decide
def n00049_expression (x t : ℝ) : ℝ := n00048_expression x t / n00043_expression x t
def n00049_pair : RationalPair := ⟨[[16334619, -26898459]], [[-16777216, 16777216]]⟩
def n00049_reduction : Reduction := ⟨rawDiv n00048_pair n00043_pair, n00049_pair, [[1]], 1⟩
theorem n00049_checked : checkReduction n00049_reduction = true := by decide
def n00050_expression (x t : ℝ) : ℝ := (29750 : ℝ)/(1 : ℝ)
def n00050_pair : RationalPair := ⟨[[29750]], [[1]]⟩
def n00051_expression (x t : ℝ) : ℝ := (4333 : ℝ)/(1 : ℝ)
def n00051_pair : RationalPair := ⟨[[4333]], [[1]]⟩
def n00052_expression (x t : ℝ) : ℝ := n00051_expression x t * n00039_expression x t
def n00052_pair : RationalPair := ⟨[[2266159, -3375407]], [[-256, 256]]⟩
def n00052_reduction : Reduction := ⟨rawMul n00051_pair n00039_pair, n00052_pair, [[1]], 1⟩
theorem n00052_checked : checkReduction n00052_reduction = true := by decide
def n00053_expression (x t : ℝ) : ℝ := n00050_expression x t + n00052_expression x t
def n00053_pair : RationalPair := ⟨[[-5349841, 4240593]], [[-256, 256]]⟩
def n00053_reduction : Reduction := ⟨rawAdd n00050_pair n00052_pair, n00053_pair, [[1]], 1⟩
theorem n00053_checked : checkReduction n00053_reduction = true := by decide
def n00054_expression (x t : ℝ) : ℝ := n00053_expression x t / n00043_expression x t
def n00054_pair : RationalPair := ⟨[[-5349841, 4240593]], [[-16777216, 16777216]]⟩
def n00054_reduction : Reduction := ⟨rawDiv n00053_pair n00043_pair, n00054_pair, [[1]], 1⟩
theorem n00054_checked : checkReduction n00054_reduction = true := by decide
def n00055_expression (x t : ℝ) : ℝ := (9083 : ℝ)/(1 : ℝ)
def n00055_pair : RationalPair := ⟨[[9083]], [[1]]⟩
def n00056_expression (x t : ℝ) : ℝ := ((-11181) : ℝ)/(1 : ℝ)
def n00056_pair : RationalPair := ⟨[[-11181]], [[1]]⟩
def n00057_expression (x t : ℝ) : ℝ := n00056_expression x t * n00039_expression x t
def n00057_pair : RationalPair := ⟨[[-5847663, 8709999]], [[-256, 256]]⟩
def n00057_reduction : Reduction := ⟨rawMul n00056_pair n00039_pair, n00057_pair, [[1]], 1⟩
theorem n00057_checked : checkReduction n00057_reduction = true := by decide
def n00058_expression (x t : ℝ) : ℝ := n00055_expression x t + n00057_expression x t
def n00058_pair : RationalPair := ⟨[[-8172911, 11035247]], [[-256, 256]]⟩
def n00058_reduction : Reduction := ⟨rawAdd n00055_pair n00057_pair, n00058_pair, [[1]], 1⟩
theorem n00058_checked : checkReduction n00058_reduction = true := by decide
def n00059_expression (x t : ℝ) : ℝ := n00058_expression x t / n00043_expression x t
def n00059_pair : RationalPair := ⟨[[-8172911, 11035247]], [[-16777216, 16777216]]⟩
def n00059_reduction : Reduction := ⟨rawDiv n00058_pair n00043_pair, n00059_pair, [[1]], 1⟩
theorem n00059_checked : checkReduction n00059_reduction = true := by decide
def n00060_expression (x t : ℝ) : ℝ := n00029_expression x t ^ 2
def n00060_pair : RationalPair := ⟨[[0, 0, 1], [0, 0, 2], [0, 0, 1]], [[4]]⟩
def n00060_reduction : Reduction := ⟨rawPow n00029_pair 2, n00060_pair, [[1]], 1⟩
theorem n00060_checked : checkReduction n00060_reduction = true := by decide
def n00061_expression (x t : ℝ) : ℝ := n00004_expression x t - n00029_expression x t
def n00061_pair : RationalPair := ⟨[[4, -1], [0, -1]], [[2]]⟩
def n00061_reduction : Reduction := ⟨rawSub n00004_pair n00029_pair, n00061_pair, [[1]], 1⟩
theorem n00061_checked : checkReduction n00061_reduction = true := by decide
def n00062_expression (x t : ℝ) : ℝ := (6 : ℝ)/(1 : ℝ)
def n00062_pair : RationalPair := ⟨[[6]], [[1]]⟩
def n00063_expression (x t : ℝ) : ℝ := (12 : ℝ)/(1 : ℝ)
def n00063_pair : RationalPair := ⟨[[12]], [[1]]⟩
def n00064_expression (x t : ℝ) : ℝ := n00063_expression x t * n00029_expression x t
def n00064_pair : RationalPair := ⟨[[0, 6], [0, 6]], [[1]]⟩
def n00064_reduction : Reduction := ⟨rawMul n00063_pair n00029_pair, n00064_pair, [[2]], 1⟩
theorem n00064_checked : checkReduction n00064_reduction = true := by decide
def n00065_expression (x t : ℝ) : ℝ := n00060_expression x t - n00064_expression x t
def n00065_pair : RationalPair := ⟨[[0, -24, 1], [0, -24, 2], [0, 0, 1]], [[4]]⟩
def n00065_reduction : Reduction := ⟨rawSub n00060_pair n00064_pair, n00065_pair, [[1]], 1⟩
theorem n00065_checked : checkReduction n00065_reduction = true := by decide
def n00066_expression (x t : ℝ) : ℝ := n00065_expression x t + n00063_expression x t
def n00066_pair : RationalPair := ⟨[[48, -24, 1], [0, -24, 2], [0, 0, 1]], [[4]]⟩
def n00066_reduction : Reduction := ⟨rawAdd n00065_pair n00063_pair, n00066_pair, [[1]], 1⟩
theorem n00066_checked : checkReduction n00066_reduction = true := by decide
def n00067_expression (x t : ℝ) : ℝ := n00029_expression x t * n00066_expression x t
def n00067_pair : RationalPair := ⟨[[0, 48, -24, 1], [0, 48, -48, 3], [0, 0, -24, 3], [0, 0, 0, 1]], [[8]]⟩
def n00067_reduction : Reduction := ⟨rawMul n00029_pair n00066_pair, n00067_pair, [[1]], 1⟩
theorem n00067_checked : checkReduction n00067_reduction = true := by decide
def n00068_expression (x t : ℝ) : ℝ := n00062_expression x t * n00030_expression x t
def n00068_pair : RationalPair := ⟨[[6, -3], [0, -3]], [[1]]⟩
def n00068_reduction : Reduction := ⟨rawMul n00062_pair n00030_pair, n00068_pair, [[2]], 1⟩
theorem n00068_checked : checkReduction n00068_reduction = true := by decide
def n00069_expression (x t : ℝ) : ℝ := n00068_expression x t * n00061_expression x t
def n00069_pair : RationalPair := ⟨[[24, -18, 3], [0, -18, 6], [0, 0, 3]], [[2]]⟩
def n00069_reduction : Reduction := ⟨rawMul n00068_pair n00061_pair, n00069_pair, [[1]], 1⟩
theorem n00069_checked : checkReduction n00069_reduction = true := by decide
def n00070_expression (x t : ℝ) : ℝ := n00067_expression x t / n00069_expression x t
def n00070_pair : RationalPair := ⟨[[0, 48, -24, 1], [0, 48, -48, 3], [0, 0, -24, 3], [0, 0, 0, 1]], [[96, -72, 12], [0, -72, 24], [0, 0, 12]]⟩
def n00070_reduction : Reduction := ⟨rawDiv n00067_pair n00069_pair, n00070_pair, [[2]], 1⟩
theorem n00070_checked : checkReduction n00070_reduction = true := by decide
def n00071_expression (x t : ℝ) : ℝ := n00033_expression x t / n00004_expression x t
def n00071_pair : RationalPair := ⟨[[0, -2, 1], [0, 0, 1]], [[-4, 0, 2], [0, 0, 2]]⟩
def n00071_reduction : Reduction := ⟨rawDiv n00033_pair n00004_pair, n00071_pair, [[1]], 1⟩
theorem n00071_checked : checkReduction n00071_reduction = true := by decide
def n00072_expression (x t : ℝ) : ℝ := n00006_expression x t - n00071_expression x t
def n00072_pair : RationalPair := ⟨[[-4, 2, 1], [0, 0, 1]], [[-4, 0, 2], [0, 0, 2]]⟩
def n00072_reduction : Reduction := ⟨rawSub n00006_pair n00071_pair, n00072_pair, [[1]], 1⟩
theorem n00072_checked : checkReduction n00072_reduction = true := by decide
def n00073_expression (x t : ℝ) : ℝ := n00033_expression x t * n00033_expression x t
def n00073_pair : RationalPair := ⟨[[0, 0, 4, -4, 1], [0, 0, 0, -4, 2], [0, 0, 0, 0, 1]], [[4, 0, -4, 0, 1], [0, 0, -4, 0, 2], [0, 0, 0, 0, 1]]⟩
def n00073_reduction : Reduction := ⟨rawMul n00033_pair n00033_pair, n00073_pair, [[1]], 1⟩
theorem n00073_checked : checkReduction n00073_reduction = true := by decide
def n00074_expression (x t : ℝ) : ℝ := n00073_expression x t / n00063_expression x t
def n00074_pair : RationalPair := ⟨[[0, 0, 4, -4, 1], [0, 0, 0, -4, 2], [0, 0, 0, 0, 1]], [[48, 0, -48, 0, 12], [0, 0, -48, 0, 24], [0, 0, 0, 0, 12]]⟩
def n00074_reduction : Reduction := ⟨rawDiv n00073_pair n00063_pair, n00074_pair, [[1]], 1⟩
theorem n00074_checked : checkReduction n00074_reduction = true := by decide
def n00075_expression (x t : ℝ) : ℝ := n00072_expression x t - n00074_expression x t
def n00075_pair : RationalPair := ⟨[[48, -24, -40, 16, 5], [0, 0, -36, 16, 10], [0, 0, 0, 0, 5]], [[48, 0, -48, 0, 12], [0, 0, -48, 0, 24], [0, 0, 0, 0, 12]]⟩
def n00075_reduction : Reduction := ⟨rawSub n00072_pair n00074_pair, n00075_pair, [[-4, 0, 2], [0, 0, 2]], 1⟩
theorem n00075_checked : checkReduction n00075_reduction = true := by decide
def n00076_expression (x t : ℝ) : ℝ := n00054_expression x t * n00075_expression x t
def n00076_pair : RationalPair := ⟨[[-256792368, 331944648, 112219408, -255221176, 41100283, 21202965], [0, 0, 192594276, -238258804, 14351078, 42405930], [0, 0, 0, 0, -26749205, 21202965]], [[-805306368, 805306368, 805306368, -805306368, -201326592, 201326592], [0, 0, 805306368, -805306368, -402653184, 402653184], [0, 0, 0, 0, -201326592, 201326592]]⟩
def n00076_reduction : Reduction := ⟨rawMul n00054_pair n00075_pair, n00076_pair, [[1]], 1⟩
theorem n00076_checked : checkReduction n00076_reduction = true := by decide
def n00077_expression (x t : ℝ) : ℝ := (7 : ℝ)/(10 : ℝ)
def n00077_pair : RationalPair := ⟨[[7]], [[10]]⟩
def n00078_expression (x t : ℝ) : ℝ := (5 : ℝ)/(6 : ℝ)
def n00078_pair : RationalPair := ⟨[[5]], [[6]]⟩
def n00079_expression (x t : ℝ) : ℝ := n00006_expression x t * n00034_expression x t
def n00079_pair : RationalPair := ⟨[[-2, 2]], [[-2, 0, 1], [0, 0, 1]]⟩
def n00079_reduction : Reduction := ⟨rawMul n00006_pair n00034_pair, n00079_pair, [[1]], 1⟩
theorem n00079_checked : checkReduction n00079_reduction = true := by decide
def n00080_expression (x t : ℝ) : ℝ := n00079_expression x t + n00076_expression x t
def n00080_pair : RationalPair := ⟨[[-1062098736, 1942557384, -290433776, -1060527544, 443753467, 21202965], [0, 0, 595247460, -1043565172, 417004262, 42405930], [0, 0, 0, 0, -26749205, 21202965]], [[-805306368, 805306368, 805306368, -805306368, -201326592, 201326592], [0, 0, 805306368, -805306368, -402653184, 402653184], [0, 0, 0, 0, -201326592, 201326592]]⟩
def n00080_reduction : Reduction := ⟨rawAdd n00079_pair n00076_pair, n00080_pair, [[-2, 0, 1], [0, 0, 1]], 1⟩
theorem n00080_checked : checkReduction n00080_reduction = true := by decide
def n00081_expression (x t : ℝ) : ℝ := n00054_expression x t - n00059_expression x t
def n00081_pair : RationalPair := ⟨[[1411535, -3397327]], [[-8388608, 8388608]]⟩
def n00081_reduction : Reduction := ⟨rawSub n00054_pair n00059_pair, n00081_pair, [[-33554432, 33554432]], 1⟩
theorem n00081_checked : checkReduction n00081_reduction = true := by decide
def n00082_expression (x t : ℝ) : ℝ := n00004_expression x t * n00081_expression x t
def n00082_pair : RationalPair := ⟨[[1411535, -3397327]], [[-4194304, 4194304]]⟩
def n00082_reduction : Reduction := ⟨rawMul n00004_pair n00081_pair, n00082_pair, [[2]], 1⟩
theorem n00082_checked : checkReduction n00082_reduction = true := by decide
def n00083_expression (x t : ℝ) : ℝ := n00082_expression x t * n00077_expression x t
def n00083_pair : RationalPair := ⟨[[9880745, -23781289]], [[-41943040, 41943040]]⟩
def n00083_reduction : Reduction := ⟨rawMul n00082_pair n00077_pair, n00083_pair, [[1]], 1⟩
theorem n00083_checked : checkReduction n00083_reduction = true := by decide
def n00084_expression (x t : ℝ) : ℝ := n00004_expression x t * n00080_expression x t
def n00084_pair : RationalPair := ⟨[[-1062098736, 1942557384, -290433776, -1060527544, 443753467, 21202965], [0, 0, 595247460, -1043565172, 417004262, 42405930], [0, 0, 0, 0, -26749205, 21202965]], [[-402653184, 402653184, 402653184, -402653184, -100663296, 100663296], [0, 0, 402653184, -402653184, -201326592, 201326592], [0, 0, 0, 0, -100663296, 100663296]]⟩
def n00084_reduction : Reduction := ⟨rawMul n00004_pair n00080_pair, n00084_pair, [[2]], 1⟩
theorem n00084_checked : checkReduction n00084_reduction = true := by decide
def n00085_expression (x t : ℝ) : ℝ := n00070_expression x t * n00077_expression x t
def n00085_pair : RationalPair := ⟨[[0, 336, -168, 7], [0, 336, -336, 21], [0, 0, -168, 21], [0, 0, 0, 7]], [[960, -720, 120], [0, -720, 240], [0, 0, 120]]⟩
def n00085_reduction : Reduction := ⟨rawMul n00070_pair n00077_pair, n00085_pair, [[1]], 1⟩
theorem n00085_checked : checkReduction n00085_reduction = true := by decide
def n00086_expression (x t : ℝ) : ℝ := n00006_expression x t - n00085_expression x t
def n00086_pair : RationalPair := ⟨[[960, -1056, 288, -7], [0, -1056, 576, -21], [0, 0, 288, -21], [0, 0, 0, -7]], [[960, -720, 120], [0, -720, 240], [0, 0, 120]]⟩
def n00086_reduction : Reduction := ⟨rawSub n00006_pair n00085_pair, n00086_pair, [[1]], 1⟩
theorem n00086_checked : checkReduction n00086_reduction = true := by decide
def n00087_expression (x t : ℝ) : ℝ := n00084_expression x t * n00086_expression x t
def n00087_pair : RationalPair := ⟨[[-1019614786560, 2986431353856, -2636041458432, -144517157040, 1448677585608, -751647710992, 112834360264, 3000179651, -148420755], [0, 1121576265216, -2091671907840, -182488688784, 2585593708056, -1777728726828, 338104265956, 12187963039, -742103775], [0, 0, -305884435968, -46820717712, 1294749489240, -1304681052900, 337306636284, 18750055646, -1484207550], [0, 0, 0, 7434691152, 157833366792, -282766769284, 111637915756, 13124185214, -1484207550], [0, 0, 0, 0, 0, -4166732220, -398814836, 3749157391, -742103775], [0, 0, 0, 0, 0, 0, 0, 187244435, -148420755]], [[-386547056640, 676457349120, 48318382080, -628138967040, 241591910400, 120795955200, -84557168640, 12079595520], [0, 289910292480, 0, -869730877440, 531502202880, 265751101440, -265751101440, 48318382080], [0, 0, -48318382080, -241591910400, 338228674560, 169114337280, -289910292480, 72477573120], [0, 0, 0, 0, 48318382080, 24159191040, -120795955200, 48318382080], [0, 0, 0, 0, 0, 0, -12079595520, 12079595520]]⟩
def n00087_reduction : Reduction := ⟨rawMul n00084_pair n00086_pair, n00087_pair, [[1]], 1⟩
theorem n00087_checked : checkReduction n00087_reduction = true := by decide
def n00088_expression (x t : ℝ) : ℝ := n00087_expression x t - n00044_expression x t
def n00088_pair : RationalPair := ⟨[[-812395100160, 2671914744576, -2698032300672, 150111721680, 1355253663048, -810389132752, 149141571304, -1971752989, -148420755], [0, 966161500416, -2127760289280, 247667224176, 2372843402136, -1914177530988, 453501514276, -7699767521, -742103775], [0, 0, -279981975168, 88706316528, 1149520645080, -1401354395940, 465655115004, -11081540194, -1484207550], [0, 0, 0, 7434691152, 131930905992, -301732729924, 167371972396, -6763545346, -1484207550], [0, 0, 0, 0, 0, -4166732220, 6076800364, -1222775249, -742103775], [0, 0, 0, 0, 0, 0, 0, 187244435, -148420755]], [[-386547056640, 676457349120, 48318382080, -628138967040, 241591910400, 120795955200, -84557168640, 12079595520], [0, 289910292480, 0, -869730877440, 531502202880, 265751101440, -265751101440, 48318382080], [0, 0, -48318382080, -241591910400, 338228674560, 169114337280, -289910292480, 72477573120], [0, 0, 0, 0, 48318382080, 24159191040, -120795955200, 48318382080], [0, 0, 0, 0, 0, 0, -12079595520, 12079595520]]⟩
def n00088_reduction : Reduction := ⟨rawSub n00087_pair n00044_pair, n00088_pair, [[-8388608, 8388608]], 1⟩
theorem n00088_checked : checkReduction n00088_reduction = true := by decide
def n00089_expression (x t : ℝ) : ℝ := n00088_expression x t - n00049_expression x t
def n00089_pair : RationalPair := ⟨[[-1188744721920, 3573917456256, -2833531753152, -674423428080, 1773015331848, -662356016752, 21179302744, 17395137491, -148420755], [0, 1248423716736, -2310303444480, -781662579984, 3255410442456, -1625013306828, 57853782916, 69767794399, -742103775], [0, 0, -327025677888, -116088337872, 1661369719320, -1267125295620, 46485532284, 105119802686, -1484207550], [0, 0, 0, 7434691152, 178974608712, -308634737764, 4126926796, 70704016574, -1484207550], [0, 0, 0, 0, 0, -4166732220, -5684125316, 18144115231, -742103775], [0, 0, 0, 0, 0, 0, 0, 187244435, -148420755]], [[-386547056640, 676457349120, 48318382080, -628138967040, 241591910400, 120795955200, -84557168640, 12079595520], [0, 289910292480, 0, -869730877440, 531502202880, 265751101440, -265751101440, 48318382080], [0, 0, -48318382080, -241591910400, 338228674560, 169114337280, -289910292480, 72477573120], [0, 0, 0, 0, 48318382080, 24159191040, -120795955200, 48318382080], [0, 0, 0, 0, 0, 0, -12079595520, 12079595520]]⟩
def n00089_reduction : Reduction := ⟨rawSub n00088_pair n00049_pair, n00089_pair, [[-16777216, 16777216]], 1⟩
theorem n00089_checked : checkReduction n00089_reduction = true := by decide
def n00090_expression (x t : ℝ) : ℝ := n00033_expression x t * n00089_expression x t
def n00090_pair : RationalPair := ⟨[[0, -1188744721920, 3573917456256, -2833531753152, -674423428080, 1773015331848, -662356016752, 21179302744, 17395137491, -148420755], [0, 0, 1248423716736, -2310303444480, -781662579984, 3255410442456, -1625013306828, 57853782916, 69767794399, -742103775], [0, 0, 0, -327025677888, -116088337872, 1661369719320, -1267125295620, 46485532284, 105119802686, -1484207550], [0, 0, 0, 0, 7434691152, 178974608712, -308634737764, 4126926796, 70704016574, -1484207550], [0, 0, 0, 0, 0, 0, -4166732220, -5684125316, 18144115231, -742103775], [0, 0, 0, 0, 0, 0, 0, 0, 187244435, -148420755]], [[-386547056640, 483183820800, 483183820800, -724775731200, -144955146240, 362387865600, -24159191040, -60397977600, 12079595520], [0, 96636764160, 483183820800, -869730877440, -289910292480, 797253304320, -72477573120, -193273528320, 48318382080], [0, 0, 0, -144955146240, -144955146240, 507343011840, -72477573120, -217432719360, 72477573120], [0, 0, 0, 0, 0, 72477573120, -24159191040, -96636764160, 48318382080], [0, 0, 0, 0, 0, 0, 0, -12079595520, 12079595520]]⟩
def n00090_reduction : Reduction := ⟨rawMul n00033_pair n00089_pair, n00090_pair, [[-2, 1], [0, 1]], 1⟩
theorem n00090_checked : checkReduction n00090_reduction = true := by decide
def n00091_expression (x t : ℝ) : ℝ := n00083_expression x t + n00090_expression x t
def n00091_pair : RationalPair := ⟨[[91060945920, -1430678317824, 3492118127232, -2470631359296, -688315853424, 1591565134920, -632644567600, 51421002232, 10546126259, -148420755], [0, -22765236480, 1166624387712, -1913255195904, -809447430672, 2875436121240, -1535878959372, 151424535940, 42371749471, -742103775], [0, 0, 0, -292877823168, -129980763216, 1445771667672, -1177990948164, 145747594428, 64025735294, -1484207550], [0, 0, 0, 0, 7434691152, 161900681352, -278923288612, 42905589964, 43307971646, -1484207550], [0, 0, 0, 0, 0, 0, -4166732220, -2838470756, 11295103999, -742103775], [0, 0, 0, 0, 0, 0, 0, 0, 187244435, -148420755]], [[-386547056640, 483183820800, 483183820800, -724775731200, -144955146240, 362387865600, -24159191040, -60397977600, 12079595520], [0, 96636764160, 483183820800, -869730877440, -289910292480, 797253304320, -72477573120, -193273528320, 48318382080], [0, 0, 0, -144955146240, -144955146240, 507343011840, -72477573120, -217432719360, 72477573120], [0, 0, 0, 0, 0, 72477573120, -24159191040, -96636764160, 48318382080], [0, 0, 0, 0, 0, 0, 0, -12079595520, 12079595520]]⟩
def n00091_reduction : Reduction := ⟨rawAdd n00083_pair n00090_pair, n00091_pair, [[-41943040, 41943040]], 1⟩
theorem n00091_checked : checkReduction n00091_reduction = true := by decide
def n00092_expression (x t : ℝ) : ℝ := n00037_expression x t * n00034_expression x t
def n00092_pair : RationalPair := ⟨[[-2, 2]], [[-2, -2, 1], [0, 0, 1]]⟩
def n00092_reduction : Reduction := ⟨rawMul n00037_pair n00034_pair, n00092_pair, [[-2, 0, 1], [0, 0, 1]], 1⟩
theorem n00092_checked : checkReduction n00092_reduction = true := by decide
def n00093_expression (x t : ℝ) : ℝ := n00092_expression x t + n00076_expression x t
def n00093_pair : RationalPair := ⟨[[2124197472, -3371530032, -1145120480, 3839173656, -667498358, -1185134040, 401347537, 21202965], [0, 0, -2252593656, 3644499176, -52677232, -2217606732, 775945869, 63608895], [0, 0, 0, 0, 648745870, -1032472692, 347849127, 63608895], [0, 0, 0, 0, 0, 0, -26749205, 21202965]], [[1610612736, 0, -4026531840, 805306368, 2818572288, -805306368, -603979776, 201326592], [0, 0, -2415919104, 805306368, 4026531840, -1610612736, -1409286144, 603979776], [0, 0, 0, 0, 1207959552, -805306368, -1006632960, 603979776], [0, 0, 0, 0, 0, 0, -201326592, 201326592]]⟩
def n00093_reduction : Reduction := ⟨rawAdd n00092_pair n00076_pair, n00093_pair, [[1]], 1⟩
theorem n00093_checked : checkReduction n00093_reduction = true := by decide
def n00094_expression (x t : ℝ) : ℝ := n00004_expression x t * n00093_expression x t
def n00094_pair : RationalPair := ⟨[[2124197472, -3371530032, -1145120480, 3839173656, -667498358, -1185134040, 401347537, 21202965], [0, 0, -2252593656, 3644499176, -52677232, -2217606732, 775945869, 63608895], [0, 0, 0, 0, 648745870, -1032472692, 347849127, 63608895], [0, 0, 0, 0, 0, 0, -26749205, 21202965]], [[805306368, 0, -2013265920, 402653184, 1409286144, -402653184, -301989888, 100663296], [0, 0, -1207959552, 402653184, 2013265920, -805306368, -704643072, 301989888], [0, 0, 0, 0, 603979776, -402653184, -503316480, 301989888], [0, 0, 0, 0, 0, 0, -100663296, 100663296]]⟩
def n00094_reduction : Reduction := ⟨rawMul n00004_pair n00093_pair, n00094_pair, [[2]], 1⟩
theorem n00094_checked : checkReduction n00094_reduction = true := by decide
def n00095_expression (x t : ℝ) : ℝ := n00094_expression x t * n00086_expression x t
def n00095_pair : RationalPair := ⟨[[2039229573120, -5479821361152, 3072788924928, 3908983905120, -5001159792432, 680847443936, 1417681439064, -740114267686, 101493697896, 3297021161, -148420755], [0, -2243152530432, 2621383547904, 5100095891232, -9190862892048, 1932398434536, 3832418051440, -2489079037250, 405498329388, 16672350240, -890524530], [0, 0, 611768871936, 1363130104608, -4782281608080, 1655643269112, 3573119102016, -3031092726724, 607056338592, 33906433785, -2226311325], [0, 0, 0, -14869382304, -625146262704, 419860434104, 1319709805968, -1559946633532, 403116018408, 34842655960, -2968415100], [0, 0, 0, 0, 0, 15768155592, 161327316328, -282359897462, 99587849112, 18357550155, -2226311325], [0, 0, 0, 0, 0, 0, 0, -4541221090, -476462196, 4233243336, -890524530], [0, 0, 0, 0, 0, 0, 0, 0, 0, 187244435, -148420755]], [[773094113280, -579820584960, -1836098519040, 1836098519040, 821412495360, -1352914698240, 169114337280, 265751101440, -108716359680, 12079595520], [0, -579820584960, -966367641600, 2705829396480, 724775731200, -3092376453120, 773094113280, 821412495360, -446945034240, 60397977600], [0, 0, 96636764160, 869730877440, -241591910400, -2126008811520, 1111322787840, 869730877440, -700616540160, 120795955200], [0, 0, 0, 0, -144955146240, -386547056640, 579820584960, 338228674560, -507343011840, 120795955200], [0, 0, 0, 0, 0, 0, 72477573120, 24159191040, -157034741760, 60397977600], [0, 0, 0, 0, 0, 0, 0, 0, -12079595520, 12079595520]]⟩
def n00095_reduction : Reduction := ⟨rawMul n00094_pair n00086_pair, n00095_pair, [[1]], 1⟩
theorem n00095_checked : checkReduction n00095_reduction = true := by decide
def n00096_expression (x t : ℝ) : ℝ := n00095_expression x t - n00044_expression x t
def n00096_pair : RationalPair := ⟨[[1624790200320, -5265227515392, 4033023514368, 3129191222880, -5465560546992, 1279807011296, 1369125937944, -861526246246, 147744774216, -1674911479, -148420755], [0, -1932323000832, 3211609526784, 3842029454112, -9723753329808, 3355581446376, 3568346934640, -2875288298690, 596978249868, -8187312960, -890524530], [0, 0, 559963950336, 884856349728, -4773063908880, 2705130590712, 3151789680576, -3461248639684, 910465257312, -15812892615, -2226311325], [0, 0, 0, -14869382304, -547438880304, 645124311224, 1075042309008, -1747278589372, 626974014888, -14876670440, -2968415100], [0, 0, 0, 0, 0, 15768155592, 122473625128, -304333223222, 171741386232, -6502113045, -2226311325], [0, 0, 0, 0, 0, 0, 0, -4541221090, 5999153004, -738689304, -890524530], [0, 0, 0, 0, 0, 0, 0, 0, 0, 187244435, -148420755]], [[773094113280, -579820584960, -1836098519040, 1836098519040, 821412495360, -1352914698240, 169114337280, 265751101440, -108716359680, 12079595520], [0, -579820584960, -966367641600, 2705829396480, 724775731200, -3092376453120, 773094113280, 821412495360, -446945034240, 60397977600], [0, 0, 96636764160, 869730877440, -241591910400, -2126008811520, 1111322787840, 869730877440, -700616540160, 120795955200], [0, 0, 0, 0, -144955146240, -386547056640, 579820584960, 338228674560, -507343011840, 120795955200], [0, 0, 0, 0, 0, 0, 72477573120, 24159191040, -157034741760, 60397977600], [0, 0, 0, 0, 0, 0, 0, 0, -12079595520, 12079595520]]⟩
def n00096_reduction : Reduction := ⟨rawSub n00095_pair n00044_pair, n00096_pair, [[-8388608, 8388608]], 1⟩
theorem n00096_checked : checkReduction n00096_reduction = true := by decide
def n00097_expression (x t : ℝ) : ℝ := n00096_expression x t - n00049_expression x t
def n00097_pair : RationalPair := ⟨[[2377489443840, -6316533695232, 2123667374208, 5951263139040, -4787513037552, -676317708064, 1746745911864, -496302374086, -18951275304, 17691979001, -148420755], [0, -2496847433472, 2635821782784, 7450040300832, -9748270409808, -841746036504, 5081642658160, -1801730619650, -81566873892, 88647139440, -890524530], [0, 0, 654051355776, 1670795280288, -5616759606480, 178849783032, 5116086759936, -2431918835524, -136754742528, 177856012185, -2226311325], [0, 0, 0, -14869382304, -688569988464, 360046267064, 1974229192848, -1448396529532, -110375737272, 178792234360, -2968415100], [0, 0, 0, 0, 0, 15768155592, 193039179208, -326447160662, -41998366008, 90332339355, -2226311325], [0, 0, 0, 0, 0, 0, 0, -4541221090, -5761772676, 18628201176, -890524530], [0, 0, 0, 0, 0, 0, 0, 0, 0, 187244435, -148420755]], [[773094113280, -579820584960, -1836098519040, 1836098519040, 821412495360, -1352914698240, 169114337280, 265751101440, -108716359680, 12079595520], [0, -579820584960, -966367641600, 2705829396480, 724775731200, -3092376453120, 773094113280, 821412495360, -446945034240, 60397977600], [0, 0, 96636764160, 869730877440, -241591910400, -2126008811520, 1111322787840, 869730877440, -700616540160, 120795955200], [0, 0, 0, 0, -144955146240, -386547056640, 579820584960, 338228674560, -507343011840, 120795955200], [0, 0, 0, 0, 0, 0, 72477573120, 24159191040, -157034741760, 60397977600], [0, 0, 0, 0, 0, 0, 0, 0, -12079595520, 12079595520]]⟩
def n00097_reduction : Reduction := ⟨rawSub n00096_pair n00049_pair, n00097_pair, [[-16777216, 16777216]], 1⟩
theorem n00097_checked : checkReduction n00097_reduction = true := by decide
def n00098_expression (x t : ℝ) : ℝ := n00033_expression x t * n00097_expression x t
def n00098_pair : RationalPair := ⟨[[0, 2377489443840, -6316533695232, 2123667374208, 5951263139040, -4787513037552, -676317708064, 1746745911864, -496302374086, -18951275304, 17691979001, -148420755], [0, 0, -2496847433472, 2635821782784, 7450040300832, -9748270409808, -841746036504, 5081642658160, -1801730619650, -81566873892, 88647139440, -890524530], [0, 0, 0, 654051355776, 1670795280288, -5616759606480, 178849783032, 5116086759936, -2431918835524, -136754742528, 177856012185, -2226311325], [0, 0, 0, 0, -14869382304, -688569988464, 360046267064, 1974229192848, -1448396529532, -110375737272, 178792234360, -2968415100], [0, 0, 0, 0, 0, 0, 15768155592, 193039179208, -326447160662, -41998366008, 90332339355, -2226311325], [0, 0, 0, 0, 0, 0, 0, 0, -4541221090, -5761772676, 18628201176, -890524530], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 187244435, -148420755]], [[773094113280, -193273528320, -2319282339840, 966367641600, 2222645575680, -1159641169920, -821412495360, 531502202880, 72477573120, -84557168640, 12079595520], [0, -193273528320, -1546188226560, 1352914698240, 3285649981440, -2609192632320, -1884416901120, 1691143372800, 193273528320, -350308270080, 60397977600], [0, 0, 0, 386547056640, 1063004405760, -1739461754880, -1304596316160, 1884416901120, 144955146240, -555661393920, 120795955200], [0, 0, 0, 0, 0, -289910292480, -241591910400, 821412495360, 0, -410706247680, 120795955200], [0, 0, 0, 0, 0, 0, 0, 96636764160, -24159191040, -132875550720, 60397977600], [0, 0, 0, 0, 0, 0, 0, 0, 0, -12079595520, 12079595520]]⟩
def n00098_reduction : Reduction := ⟨rawMul n00033_pair n00097_pair, n00098_pair, [[-2, 1], [0, 1]], 1⟩
theorem n00098_checked : checkReduction n00098_reduction = true := by decide
def n00099_expression (x t : ℝ) : ℝ := n00083_expression x t + n00098_expression x t
def n00099_pair : RationalPair := ⟨[[-182121891840, 2679234743808, -5578006899456, 1319531648640, 5171447872992, -4033927399152, -386732637856, 1445389417656, -513376301446, 24988446648, 10842967769, -148420755], [0, 45530472960, -2196657356544, 1740625111296, 6547914847008, -8172803423568, -301743365016, 4154807939056, -1815234239234, 97037668476, 54402083280, -890524530], [0, 0, 0, 562990409856, 1548485092512, -4726582549200, 390099915384, 4143721567872, -2369986130116, 138266207424, 109365899865, -2226311325], [0, 0, 0, 0, -14869382304, -620274279024, 320878798136, 1604576989200, -1352315969404, 82457077896, 110302122040, -2968415100], [0, 0, 0, 0, 0, 0, 15768155592, 170273942728, -288728998166, 13323974184, 56087283195, -2226311325], [0, 0, 0, 0, 0, 0, 0, 0, -4541221090, -2916118116, 11779189944, -890524530], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 187244435, -148420755]], [[773094113280, -193273528320, -2319282339840, 966367641600, 2222645575680, -1159641169920, -821412495360, 531502202880, 72477573120, -84557168640, 12079595520], [0, -193273528320, -1546188226560, 1352914698240, 3285649981440, -2609192632320, -1884416901120, 1691143372800, 193273528320, -350308270080, 60397977600], [0, 0, 0, 386547056640, 1063004405760, -1739461754880, -1304596316160, 1884416901120, 144955146240, -555661393920, 120795955200], [0, 0, 0, 0, 0, -289910292480, -241591910400, 821412495360, 0, -410706247680, 120795955200], [0, 0, 0, 0, 0, 0, 0, 96636764160, -24159191040, -132875550720, 60397977600], [0, 0, 0, 0, 0, 0, 0, 0, 0, -12079595520, 12079595520]]⟩
def n00099_reduction : Reduction := ⟨rawAdd n00083_pair n00098_pair, n00099_pair, [[-41943040, 41943040]], 1⟩
theorem n00099_checked : checkReduction n00099_reduction = true := by decide
def n00100_expression (x t : ℝ) : ℝ := n00082_expression x t * n00078_expression x t
def n00100_pair : RationalPair := ⟨[[7057675, -16986635]], [[-25165824, 25165824]]⟩
def n00100_reduction : Reduction := ⟨rawMul n00082_pair n00078_pair, n00100_pair, [[1]], 1⟩
theorem n00100_checked : checkReduction n00100_reduction = true := by decide
def n00101_expression (x t : ℝ) : ℝ := n00070_expression x t * n00078_expression x t
def n00101_pair : RationalPair := ⟨[[0, 240, -120, 5], [0, 240, -240, 15], [0, 0, -120, 15], [0, 0, 0, 5]], [[576, -432, 72], [0, -432, 144], [0, 0, 72]]⟩
def n00101_reduction : Reduction := ⟨rawMul n00070_pair n00078_pair, n00101_pair, [[1]], 1⟩
theorem n00101_checked : checkReduction n00101_reduction = true := by decide
def n00102_expression (x t : ℝ) : ℝ := n00006_expression x t - n00101_expression x t
def n00102_pair : RationalPair := ⟨[[576, -672, 192, -5], [0, -672, 384, -15], [0, 0, 192, -15], [0, 0, 0, -5]], [[576, -432, 72], [0, -432, 144], [0, 0, 72]]⟩
def n00102_reduction : Reduction := ⟨rawSub n00006_pair n00101_pair, n00102_pair, [[1]], 1⟩
theorem n00102_checked : checkReduction n00102_reduction = true := by decide
def n00103_expression (x t : ℝ) : ℝ := n00084_expression x t * n00102_expression x t
def n00103_pair : RationalPair := ⟨[[-611768871936, 1832643403776, -1676611374336, -37410856464, 902800434648, -488158541552, 76254910904, 1852201945, -106014825], [0, 713730350592, -1370381939712, -44054818224, 1627767341640, -1160230198788, 228846711212, 7542553805, -530074125], [0, 0, -203922957312, -11103794352, 829541632392, -858961010220, 229010668212, 11648195770, -1060148250], [0, 0, 0, 5310493680, 104574725400, -189865590284, 76500846404, 8211283930, -1060148250], [0, 0, 0, 0, 0, -2976237300, 81978500, 2387186045, -530074125], [0, 0, 0, 0, 0, 0, 0, 133746025, -106014825]], [[-231928233984, 405874409472, 28991029248, -376883380224, 144955146240, 72477573120, -50734301184, 7247757312], [0, 173946175488, 0, -521838526464, 318901321728, 159450660864, -159450660864, 28991029248], [0, 0, -28991029248, -144955146240, 202937204736, 101468602368, -173946175488, 43486543872], [0, 0, 0, 0, 28991029248, 14495514624, -72477573120, 28991029248], [0, 0, 0, 0, 0, 0, -7247757312, 7247757312]]⟩
def n00103_reduction : Reduction := ⟨rawMul n00084_pair n00102_pair, n00103_pair, [[1]], 1⟩
theorem n00103_checked : checkReduction n00103_reduction = true := by decide
def n00104_expression (x t : ℝ) : ℝ := n00103_expression x t - n00044_expression x t
def n00104_pair : RationalPair := ⟨[[-487437060096, 1643933438208, -1713805879680, 139366470768, 846746081112, -523403394608, 98039237528, -1130957639, -106014825], [0, 620481491712, -1392034968576, 214038729552, 1500117158088, -1242099481284, 298085060204, -4390084531, -530074125], [0, 0, -188381480832, 70212426192, 742404325896, -916965016044, 306019755444, -6250761734, -1060148250], [0, 0, 0, 5310493680, 89033248920, -201245166668, 109941280388, -3721354406, -1060148250], [0, 0, 0, 0, 0, -2976237300, 3967347620, -595973539, -530074125], [0, 0, 0, 0, 0, 0, 0, 133746025, -106014825]], [[-231928233984, 405874409472, 28991029248, -376883380224, 144955146240, 72477573120, -50734301184, 7247757312], [0, 173946175488, 0, -521838526464, 318901321728, 159450660864, -159450660864, 28991029248], [0, 0, -28991029248, -144955146240, 202937204736, 101468602368, -173946175488, 43486543872], [0, 0, 0, 0, 28991029248, 14495514624, -72477573120, 28991029248], [0, 0, 0, 0, 0, 0, -7247757312, 7247757312]]⟩
def n00104_reduction : Reduction := ⟨rawSub n00103_pair n00044_pair, n00104_pair, [[-8388608, 8388608]], 1⟩
theorem n00104_checked : checkReduction n00104_reduction = true := by decide
def n00105_expression (x t : ℝ) : ℝ := n00104_expression x t - n00049_expression x t
def n00105_pair : RationalPair := ⟨[[-713246833152, 2185135065216, -1795105551168, -355354619088, 1097403082392, -434583525008, 21261876392, 10489176649, -106014825], [0, 789838821504, -1501560861696, -403559152944, 2029657382280, -1068600946788, 60696421388, 42090452621, -530074125], [0, 0, -216607702464, -52664366448, 1049513770440, -836427555852, 54518005812, 63470043994, -1060148250], [0, 0, 0, 5310493680, 117259470552, -205386371372, 11994253028, 42759182746, -1060148250], [0, 0, 0, 0, 0, -2976237300, -3089207788, 11024160749, -530074125], [0, 0, 0, 0, 0, 0, 0, 133746025, -106014825]], [[-231928233984, 405874409472, 28991029248, -376883380224, 144955146240, 72477573120, -50734301184, 7247757312], [0, 173946175488, 0, -521838526464, 318901321728, 159450660864, -159450660864, 28991029248], [0, 0, -28991029248, -144955146240, 202937204736, 101468602368, -173946175488, 43486543872], [0, 0, 0, 0, 28991029248, 14495514624, -72477573120, 28991029248], [0, 0, 0, 0, 0, 0, -7247757312, 7247757312]]⟩
def n00105_reduction : Reduction := ⟨rawSub n00104_pair n00049_pair, n00105_pair, [[-16777216, 16777216]], 1⟩
theorem n00105_checked : checkReduction n00105_reduction = true := by decide
def n00106_expression (x t : ℝ) : ℝ := n00033_expression x t * n00105_expression x t
def n00106_pair : RationalPair := ⟨[[0, -713246833152, 2185135065216, -1795105551168, -355354619088, 1097403082392, -434583525008, 21261876392, 10489176649, -106014825], [0, 0, 789838821504, -1501560861696, -403559152944, 2029657382280, -1068600946788, 60696421388, 42090452621, -530074125], [0, 0, 0, -216607702464, -52664366448, 1049513770440, -836427555852, 54518005812, 63470043994, -1060148250], [0, 0, 0, 0, 5310493680, 117259470552, -205386371372, 11994253028, 42759182746, -1060148250], [0, 0, 0, 0, 0, 0, -2976237300, -3089207788, 11024160749, -530074125], [0, 0, 0, 0, 0, 0, 0, 0, 133746025, -106014825]], [[-231928233984, 289910292480, 289910292480, -434865438720, -86973087744, 217432719360, -14495514624, -36238786560, 7247757312], [0, 57982058496, 289910292480, -521838526464, -173946175488, 478351982592, -43486543872, -115964116992, 28991029248], [0, 0, 0, -86973087744, -86973087744, 304405807104, -43486543872, -130459631616, 43486543872], [0, 0, 0, 0, 0, 43486543872, -14495514624, -57982058496, 28991029248], [0, 0, 0, 0, 0, 0, 0, -7247757312, 7247757312]]⟩
def n00106_reduction : Reduction := ⟨rawMul n00033_pair n00105_pair, n00106_pair, [[-2, 1], [0, 1]], 1⟩
theorem n00106_checked : checkReduction n00106_reduction = true := by decide
def n00107_expression (x t : ℝ) : ℝ := n00100_expression x t + n00106_expression x t
def n00107_pair : RationalPair := ⟨[[65043532800, -886056544512, 2126706973056, -1535890984128, -365277780048, 967795798872, -413361061328, 42863090312, 5597025769, -106014825], [0, -16260883200, 731410729344, -1217954969856, -423405474864, 1758247152840, -1004933555748, 127532673548, 22521849101, -530074125], [0, 0, 0, -192216377664, -62587527408, 895515162120, -772760164812, 125419478772, 34117138714, -1060148250], [0, 0, 0, 0, 5310493680, 105063808152, -184163907692, 39693298148, 23190579226, -1060148250], [0, 0, 0, 0, 0, 0, -2976237300, -1056597388, 6132009869, -530074125], [0, 0, 0, 0, 0, 0, 0, 0, 133746025, -106014825]], [[-231928233984, 289910292480, 289910292480, -434865438720, -86973087744, 217432719360, -14495514624, -36238786560, 7247757312], [0, 57982058496, 289910292480, -521838526464, -173946175488, 478351982592, -43486543872, -115964116992, 28991029248], [0, 0, 0, -86973087744, -86973087744, 304405807104, -43486543872, -130459631616, 43486543872], [0, 0, 0, 0, 0, 43486543872, -14495514624, -57982058496, 28991029248], [0, 0, 0, 0, 0, 0, 0, -7247757312, 7247757312]]⟩
def n00107_reduction : Reduction := ⟨rawAdd n00100_pair n00106_pair, n00107_pair, [[-25165824, 25165824]], 1⟩
theorem n00107_checked : checkReduction n00107_reduction = true := by decide
def n00108_expression (x t : ℝ) : ℝ := n00094_expression x t * n00102_expression x t
def n00108_pair : RationalPair := ⟨[[1223537743872, -3369461999616, 2013924699648, 2322930234912, -3167409233040, 508768633888, 880230703176, -481700880914, 68736004824, 2064231595, -106014825], [0, -1427460701184, 1783866064896, 3055964930400, -5881021524528, 1409042820024, 2391343120592, -1625098547686, 274970535396, 10454904000, -636088950], [0, 0, 407845914624, 834546208608, -3109711970736, 1192312342248, 2248330842816, -1988334086924, 412522093344, 21311046075, -1590222375], [0, 0, 0, -10620987360, -415640331792, 303301124392, 843555136560, -1031419783796, 275103115896, 21979776200, -2120296500], [0, 0, 0, 0, 0, 11262968280, 106336711160, -189727092994, 68842069224, 11658618225, -1590222375], [0, 0, 0, 0, 0, 0, 0, -3243729350, 26516100, 2732961720, -636088950], [0, 0, 0, 0, 0, 0, 0, 0, 0, 133746025, -106014825]], [[463856467968, -347892350976, -1101659111424, 1101659111424, 492847497216, -811748818944, 101468602368, 159450660864, -65229815808, 7247757312], [0, -347892350976, -579820584960, 1623497637888, 434865438720, -1855425871872, 463856467968, 492847497216, -268167020544, 36238786560], [0, 0, 57982058496, 521838526464, -144955146240, -1275605286912, 666793672704, 521838526464, -420369924096, 72477573120], [0, 0, 0, 0, -86973087744, -231928233984, 347892350976, 202937204736, -304405807104, 72477573120], [0, 0, 0, 0, 0, 0, 43486543872, 14495514624, -94220845056, 36238786560], [0, 0, 0, 0, 0, 0, 0, 0, -7247757312, 7247757312]]⟩
def n00108_reduction : Reduction := ⟨rawMul n00094_pair n00102_pair, n00108_pair, [[1]], 1⟩
theorem n00108_checked : checkReduction n00108_reduction = true := by decide
def n00109_expression (x t : ℝ) : ℝ := n00108_expression x t - n00044_expression x t
def n00109_pair : RationalPair := ⟨[[974874120192, -3240705692160, 2590065453312, 1855054625568, -3446049685776, 868144374304, 851097402504, -554548068050, 96486650616, -918927989, -106014825], [0, -1240962983424, 2138001652224, 2301125068128, -6200755787184, 2262952627128, 2232900450512, -1856824104550, 389858487684, -4460893920, -636088950], [0, 0, 376762961664, 547581955680, -3104181351216, 1822004735208, 1995533189952, -2246427634700, 594567444576, -8520549765, -1590222375], [0, 0, 0, -10620987360, -369015902352, 438459450664, 696754638384, -1143818957300, 409417913784, -7851819640, -2120296500], [0, 0, 0, 0, 0, 11262968280, 83024496440, -202911088450, 112134191496, -3257179695, -1590222375], [0, 0, 0, 0, 0, 0, 0, -3243729350, 3911885220, -250197864, -636088950], [0, 0, 0, 0, 0, 0, 0, 0, 0, 133746025, -106014825]], [[463856467968, -347892350976, -1101659111424, 1101659111424, 492847497216, -811748818944, 101468602368, 159450660864, -65229815808, 7247757312], [0, -347892350976, -579820584960, 1623497637888, 434865438720, -1855425871872, 463856467968, 492847497216, -268167020544, 36238786560], [0, 0, 57982058496, 521838526464, -144955146240, -1275605286912, 666793672704, 521838526464, -420369924096, 72477573120], [0, 0, 0, 0, -86973087744, -231928233984, 347892350976, 202937204736, -304405807104, 72477573120], [0, 0, 0, 0, 0, 0, 43486543872, 14495514624, -94220845056, 36238786560], [0, 0, 0, 0, 0, 0, 0, 0, -7247757312, 7247757312]]⟩
def n00109_reduction : Reduction := ⟨rawSub n00108_pair n00044_pair, n00109_pair, [[-8388608, 8388608]], 1⟩
theorem n00109_checked : checkReduction n00109_reduction = true := by decide
def n00110_expression (x t : ℝ) : ℝ := n00109_expression x t - n00049_expression x t
def n00110_pair : RationalPair := ⟨[[1426493666304, -3871489400064, 1444451769216, 3548297775264, -3039221180112, -305530457312, 1077669386856, -335413744754, -3530979096, 10701206299, -106014825], [0, -1579677643008, 1792529005824, 4465931576160, -6215466035184, -255443862600, 3140877884624, -1212689497126, -17268586572, 53639777520, -636088950], [0, 0, 433215404928, 1019145314016, -3610398769776, 306236250600, 3174111437568, -1628829752204, -33764555328, 107680793115, -1590222375], [0, 0, 0, -10620987360, -453694567248, 267412624168, 1236266768688, -964489721396, -32991937512, 108349523240, -2120296500], [0, 0, 0, 0, 0, 11262968280, 125363828888, -216179450914, -16109659848, 54843491745, -1590222375], [0, 0, 0, 0, 0, 0, 0, -3243729350, -3144670188, 11369936424, -636088950], [0, 0, 0, 0, 0, 0, 0, 0, 0, 133746025, -106014825]], [[463856467968, -347892350976, -1101659111424, 1101659111424, 492847497216, -811748818944, 101468602368, 159450660864, -65229815808, 7247757312], [0, -347892350976, -579820584960, 1623497637888, 434865438720, -1855425871872, 463856467968, 492847497216, -268167020544, 36238786560], [0, 0, 57982058496, 521838526464, -144955146240, -1275605286912, 666793672704, 521838526464, -420369924096, 72477573120], [0, 0, 0, 0, -86973087744, -231928233984, 347892350976, 202937204736, -304405807104, 72477573120], [0, 0, 0, 0, 0, 0, 43486543872, 14495514624, -94220845056, 36238786560], [0, 0, 0, 0, 0, 0, 0, 0, -7247757312, 7247757312]]⟩
def n00110_reduction : Reduction := ⟨rawSub n00109_pair n00049_pair, n00110_pair, [[-16777216, 16777216]], 1⟩
theorem n00110_checked : checkReduction n00110_reduction = true := by decide
def n00111_expression (x t : ℝ) : ℝ := n00033_expression x t * n00110_expression x t
def n00111_pair : RationalPair := ⟨[[0, 1426493666304, -3871489400064, 1444451769216, 3548297775264, -3039221180112, -305530457312, 1077669386856, -335413744754, -3530979096, 10701206299, -106014825], [0, 0, -1579677643008, 1792529005824, 4465931576160, -6215466035184, -255443862600, 3140877884624, -1212689497126, -17268586572, 53639777520, -636088950], [0, 0, 0, 433215404928, 1019145314016, -3610398769776, 306236250600, 3174111437568, -1628829752204, -33764555328, 107680793115, -1590222375], [0, 0, 0, 0, -10620987360, -453694567248, 267412624168, 1236266768688, -964489721396, -32991937512, 108349523240, -2120296500], [0, 0, 0, 0, 0, 0, 11262968280, 125363828888, -216179450914, -16109659848, 54843491745, -1590222375], [0, 0, 0, 0, 0, 0, 0, 0, -3243729350, -3144670188, 11369936424, -636088950], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 133746025, -106014825]], [[463856467968, -115964116992, -1391569403904, 579820584960, 1333587345408, -695784701952, -492847497216, 318901321728, 43486543872, -50734301184, 7247757312], [0, -115964116992, -927712935936, 811748818944, 1971389988864, -1565515579392, -1130650140672, 1014686023680, 115964116992, -210184962048, 36238786560], [0, 0, 0, 231928233984, 637802643456, -1043677052928, -782757789696, 1130650140672, 86973087744, -333396836352, 72477573120], [0, 0, 0, 0, 0, -173946175488, -144955146240, 492847497216, 0, -246423748608, 72477573120], [0, 0, 0, 0, 0, 0, 0, 57982058496, -14495514624, -79725330432, 36238786560], [0, 0, 0, 0, 0, 0, 0, 0, 0, -7247757312, 7247757312]]⟩
def n00111_reduction : Reduction := ⟨rawMul n00033_pair n00110_pair, n00111_pair, [[-2, 1], [0, 1]], 1⟩
theorem n00111_checked : checkReduction n00111_reduction = true := by decide
def n00112_expression (x t : ℝ) : ℝ := n00100_expression x t + n00111_expression x t
def n00112_pair : RationalPair := ⟨[[-130087065600, 1642026023424, -3343970260224, 870069108096, 2991286870944, -2500945724112, -98683978592, 862414748136, -347609407154, 27854536584, 5809055419, -106014825], [0, 32521766400, -1365256159488, 1153102811904, 3821556252000, -5090132473584, 130272331320, 2478853085264, -1222334939686, 110306086548, 29179023120, -636088950], [0, 0, 0, 368171872128, 931780894176, -2974558014576, 457129202280, 2479564871808, -1584592105484, 162678980352, 58759284315, -1590222375], [0, 0, 0, 0, -10620987360, -404911917648, 239435860648, 972229480368, -895860749876, 104745787608, 59428014440, -2120296500], [0, 0, 0, 0, 0, 0, 11262968280, 109102945688, -189237906274, 23406297432, 30382737345, -1590222375], [0, 0, 0, 0, 0, 0, 0, 0, -3243729350, -1112059788, 6477785544, -636088950], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 133746025, -106014825]], [[463856467968, -115964116992, -1391569403904, 579820584960, 1333587345408, -695784701952, -492847497216, 318901321728, 43486543872, -50734301184, 7247757312], [0, -115964116992, -927712935936, 811748818944, 1971389988864, -1565515579392, -1130650140672, 1014686023680, 115964116992, -210184962048, 36238786560], [0, 0, 0, 231928233984, 637802643456, -1043677052928, -782757789696, 1130650140672, 86973087744, -333396836352, 72477573120], [0, 0, 0, 0, 0, -173946175488, -144955146240, 492847497216, 0, -246423748608, 72477573120], [0, 0, 0, 0, 0, 0, 0, 57982058496, -14495514624, -79725330432, 36238786560], [0, 0, 0, 0, 0, 0, 0, 0, 0, -7247757312, 7247757312]]⟩
def n00112_reduction : Reduction := ⟨rawAdd n00100_pair n00111_pair, n00112_pair, [[-25165824, 25165824]], 1⟩
theorem n00112_checked : checkReduction n00112_reduction = true := by decide
def n00113_expression (x t : ℝ) : ℝ := n00034_expression x t + n00076_expression x t
def n00113_pair : RationalPair := ⟨[[-1062098736, 1942557384, -290433776, -1060527544, 443753467, 21202965], [0, 0, 595247460, -1043565172, 417004262, 42405930], [0, 0, 0, 0, -26749205, 21202965]], [[-805306368, 805306368, 805306368, -805306368, -201326592, 201326592], [0, 0, 805306368, -805306368, -402653184, 402653184], [0, 0, 0, 0, -201326592, 201326592]]⟩
def n00113_reduction : Reduction := ⟨rawAdd n00034_pair n00076_pair, n00113_pair, [[-2, 0, 1], [0, 0, 1]], 1⟩
theorem n00113_checked : checkReduction n00113_reduction = true := by decide
def n00114_expression (x t : ℝ) : ℝ := (10 : ℝ)/(1 : ℝ)
def n00114_pair : RationalPair := ⟨[[10]], [[1]]⟩
def n00115_expression (x t : ℝ) : ℝ := n00114_expression x t * n00059_expression x t
def n00115_pair : RationalPair := ⟨[[-40864555, 55176235]], [[-8388608, 8388608]]⟩
def n00115_reduction : Reduction := ⟨rawMul n00114_pair n00059_pair, n00115_pair, [[2]], 1⟩
theorem n00115_checked : checkReduction n00115_reduction = true := by decide
def n00116_expression (x t : ℝ) : ℝ := n00044_expression x t + n00049_expression x t
def n00116_pair : RationalPair := ⟨[[7340709, -19992997]], [[-16777216, 16777216]]⟩
def n00116_reduction : Reduction := ⟨rawAdd n00044_pair n00049_pair, n00116_pair, [[-8388608, 8388608]], 1⟩
theorem n00116_checked : checkReduction n00116_reduction = true := by decide
def n00117_expression (x t : ℝ) : ℝ := n00033_expression x t * n00116_expression x t
def n00117_pair : RationalPair := ⟨[[0, -14681418, 47326703, -19992997], [0, 0, 7340709, -19992997]], [[33554432, -33554432, -16777216, 16777216], [0, 0, -16777216, 16777216]]⟩
def n00117_reduction : Reduction := ⟨rawMul n00033_pair n00116_pair, n00117_pair, [[1]], 1⟩
theorem n00117_checked : checkReduction n00117_reduction = true := by decide
def n00118_expression (x t : ℝ) : ℝ := n00115_expression x t + n00117_expression x t
def n00118_pair : RationalPair := ⟨[[163458220, -235386358, -34402407, 90359473], [0, 0, -74388401, 90359473]], [[33554432, -33554432, -16777216, 16777216], [0, 0, -16777216, 16777216]]⟩
def n00118_reduction : Reduction := ⟨rawAdd n00115_pair n00117_pair, n00118_pair, [[-8388608, 8388608]], 1⟩
theorem n00118_checked : checkReduction n00118_reduction = true := by decide
def n00119_expression (x t : ℝ) : ℝ := n00114_expression x t * n00025_expression x t
def n00119_pair : RationalPair := ⟨[[-21888492864, 40079453975]], [[3500000000]]⟩
def n00119_reduction : Reduction := ⟨rawMul n00114_pair n00025_pair, n00119_pair, [[10]], 1⟩
theorem n00119_checked : checkReduction n00119_reduction = true := by decide
def n00120_expression (x t : ℝ) : ℝ := n00077_expression x t + n00119_expression x t
def n00120_pair : RationalPair := ⟨[[-19438492864, 40079453975]], [[3500000000]]⟩
def n00120_reduction : Reduction := ⟨rawAdd n00077_pair n00119_pair, n00120_pair, [[10]], 1⟩
theorem n00120_checked : checkReduction n00120_reduction = true := by decide
def n00121_expression (x t : ℝ) : ℝ := n00081_expression x t * n00120_expression x t
def n00121_pair : RationalPair := ⟨[[-27438113024786240, 122612468712776153, -136163011134524825]], [[-29360128000000000, 29360128000000000]]⟩
def n00121_reduction : Reduction := ⟨rawMul n00081_pair n00120_pair, n00121_pair, [[1]], 1⟩
theorem n00121_checked : checkReduction n00121_reduction = true := by decide
def n00122_expression (x t : ℝ) : ℝ := n00118_expression x t + n00121_expression x t
def n00122_pair : RationalPair := ⟨[[340928111049572480, -657151063925552306, 184683696994263410, 280741546462776153, -136163011134524825], [0, 0, -157617814774786240, 280741546462776153, -136163011134524825]], [[58720256000000000, -58720256000000000, -29360128000000000, 29360128000000000], [0, 0, -29360128000000000, 29360128000000000]]⟩
def n00122_reduction : Reduction := ⟨rawAdd n00118_pair n00121_pair, n00122_pair, [[-16777216, 16777216]], 1⟩
theorem n00122_checked : checkReduction n00122_reduction = true := by decide
def n00123_expression (x t : ℝ) : ℝ := n00033_expression x t * n00113_expression x t
def n00123_pair : RationalPair := ⟨[[0, 2124197472, -4947213504, 2523424936, 1830621312, -1948034478, 401347537, 21202965], [0, 0, -1062098736, 752062464, 2391944028, -2938101240, 775945869, 63608895], [0, 0, 0, 0, 595247460, -990066762, 347849127, 63608895], [0, 0, 0, 0, 0, 0, -26749205, 21202965]], [[1610612736, -1610612736, -2415919104, 2415919104, 1207959552, -1207959552, -201326592, 201326592], [0, 0, -2415919104, 2415919104, 2415919104, -2415919104, -603979776, 603979776], [0, 0, 0, 0, 1207959552, -1207959552, -603979776, 603979776], [0, 0, 0, 0, 0, 0, -201326592, 201326592]]⟩
def n00123_reduction : Reduction := ⟨rawMul n00033_pair n00113_pair, n00123_pair, [[1]], 1⟩
theorem n00123_checked : checkReduction n00123_reduction = true := by decide
def n00124_expression (x t : ℝ) : ℝ := n00070_expression x t * n00120_expression x t
def n00124_pair : RationalPair := ⟨[[0, -933047657472, 2390337619536, -981345388264, 40079453975], [0, -933047657472, 2856861448272, -1982129269392, 120238361925], [0, 0, 466523828736, -1020222373992, 120238361925], [0, 0, 0, -19438492864, 40079453975]], [[336000000000, -252000000000, 42000000000], [0, -252000000000, 84000000000], [0, 0, 42000000000]]⟩
def n00124_reduction : Reduction := ⟨rawMul n00070_pair n00120_pair, n00124_pair, [[1]], 1⟩
theorem n00124_checked : checkReduction n00124_reduction = true := by decide
def n00125_expression (x t : ℝ) : ℝ := n00004_expression x t + n00124_expression x t
def n00125_pair : RationalPair := ⟨[[672000000000, -1437047657472, 2474337619536, -981345388264, 40079453975], [0, -1437047657472, 3024861448272, -1982129269392, 120238361925], [0, 0, 550523828736, -1020222373992, 120238361925], [0, 0, 0, -19438492864, 40079453975]], [[336000000000, -252000000000, 42000000000], [0, -252000000000, 84000000000], [0, 0, 42000000000]]⟩
def n00125_reduction : Reduction := ⟨rawAdd n00004_pair n00124_pair, n00125_pair, [[1]], 1⟩
theorem n00125_checked : checkReduction n00125_reduction = true := by decide
def n00126_expression (x t : ℝ) : ℝ := n00123_expression x t * n00125_expression x t
def n00126_pair : RationalPair := ⟨[[0, -713730350592000000000, 2831685062620772155392, -5614709893800570879744, 5553521177676810662400, -845288332959956256144, -2884677200501224948744, 2096629613286285010848, -425517489310373774448, -3022035263399821435, 849803259851035875], [0, 0, 1526286500572772155392, -5604242765846956957440, 6841876347385943882112, -79875236910724899888, -6773430683063459026296, 5397829540841468557372, -1289080942375029309172, -13572388268112767375, 4249016299255179375], [0, 0, 0, -584710662638386077696, 1297602054425732639616, 1012782281520598183440, -4937032923305047109400, 4535186694397684513428, -1313617927032335107708, -24069200438452855150, 8498032598510358750], [0, 0, 0, 0, 20645598700599419904, 247369185471366827184, -1059850154246337157288, 1263403219416103398132, -461543019950567212572, -20993624340680175550, 8498032598510358750], [0, 0, 0, 0, 0, 0, -11570713503524125440, 29416452573602431228, -10968581752377466468, -8959024121453747975, 4249016299255179375], [0, 0, 0, 0, 0, 0, 0, 0, 519964230510173120, -1484247214513481635, 849803259851035875]], [[-270582939648000000000, 338228674560000000000, 338228674560000000000, -507343011840000000000, -101468602368000000000, 253671505920000000000, -16911433728000000000, -42278584320000000000, 8455716864000000000], [0, 67645734912000000000, 338228674560000000000, -608811614208000000000, -202937204736000000000, 558077313024000000000, -50734301184000000000, -135291469824000000000, 33822867456000000000], [0, 0, 0, -101468602368000000000, -101468602368000000000, 355140108288000000000, -50734301184000000000, -152202903552000000000, 50734301184000000000], [0, 0, 0, 0, 0, 50734301184000000000, -16911433728000000000, -67645734912000000000, 33822867456000000000], [0, 0, 0, 0, 0, 0, 0, -8455716864000000000, 8455716864000000000]]⟩
def n00126_reduction : Reduction := ⟨rawMul n00123_pair n00125_pair, n00126_pair, [[-2, 1], [0, 1]], 1⟩
theorem n00126_checked : checkReduction n00126_reduction = true := by decide
def n00127_expression (x t : ℝ) : ℝ := n00122_expression x t - n00126_expression x t
def n00127_pair : RationalPair := ⟨[[-1570996735716429987840, 4134631637090052523008, -2868748828296144217344, 1112907180139437292032, -3387356443381107587712, 2624555292920577853200, 1531808658320265914440, -2209995181250082678624, 663230843518625904912, -36192911943343328165, -849803259851035875], [0, 392749183929107496960, 13975099983636569856, 528115145636162124288, -4714311400334208913536, 3918172175434798716720, 3736595553386417513784, -5783320175387999997820, 2083074570381065232628, -143287400558859831025, -4249016299255179375], [0, 0, 0, 10385756088724832256, -1336201841669700745728, 1326010715645684659056, 2921968290493841187288, -5011465190254492828116, 2269318685800930095292, -211220482802006042450, -8498032598510358750], [0, 0, 0, 0, -20645598700599419904, 32393833131463795536, 728752108931213713384, -1512950579345316377268, 941817070302657939228, -135866164486292422850, -8498032598510358750], [0, 0, 0, 0, 0, 0, 11570713503524125440, -74810383228740868348, 91822147133656998532, -30255923085289401625, -4249016299255179375], [0, 0, 0, 0, 0, 0, 0, 0, -519964230510173120, 1484247214513481635, -849803259851035875]], [[-270582939648000000000, 338228674560000000000, 338228674560000000000, -507343011840000000000, -101468602368000000000, 253671505920000000000, -16911433728000000000, -42278584320000000000, 8455716864000000000], [0, 67645734912000000000, 338228674560000000000, -608811614208000000000, -202937204736000000000, 558077313024000000000, -50734301184000000000, -135291469824000000000, 33822867456000000000], [0, 0, 0, -101468602368000000000, -101468602368000000000, 355140108288000000000, -50734301184000000000, -152202903552000000000, 50734301184000000000], [0, 0, 0, 0, 0, 50734301184000000000, -16911433728000000000, -67645734912000000000, 33822867456000000000], [0, 0, 0, 0, 0, 0, 0, -8455716864000000000, 8455716864000000000]]⟩
def n00127_reduction : Reduction := ⟨rawSub n00122_pair n00126_pair, n00127_pair, [[58720256000000000, -58720256000000000, -29360128000000000, 29360128000000000], [0, 0, -29360128000000000, 29360128000000000]], 1⟩
theorem n00127_checked : checkReduction n00127_reduction = true := by decide
def n00128_expression (x t : ℝ) : ℝ := n00078_expression x t + n00119_expression x t
def n00128_pair : RationalPair := ⟨[[-56915478592, 120238361925]], [[10500000000]]⟩
def n00128_reduction : Reduction := ⟨rawAdd n00078_pair n00119_pair, n00128_pair, [[2]], 1⟩
theorem n00128_checked : checkReduction n00128_reduction = true := by decide
def n00129_expression (x t : ℝ) : ℝ := n00081_expression x t * n00128_expression x t
def n00129_pair : RationalPair := ⟨[[-80338190074358720, 363081148338328459, -408489033403574475]], [[-88080384000000000, 88080384000000000]]⟩
def n00129_reduction : Reduction := ⟨rawMul n00081_pair n00128_pair, n00129_pair, [[1]], 1⟩
theorem n00129_checked : checkReduction n00129_reduction = true := by decide
def n00130_expression (x t : ℝ) : ℝ := n00118_expression x t + n00129_expression x t
def n00130_pair : RationalPair := ⟨[[1018832035148717440, -1961940676176656918, 556027239982790230, 837468381588328459, -408489033403574475], [0, 0, -470877295324358720, 837468381588328459, -408489033403574475]], [[176160768000000000, -176160768000000000, -88080384000000000, 88080384000000000], [0, 0, -88080384000000000, 88080384000000000]]⟩
def n00130_reduction : Reduction := ⟨rawAdd n00118_pair n00129_pair, n00130_pair, [[-16777216, 16777216]], 1⟩
theorem n00130_checked : checkReduction n00130_reduction = true := by decide
def n00131_expression (x t : ℝ) : ℝ := n00070_expression x t * n00128_expression x t
def n00131_pair : RationalPair := ⟨[[0, -2731942972416, 7137412858608, -2942636164792, 120238361925], [0, -2731942972416, 8503384344816, -5942187808176, 360715085775], [0, 0, 1365971486208, -3056467121976, 360715085775], [0, 0, 0, -56915478592, 120238361925]], [[1008000000000, -756000000000, 126000000000], [0, -756000000000, 252000000000], [0, 0, 126000000000]]⟩
def n00131_reduction : Reduction := ⟨rawMul n00070_pair n00128_pair, n00131_pair, [[1]], 1⟩
theorem n00131_checked : checkReduction n00131_reduction = true := by decide
def n00132_expression (x t : ℝ) : ℝ := n00004_expression x t + n00131_expression x t
def n00132_pair : RationalPair := ⟨[[2016000000000, -4243942972416, 7389412858608, -2942636164792, 120238361925], [0, -4243942972416, 9007384344816, -5942187808176, 360715085775], [0, 0, 1617971486208, -3056467121976, 360715085775], [0, 0, 0, -56915478592, 120238361925]], [[1008000000000, -756000000000, 126000000000], [0, -756000000000, 252000000000], [0, 0, 126000000000]]⟩
def n00132_reduction : Reduction := ⟨rawAdd n00004_pair n00131_pair, n00132_pair, [[1]], 1⟩
theorem n00132_checked : checkReduction n00132_reduction = true := by decide
def n00133_expression (x t : ℝ) : ℝ := n00123_expression x t * n00132_expression x t
def n00133_pair : RationalPair := ⟨[[0, -2141191051776000000000, 8423682152803116466176, -16677903307667312639232, 16574289516950431987200, -2594654294625468768432, -8588984250329274846232, 6274918824054055032544, -1276643632701321323344, -9036421639199464305, 2549409779553107625], [0, 0, 4507486466659116466176, -16610815406276870872320, 20411111850826631646336, -373345165143374699664, -20156504364480777078888, 16148016357157205672116, -3867644935092887927516, -40568744049338302125, 12747048897765538125], [0, 0, 0, -1718445470385558233088, 3863076049795597918848, 2946135951577794550320, -14677832107575141328200, 13558963381920253540284, -3941550565266205323124, -71910759805358565450, 25494097795531076250], [0, 0, 0, 0, 60449857871398259712, 724826822095700481552, -3144190787490211471864, 3773552988585110194396, -1385218412254501637716, -62684031512040526650, 25494097795531076250], [0, 0, 0, 0, 0, 0, -33878794066572376320, 87687139768007293684, -33146705575332399404, -26728651609361243925, 12747048897765538125], [0, 0, 0, 0, 0, 0, 0, 0, 1522443804530519360, -4423057492540444905, 2549409779553107625]], [[-811748818944000000000, 1014686023680000000000, 1014686023680000000000, -1522029035520000000000, -304405807104000000000, 761014517760000000000, -50734301184000000000, -126835752960000000000, 25367150592000000000], [0, 202937204736000000000, 1014686023680000000000, -1826434842624000000000, -608811614208000000000, 1674231939072000000000, -152202903552000000000, -405874409472000000000, 101468602368000000000], [0, 0, 0, -304405807104000000000, -304405807104000000000, 1065420324864000000000, -152202903552000000000, -456608710656000000000, 152202903552000000000], [0, 0, 0, 0, 0, 152202903552000000000, -50734301184000000000, -202937204736000000000, 101468602368000000000], [0, 0, 0, 0, 0, 0, 0, -25367150592000000000, 25367150592000000000]]⟩
def n00133_reduction : Reduction := ⟨rawMul n00123_pair n00132_pair, n00133_pair, [[-2, 1], [0, 1]], 1⟩
theorem n00133_checked : checkReduction n00133_reduction = true := by decide
def n00134_expression (x t : ℝ) : ℝ := n00130_expression x t - n00133_expression x t
def n00134_pair : RationalPair := ⟨[[-4694778017965289963520, 12355508192089357569024, -8551233315634032652032, 3245075245455111876096, -10078573799132122763136, 7896165135121733559600, 4536320913616797743320, -6608967188047848035872, 1988413893079677714736, -108608419981029984495, -2549409779553107625], [0, 1173694504491322490880, 96938469205309709568, 1461842195359686372864, -14033973979809026740608, 11812241116472396150160, 11063825844940852541352, -17285774110191999993460, 6244146610125395697884, -430010622431579493075, -12747048897765538125], [0, 0, 0, 2300321680574496768, -3981653896596302237184, 4027123429591453977168, 8650465078632723561864, -14967946457061878484348, 6800434028093590285876, -633958289916018127350, -25494097795531076250], [0, 0, 0, 0, -60449857871398259712, 111047448240791386608, 2156838941375241140152, -4514439335739149131804, 2820561354325173817684, -407895334968877268550, -25494097795531076250], [0, 0, 0, 0, 0, 0, 33878794066572376320, -223299800821422605044, 274337599472770995596, -90916190010868204875, -12747048897765538125], [0, 0, 0, 0, 0, 0, 0, 0, -1522443804530519360, 4423057492540444905, -2549409779553107625]], [[-811748818944000000000, 1014686023680000000000, 1014686023680000000000, -1522029035520000000000, -304405807104000000000, 761014517760000000000, -50734301184000000000, -126835752960000000000, 25367150592000000000], [0, 202937204736000000000, 1014686023680000000000, -1826434842624000000000, -608811614208000000000, 1674231939072000000000, -152202903552000000000, -405874409472000000000, 101468602368000000000], [0, 0, 0, -304405807104000000000, -304405807104000000000, 1065420324864000000000, -152202903552000000000, -456608710656000000000, 152202903552000000000], [0, 0, 0, 0, 0, 152202903552000000000, -50734301184000000000, -202937204736000000000, 101468602368000000000], [0, 0, 0, 0, 0, 0, 0, -25367150592000000000, 25367150592000000000]]⟩
def n00134_reduction : Reduction := ⟨rawSub n00130_pair n00133_pair, n00134_pair, [[176160768000000000, -176160768000000000, -88080384000000000, 88080384000000000], [0, 0, -88080384000000000, 88080384000000000]], 1⟩
theorem n00134_checked : checkReduction n00134_reduction = true := by decide
def divisorExpression (i : Fin 16) (x t : ℝ) : ℝ :=
  match i.val with
  | 0 => n00007_expression x t
  | 1 => n00009_expression x t
  | 2 => n00011_expression x t
  | 3 => n00013_expression x t
  | 4 => n00016_expression x t
  | 5 => n00004_expression x t
  | 6 => n00004_expression x t
  | 7 => n00032_expression x t
  | 8 => n00036_expression x t
  | 9 => n00043_expression x t
  | 10 => n00043_expression x t
  | 11 => n00043_expression x t
  | 12 => n00043_expression x t
  | 13 => n00069_expression x t
  | 14 => n00004_expression x t
  | 15 => n00063_expression x t
  | _ => 1
def DivisorsNonzero (x t : ℝ) : Prop := ∀ i : Fin 16, divisorExpression i x t ≠ 0
theorem n00000_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00000_pair.NonzeroDenominator x t ∧ n00000_pair.value x t = n00000_expression x t := by
  simpa [n00000_pair, n00000_expression, rationalX, Polynomial2.X, Polynomial2.const] using rationalX_sound x t
theorem n00001_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00001_pair.NonzeroDenominator x t ∧ n00001_pair.value x t = n00001_expression x t := by
  simpa [n00001_pair, n00001_expression, rationalT, Polynomial2.Y, Polynomial2.const] using rationalT_sound x t
theorem n00002_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00002_pair.NonzeroDenominator x t ∧ n00002_pair.value x t = n00002_expression x t := by
  simpa [n00002_pair, n00002_expression, rationalConst, Polynomial2.const] using rationalConst_sound 7 4 x t (by decide)
theorem n00003_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00003_pair.NonzeroDenominator x t ∧ n00003_pair.value x t = n00003_expression x t := by
  simpa [n00003_pair, n00003_expression, rationalConst, Polynomial2.const] using rationalConst_sound 7 3 x t (by decide)
theorem n00004_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00004_pair.NonzeroDenominator x t ∧ n00004_pair.value x t = n00004_expression x t := by
  simpa [n00004_pair, n00004_expression, rationalConst, Polynomial2.const] using rationalConst_sound 2 1 x t (by decide)
theorem n00005_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00005_pair.NonzeroDenominator x t ∧ n00005_pair.value x t = n00005_expression x t := by
  simpa [n00005_pair, n00005_expression, rationalConst, Polynomial2.const] using rationalConst_sound 523 256 x t (by decide)
theorem n00006_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00006_pair.NonzeroDenominator x t ∧ n00006_pair.value x t = n00006_expression x t := by
  simpa [n00006_pair, n00006_expression, rationalConst, Polynomial2.const] using rationalConst_sound 1 1 x t (by decide)
theorem n00007_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00007_pair.NonzeroDenominator x t ∧ n00007_pair.value x t = n00007_expression x t := by
  have ha := n00006_sound x t hnz
  have hb := n00000_sound x t hnz
  have hraw := rawSub_sound n00006_pair n00000_pair x t ha.1 hb.1
  have hred := checkReduction_sound n00007_checked x t hraw.1
  dsimp only [n00007_reduction] at hred
  refine ⟨hred.1, ?_⟩
  rw [← hred.2, hraw.2]
  simp only [n00007_expression, ha.2, hb.2]
theorem n00008_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00008_pair.NonzeroDenominator x t ∧ n00008_pair.value x t = n00008_expression x t := by
  have ha := n00000_sound x t hnz
  have hb := n00007_sound x t hnz
  have hd : n00007_pair.value x t ≠ 0 := by
    rw [hb.2]
    simpa only [divisorExpression] using hnz ⟨0, by decide⟩
  have hraw := rawDiv_sound n00000_pair n00007_pair x t ha.1 hb.1 hd
  have hred := checkReduction_sound n00008_checked x t hraw.1
  dsimp only [n00008_reduction] at hred
  refine ⟨hred.1, ?_⟩
  rw [← hred.2, hraw.2]
  simp only [n00008_expression, ha.2, hb.2]
theorem n00009_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00009_pair.NonzeroDenominator x t ∧ n00009_pair.value x t = n00009_expression x t := by
  have ha := n00006_sound x t hnz
  have hb := n00008_sound x t hnz
  have hraw := rawAdd_sound n00006_pair n00008_pair x t ha.1 hb.1
  have hred := checkReduction_sound n00009_checked x t hraw.1
  dsimp only [n00009_reduction] at hred
  refine ⟨hred.1, ?_⟩
  rw [← hred.2, hraw.2]
  simp only [n00009_expression, ha.2, hb.2]
theorem n00010_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00010_pair.NonzeroDenominator x t ∧ n00010_pair.value x t = n00010_expression x t := by
  have ha := n00008_sound x t hnz
  have hb := n00009_sound x t hnz
  have hd : n00009_pair.value x t ≠ 0 := by
    rw [hb.2]
    simpa only [divisorExpression] using hnz ⟨1, by decide⟩
  have hraw := rawDiv_sound n00008_pair n00009_pair x t ha.1 hb.1 hd
  have hred := checkReduction_sound n00010_checked x t hraw.1
  dsimp only [n00010_reduction] at hred
  refine ⟨hred.1, ?_⟩
  rw [← hred.2, hraw.2]
  simp only [n00010_expression, ha.2, hb.2]
theorem n00011_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00011_pair.NonzeroDenominator x t ∧ n00011_pair.value x t = n00011_expression x t := by
  have ha := n00006_sound x t hnz
  have hb := n00002_sound x t hnz
  have hraw := rawAdd_sound n00006_pair n00002_pair x t ha.1 hb.1
  have hred := checkReduction_sound n00011_checked x t hraw.1
  dsimp only [n00011_reduction] at hred
  refine ⟨hred.1, ?_⟩
  rw [← hred.2, hraw.2]
  simp only [n00011_expression, ha.2, hb.2]
theorem n00012_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00012_pair.NonzeroDenominator x t ∧ n00012_pair.value x t = n00012_expression x t := by
  have ha := n00002_sound x t hnz
  have hb := n00011_sound x t hnz
  have hd : n00011_pair.value x t ≠ 0 := by
    rw [hb.2]
    simpa only [divisorExpression] using hnz ⟨2, by decide⟩
  have hraw := rawDiv_sound n00002_pair n00011_pair x t ha.1 hb.1 hd
  have hred := checkReduction_sound n00012_checked x t hraw.1
  dsimp only [n00012_reduction] at hred
  refine ⟨hred.1, ?_⟩
  rw [← hred.2, hraw.2]
  simp only [n00012_expression, ha.2, hb.2]
theorem n00013_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00013_pair.NonzeroDenominator x t ∧ n00013_pair.value x t = n00013_expression x t := by
  have ha := n00006_sound x t hnz
  have hb := n00003_sound x t hnz
  have hraw := rawAdd_sound n00006_pair n00003_pair x t ha.1 hb.1
  have hred := checkReduction_sound n00013_checked x t hraw.1
  dsimp only [n00013_reduction] at hred
  refine ⟨hred.1, ?_⟩
  rw [← hred.2, hraw.2]
  simp only [n00013_expression, ha.2, hb.2]
theorem n00014_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00014_pair.NonzeroDenominator x t ∧ n00014_pair.value x t = n00014_expression x t := by
  have ha := n00003_sound x t hnz
  have hb := n00013_sound x t hnz
  have hd : n00013_pair.value x t ≠ 0 := by
    rw [hb.2]
    simpa only [divisorExpression] using hnz ⟨3, by decide⟩
  have hraw := rawDiv_sound n00003_pair n00013_pair x t ha.1 hb.1 hd
  have hred := checkReduction_sound n00014_checked x t hraw.1
  dsimp only [n00014_reduction] at hred
  refine ⟨hred.1, ?_⟩
  rw [← hred.2, hraw.2]
  simp only [n00014_expression, ha.2, hb.2]
theorem n00015_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00015_pair.NonzeroDenominator x t ∧ n00015_pair.value x t = n00015_expression x t := by
  have ha := n00010_sound x t hnz
  have hb := n00012_sound x t hnz
  have hraw := rawSub_sound n00010_pair n00012_pair x t ha.1 hb.1
  have hred := checkReduction_sound n00015_checked x t hraw.1
  dsimp only [n00015_reduction] at hred
  refine ⟨hred.1, ?_⟩
  rw [← hred.2, hraw.2]
  simp only [n00015_expression, ha.2, hb.2]
theorem n00016_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00016_pair.NonzeroDenominator x t ∧ n00016_pair.value x t = n00016_expression x t := by
  have ha := n00014_sound x t hnz
  have hb := n00012_sound x t hnz
  have hraw := rawSub_sound n00014_pair n00012_pair x t ha.1 hb.1
  have hred := checkReduction_sound n00016_checked x t hraw.1
  dsimp only [n00016_reduction] at hred
  refine ⟨hred.1, ?_⟩
  rw [← hred.2, hraw.2]
  simp only [n00016_expression, ha.2, hb.2]
theorem n00017_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00017_pair.NonzeroDenominator x t ∧ n00017_pair.value x t = n00017_expression x t := by
  have ha := n00015_sound x t hnz
  have hb := n00016_sound x t hnz
  have hd : n00016_pair.value x t ≠ 0 := by
    rw [hb.2]
    simpa only [divisorExpression] using hnz ⟨4, by decide⟩
  have hraw := rawDiv_sound n00015_pair n00016_pair x t ha.1 hb.1 hd
  have hred := checkReduction_sound n00017_checked x t hraw.1
  dsimp only [n00017_reduction] at hred
  refine ⟨hred.1, ?_⟩
  rw [← hred.2, hraw.2]
  simp only [n00017_expression, ha.2, hb.2]
theorem n00018_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00018_pair.NonzeroDenominator x t ∧ n00018_pair.value x t = n00018_expression x t := by
  constructor <;> simp [n00018_pair, n00018_expression, RationalPair.NonzeroDenominator, RationalPair.value, Polynomial2.eval, F4U.Light.eval]
theorem n00019_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00019_pair.NonzeroDenominator x t ∧ n00019_pair.value x t = n00019_expression x t := by
  have ha := n00006_sound x t hnz
  have hb := n00017_sound x t hnz
  have hraw := rawSub_sound n00006_pair n00017_pair x t ha.1 hb.1
  have hred := checkReduction_sound n00019_checked x t hraw.1
  dsimp only [n00019_reduction] at hred
  refine ⟨hred.1, ?_⟩
  rw [← hred.2, hraw.2]
  simp only [n00019_expression, ha.2, hb.2]
theorem n00020_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00020_pair.NonzeroDenominator x t ∧ n00020_pair.value x t = n00020_expression x t := by
  simpa [n00020_pair, n00020_expression, rationalConst, Polynomial2.const] using rationalConst_sound 516659173 5000000000 x t (by decide)
theorem n00021_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00021_pair.NonzeroDenominator x t ∧ n00021_pair.value x t = n00021_expression x t := by
  have ha := n00019_sound x t hnz
  have hb := n00020_sound x t hnz
  have hraw := rawMul_sound n00019_pair n00020_pair x t ha.1 hb.1
  have hred := checkReduction_sound n00021_checked x t hraw.1
  dsimp only [n00021_reduction] at hred
  refine ⟨hred.1, ?_⟩
  rw [← hred.2, hraw.2]
  simp only [n00021_expression, ha.2, hb.2]
theorem n00022_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00022_pair.NonzeroDenominator x t ∧ n00022_pair.value x t = n00022_expression x t := by
  simpa [n00022_pair, n00022_expression, rationalConst, Polynomial2.const] using rationalConst_sound 1762035691 10000000000 x t (by decide)
theorem n00023_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00023_pair.NonzeroDenominator x t ∧ n00023_pair.value x t = n00023_expression x t := by
  have ha := n00017_sound x t hnz
  have hb := n00022_sound x t hnz
  have hraw := rawMul_sound n00017_pair n00022_pair x t ha.1 hb.1
  have hred := checkReduction_sound n00023_checked x t hraw.1
  dsimp only [n00023_reduction] at hred
  refine ⟨hred.1, ?_⟩
  rw [← hred.2, hraw.2]
  simp only [n00023_expression, ha.2, hb.2]
theorem n00024_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00024_pair.NonzeroDenominator x t ∧ n00024_pair.value x t = n00024_expression x t := by
  have ha := n00021_sound x t hnz
  have hb := n00023_sound x t hnz
  have hraw := rawAdd_sound n00021_pair n00023_pair x t ha.1 hb.1
  have hred := checkReduction_sound n00024_checked x t hraw.1
  dsimp only [n00024_reduction] at hred
  refine ⟨hred.1, ?_⟩
  rw [← hred.2, hraw.2]
  simp only [n00024_expression, ha.2, hb.2]
theorem n00025_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00025_pair.NonzeroDenominator x t ∧ n00025_pair.value x t = n00025_expression x t := by
  have ha := n00024_sound x t hnz
  have hb := n00018_sound x t hnz
  have hraw := rawAdd_sound n00024_pair n00018_pair x t ha.1 hb.1
  have hred := checkReduction_sound n00025_checked x t hraw.1
  dsimp only [n00025_reduction] at hred
  refine ⟨hred.1, ?_⟩
  rw [← hred.2, hraw.2]
  simp only [n00025_expression, ha.2, hb.2]
theorem n00026_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00026_pair.NonzeroDenominator x t ∧ n00026_pair.value x t = n00026_expression x t := by
  have ha := n00010_sound x t hnz
  have hb := n00004_sound x t hnz
  have hd : n00004_pair.value x t ≠ 0 := by
    rw [hb.2]
    simpa only [divisorExpression] using hnz ⟨5, by decide⟩
  have hraw := rawDiv_sound n00010_pair n00004_pair x t ha.1 hb.1 hd
  have hred := checkReduction_sound n00026_checked x t hraw.1
  dsimp only [n00026_reduction] at hred
  refine ⟨hred.1, ?_⟩
  rw [← hred.2, hraw.2]
  simp only [n00026_expression, ha.2, hb.2]
theorem n00027_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00027_pair.NonzeroDenominator x t ∧ n00027_pair.value x t = n00027_expression x t := by
  have ha := n00010_sound x t hnz
  have hb := n00001_sound x t hnz
  have hraw := rawMul_sound n00010_pair n00001_pair x t ha.1 hb.1
  have hred := checkReduction_sound n00027_checked x t hraw.1
  dsimp only [n00027_reduction] at hred
  refine ⟨hred.1, ?_⟩
  rw [← hred.2, hraw.2]
  simp only [n00027_expression, ha.2, hb.2]
theorem n00028_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00028_pair.NonzeroDenominator x t ∧ n00028_pair.value x t = n00028_expression x t := by
  have ha := n00027_sound x t hnz
  have hb := n00004_sound x t hnz
  have hd : n00004_pair.value x t ≠ 0 := by
    rw [hb.2]
    simpa only [divisorExpression] using hnz ⟨6, by decide⟩
  have hraw := rawDiv_sound n00027_pair n00004_pair x t ha.1 hb.1 hd
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
  have ha := n00006_sound x t hnz
  have hb := n00029_sound x t hnz
  have hraw := rawSub_sound n00006_pair n00029_pair x t ha.1 hb.1
  have hred := checkReduction_sound n00030_checked x t hraw.1
  dsimp only [n00030_reduction] at hred
  refine ⟨hred.1, ?_⟩
  rw [← hred.2, hraw.2]
  simp only [n00030_expression, ha.2, hb.2]
theorem n00031_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00031_pair.NonzeroDenominator x t ∧ n00031_pair.value x t = n00031_expression x t := by
  have ha := n00008_sound x t hnz
  have hb := n00030_sound x t hnz
  have hraw := rawMul_sound n00008_pair n00030_pair x t ha.1 hb.1
  have hred := checkReduction_sound n00031_checked x t hraw.1
  dsimp only [n00031_reduction] at hred
  refine ⟨hred.1, ?_⟩
  rw [← hred.2, hraw.2]
  simp only [n00031_expression, ha.2, hb.2]
theorem n00032_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00032_pair.NonzeroDenominator x t ∧ n00032_pair.value x t = n00032_expression x t := by
  have ha := n00006_sound x t hnz
  have hb := n00031_sound x t hnz
  have hraw := rawAdd_sound n00006_pair n00031_pair x t ha.1 hb.1
  have hred := checkReduction_sound n00032_checked x t hraw.1
  dsimp only [n00032_reduction] at hred
  refine ⟨hred.1, ?_⟩
  rw [← hred.2, hraw.2]
  simp only [n00032_expression, ha.2, hb.2]
theorem n00033_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00033_pair.NonzeroDenominator x t ∧ n00033_pair.value x t = n00033_expression x t := by
  have ha := n00031_sound x t hnz
  have hb := n00032_sound x t hnz
  have hd : n00032_pair.value x t ≠ 0 := by
    rw [hb.2]
    simpa only [divisorExpression] using hnz ⟨7, by decide⟩
  have hraw := rawDiv_sound n00031_pair n00032_pair x t ha.1 hb.1 hd
  have hred := checkReduction_sound n00033_checked x t hraw.1
  dsimp only [n00033_reduction] at hred
  refine ⟨hred.1, ?_⟩
  rw [← hred.2, hraw.2]
  simp only [n00033_expression, ha.2, hb.2]
theorem n00034_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00034_pair.NonzeroDenominator x t ∧ n00034_pair.value x t = n00034_expression x t := by
  have ha := n00006_sound x t hnz
  have hb := n00033_sound x t hnz
  have hraw := rawSub_sound n00006_pair n00033_pair x t ha.1 hb.1
  have hred := checkReduction_sound n00034_checked x t hraw.1
  dsimp only [n00034_reduction] at hred
  refine ⟨hred.1, ?_⟩
  rw [← hred.2, hraw.2]
  simp only [n00034_expression, ha.2, hb.2]
theorem n00035_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00035_pair.NonzeroDenominator x t ∧ n00035_pair.value x t = n00035_expression x t := by
  have ha := n00008_sound x t hnz
  have hb := n00034_sound x t hnz
  have hraw := rawMul_sound n00008_pair n00034_pair x t ha.1 hb.1
  have hred := checkReduction_sound n00035_checked x t hraw.1
  dsimp only [n00035_reduction] at hred
  refine ⟨hred.1, ?_⟩
  rw [← hred.2, hraw.2]
  simp only [n00035_expression, ha.2, hb.2]
theorem n00036_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00036_pair.NonzeroDenominator x t ∧ n00036_pair.value x t = n00036_expression x t := by
  have ha := n00006_sound x t hnz
  have hb := n00035_sound x t hnz
  have hraw := rawAdd_sound n00006_pair n00035_pair x t ha.1 hb.1
  have hred := checkReduction_sound n00036_checked x t hraw.1
  dsimp only [n00036_reduction] at hred
  refine ⟨hred.1, ?_⟩
  rw [← hred.2, hraw.2]
  simp only [n00036_expression, ha.2, hb.2]
theorem n00037_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00037_pair.NonzeroDenominator x t ∧ n00037_pair.value x t = n00037_expression x t := by
  have ha := n00006_sound x t hnz
  have hb := n00036_sound x t hnz
  have hd : n00036_pair.value x t ≠ 0 := by
    rw [hb.2]
    simpa only [divisorExpression] using hnz ⟨8, by decide⟩
  have hraw := rawDiv_sound n00006_pair n00036_pair x t ha.1 hb.1 hd
  have hred := checkReduction_sound n00037_checked x t hraw.1
  dsimp only [n00037_reduction] at hred
  refine ⟨hred.1, ?_⟩
  rw [← hred.2, hraw.2]
  simp only [n00037_expression, ha.2, hb.2]
theorem n00038_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00038_pair.NonzeroDenominator x t ∧ n00038_pair.value x t = n00038_expression x t := by
  simpa [n00038_pair, n00038_expression, rationalConst, Polynomial2.const] using rationalConst_sound 51799 1 x t (by decide)
theorem n00039_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00039_pair.NonzeroDenominator x t ∧ n00039_pair.value x t = n00039_expression x t := by
  have ha := n00008_sound x t hnz
  have hb := n00005_sound x t hnz
  have hraw := rawSub_sound n00008_pair n00005_pair x t ha.1 hb.1
  have hred := checkReduction_sound n00039_checked x t hraw.1
  dsimp only [n00039_reduction] at hred
  refine ⟨hred.1, ?_⟩
  rw [← hred.2, hraw.2]
  simp only [n00039_expression, ha.2, hb.2]
theorem n00040_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00040_pair.NonzeroDenominator x t ∧ n00040_pair.value x t = n00040_expression x t := by
  simpa [n00040_pair, n00040_expression, rationalConst, Polynomial2.const] using rationalConst_sound 8158 1 x t (by decide)
theorem n00041_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00041_pair.NonzeroDenominator x t ∧ n00041_pair.value x t = n00041_expression x t := by
  have ha := n00040_sound x t hnz
  have hb := n00039_sound x t hnz
  have hraw := rawMul_sound n00040_pair n00039_pair x t ha.1 hb.1
  have hred := checkReduction_sound n00041_checked x t hraw.1
  dsimp only [n00041_reduction] at hred
  refine ⟨hred.1, ?_⟩
  rw [← hred.2, hraw.2]
  simp only [n00041_expression, ha.2, hb.2]
theorem n00042_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00042_pair.NonzeroDenominator x t ∧ n00042_pair.value x t = n00042_expression x t := by
  have ha := n00038_sound x t hnz
  have hb := n00041_sound x t hnz
  have hraw := rawAdd_sound n00038_pair n00041_pair x t ha.1 hb.1
  have hred := checkReduction_sound n00042_checked x t hraw.1
  dsimp only [n00042_reduction] at hred
  refine ⟨hred.1, ?_⟩
  rw [← hred.2, hraw.2]
  simp only [n00042_expression, ha.2, hb.2]
theorem n00043_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00043_pair.NonzeroDenominator x t ∧ n00043_pair.value x t = n00043_expression x t := by
  simpa [n00043_pair, n00043_expression, rationalConst, Polynomial2.const] using rationalConst_sound 65536 1 x t (by decide)
theorem n00044_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00044_pair.NonzeroDenominator x t ∧ n00044_pair.value x t = n00044_expression x t := by
  have ha := n00042_sound x t hnz
  have hb := n00043_sound x t hnz
  have hd : n00043_pair.value x t ≠ 0 := by
    rw [hb.2]
    simpa only [divisorExpression] using hnz ⟨9, by decide⟩
  have hraw := rawDiv_sound n00042_pair n00043_pair x t ha.1 hb.1 hd
  have hred := checkReduction_sound n00044_checked x t hraw.1
  dsimp only [n00044_reduction] at hred
  refine ⟨hred.1, ?_⟩
  rw [← hred.2, hraw.2]
  simp only [n00044_expression, ha.2, hb.2]
theorem n00045_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00045_pair.NonzeroDenominator x t ∧ n00045_pair.value x t = n00045_expression x t := by
  simpa [n00045_pair, n00045_expression, rationalConst, Polynomial2.const] using rationalConst_sound 20496 1 x t (by decide)
theorem n00046_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00046_pair.NonzeroDenominator x t ∧ n00046_pair.value x t = n00046_expression x t := by
  simpa [n00046_pair, n00046_expression, rationalConst, Polynomial2.const] using rationalConst_sound 41265 1 x t (by decide)
theorem n00047_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00047_pair.NonzeroDenominator x t ∧ n00047_pair.value x t = n00047_expression x t := by
  have ha := n00046_sound x t hnz
  have hb := n00039_sound x t hnz
  have hraw := rawMul_sound n00046_pair n00039_pair x t ha.1 hb.1
  have hred := checkReduction_sound n00047_checked x t hraw.1
  dsimp only [n00047_reduction] at hred
  refine ⟨hred.1, ?_⟩
  rw [← hred.2, hraw.2]
  simp only [n00047_expression, ha.2, hb.2]
theorem n00048_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00048_pair.NonzeroDenominator x t ∧ n00048_pair.value x t = n00048_expression x t := by
  have ha := n00045_sound x t hnz
  have hb := n00047_sound x t hnz
  have hraw := rawAdd_sound n00045_pair n00047_pair x t ha.1 hb.1
  have hred := checkReduction_sound n00048_checked x t hraw.1
  dsimp only [n00048_reduction] at hred
  refine ⟨hred.1, ?_⟩
  rw [← hred.2, hraw.2]
  simp only [n00048_expression, ha.2, hb.2]
theorem n00049_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00049_pair.NonzeroDenominator x t ∧ n00049_pair.value x t = n00049_expression x t := by
  have ha := n00048_sound x t hnz
  have hb := n00043_sound x t hnz
  have hd : n00043_pair.value x t ≠ 0 := by
    rw [hb.2]
    simpa only [divisorExpression] using hnz ⟨10, by decide⟩
  have hraw := rawDiv_sound n00048_pair n00043_pair x t ha.1 hb.1 hd
  have hred := checkReduction_sound n00049_checked x t hraw.1
  dsimp only [n00049_reduction] at hred
  refine ⟨hred.1, ?_⟩
  rw [← hred.2, hraw.2]
  simp only [n00049_expression, ha.2, hb.2]
theorem n00050_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00050_pair.NonzeroDenominator x t ∧ n00050_pair.value x t = n00050_expression x t := by
  simpa [n00050_pair, n00050_expression, rationalConst, Polynomial2.const] using rationalConst_sound 29750 1 x t (by decide)
theorem n00051_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00051_pair.NonzeroDenominator x t ∧ n00051_pair.value x t = n00051_expression x t := by
  simpa [n00051_pair, n00051_expression, rationalConst, Polynomial2.const] using rationalConst_sound 4333 1 x t (by decide)
theorem n00052_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00052_pair.NonzeroDenominator x t ∧ n00052_pair.value x t = n00052_expression x t := by
  have ha := n00051_sound x t hnz
  have hb := n00039_sound x t hnz
  have hraw := rawMul_sound n00051_pair n00039_pair x t ha.1 hb.1
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
  have hb := n00043_sound x t hnz
  have hd : n00043_pair.value x t ≠ 0 := by
    rw [hb.2]
    simpa only [divisorExpression] using hnz ⟨11, by decide⟩
  have hraw := rawDiv_sound n00053_pair n00043_pair x t ha.1 hb.1 hd
  have hred := checkReduction_sound n00054_checked x t hraw.1
  dsimp only [n00054_reduction] at hred
  refine ⟨hred.1, ?_⟩
  rw [← hred.2, hraw.2]
  simp only [n00054_expression, ha.2, hb.2]
theorem n00055_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00055_pair.NonzeroDenominator x t ∧ n00055_pair.value x t = n00055_expression x t := by
  simpa [n00055_pair, n00055_expression, rationalConst, Polynomial2.const] using rationalConst_sound 9083 1 x t (by decide)
theorem n00056_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00056_pair.NonzeroDenominator x t ∧ n00056_pair.value x t = n00056_expression x t := by
  simpa [n00056_pair, n00056_expression, rationalConst, Polynomial2.const] using rationalConst_sound (-11181) 1 x t (by decide)
theorem n00057_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00057_pair.NonzeroDenominator x t ∧ n00057_pair.value x t = n00057_expression x t := by
  have ha := n00056_sound x t hnz
  have hb := n00039_sound x t hnz
  have hraw := rawMul_sound n00056_pair n00039_pair x t ha.1 hb.1
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
  have hb := n00043_sound x t hnz
  have hd : n00043_pair.value x t ≠ 0 := by
    rw [hb.2]
    simpa only [divisorExpression] using hnz ⟨12, by decide⟩
  have hraw := rawDiv_sound n00058_pair n00043_pair x t ha.1 hb.1 hd
  have hred := checkReduction_sound n00059_checked x t hraw.1
  dsimp only [n00059_reduction] at hred
  refine ⟨hred.1, ?_⟩
  rw [← hred.2, hraw.2]
  simp only [n00059_expression, ha.2, hb.2]
theorem n00060_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00060_pair.NonzeroDenominator x t ∧ n00060_pair.value x t = n00060_expression x t := by
  have ha := n00029_sound x t hnz
  have hraw := rawPow_sound n00029_pair 2 x t ha.1
  have hred := checkReduction_sound n00060_checked x t hraw.1
  dsimp only [n00060_reduction] at hred
  refine ⟨hred.1, ?_⟩
  rw [← hred.2, hraw.2]
  simp only [n00060_expression, ha.2]
theorem n00061_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00061_pair.NonzeroDenominator x t ∧ n00061_pair.value x t = n00061_expression x t := by
  have ha := n00004_sound x t hnz
  have hb := n00029_sound x t hnz
  have hraw := rawSub_sound n00004_pair n00029_pair x t ha.1 hb.1
  have hred := checkReduction_sound n00061_checked x t hraw.1
  dsimp only [n00061_reduction] at hred
  refine ⟨hred.1, ?_⟩
  rw [← hred.2, hraw.2]
  simp only [n00061_expression, ha.2, hb.2]
theorem n00062_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00062_pair.NonzeroDenominator x t ∧ n00062_pair.value x t = n00062_expression x t := by
  simpa [n00062_pair, n00062_expression, rationalConst, Polynomial2.const] using rationalConst_sound 6 1 x t (by decide)
theorem n00063_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00063_pair.NonzeroDenominator x t ∧ n00063_pair.value x t = n00063_expression x t := by
  simpa [n00063_pair, n00063_expression, rationalConst, Polynomial2.const] using rationalConst_sound 12 1 x t (by decide)
theorem n00064_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00064_pair.NonzeroDenominator x t ∧ n00064_pair.value x t = n00064_expression x t := by
  have ha := n00063_sound x t hnz
  have hb := n00029_sound x t hnz
  have hraw := rawMul_sound n00063_pair n00029_pair x t ha.1 hb.1
  have hred := checkReduction_sound n00064_checked x t hraw.1
  dsimp only [n00064_reduction] at hred
  refine ⟨hred.1, ?_⟩
  rw [← hred.2, hraw.2]
  simp only [n00064_expression, ha.2, hb.2]
theorem n00065_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00065_pair.NonzeroDenominator x t ∧ n00065_pair.value x t = n00065_expression x t := by
  have ha := n00060_sound x t hnz
  have hb := n00064_sound x t hnz
  have hraw := rawSub_sound n00060_pair n00064_pair x t ha.1 hb.1
  have hred := checkReduction_sound n00065_checked x t hraw.1
  dsimp only [n00065_reduction] at hred
  refine ⟨hred.1, ?_⟩
  rw [← hred.2, hraw.2]
  simp only [n00065_expression, ha.2, hb.2]
theorem n00066_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00066_pair.NonzeroDenominator x t ∧ n00066_pair.value x t = n00066_expression x t := by
  have ha := n00065_sound x t hnz
  have hb := n00063_sound x t hnz
  have hraw := rawAdd_sound n00065_pair n00063_pair x t ha.1 hb.1
  have hred := checkReduction_sound n00066_checked x t hraw.1
  dsimp only [n00066_reduction] at hred
  refine ⟨hred.1, ?_⟩
  rw [← hred.2, hraw.2]
  simp only [n00066_expression, ha.2, hb.2]
theorem n00067_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00067_pair.NonzeroDenominator x t ∧ n00067_pair.value x t = n00067_expression x t := by
  have ha := n00029_sound x t hnz
  have hb := n00066_sound x t hnz
  have hraw := rawMul_sound n00029_pair n00066_pair x t ha.1 hb.1
  have hred := checkReduction_sound n00067_checked x t hraw.1
  dsimp only [n00067_reduction] at hred
  refine ⟨hred.1, ?_⟩
  rw [← hred.2, hraw.2]
  simp only [n00067_expression, ha.2, hb.2]
theorem n00068_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00068_pair.NonzeroDenominator x t ∧ n00068_pair.value x t = n00068_expression x t := by
  have ha := n00062_sound x t hnz
  have hb := n00030_sound x t hnz
  have hraw := rawMul_sound n00062_pair n00030_pair x t ha.1 hb.1
  have hred := checkReduction_sound n00068_checked x t hraw.1
  dsimp only [n00068_reduction] at hred
  refine ⟨hred.1, ?_⟩
  rw [← hred.2, hraw.2]
  simp only [n00068_expression, ha.2, hb.2]
theorem n00069_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00069_pair.NonzeroDenominator x t ∧ n00069_pair.value x t = n00069_expression x t := by
  have ha := n00068_sound x t hnz
  have hb := n00061_sound x t hnz
  have hraw := rawMul_sound n00068_pair n00061_pair x t ha.1 hb.1
  have hred := checkReduction_sound n00069_checked x t hraw.1
  dsimp only [n00069_reduction] at hred
  refine ⟨hred.1, ?_⟩
  rw [← hred.2, hraw.2]
  simp only [n00069_expression, ha.2, hb.2]
theorem n00070_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00070_pair.NonzeroDenominator x t ∧ n00070_pair.value x t = n00070_expression x t := by
  have ha := n00067_sound x t hnz
  have hb := n00069_sound x t hnz
  have hd : n00069_pair.value x t ≠ 0 := by
    rw [hb.2]
    simpa only [divisorExpression] using hnz ⟨13, by decide⟩
  have hraw := rawDiv_sound n00067_pair n00069_pair x t ha.1 hb.1 hd
  have hred := checkReduction_sound n00070_checked x t hraw.1
  dsimp only [n00070_reduction] at hred
  refine ⟨hred.1, ?_⟩
  rw [← hred.2, hraw.2]
  simp only [n00070_expression, ha.2, hb.2]
theorem n00071_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00071_pair.NonzeroDenominator x t ∧ n00071_pair.value x t = n00071_expression x t := by
  have ha := n00033_sound x t hnz
  have hb := n00004_sound x t hnz
  have hd : n00004_pair.value x t ≠ 0 := by
    rw [hb.2]
    simpa only [divisorExpression] using hnz ⟨14, by decide⟩
  have hraw := rawDiv_sound n00033_pair n00004_pair x t ha.1 hb.1 hd
  have hred := checkReduction_sound n00071_checked x t hraw.1
  dsimp only [n00071_reduction] at hred
  refine ⟨hred.1, ?_⟩
  rw [← hred.2, hraw.2]
  simp only [n00071_expression, ha.2, hb.2]
theorem n00072_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00072_pair.NonzeroDenominator x t ∧ n00072_pair.value x t = n00072_expression x t := by
  have ha := n00006_sound x t hnz
  have hb := n00071_sound x t hnz
  have hraw := rawSub_sound n00006_pair n00071_pair x t ha.1 hb.1
  have hred := checkReduction_sound n00072_checked x t hraw.1
  dsimp only [n00072_reduction] at hred
  refine ⟨hred.1, ?_⟩
  rw [← hred.2, hraw.2]
  simp only [n00072_expression, ha.2, hb.2]
theorem n00073_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00073_pair.NonzeroDenominator x t ∧ n00073_pair.value x t = n00073_expression x t := by
  have ha := n00033_sound x t hnz
  have hb := n00033_sound x t hnz
  have hraw := rawMul_sound n00033_pair n00033_pair x t ha.1 hb.1
  have hred := checkReduction_sound n00073_checked x t hraw.1
  dsimp only [n00073_reduction] at hred
  refine ⟨hred.1, ?_⟩
  rw [← hred.2, hraw.2]
  simp only [n00073_expression, ha.2, hb.2]
theorem n00074_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00074_pair.NonzeroDenominator x t ∧ n00074_pair.value x t = n00074_expression x t := by
  have ha := n00073_sound x t hnz
  have hb := n00063_sound x t hnz
  have hd : n00063_pair.value x t ≠ 0 := by
    rw [hb.2]
    simpa only [divisorExpression] using hnz ⟨15, by decide⟩
  have hraw := rawDiv_sound n00073_pair n00063_pair x t ha.1 hb.1 hd
  have hred := checkReduction_sound n00074_checked x t hraw.1
  dsimp only [n00074_reduction] at hred
  refine ⟨hred.1, ?_⟩
  rw [← hred.2, hraw.2]
  simp only [n00074_expression, ha.2, hb.2]
theorem n00075_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00075_pair.NonzeroDenominator x t ∧ n00075_pair.value x t = n00075_expression x t := by
  have ha := n00072_sound x t hnz
  have hb := n00074_sound x t hnz
  have hraw := rawSub_sound n00072_pair n00074_pair x t ha.1 hb.1
  have hred := checkReduction_sound n00075_checked x t hraw.1
  dsimp only [n00075_reduction] at hred
  refine ⟨hred.1, ?_⟩
  rw [← hred.2, hraw.2]
  simp only [n00075_expression, ha.2, hb.2]
theorem n00076_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00076_pair.NonzeroDenominator x t ∧ n00076_pair.value x t = n00076_expression x t := by
  have ha := n00054_sound x t hnz
  have hb := n00075_sound x t hnz
  have hraw := rawMul_sound n00054_pair n00075_pair x t ha.1 hb.1
  have hred := checkReduction_sound n00076_checked x t hraw.1
  dsimp only [n00076_reduction] at hred
  refine ⟨hred.1, ?_⟩
  rw [← hred.2, hraw.2]
  simp only [n00076_expression, ha.2, hb.2]
theorem n00077_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00077_pair.NonzeroDenominator x t ∧ n00077_pair.value x t = n00077_expression x t := by
  simpa [n00077_pair, n00077_expression, rationalConst, Polynomial2.const] using rationalConst_sound 7 10 x t (by decide)
theorem n00078_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00078_pair.NonzeroDenominator x t ∧ n00078_pair.value x t = n00078_expression x t := by
  simpa [n00078_pair, n00078_expression, rationalConst, Polynomial2.const] using rationalConst_sound 5 6 x t (by decide)
theorem n00079_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00079_pair.NonzeroDenominator x t ∧ n00079_pair.value x t = n00079_expression x t := by
  have ha := n00006_sound x t hnz
  have hb := n00034_sound x t hnz
  have hraw := rawMul_sound n00006_pair n00034_pair x t ha.1 hb.1
  have hred := checkReduction_sound n00079_checked x t hraw.1
  dsimp only [n00079_reduction] at hred
  refine ⟨hred.1, ?_⟩
  rw [← hred.2, hraw.2]
  simp only [n00079_expression, ha.2, hb.2]
theorem n00080_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00080_pair.NonzeroDenominator x t ∧ n00080_pair.value x t = n00080_expression x t := by
  have ha := n00079_sound x t hnz
  have hb := n00076_sound x t hnz
  have hraw := rawAdd_sound n00079_pair n00076_pair x t ha.1 hb.1
  have hred := checkReduction_sound n00080_checked x t hraw.1
  dsimp only [n00080_reduction] at hred
  refine ⟨hred.1, ?_⟩
  rw [← hred.2, hraw.2]
  simp only [n00080_expression, ha.2, hb.2]
theorem n00081_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00081_pair.NonzeroDenominator x t ∧ n00081_pair.value x t = n00081_expression x t := by
  have ha := n00054_sound x t hnz
  have hb := n00059_sound x t hnz
  have hraw := rawSub_sound n00054_pair n00059_pair x t ha.1 hb.1
  have hred := checkReduction_sound n00081_checked x t hraw.1
  dsimp only [n00081_reduction] at hred
  refine ⟨hred.1, ?_⟩
  rw [← hred.2, hraw.2]
  simp only [n00081_expression, ha.2, hb.2]
theorem n00082_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00082_pair.NonzeroDenominator x t ∧ n00082_pair.value x t = n00082_expression x t := by
  have ha := n00004_sound x t hnz
  have hb := n00081_sound x t hnz
  have hraw := rawMul_sound n00004_pair n00081_pair x t ha.1 hb.1
  have hred := checkReduction_sound n00082_checked x t hraw.1
  dsimp only [n00082_reduction] at hred
  refine ⟨hred.1, ?_⟩
  rw [← hred.2, hraw.2]
  simp only [n00082_expression, ha.2, hb.2]
theorem n00083_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00083_pair.NonzeroDenominator x t ∧ n00083_pair.value x t = n00083_expression x t := by
  have ha := n00082_sound x t hnz
  have hb := n00077_sound x t hnz
  have hraw := rawMul_sound n00082_pair n00077_pair x t ha.1 hb.1
  have hred := checkReduction_sound n00083_checked x t hraw.1
  dsimp only [n00083_reduction] at hred
  refine ⟨hred.1, ?_⟩
  rw [← hred.2, hraw.2]
  simp only [n00083_expression, ha.2, hb.2]
theorem n00084_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00084_pair.NonzeroDenominator x t ∧ n00084_pair.value x t = n00084_expression x t := by
  have ha := n00004_sound x t hnz
  have hb := n00080_sound x t hnz
  have hraw := rawMul_sound n00004_pair n00080_pair x t ha.1 hb.1
  have hred := checkReduction_sound n00084_checked x t hraw.1
  dsimp only [n00084_reduction] at hred
  refine ⟨hred.1, ?_⟩
  rw [← hred.2, hraw.2]
  simp only [n00084_expression, ha.2, hb.2]
theorem n00085_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00085_pair.NonzeroDenominator x t ∧ n00085_pair.value x t = n00085_expression x t := by
  have ha := n00070_sound x t hnz
  have hb := n00077_sound x t hnz
  have hraw := rawMul_sound n00070_pair n00077_pair x t ha.1 hb.1
  have hred := checkReduction_sound n00085_checked x t hraw.1
  dsimp only [n00085_reduction] at hred
  refine ⟨hred.1, ?_⟩
  rw [← hred.2, hraw.2]
  simp only [n00085_expression, ha.2, hb.2]
theorem n00086_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00086_pair.NonzeroDenominator x t ∧ n00086_pair.value x t = n00086_expression x t := by
  have ha := n00006_sound x t hnz
  have hb := n00085_sound x t hnz
  have hraw := rawSub_sound n00006_pair n00085_pair x t ha.1 hb.1
  have hred := checkReduction_sound n00086_checked x t hraw.1
  dsimp only [n00086_reduction] at hred
  refine ⟨hred.1, ?_⟩
  rw [← hred.2, hraw.2]
  simp only [n00086_expression, ha.2, hb.2]
theorem n00087_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00087_pair.NonzeroDenominator x t ∧ n00087_pair.value x t = n00087_expression x t := by
  have ha := n00084_sound x t hnz
  have hb := n00086_sound x t hnz
  have hraw := rawMul_sound n00084_pair n00086_pair x t ha.1 hb.1
  have hred := checkReduction_sound n00087_checked x t hraw.1
  dsimp only [n00087_reduction] at hred
  refine ⟨hred.1, ?_⟩
  rw [← hred.2, hraw.2]
  simp only [n00087_expression, ha.2, hb.2]
theorem n00088_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00088_pair.NonzeroDenominator x t ∧ n00088_pair.value x t = n00088_expression x t := by
  have ha := n00087_sound x t hnz
  have hb := n00044_sound x t hnz
  have hraw := rawSub_sound n00087_pair n00044_pair x t ha.1 hb.1
  have hred := checkReduction_sound n00088_checked x t hraw.1
  dsimp only [n00088_reduction] at hred
  refine ⟨hred.1, ?_⟩
  rw [← hred.2, hraw.2]
  simp only [n00088_expression, ha.2, hb.2]
theorem n00089_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00089_pair.NonzeroDenominator x t ∧ n00089_pair.value x t = n00089_expression x t := by
  have ha := n00088_sound x t hnz
  have hb := n00049_sound x t hnz
  have hraw := rawSub_sound n00088_pair n00049_pair x t ha.1 hb.1
  have hred := checkReduction_sound n00089_checked x t hraw.1
  dsimp only [n00089_reduction] at hred
  refine ⟨hred.1, ?_⟩
  rw [← hred.2, hraw.2]
  simp only [n00089_expression, ha.2, hb.2]
theorem n00090_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00090_pair.NonzeroDenominator x t ∧ n00090_pair.value x t = n00090_expression x t := by
  have ha := n00033_sound x t hnz
  have hb := n00089_sound x t hnz
  have hraw := rawMul_sound n00033_pair n00089_pair x t ha.1 hb.1
  have hred := checkReduction_sound n00090_checked x t hraw.1
  dsimp only [n00090_reduction] at hred
  refine ⟨hred.1, ?_⟩
  rw [← hred.2, hraw.2]
  simp only [n00090_expression, ha.2, hb.2]
theorem n00091_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00091_pair.NonzeroDenominator x t ∧ n00091_pair.value x t = n00091_expression x t := by
  have ha := n00083_sound x t hnz
  have hb := n00090_sound x t hnz
  have hraw := rawAdd_sound n00083_pair n00090_pair x t ha.1 hb.1
  have hred := checkReduction_sound n00091_checked x t hraw.1
  dsimp only [n00091_reduction] at hred
  refine ⟨hred.1, ?_⟩
  rw [← hred.2, hraw.2]
  simp only [n00091_expression, ha.2, hb.2]
theorem n00092_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00092_pair.NonzeroDenominator x t ∧ n00092_pair.value x t = n00092_expression x t := by
  have ha := n00037_sound x t hnz
  have hb := n00034_sound x t hnz
  have hraw := rawMul_sound n00037_pair n00034_pair x t ha.1 hb.1
  have hred := checkReduction_sound n00092_checked x t hraw.1
  dsimp only [n00092_reduction] at hred
  refine ⟨hred.1, ?_⟩
  rw [← hred.2, hraw.2]
  simp only [n00092_expression, ha.2, hb.2]
theorem n00093_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00093_pair.NonzeroDenominator x t ∧ n00093_pair.value x t = n00093_expression x t := by
  have ha := n00092_sound x t hnz
  have hb := n00076_sound x t hnz
  have hraw := rawAdd_sound n00092_pair n00076_pair x t ha.1 hb.1
  have hred := checkReduction_sound n00093_checked x t hraw.1
  dsimp only [n00093_reduction] at hred
  refine ⟨hred.1, ?_⟩
  rw [← hred.2, hraw.2]
  simp only [n00093_expression, ha.2, hb.2]
theorem n00094_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00094_pair.NonzeroDenominator x t ∧ n00094_pair.value x t = n00094_expression x t := by
  have ha := n00004_sound x t hnz
  have hb := n00093_sound x t hnz
  have hraw := rawMul_sound n00004_pair n00093_pair x t ha.1 hb.1
  have hred := checkReduction_sound n00094_checked x t hraw.1
  dsimp only [n00094_reduction] at hred
  refine ⟨hred.1, ?_⟩
  rw [← hred.2, hraw.2]
  simp only [n00094_expression, ha.2, hb.2]
theorem n00095_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00095_pair.NonzeroDenominator x t ∧ n00095_pair.value x t = n00095_expression x t := by
  have ha := n00094_sound x t hnz
  have hb := n00086_sound x t hnz
  have hraw := rawMul_sound n00094_pair n00086_pair x t ha.1 hb.1
  have hred := checkReduction_sound n00095_checked x t hraw.1
  dsimp only [n00095_reduction] at hred
  refine ⟨hred.1, ?_⟩
  rw [← hred.2, hraw.2]
  simp only [n00095_expression, ha.2, hb.2]
theorem n00096_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00096_pair.NonzeroDenominator x t ∧ n00096_pair.value x t = n00096_expression x t := by
  have ha := n00095_sound x t hnz
  have hb := n00044_sound x t hnz
  have hraw := rawSub_sound n00095_pair n00044_pair x t ha.1 hb.1
  have hred := checkReduction_sound n00096_checked x t hraw.1
  dsimp only [n00096_reduction] at hred
  refine ⟨hred.1, ?_⟩
  rw [← hred.2, hraw.2]
  simp only [n00096_expression, ha.2, hb.2]
theorem n00097_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00097_pair.NonzeroDenominator x t ∧ n00097_pair.value x t = n00097_expression x t := by
  have ha := n00096_sound x t hnz
  have hb := n00049_sound x t hnz
  have hraw := rawSub_sound n00096_pair n00049_pair x t ha.1 hb.1
  have hred := checkReduction_sound n00097_checked x t hraw.1
  dsimp only [n00097_reduction] at hred
  refine ⟨hred.1, ?_⟩
  rw [← hred.2, hraw.2]
  simp only [n00097_expression, ha.2, hb.2]
theorem n00098_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00098_pair.NonzeroDenominator x t ∧ n00098_pair.value x t = n00098_expression x t := by
  have ha := n00033_sound x t hnz
  have hb := n00097_sound x t hnz
  have hraw := rawMul_sound n00033_pair n00097_pair x t ha.1 hb.1
  have hred := checkReduction_sound n00098_checked x t hraw.1
  dsimp only [n00098_reduction] at hred
  refine ⟨hred.1, ?_⟩
  rw [← hred.2, hraw.2]
  simp only [n00098_expression, ha.2, hb.2]
theorem n00099_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00099_pair.NonzeroDenominator x t ∧ n00099_pair.value x t = n00099_expression x t := by
  have ha := n00083_sound x t hnz
  have hb := n00098_sound x t hnz
  have hraw := rawAdd_sound n00083_pair n00098_pair x t ha.1 hb.1
  have hred := checkReduction_sound n00099_checked x t hraw.1
  dsimp only [n00099_reduction] at hred
  refine ⟨hred.1, ?_⟩
  rw [← hred.2, hraw.2]
  simp only [n00099_expression, ha.2, hb.2]
theorem n00100_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00100_pair.NonzeroDenominator x t ∧ n00100_pair.value x t = n00100_expression x t := by
  have ha := n00082_sound x t hnz
  have hb := n00078_sound x t hnz
  have hraw := rawMul_sound n00082_pair n00078_pair x t ha.1 hb.1
  have hred := checkReduction_sound n00100_checked x t hraw.1
  dsimp only [n00100_reduction] at hred
  refine ⟨hred.1, ?_⟩
  rw [← hred.2, hraw.2]
  simp only [n00100_expression, ha.2, hb.2]
theorem n00101_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00101_pair.NonzeroDenominator x t ∧ n00101_pair.value x t = n00101_expression x t := by
  have ha := n00070_sound x t hnz
  have hb := n00078_sound x t hnz
  have hraw := rawMul_sound n00070_pair n00078_pair x t ha.1 hb.1
  have hred := checkReduction_sound n00101_checked x t hraw.1
  dsimp only [n00101_reduction] at hred
  refine ⟨hred.1, ?_⟩
  rw [← hred.2, hraw.2]
  simp only [n00101_expression, ha.2, hb.2]
theorem n00102_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00102_pair.NonzeroDenominator x t ∧ n00102_pair.value x t = n00102_expression x t := by
  have ha := n00006_sound x t hnz
  have hb := n00101_sound x t hnz
  have hraw := rawSub_sound n00006_pair n00101_pair x t ha.1 hb.1
  have hred := checkReduction_sound n00102_checked x t hraw.1
  dsimp only [n00102_reduction] at hred
  refine ⟨hred.1, ?_⟩
  rw [← hred.2, hraw.2]
  simp only [n00102_expression, ha.2, hb.2]
theorem n00103_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00103_pair.NonzeroDenominator x t ∧ n00103_pair.value x t = n00103_expression x t := by
  have ha := n00084_sound x t hnz
  have hb := n00102_sound x t hnz
  have hraw := rawMul_sound n00084_pair n00102_pair x t ha.1 hb.1
  have hred := checkReduction_sound n00103_checked x t hraw.1
  dsimp only [n00103_reduction] at hred
  refine ⟨hred.1, ?_⟩
  rw [← hred.2, hraw.2]
  simp only [n00103_expression, ha.2, hb.2]
theorem n00104_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00104_pair.NonzeroDenominator x t ∧ n00104_pair.value x t = n00104_expression x t := by
  have ha := n00103_sound x t hnz
  have hb := n00044_sound x t hnz
  have hraw := rawSub_sound n00103_pair n00044_pair x t ha.1 hb.1
  have hred := checkReduction_sound n00104_checked x t hraw.1
  dsimp only [n00104_reduction] at hred
  refine ⟨hred.1, ?_⟩
  rw [← hred.2, hraw.2]
  simp only [n00104_expression, ha.2, hb.2]
theorem n00105_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00105_pair.NonzeroDenominator x t ∧ n00105_pair.value x t = n00105_expression x t := by
  have ha := n00104_sound x t hnz
  have hb := n00049_sound x t hnz
  have hraw := rawSub_sound n00104_pair n00049_pair x t ha.1 hb.1
  have hred := checkReduction_sound n00105_checked x t hraw.1
  dsimp only [n00105_reduction] at hred
  refine ⟨hred.1, ?_⟩
  rw [← hred.2, hraw.2]
  simp only [n00105_expression, ha.2, hb.2]
theorem n00106_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00106_pair.NonzeroDenominator x t ∧ n00106_pair.value x t = n00106_expression x t := by
  have ha := n00033_sound x t hnz
  have hb := n00105_sound x t hnz
  have hraw := rawMul_sound n00033_pair n00105_pair x t ha.1 hb.1
  have hred := checkReduction_sound n00106_checked x t hraw.1
  dsimp only [n00106_reduction] at hred
  refine ⟨hred.1, ?_⟩
  rw [← hred.2, hraw.2]
  simp only [n00106_expression, ha.2, hb.2]
theorem n00107_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00107_pair.NonzeroDenominator x t ∧ n00107_pair.value x t = n00107_expression x t := by
  have ha := n00100_sound x t hnz
  have hb := n00106_sound x t hnz
  have hraw := rawAdd_sound n00100_pair n00106_pair x t ha.1 hb.1
  have hred := checkReduction_sound n00107_checked x t hraw.1
  dsimp only [n00107_reduction] at hred
  refine ⟨hred.1, ?_⟩
  rw [← hred.2, hraw.2]
  simp only [n00107_expression, ha.2, hb.2]
theorem n00108_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00108_pair.NonzeroDenominator x t ∧ n00108_pair.value x t = n00108_expression x t := by
  have ha := n00094_sound x t hnz
  have hb := n00102_sound x t hnz
  have hraw := rawMul_sound n00094_pair n00102_pair x t ha.1 hb.1
  have hred := checkReduction_sound n00108_checked x t hraw.1
  dsimp only [n00108_reduction] at hred
  refine ⟨hred.1, ?_⟩
  rw [← hred.2, hraw.2]
  simp only [n00108_expression, ha.2, hb.2]
theorem n00109_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00109_pair.NonzeroDenominator x t ∧ n00109_pair.value x t = n00109_expression x t := by
  have ha := n00108_sound x t hnz
  have hb := n00044_sound x t hnz
  have hraw := rawSub_sound n00108_pair n00044_pair x t ha.1 hb.1
  have hred := checkReduction_sound n00109_checked x t hraw.1
  dsimp only [n00109_reduction] at hred
  refine ⟨hred.1, ?_⟩
  rw [← hred.2, hraw.2]
  simp only [n00109_expression, ha.2, hb.2]
theorem n00110_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00110_pair.NonzeroDenominator x t ∧ n00110_pair.value x t = n00110_expression x t := by
  have ha := n00109_sound x t hnz
  have hb := n00049_sound x t hnz
  have hraw := rawSub_sound n00109_pair n00049_pair x t ha.1 hb.1
  have hred := checkReduction_sound n00110_checked x t hraw.1
  dsimp only [n00110_reduction] at hred
  refine ⟨hred.1, ?_⟩
  rw [← hred.2, hraw.2]
  simp only [n00110_expression, ha.2, hb.2]
theorem n00111_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00111_pair.NonzeroDenominator x t ∧ n00111_pair.value x t = n00111_expression x t := by
  have ha := n00033_sound x t hnz
  have hb := n00110_sound x t hnz
  have hraw := rawMul_sound n00033_pair n00110_pair x t ha.1 hb.1
  have hred := checkReduction_sound n00111_checked x t hraw.1
  dsimp only [n00111_reduction] at hred
  refine ⟨hred.1, ?_⟩
  rw [← hred.2, hraw.2]
  simp only [n00111_expression, ha.2, hb.2]
theorem n00112_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00112_pair.NonzeroDenominator x t ∧ n00112_pair.value x t = n00112_expression x t := by
  have ha := n00100_sound x t hnz
  have hb := n00111_sound x t hnz
  have hraw := rawAdd_sound n00100_pair n00111_pair x t ha.1 hb.1
  have hred := checkReduction_sound n00112_checked x t hraw.1
  dsimp only [n00112_reduction] at hred
  refine ⟨hred.1, ?_⟩
  rw [← hred.2, hraw.2]
  simp only [n00112_expression, ha.2, hb.2]
theorem n00113_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00113_pair.NonzeroDenominator x t ∧ n00113_pair.value x t = n00113_expression x t := by
  have ha := n00034_sound x t hnz
  have hb := n00076_sound x t hnz
  have hraw := rawAdd_sound n00034_pair n00076_pair x t ha.1 hb.1
  have hred := checkReduction_sound n00113_checked x t hraw.1
  dsimp only [n00113_reduction] at hred
  refine ⟨hred.1, ?_⟩
  rw [← hred.2, hraw.2]
  simp only [n00113_expression, ha.2, hb.2]
theorem n00114_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00114_pair.NonzeroDenominator x t ∧ n00114_pair.value x t = n00114_expression x t := by
  simpa [n00114_pair, n00114_expression, rationalConst, Polynomial2.const] using rationalConst_sound 10 1 x t (by decide)
theorem n00115_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00115_pair.NonzeroDenominator x t ∧ n00115_pair.value x t = n00115_expression x t := by
  have ha := n00114_sound x t hnz
  have hb := n00059_sound x t hnz
  have hraw := rawMul_sound n00114_pair n00059_pair x t ha.1 hb.1
  have hred := checkReduction_sound n00115_checked x t hraw.1
  dsimp only [n00115_reduction] at hred
  refine ⟨hred.1, ?_⟩
  rw [← hred.2, hraw.2]
  simp only [n00115_expression, ha.2, hb.2]
theorem n00116_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00116_pair.NonzeroDenominator x t ∧ n00116_pair.value x t = n00116_expression x t := by
  have ha := n00044_sound x t hnz
  have hb := n00049_sound x t hnz
  have hraw := rawAdd_sound n00044_pair n00049_pair x t ha.1 hb.1
  have hred := checkReduction_sound n00116_checked x t hraw.1
  dsimp only [n00116_reduction] at hred
  refine ⟨hred.1, ?_⟩
  rw [← hred.2, hraw.2]
  simp only [n00116_expression, ha.2, hb.2]
theorem n00117_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00117_pair.NonzeroDenominator x t ∧ n00117_pair.value x t = n00117_expression x t := by
  have ha := n00033_sound x t hnz
  have hb := n00116_sound x t hnz
  have hraw := rawMul_sound n00033_pair n00116_pair x t ha.1 hb.1
  have hred := checkReduction_sound n00117_checked x t hraw.1
  dsimp only [n00117_reduction] at hred
  refine ⟨hred.1, ?_⟩
  rw [← hred.2, hraw.2]
  simp only [n00117_expression, ha.2, hb.2]
theorem n00118_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00118_pair.NonzeroDenominator x t ∧ n00118_pair.value x t = n00118_expression x t := by
  have ha := n00115_sound x t hnz
  have hb := n00117_sound x t hnz
  have hraw := rawAdd_sound n00115_pair n00117_pair x t ha.1 hb.1
  have hred := checkReduction_sound n00118_checked x t hraw.1
  dsimp only [n00118_reduction] at hred
  refine ⟨hred.1, ?_⟩
  rw [← hred.2, hraw.2]
  simp only [n00118_expression, ha.2, hb.2]
theorem n00119_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00119_pair.NonzeroDenominator x t ∧ n00119_pair.value x t = n00119_expression x t := by
  have ha := n00114_sound x t hnz
  have hb := n00025_sound x t hnz
  have hraw := rawMul_sound n00114_pair n00025_pair x t ha.1 hb.1
  have hred := checkReduction_sound n00119_checked x t hraw.1
  dsimp only [n00119_reduction] at hred
  refine ⟨hred.1, ?_⟩
  rw [← hred.2, hraw.2]
  simp only [n00119_expression, ha.2, hb.2]
theorem n00120_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00120_pair.NonzeroDenominator x t ∧ n00120_pair.value x t = n00120_expression x t := by
  have ha := n00077_sound x t hnz
  have hb := n00119_sound x t hnz
  have hraw := rawAdd_sound n00077_pair n00119_pair x t ha.1 hb.1
  have hred := checkReduction_sound n00120_checked x t hraw.1
  dsimp only [n00120_reduction] at hred
  refine ⟨hred.1, ?_⟩
  rw [← hred.2, hraw.2]
  simp only [n00120_expression, ha.2, hb.2]
theorem n00121_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00121_pair.NonzeroDenominator x t ∧ n00121_pair.value x t = n00121_expression x t := by
  have ha := n00081_sound x t hnz
  have hb := n00120_sound x t hnz
  have hraw := rawMul_sound n00081_pair n00120_pair x t ha.1 hb.1
  have hred := checkReduction_sound n00121_checked x t hraw.1
  dsimp only [n00121_reduction] at hred
  refine ⟨hred.1, ?_⟩
  rw [← hred.2, hraw.2]
  simp only [n00121_expression, ha.2, hb.2]
theorem n00122_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00122_pair.NonzeroDenominator x t ∧ n00122_pair.value x t = n00122_expression x t := by
  have ha := n00118_sound x t hnz
  have hb := n00121_sound x t hnz
  have hraw := rawAdd_sound n00118_pair n00121_pair x t ha.1 hb.1
  have hred := checkReduction_sound n00122_checked x t hraw.1
  dsimp only [n00122_reduction] at hred
  refine ⟨hred.1, ?_⟩
  rw [← hred.2, hraw.2]
  simp only [n00122_expression, ha.2, hb.2]
theorem n00123_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00123_pair.NonzeroDenominator x t ∧ n00123_pair.value x t = n00123_expression x t := by
  have ha := n00033_sound x t hnz
  have hb := n00113_sound x t hnz
  have hraw := rawMul_sound n00033_pair n00113_pair x t ha.1 hb.1
  have hred := checkReduction_sound n00123_checked x t hraw.1
  dsimp only [n00123_reduction] at hred
  refine ⟨hred.1, ?_⟩
  rw [← hred.2, hraw.2]
  simp only [n00123_expression, ha.2, hb.2]
theorem n00124_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00124_pair.NonzeroDenominator x t ∧ n00124_pair.value x t = n00124_expression x t := by
  have ha := n00070_sound x t hnz
  have hb := n00120_sound x t hnz
  have hraw := rawMul_sound n00070_pair n00120_pair x t ha.1 hb.1
  have hred := checkReduction_sound n00124_checked x t hraw.1
  dsimp only [n00124_reduction] at hred
  refine ⟨hred.1, ?_⟩
  rw [← hred.2, hraw.2]
  simp only [n00124_expression, ha.2, hb.2]
theorem n00125_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00125_pair.NonzeroDenominator x t ∧ n00125_pair.value x t = n00125_expression x t := by
  have ha := n00004_sound x t hnz
  have hb := n00124_sound x t hnz
  have hraw := rawAdd_sound n00004_pair n00124_pair x t ha.1 hb.1
  have hred := checkReduction_sound n00125_checked x t hraw.1
  dsimp only [n00125_reduction] at hred
  refine ⟨hred.1, ?_⟩
  rw [← hred.2, hraw.2]
  simp only [n00125_expression, ha.2, hb.2]
theorem n00126_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00126_pair.NonzeroDenominator x t ∧ n00126_pair.value x t = n00126_expression x t := by
  have ha := n00123_sound x t hnz
  have hb := n00125_sound x t hnz
  have hraw := rawMul_sound n00123_pair n00125_pair x t ha.1 hb.1
  have hred := checkReduction_sound n00126_checked x t hraw.1
  dsimp only [n00126_reduction] at hred
  refine ⟨hred.1, ?_⟩
  rw [← hred.2, hraw.2]
  simp only [n00126_expression, ha.2, hb.2]
theorem n00127_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00127_pair.NonzeroDenominator x t ∧ n00127_pair.value x t = n00127_expression x t := by
  have ha := n00122_sound x t hnz
  have hb := n00126_sound x t hnz
  have hraw := rawSub_sound n00122_pair n00126_pair x t ha.1 hb.1
  have hred := checkReduction_sound n00127_checked x t hraw.1
  dsimp only [n00127_reduction] at hred
  refine ⟨hred.1, ?_⟩
  rw [← hred.2, hraw.2]
  simp only [n00127_expression, ha.2, hb.2]
theorem n00128_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00128_pair.NonzeroDenominator x t ∧ n00128_pair.value x t = n00128_expression x t := by
  have ha := n00078_sound x t hnz
  have hb := n00119_sound x t hnz
  have hraw := rawAdd_sound n00078_pair n00119_pair x t ha.1 hb.1
  have hred := checkReduction_sound n00128_checked x t hraw.1
  dsimp only [n00128_reduction] at hred
  refine ⟨hred.1, ?_⟩
  rw [← hred.2, hraw.2]
  simp only [n00128_expression, ha.2, hb.2]
theorem n00129_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00129_pair.NonzeroDenominator x t ∧ n00129_pair.value x t = n00129_expression x t := by
  have ha := n00081_sound x t hnz
  have hb := n00128_sound x t hnz
  have hraw := rawMul_sound n00081_pair n00128_pair x t ha.1 hb.1
  have hred := checkReduction_sound n00129_checked x t hraw.1
  dsimp only [n00129_reduction] at hred
  refine ⟨hred.1, ?_⟩
  rw [← hred.2, hraw.2]
  simp only [n00129_expression, ha.2, hb.2]
theorem n00130_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00130_pair.NonzeroDenominator x t ∧ n00130_pair.value x t = n00130_expression x t := by
  have ha := n00118_sound x t hnz
  have hb := n00129_sound x t hnz
  have hraw := rawAdd_sound n00118_pair n00129_pair x t ha.1 hb.1
  have hred := checkReduction_sound n00130_checked x t hraw.1
  dsimp only [n00130_reduction] at hred
  refine ⟨hred.1, ?_⟩
  rw [← hred.2, hraw.2]
  simp only [n00130_expression, ha.2, hb.2]
theorem n00131_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00131_pair.NonzeroDenominator x t ∧ n00131_pair.value x t = n00131_expression x t := by
  have ha := n00070_sound x t hnz
  have hb := n00128_sound x t hnz
  have hraw := rawMul_sound n00070_pair n00128_pair x t ha.1 hb.1
  have hred := checkReduction_sound n00131_checked x t hraw.1
  dsimp only [n00131_reduction] at hred
  refine ⟨hred.1, ?_⟩
  rw [← hred.2, hraw.2]
  simp only [n00131_expression, ha.2, hb.2]
theorem n00132_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00132_pair.NonzeroDenominator x t ∧ n00132_pair.value x t = n00132_expression x t := by
  have ha := n00004_sound x t hnz
  have hb := n00131_sound x t hnz
  have hraw := rawAdd_sound n00004_pair n00131_pair x t ha.1 hb.1
  have hred := checkReduction_sound n00132_checked x t hraw.1
  dsimp only [n00132_reduction] at hred
  refine ⟨hred.1, ?_⟩
  rw [← hred.2, hraw.2]
  simp only [n00132_expression, ha.2, hb.2]
theorem n00133_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00133_pair.NonzeroDenominator x t ∧ n00133_pair.value x t = n00133_expression x t := by
  have ha := n00123_sound x t hnz
  have hb := n00132_sound x t hnz
  have hraw := rawMul_sound n00123_pair n00132_pair x t ha.1 hb.1
  have hred := checkReduction_sound n00133_checked x t hraw.1
  dsimp only [n00133_reduction] at hred
  refine ⟨hred.1, ?_⟩
  rw [← hred.2, hraw.2]
  simp only [n00133_expression, ha.2, hb.2]
theorem n00134_sound (x t : ℝ) (hnz : DivisorsNonzero x t) :
    n00134_pair.NonzeroDenominator x t ∧ n00134_pair.value x t = n00134_expression x t := by
  have ha := n00130_sound x t hnz
  have hb := n00133_sound x t hnz
  have hraw := rawSub_sound n00130_pair n00133_pair x t ha.1 hb.1
  have hred := checkReduction_sound n00134_checked x t hraw.1
  dsimp only [n00134_reduction] at hred
  refine ⟨hred.1, ?_⟩
  rw [← hred.2, hraw.2]
  simp only [n00134_expression, ha.2, hb.2]
abbrev H_mono_r0_hi_pair := n00091_pair
abbrev H_mono_r0_hi_expression := n00091_expression
theorem H_mono_r0_hi_sound (x t : ℝ) (hnz : DivisorsNonzero x t) : n00091_pair.NonzeroDenominator x t ∧ n00091_pair.value x t = n00091_expression x t := n00091_sound x t hnz
#print axioms H_mono_r0_hi_sound
abbrev H_mono_r0_lo_pair := n00099_pair
abbrev H_mono_r0_lo_expression := n00099_expression
theorem H_mono_r0_lo_sound (x t : ℝ) (hnz : DivisorsNonzero x t) : n00099_pair.NonzeroDenominator x t ∧ n00099_pair.value x t = n00099_expression x t := n00099_sound x t hnz
#print axioms H_mono_r0_lo_sound
abbrev H_mono_r1_hi_pair := n00107_pair
abbrev H_mono_r1_hi_expression := n00107_expression
theorem H_mono_r1_hi_sound (x t : ℝ) (hnz : DivisorsNonzero x t) : n00107_pair.NonzeroDenominator x t ∧ n00107_pair.value x t = n00107_expression x t := n00107_sound x t hnz
#print axioms H_mono_r1_hi_sound
abbrev H_mono_r1_lo_pair := n00112_pair
abbrev H_mono_r1_lo_expression := n00112_expression
theorem H_mono_r1_lo_sound (x t : ℝ) (hnz : DivisorsNonzero x t) : n00112_pair.NonzeroDenominator x t ∧ n00112_pair.value x t = n00112_expression x t := n00112_sound x t hnz
#print axioms H_mono_r1_lo_sound
abbrev H_mono_s0_pair := n00127_pair
abbrev H_mono_s0_expression := n00127_expression
theorem H_mono_s0_sound (x t : ℝ) (hnz : DivisorsNonzero x t) : n00127_pair.NonzeroDenominator x t ∧ n00127_pair.value x t = n00127_expression x t := n00127_sound x t hnz
#print axioms H_mono_s0_sound
abbrev H_mono_s1_pair := n00134_pair
abbrev H_mono_s1_expression := n00134_expression
theorem H_mono_s1_sound (x t : ℝ) (hnz : DivisorsNonzero x t) : n00134_pair.NonzeroDenominator x t ∧ n00134_pair.value x t = n00134_expression x t := n00134_sound x t hnz
#print axioms H_mono_s1_sound
end
end F4U.Light.Linking.Generated.DAG_H_FULL_01
