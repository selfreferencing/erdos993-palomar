module

public import Erdos993Lean.Analytic.V213.SmallForestAffineIdentity

/-! Current printed literals (data only; no finite claims are proved here). -/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.SmallForestPrinted

structure RisingInput where
  k : ℕ
  aOffset : ℕ
  c : ℕ
  margin : ℤ
  deriving Repr, DecidableEq
-- rising_margins.01; r12:eq114 / rising table
-- 3 & 1 & 13 & -- & --\\
def rising_3_first : RisingInput := ⟨3, 1, 1, 13⟩
-- rising_margins.02; r12:eq114 / rising table
-- 4 & 3 & 32 & 3 & 4\\
def rising_4_first : RisingInput := ⟨4, 1, 3, 32⟩
-- rising_margins.02; r12:eq114 / rising table
-- 4 & 3 & 32 & 3 & 4\\
def rising_4_second : RisingInput := ⟨4, 0, 3, 4⟩
-- rising_margins.03; r12:eq114 / rising table
-- 5 & 5 & 72 & 4 & 5\\
def rising_5_first : RisingInput := ⟨5, 1, 5, 72⟩
-- rising_margins.03; r12:eq114 / rising table
-- 5 & 5 & 72 & 4 & 5\\
def rising_5_second : RisingInput := ⟨5, 0, 4, 5⟩
-- rising_margins.04; r12:eq114 / rising table
-- 6 & 7 & 100 & 4 & 37\\
def rising_6_first : RisingInput := ⟨6, 1, 7, 100⟩
-- rising_margins.04; r12:eq114 / rising table
-- 6 & 7 & 100 & 4 & 37\\
def rising_6_second : RisingInput := ⟨6, 0, 4, 37⟩
-- rising_margins.05; r12:eq114 / rising table
-- 7 & 8 & 198 & 5 & 18\\
def rising_7_first : RisingInput := ⟨7, 1, 8, 198⟩
-- rising_margins.05; r12:eq114 / rising table
-- 7 & 8 & 198 & 5 & 18\\
def rising_7_second : RisingInput := ⟨7, 0, 5, 18⟩
-- rising_margins.06; r12:eq114 / rising table
-- 8 & 8 & 1348 & 5 & 183\\
def rising_8_first : RisingInput := ⟨8, 1, 8, 1348⟩
-- rising_margins.06; r12:eq114 / rising table
-- 8 & 8 & 1348 & 5 & 183\\
def rising_8_second : RisingInput := ⟨8, 0, 5, 183⟩
-- rising_margins.07; r12:eq114 / rising table
-- 9 & 7 & 8941 & 5 & 902\\
def rising_9_first : RisingInput := ⟨9, 1, 7, 8941⟩
-- rising_margins.07; r12:eq114 / rising table
-- 9 & 7 & 8941 & 5 & 902\\
def rising_9_second : RisingInput := ⟨9, 0, 5, 902⟩
-- rising_margins.08; r12:eq114 / rising table
-- 10 & 5 & 45802 & 5 & 3812\\
def rising_10_first : RisingInput := ⟨10, 1, 5, 45802⟩
-- rising_margins.08; r12:eq114 / rising table
-- 10 & 5 & 45802 & 5 & 3812\\
def rising_10_second : RisingInput := ⟨10, 0, 5, 3812⟩
-- rising_margins.09; r12:eq114 / rising table
-- 11 & 3 & 188707 & -- & --\\
def rising_11_first : RisingInput := ⟨11, 1, 3, 188707⟩
def risingInputs : List RisingInput := [rising_3_first, rising_4_first, rising_4_second, rising_5_first, rising_5_second, rising_6_first, rising_6_second, rising_7_first, rising_7_second, rising_8_first, rising_8_second, rising_9_first, rising_9_second, rising_10_first, rising_10_second, rising_11_first]
structure CatalanInput where
  a : ℕ
  c : ℕ
  k : ℕ
  s : ℕ
  t : ℕ
  constant : ℚ
  slope : ℚ
  deriving Repr, DecidableEq
-- affine_catalan_named.01; r12:eq109 / eight affine Catalan cases
-- 15 & 7 & 9 & 3 & 3 & 5540 & 449/6\\
def catalan_named_1 : CatalanInput := ⟨15, 9, 7, 3, 3, ((5540 : ℚ) / 1), ((449 : ℚ) / 6)⟩
-- affine_catalan_named.02; r12:eq109 / eight affine Catalan cases
-- 13 & 7 & 11 & 3 & 5 & 1146 & 732/5\\
def catalan_named_2 : CatalanInput := ⟨13, 11, 7, 3, 5, ((1146 : ℚ) / 1), ((732 : ℚ) / 5)⟩
-- affine_catalan_named.03; r12:eq109 / eight affine Catalan cases
-- 16 & 8 & 6 & 0 & 1 & 36 & 2978/15\\
def catalan_named_3 : CatalanInput := ⟨16, 6, 8, 0, 1, ((36 : ℚ) / 1), ((2978 : ℚ) / 15)⟩
-- affine_catalan_named.04; r12:eq109 / eight affine Catalan cases
-- 16 & 8 & 8 & 1 & 4 & 87 & 1115/7\\
def catalan_named_4 : CatalanInput := ⟨16, 8, 8, 1, 4, ((87 : ℚ) / 1), ((1115 : ℚ) / 7)⟩
def namedCatalanInputs : List CatalanInput := [catalan_named_1, catalan_named_2, catalan_named_3, catalan_named_4]
-- display.newton_A; a=14,k=7,s=1,t=4,x∈{0,1,2,3}; first Newton identity
-- A(7+x)&=232+474\binom x1+147\binom x2+14\binom x3\ge232,\\
def a14Constant (x : ℕ) : ℚ := 232 + 474 * (x.choose 1 : ℚ) + 147 * (x.choose 2 : ℚ) + 14 * (x.choose 3 : ℚ)
-- display.newton_B; a=14,k=7,s=1,t=4,x∈{0,1,2,3}; second Newton identity
-- B(7+x)&=\frac{94}3-\frac{28}3\binom x1+\frac{37}6\binom x2+\frac{73}{30}\binom x3>18.
def a14Slope (x : ℕ) : ℚ := 94/3 - (28/3) * (x.choose 1 : ℚ) + (37/6) * (x.choose 2 : ℚ) + (73/30) * (x.choose 3 : ℚ)
-- Newton integer domain
-- For $(a,k)=(14,7)$, use $(s,t)=(1,4)$ and $c=7+x$, $x\in\{0,1,2,3\}$. The finite Newton identities, obtained
def a14Indices : List ℕ := [0, 1, 2, 3]
structure FamilyInput where
  row : ℕ
  a : ℕ
  k : ℕ
  w : ℚ
  lo : ℕ
  hi : ℕ
  tangents : List ℕ
  constantLo : ℚ
  constantHi : ℚ
  slopeLo : ℚ
  deriving Repr, DecidableEq
-- family_endpoints.01; r12:tab5
-- 1 & 8 & 4 & $1/2$ & $[4,4]$ & $(5,2)$ & $26$ & $26$ & $3/2$\\
def family_1 : FamilyInput := ⟨1, 8, 4, ((1 : ℚ) / 2), 4, 4, [5, 2], ((26 : ℚ) / 1), ((26 : ℚ) / 1), ((3 : ℚ) / 2)⟩
-- family_endpoints.02; r12:tab5
-- 2 & 9 & 5 & $1/2$ & $[6,7]$ & $(7,5,2)$ & $153/2$ & $201/2$ & $73/30$\\
def family_2 : FamilyInput := ⟨2, 9, 5, ((1 : ℚ) / 2), 6, 7, [7, 5, 2], ((153 : ℚ) / 2), ((201 : ℚ) / 2), ((73 : ℚ) / 30)⟩
-- family_endpoints.03; r12:tab5
-- 3 & 10 & 5 & $1/2$ & $[5,6]$ & $(8,4)$ & $161/2$ & $83$ & $143/20$\\
def family_3 : FamilyInput := ⟨3, 10, 5, ((1 : ℚ) / 2), 5, 6, [8, 4], ((161 : ℚ) / 2), ((83 : ℚ) / 1), ((143 : ℚ) / 20)⟩
-- family_endpoints.04; r12:tab5
-- 4 & 10 & 6 & $1/2$ & $[9,10]$ & $(8,7,5,2)$ & $272$ & $329$ & $79/12$\\
def family_4 : FamilyInput := ⟨4, 10, 6, ((1 : ℚ) / 2), 9, 10, [8, 7, 5, 2], ((272 : ℚ) / 1), ((329 : ℚ) / 1), ((79 : ℚ) / 12)⟩
-- family_endpoints.05; r12:tab5
-- 5 & 11 & 6 & $1/2$ & $[6,9]$ & $(9,7,4)$ & $155$ & $188$ & $32/5$\\
def family_5 : FamilyInput := ⟨5, 11, 6, ((1 : ℚ) / 2), 6, 9, [9, 7, 4], ((155 : ℚ) / 1), ((188 : ℚ) / 1), ((32 : ℚ) / 5)⟩
-- family_endpoints.06; r12:tab5
-- 6 & 12 & 6 & $1/2$ & $[5,8]$ & $(10,7)$ & $207$ & $79$ & $169/10$\\
def family_6 : FamilyInput := ⟨6, 12, 6, ((1 : ℚ) / 2), 5, 8, [10, 7], ((207 : ℚ) / 1), ((79 : ℚ) / 1), ((169 : ℚ) / 10)⟩
-- family_endpoints.07; r12:tab5
-- 7 & 12 & 7 & $1/2$ & $[9,11]$ & $(10,9,7,4)$ & $394$ & $444$ & $445/24$\\
def family_7 : FamilyInput := ⟨7, 12, 7, ((1 : ℚ) / 2), 9, 11, [10, 9, 7, 4], ((394 : ℚ) / 1), ((444 : ℚ) / 1), ((445 : ℚ) / 24)⟩
-- family_endpoints.08; r12:tab5
-- 8 & 12 & 7 & $2/3$ & $[12,12]$ & $(11,9,8,6,3)$ & $7051/3$ & $7051/3$ & $-229/2$\\
def family_8 : FamilyInput := ⟨8, 12, 7, ((2 : ℚ) / 3), 12, 12, [11, 9, 8, 6, 3], ((7051 : ℚ) / 3), ((7051 : ℚ) / 3), ((-229 : ℚ) / 2)⟩
-- family_endpoints.09; r12:tab5
-- 9 & 13 & 7 & $1/2$ & $[6,10]$ & $(11,9,7)$ & $228$ & $234$ & $-199/30$\\
def family_9 : FamilyInput := ⟨9, 13, 7, ((1 : ℚ) / 2), 6, 10, [11, 9, 7], ((228 : ℚ) / 1), ((234 : ℚ) / 1), ((-199 : ℚ) / 30)⟩
-- family_endpoints.10; r12:tab5
-- 10 & 14 & 7 & $1/2$ & $[6,6]$ & $(11,8,6)$ & $721$ & $721$ & $62/15$\\
def family_10 : FamilyInput := ⟨10, 14, 7, ((1 : ℚ) / 2), 6, 6, [11, 8, 6], ((721 : ℚ) / 1), ((721 : ℚ) / 1), ((62 : ℚ) / 15)⟩
-- family_endpoints.11; r12:tab5
-- 11 & 14 & 8 & $1/2$ & $[9,10]$ & $(12,10,8,5)$ & $731$ & $662$ & $6415/72$\\
def family_11 : FamilyInput := ⟨11, 14, 8, ((1 : ℚ) / 2), 9, 10, [12, 10, 8, 5], ((731 : ℚ) / 1), ((662 : ℚ) / 1), ((6415 : ℚ) / 72)⟩
-- family_endpoints.12; r12:tab5
-- 12 & 15 & 8 & $1/2$ & $[6,9]$ & $(13,10,7)$ & $1551/2$ & $1783/2$ & $1057/10$\\
def family_12 : FamilyInput := ⟨12, 15, 8, ((1 : ℚ) / 2), 6, 9, [13, 10, 7], ((1551 : ℚ) / 2), ((1783 : ℚ) / 2), ((1057 : ℚ) / 10)⟩
-- family_endpoints.13; r12:tab5
-- 13 & 16 & 8 & $1/2$ & $[7,7]$ & $(13,10,8)$ & $4593/2$ & $4593/2$ & $881/21$\\
def family_13 : FamilyInput := ⟨13, 16, 8, ((1 : ℚ) / 2), 7, 7, [13, 10, 8], ((4593 : ℚ) / 2), ((4593 : ℚ) / 2), ((881 : ℚ) / 21)⟩
-- family_endpoints.14; r12:tab5
-- 14 & 17 & 9 & $1/2$ & $[6,7]$ & $(14,10)$ & $2973$ & $3238$ & $6977/30$\\
def family_14 : FamilyInput := ⟨14, 17, 9, ((1 : ℚ) / 2), 6, 7, [14, 10], ((2973 : ℚ) / 1), ((3238 : ℚ) / 1), ((6977 : ℚ) / 30)⟩
-- family_endpoints.15; r12:tab5
-- 15 & 18 & 9 & $1/2$ & $[6,6]$ & $(15,11)$ & $6535$ & $6535$ & $6427/15$\\
def family_15 : FamilyInput := ⟨15, 18, 9, ((1 : ℚ) / 2), 6, 6, [15, 11], ((6535 : ℚ) / 1), ((6535 : ℚ) / 1), ((6427 : ℚ) / 15)⟩
def familyInputs : List FamilyInput := [family_1, family_2, family_3, family_4, family_5, family_6, family_7, family_8, family_9, family_10, family_11, family_12, family_13, family_14, family_15]
structure DifferenceInput where
  row : ℕ
  constantDifferences : List ℚ
  slopeDifferences : List ℚ
  deriving Repr, DecidableEq
-- finite_differences.01; r12:eq119–120 / difference table
-- 2 & -- & $(46/15)$\\
def differences_2 : DifferenceInput := ⟨2, [], [((46 : ℚ) / 15)]⟩
-- finite_differences.02; r12:eq119–120 / difference table
-- 3 & -- & $(53/20)$\\
def differences_3 : DifferenceInput := ⟨3, [], [((53 : ℚ) / 20)]⟩
-- finite_differences.03; r12:eq119–120 / difference table
-- 4 & -- & $(793/60)$\\
def differences_4 : DifferenceInput := ⟨4, [], [((793 : ℚ) / 60)]⟩
-- finite_differences.04; r12:eq119–120 / difference table
-- 5 & $(-37,-66)$ & $(226/35,361/140,26/35)$\\
def differences_5 : DifferenceInput := ⟨5, [((-37 : ℚ) / 1), ((-66 : ℚ) / 1)], [((226 : ℚ) / 35), ((361 : ℚ) / 140), ((26 : ℚ) / 35)]⟩
-- finite_differences.05; r12:eq119–120 / difference table
-- 6 & $(-71,-83)$ & $(17/2,481/210,61/70)$\\
def differences_6 : DifferenceInput := ⟨6, [((-71 : ℚ) / 1), ((-83 : ℚ) / 1)], [((17 : ℚ) / 2), ((481 : ℚ) / 210), ((61 : ℚ) / 70)]⟩
-- finite_differences.06; r12:eq119–120 / difference table
-- 7 & $(-284)$ & $(3611/120,551/40)$\\
def differences_7 : DifferenceInput := ⟨7, [((-284 : ℚ) / 1)], [((3611 : ℚ) / 120), ((551 : ℚ) / 40)]⟩
-- finite_differences.07; r12:eq119–120 / difference table
-- 9 & $(-29,-154,-132)$ & $(1669/105,2431/280,443/210,317/420)$\\
def differences_9 : DifferenceInput := ⟨9, [((-29 : ℚ) / 1), ((-154 : ℚ) / 1), ((-132 : ℚ) / 1)], [((1669 : ℚ) / 105), ((2431 : ℚ) / 280), ((443 : ℚ) / 210), ((317 : ℚ) / 420)]⟩
-- finite_differences.08; r12:eq119–120 / difference table
-- 11 & -- & $(20573/360)$\\
def differences_11 : DifferenceInput := ⟨11, [], [((20573 : ℚ) / 360)]⟩
-- finite_differences.09; r12:eq119–120 / difference table
-- 12 & $(-241,-863/2)$ & $(2864/105,8983/840,14561/2520)$\\
def differences_12 : DifferenceInput := ⟨12, [((-241 : ℚ) / 1), ((-863 : ℚ) / 2)], [((2864 : ℚ) / 105), ((8983 : ℚ) / 840), ((14561 : ℚ) / 2520)]⟩
-- finite_differences.10; r12:eq119–120 / difference table
-- 14 & -- & $(2158/105)$\\
def differences_14 : DifferenceInput := ⟨14, [], [((2158 : ℚ) / 105)]⟩
def differenceInputs : List DifferenceInput := [differences_2, differences_3, differences_4, differences_5, differences_6, differences_7, differences_9, differences_11, differences_12, differences_14]
-- display.horizontal_floors; r12:eq117
-- (g_1,\dots,g_6)=(-1/2,-1/2,-1/2,-1,-2,-4).
def horizontalFloors : List ℚ := [-1/2, -1/2, -1/2, -1, -2, -4]
-- supplement.first_minimum_indices; r12:eq117 horizontal first minima
-- $1,2,4,6,7$, and their values are the listed floors. The minimum on an initial interval is at this first minimum or at
def firstMinimumIndices : List ℕ := [1, 2, 4, 6, 7]
-- supplement.horizontal_two_thirds; horizontal two-thirds paragraph following r12:eq117
-- its last point. For $w=2/3$ only the additional bound $G_1(m)\ge-2/3$ for $0\le m\le6$ is needed; concavity and the
-- values $-2/3,1/3$ at $0,6$ prove it.
def horizontalTwoThirdsEndpoints : List (ℕ × ℚ) := [(0, -2/3), (6, 1/3)]
end Erdos993Lean.Analytic.V213.SmallForestPrinted

#check Erdos993Lean.Analytic.V213.SmallForestPrinted.RisingInput
#print axioms Erdos993Lean.Analytic.V213.SmallForestPrinted.RisingInput
#check Erdos993Lean.Analytic.V213.SmallForestPrinted.rising_3_first
#print axioms Erdos993Lean.Analytic.V213.SmallForestPrinted.rising_3_first
#check Erdos993Lean.Analytic.V213.SmallForestPrinted.rising_4_first
#print axioms Erdos993Lean.Analytic.V213.SmallForestPrinted.rising_4_first
#check Erdos993Lean.Analytic.V213.SmallForestPrinted.rising_4_second
#print axioms Erdos993Lean.Analytic.V213.SmallForestPrinted.rising_4_second
#check Erdos993Lean.Analytic.V213.SmallForestPrinted.rising_5_first
#print axioms Erdos993Lean.Analytic.V213.SmallForestPrinted.rising_5_first
#check Erdos993Lean.Analytic.V213.SmallForestPrinted.rising_5_second
#print axioms Erdos993Lean.Analytic.V213.SmallForestPrinted.rising_5_second
#check Erdos993Lean.Analytic.V213.SmallForestPrinted.rising_6_first
#print axioms Erdos993Lean.Analytic.V213.SmallForestPrinted.rising_6_first
#check Erdos993Lean.Analytic.V213.SmallForestPrinted.rising_6_second
#print axioms Erdos993Lean.Analytic.V213.SmallForestPrinted.rising_6_second
#check Erdos993Lean.Analytic.V213.SmallForestPrinted.rising_7_first
#print axioms Erdos993Lean.Analytic.V213.SmallForestPrinted.rising_7_first
#check Erdos993Lean.Analytic.V213.SmallForestPrinted.rising_7_second
#print axioms Erdos993Lean.Analytic.V213.SmallForestPrinted.rising_7_second
#check Erdos993Lean.Analytic.V213.SmallForestPrinted.rising_8_first
#print axioms Erdos993Lean.Analytic.V213.SmallForestPrinted.rising_8_first
#check Erdos993Lean.Analytic.V213.SmallForestPrinted.rising_8_second
#print axioms Erdos993Lean.Analytic.V213.SmallForestPrinted.rising_8_second
#check Erdos993Lean.Analytic.V213.SmallForestPrinted.rising_9_first
#print axioms Erdos993Lean.Analytic.V213.SmallForestPrinted.rising_9_first
#check Erdos993Lean.Analytic.V213.SmallForestPrinted.rising_9_second
#print axioms Erdos993Lean.Analytic.V213.SmallForestPrinted.rising_9_second
#check Erdos993Lean.Analytic.V213.SmallForestPrinted.rising_10_first
#print axioms Erdos993Lean.Analytic.V213.SmallForestPrinted.rising_10_first
#check Erdos993Lean.Analytic.V213.SmallForestPrinted.rising_10_second
#print axioms Erdos993Lean.Analytic.V213.SmallForestPrinted.rising_10_second
#check Erdos993Lean.Analytic.V213.SmallForestPrinted.rising_11_first
#print axioms Erdos993Lean.Analytic.V213.SmallForestPrinted.rising_11_first
#check Erdos993Lean.Analytic.V213.SmallForestPrinted.risingInputs
#print axioms Erdos993Lean.Analytic.V213.SmallForestPrinted.risingInputs
#check Erdos993Lean.Analytic.V213.SmallForestPrinted.CatalanInput
#print axioms Erdos993Lean.Analytic.V213.SmallForestPrinted.CatalanInput
#check Erdos993Lean.Analytic.V213.SmallForestPrinted.catalan_named_1
#print axioms Erdos993Lean.Analytic.V213.SmallForestPrinted.catalan_named_1
#check Erdos993Lean.Analytic.V213.SmallForestPrinted.catalan_named_2
#print axioms Erdos993Lean.Analytic.V213.SmallForestPrinted.catalan_named_2
#check Erdos993Lean.Analytic.V213.SmallForestPrinted.catalan_named_3
#print axioms Erdos993Lean.Analytic.V213.SmallForestPrinted.catalan_named_3
#check Erdos993Lean.Analytic.V213.SmallForestPrinted.catalan_named_4
#print axioms Erdos993Lean.Analytic.V213.SmallForestPrinted.catalan_named_4
#check Erdos993Lean.Analytic.V213.SmallForestPrinted.namedCatalanInputs
#print axioms Erdos993Lean.Analytic.V213.SmallForestPrinted.namedCatalanInputs
#check Erdos993Lean.Analytic.V213.SmallForestPrinted.a14Constant
#print axioms Erdos993Lean.Analytic.V213.SmallForestPrinted.a14Constant
#check Erdos993Lean.Analytic.V213.SmallForestPrinted.a14Slope
#print axioms Erdos993Lean.Analytic.V213.SmallForestPrinted.a14Slope
#check Erdos993Lean.Analytic.V213.SmallForestPrinted.a14Indices
#print axioms Erdos993Lean.Analytic.V213.SmallForestPrinted.a14Indices
#check Erdos993Lean.Analytic.V213.SmallForestPrinted.FamilyInput
#print axioms Erdos993Lean.Analytic.V213.SmallForestPrinted.FamilyInput
#check Erdos993Lean.Analytic.V213.SmallForestPrinted.family_1
#print axioms Erdos993Lean.Analytic.V213.SmallForestPrinted.family_1
#check Erdos993Lean.Analytic.V213.SmallForestPrinted.family_2
#print axioms Erdos993Lean.Analytic.V213.SmallForestPrinted.family_2
#check Erdos993Lean.Analytic.V213.SmallForestPrinted.family_3
#print axioms Erdos993Lean.Analytic.V213.SmallForestPrinted.family_3
#check Erdos993Lean.Analytic.V213.SmallForestPrinted.family_4
#print axioms Erdos993Lean.Analytic.V213.SmallForestPrinted.family_4
#check Erdos993Lean.Analytic.V213.SmallForestPrinted.family_5
#print axioms Erdos993Lean.Analytic.V213.SmallForestPrinted.family_5
#check Erdos993Lean.Analytic.V213.SmallForestPrinted.family_6
#print axioms Erdos993Lean.Analytic.V213.SmallForestPrinted.family_6
#check Erdos993Lean.Analytic.V213.SmallForestPrinted.family_7
#print axioms Erdos993Lean.Analytic.V213.SmallForestPrinted.family_7
#check Erdos993Lean.Analytic.V213.SmallForestPrinted.family_8
#print axioms Erdos993Lean.Analytic.V213.SmallForestPrinted.family_8
#check Erdos993Lean.Analytic.V213.SmallForestPrinted.family_9
#print axioms Erdos993Lean.Analytic.V213.SmallForestPrinted.family_9
#check Erdos993Lean.Analytic.V213.SmallForestPrinted.family_10
#print axioms Erdos993Lean.Analytic.V213.SmallForestPrinted.family_10
#check Erdos993Lean.Analytic.V213.SmallForestPrinted.family_11
#print axioms Erdos993Lean.Analytic.V213.SmallForestPrinted.family_11
#check Erdos993Lean.Analytic.V213.SmallForestPrinted.family_12
#print axioms Erdos993Lean.Analytic.V213.SmallForestPrinted.family_12
#check Erdos993Lean.Analytic.V213.SmallForestPrinted.family_13
#print axioms Erdos993Lean.Analytic.V213.SmallForestPrinted.family_13
#check Erdos993Lean.Analytic.V213.SmallForestPrinted.family_14
#print axioms Erdos993Lean.Analytic.V213.SmallForestPrinted.family_14
#check Erdos993Lean.Analytic.V213.SmallForestPrinted.family_15
#print axioms Erdos993Lean.Analytic.V213.SmallForestPrinted.family_15
#check Erdos993Lean.Analytic.V213.SmallForestPrinted.familyInputs
#print axioms Erdos993Lean.Analytic.V213.SmallForestPrinted.familyInputs
#check Erdos993Lean.Analytic.V213.SmallForestPrinted.DifferenceInput
#print axioms Erdos993Lean.Analytic.V213.SmallForestPrinted.DifferenceInput
#check Erdos993Lean.Analytic.V213.SmallForestPrinted.differences_2
#print axioms Erdos993Lean.Analytic.V213.SmallForestPrinted.differences_2
#check Erdos993Lean.Analytic.V213.SmallForestPrinted.differences_3
#print axioms Erdos993Lean.Analytic.V213.SmallForestPrinted.differences_3
#check Erdos993Lean.Analytic.V213.SmallForestPrinted.differences_4
#print axioms Erdos993Lean.Analytic.V213.SmallForestPrinted.differences_4
#check Erdos993Lean.Analytic.V213.SmallForestPrinted.differences_5
#print axioms Erdos993Lean.Analytic.V213.SmallForestPrinted.differences_5
#check Erdos993Lean.Analytic.V213.SmallForestPrinted.differences_6
#print axioms Erdos993Lean.Analytic.V213.SmallForestPrinted.differences_6
#check Erdos993Lean.Analytic.V213.SmallForestPrinted.differences_7
#print axioms Erdos993Lean.Analytic.V213.SmallForestPrinted.differences_7
#check Erdos993Lean.Analytic.V213.SmallForestPrinted.differences_9
#print axioms Erdos993Lean.Analytic.V213.SmallForestPrinted.differences_9
#check Erdos993Lean.Analytic.V213.SmallForestPrinted.differences_11
#print axioms Erdos993Lean.Analytic.V213.SmallForestPrinted.differences_11
#check Erdos993Lean.Analytic.V213.SmallForestPrinted.differences_12
#print axioms Erdos993Lean.Analytic.V213.SmallForestPrinted.differences_12
#check Erdos993Lean.Analytic.V213.SmallForestPrinted.differences_14
#print axioms Erdos993Lean.Analytic.V213.SmallForestPrinted.differences_14
#check Erdos993Lean.Analytic.V213.SmallForestPrinted.differenceInputs
#print axioms Erdos993Lean.Analytic.V213.SmallForestPrinted.differenceInputs
#check Erdos993Lean.Analytic.V213.SmallForestPrinted.horizontalFloors
#print axioms Erdos993Lean.Analytic.V213.SmallForestPrinted.horizontalFloors
#check Erdos993Lean.Analytic.V213.SmallForestPrinted.firstMinimumIndices
#print axioms Erdos993Lean.Analytic.V213.SmallForestPrinted.firstMinimumIndices
#check Erdos993Lean.Analytic.V213.SmallForestPrinted.horizontalTwoThirdsEndpoints
#print axioms Erdos993Lean.Analytic.V213.SmallForestPrinted.horizontalTwoThirdsEndpoints
