module
public import Erdos993Lean.F4U.Light.Reflect.DAG_E2_B_01.Program
public import Erdos993Lean.F4U.Light.Data.E2_B_2_1_V0_3
public import Erdos993Lean.F4U.Light.Linking.BasePoint
@[expose] public section
namespace F4U.Light.Linking.CheckedNumerators.E2_B_2_1_V0_3
open F4U.Light.Short3.DAG_E2_B_01_P10
def numeratorOrientation : Int := 1
def primitiveScale : Int := 1
def baseActivityNumerator : Int := 29
def baseActivityDenominator : Int := 20
theorem numerator_checked : Polynomial2.normalizedEq (Polynomial2.pscale numeratorOrientation E2_B_2_1_V0_3_pair.numerator) (Polynomial2.pscale primitiveScale F4U.Light.Data.E2_B_2_1_V0_3.rows) = true := by decide +kernel
theorem base_checked : checkPositiveBase (Polynomial2.pscale numeratorOrientation E2_B_2_1_V0_3_pair.denominator) baseActivityNumerator baseActivityDenominator = true := by decide +kernel
#print axioms numerator_checked
#print axioms base_checked
end F4U.Light.Linking.CheckedNumerators.E2_B_2_1_V0_3
