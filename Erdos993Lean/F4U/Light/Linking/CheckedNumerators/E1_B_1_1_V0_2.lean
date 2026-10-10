module
public import Erdos993Lean.F4U.Light.Reflect.DAG_E1_B_01.Program
public import Erdos993Lean.F4U.Light.Data.E1_B_1_1_V0_2
public import Erdos993Lean.F4U.Light.Linking.BasePoint
@[expose] public section
namespace F4U.Light.Linking.CheckedNumerators.E1_B_1_1_V0_2
open F4U.Light.Short3.DAG_E1_B_01_P10
def numeratorOrientation : Int := 1
def primitiveScale : Int := 1
def baseActivityNumerator : Int := 13
def baseActivityDenominator : Int := 10
theorem numerator_checked : Polynomial2.normalizedEq (Polynomial2.pscale numeratorOrientation E1_B_1_1_V0_2_pair.numerator) (Polynomial2.pscale primitiveScale F4U.Light.Data.E1_B_1_1_V0_2.rows) = true := by decide +kernel
theorem base_checked : checkPositiveBase (Polynomial2.pscale numeratorOrientation E1_B_1_1_V0_2_pair.denominator) baseActivityNumerator baseActivityDenominator = true := by decide +kernel
#print axioms numerator_checked
#print axioms base_checked
end F4U.Light.Linking.CheckedNumerators.E1_B_1_1_V0_2
