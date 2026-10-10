module
public import Erdos993Lean.F4U.Light.Reflect.DAG_H_A_01.Program
public import Erdos993Lean.F4U.Light.Data.H_A_1_0_V0_4
public import Erdos993Lean.F4U.Light.Linking.BasePoint
@[expose] public section
namespace F4U.Light.Linking.CheckedNumerators.H_A_1_0_V0_4
open F4U.Light.Short3.DAG_H_A_01_P10
def numeratorOrientation : Int := (-1)
def primitiveScale : Int := 1
def baseActivityNumerator : Int := 7
def baseActivityDenominator : Int := 11
theorem numerator_checked : Polynomial2.normalizedEq (Polynomial2.pscale numeratorOrientation H_A_1_0_V0_4_pair.numerator) (Polynomial2.pscale primitiveScale F4U.Light.Data.H_A_1_0_V0_4.rows) = true := by decide +kernel
theorem base_checked : checkPositiveBase (Polynomial2.pscale numeratorOrientation H_A_1_0_V0_4_pair.denominator) baseActivityNumerator baseActivityDenominator = true := by decide +kernel
#print axioms numerator_checked
#print axioms base_checked
end F4U.Light.Linking.CheckedNumerators.H_A_1_0_V0_4
