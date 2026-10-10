module
public import Erdos993Lean.F4U.Light.Linking.Generated.DAG_E1_FULL_01.Program
public import Erdos993Lean.F4U.Light.Data.E1_guard_r_lo
public import Erdos993Lean.F4U.Light.Linking.BasePoint
@[expose] public section
namespace F4U.Light.Linking.CheckedNumerators.E1_guard_r_lo
open F4U.Light.Linking.Generated.DAG_E1_FULL_01
def numeratorOrientation : Int := (-1)
def primitiveScale : Int := 1
def baseActivityNumerator : Int := 13
def baseActivityDenominator : Int := 10
theorem numerator_checked : Polynomial2.normalizedEq (Polynomial2.pscale numeratorOrientation E1_guard_r_lo_pair.numerator) (Polynomial2.pscale primitiveScale F4U.Light.Data.E1_guard_r_lo.rows) = true := by decide +kernel
theorem base_checked : checkPositiveBase (Polynomial2.pscale numeratorOrientation E1_guard_r_lo_pair.denominator) baseActivityNumerator baseActivityDenominator = true := by decide +kernel
#print axioms numerator_checked
#print axioms base_checked
end F4U.Light.Linking.CheckedNumerators.E1_guard_r_lo
