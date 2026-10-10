module
public import Erdos993Lean.F4U.Light.Linking.Generated.DAG_H_FULL_01.Program
public import Erdos993Lean.F4U.Light.Data.H_mono_r1_hi
public import Erdos993Lean.F4U.Light.Linking.BasePoint
@[expose] public section
namespace F4U.Light.Linking.CheckedNumerators.H_mono_r1_hi
open F4U.Light.Linking.Generated.DAG_H_FULL_01
def numeratorOrientation : Int := (-1)
def primitiveScale : Int := 1
def baseActivityNumerator : Int := 7
def baseActivityDenominator : Int := 11
theorem numerator_checked : Polynomial2.normalizedEq (Polynomial2.pscale numeratorOrientation H_mono_r1_hi_pair.numerator) (Polynomial2.pscale primitiveScale F4U.Light.Data.H_mono_r1_hi.rows) = true := by decide +kernel
theorem base_checked : checkPositiveBase (Polynomial2.pscale numeratorOrientation H_mono_r1_hi_pair.denominator) baseActivityNumerator baseActivityDenominator = true := by decide +kernel
#print axioms numerator_checked
#print axioms base_checked
end F4U.Light.Linking.CheckedNumerators.H_mono_r1_hi
