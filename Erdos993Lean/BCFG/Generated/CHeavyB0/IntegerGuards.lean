module

public import Erdos993Lean.BCFG.Generated.CHeavyB0.IntegerTables
public import Erdos993Lean.F4Fast.IntegerInputAdapter
public import Erdos993Lean.F4Fast.RangeAll

/-! Original list shape by reflexivity, small rational chart guards, and finite source lengths. -/

@[expose] public section

set_option autoImplicit false

namespace Erdos993Lean.BCFG.CertData.CHeavyB0

theorem integer_source_p : p = pInt.map IUni.castRat := by rfl

theorem integer_source_A :
    A = IUni.ratioMatrix N M certificateSourceNumInt certificateSourceDenInt := by rfl

theorem integer_base_guards :
    chartDenInt ≠ 0 ∧ outerBaseDenInt ≠ 0 ∧
    a = (chartAInt : Rat)/(chartDenInt : Rat) ∧
    b = (chartBInt : Rat)/(chartDenInt : Rat) ∧
    qc = (outerQInt : Rat)/(outerBaseDenInt : Rat) ∧
    rq = (outerRInt : Rat)/(outerBaseDenInt : Rat) := by
  decide +kernel

theorem integer_source_length_checks :
    (List.range (N+1)).all (fun k =>
      decide ((pInt.getD k []).length ≤ M+1) &&
      decide ((certificateSourceDenInt.getD k []).length = M+1)) = true := by
  decide +kernel

theorem integer_source_den_default (i j : Nat) (hi : i < N+1) (hj : j < M+1) :
    (certificateSourceDenInt.getD i []).getD j 1 =
      (certificateSourceDenInt.getD i []).getD j 0 := by
  have hl := List.all_eq_true.mp integer_source_length_checks i (List.mem_range.mpr hi)
  have hlen := of_decide_eq_true (Bool.and_eq_true_iff.mp hl).2
  have hjlen : j < (certificateSourceDenInt.getD i []).length := by
    rw [hlen]
    exact hj
  rw [List.getD_eq_getElem _ 1 hjlen, List.getD_eq_getElem _ 0 hjlen]

theorem integer_composition_den_ne_zero : compositionDenInt ≠ 0 :=
  pow_ne_zero _ integer_base_guards.1

theorem integer_outer_den_ne_zero : outerDenInt ≠ 0 :=
  pow_ne_zero _ integer_base_guards.2.1

end Erdos993Lean.BCFG.CertData.CHeavyB0
