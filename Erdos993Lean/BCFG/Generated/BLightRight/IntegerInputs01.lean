module

public import Erdos993Lean.BCFG.Generated.BLightRight.IntegerGuards
public import Erdos993Lean.F4Fast.RangeAll

/-! Integer affine and outer component checks for source rows 8 through 15. -/

@[expose] public section

set_option autoImplicit false

namespace Erdos993Lean.BCFG.CertData.BLightRight

theorem integer_input_checks01 :
    (List.range 8).all (fun j =>
      decide (IUni.affineHom (pInt.getD (8+j) [])
        chartAInt chartBInt chartDenInt M = compositionInt.getD (8+j) []) &&
      decide (IUni.mul (IUni.pow [outerQInt,outerRInt] (8+j))
        (IUni.pow [outerBaseDenInt-outerQInt,-outerRInt] (N-(8+j))) =
          outerInt.getD (8+j) [])) = true := by
  decide +kernel

theorem integer_input_rows01 :
    ∀ j < 8,
      IUni.affineHom (pInt.getD (8+j) []) chartAInt chartBInt chartDenInt M =
        compositionInt.getD (8+j) [] ∧
      IUni.mul (IUni.pow [outerQInt,outerRInt] (8+j))
        (IUni.pow [outerBaseDenInt-outerQInt,-outerRInt] (N-(8+j))) =
          outerInt.getD (8+j) [] := by
  intro j hj
  have h := Erdos993Lean.F4Fast.forall_lt_of_range_all integer_input_checks01 j hj
  have hs := Bool.and_eq_true_iff.mp h
  exact ⟨of_decide_eq_true hs.1, of_decide_eq_true hs.2⟩

end Erdos993Lean.BCFG.CertData.BLightRight
