module

public import Erdos993Lean.BCFG.Generated.BLightRight.IntegerGuards
public import Erdos993Lean.F4Fast.RangeAll

/-! Integer affine and outer component checks for source rows 0 through 7. -/

@[expose] public section

set_option autoImplicit false

namespace Erdos993Lean.BCFG.CertData.BLightRight

theorem integer_input_checks00 :
    (List.range 8).all (fun j =>
      decide (IUni.affineHom (pInt.getD (0+j) [])
        chartAInt chartBInt chartDenInt M = compositionInt.getD (0+j) []) &&
      decide (IUni.mul (IUni.pow [outerQInt,outerRInt] (0+j))
        (IUni.pow [outerBaseDenInt-outerQInt,-outerRInt] (N-(0+j))) =
          outerInt.getD (0+j) [])) = true := by
  decide +kernel

theorem integer_input_rows00 :
    ∀ j < 8,
      IUni.affineHom (pInt.getD (0+j) []) chartAInt chartBInt chartDenInt M =
        compositionInt.getD (0+j) [] ∧
      IUni.mul (IUni.pow [outerQInt,outerRInt] (0+j))
        (IUni.pow [outerBaseDenInt-outerQInt,-outerRInt] (N-(0+j))) =
          outerInt.getD (0+j) [] := by
  intro j hj
  have h := Erdos993Lean.F4Fast.forall_lt_of_range_all integer_input_checks00 j hj
  have hs := Bool.and_eq_true_iff.mp h
  exact ⟨of_decide_eq_true hs.1, of_decide_eq_true hs.2⟩

end Erdos993Lean.BCFG.CertData.BLightRight
