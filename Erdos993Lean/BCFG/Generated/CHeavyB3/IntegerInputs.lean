module

public import Erdos993Lean.BCFG.Generated.CHeavyB3.IntegerInputs00
public import Erdos993Lean.BCFG.Generated.CHeavyB3.IntegerInputs01
public import Erdos993Lean.BCFG.Generated.CHeavyB3.IntegerInputs02
public import Lean.Elab.Tactic.Omega

/-! The three integer component ranges cover every source row; generic adapters recover exact rational lists. -/

@[expose] public section

set_option autoImplicit false

namespace Erdos993Lean.BCFG.CertData.CHeavyB3

theorem integer_input_rows_checked :
    ∀ i < N+1,
      IUni.affineHom (pInt.getD i []) chartAInt chartBInt chartDenInt M =
        compositionInt.getD i [] ∧
      IUni.mul (IUni.pow [outerQInt,outerRInt] i)
        (IUni.pow [outerBaseDenInt-outerQInt,-outerRInt] (N-i)) = outerInt.getD i [] := by
  intro i hi
  have hi' : i < 11 := by simpa only [N] using hi
  by_cases h0 : i < 4
  · simpa only [Nat.zero_add] using integer_input_rows00 i h0
  · by_cases h1 : i < 8
    · have hs : 4 ≤ i := by omega
      have hj : i-4 < 4 := by omega
      simpa only [Nat.add_sub_of_le hs] using integer_input_rows01 (i-4) hj
    · have hs : 8 ≤ i := by omega
      have hj : i-8 < 3 := by omega
      simpa only [Nat.add_sub_of_le hs] using integer_input_rows02 (i-8) hj

theorem integer_composition_checked : ∀ k < N+1,
    Uni.comp (p.getD k []) [a,b] =
      Uni.scale ((1 : Rat)/(compositionDenInt : Rat))
        (IUni.castRat (compositionInt.getD k [])) := by
  intro k hk
  have hp : p.getD k [] = IUni.castRat (pInt.getD k []) := by
    rw [integer_source_p]
    exact List.getD_map pInt [] IUni.castRat
  have hl := List.all_eq_true.mp integer_source_length_checks k (List.mem_range.mpr hk)
  have hlen := of_decide_eq_true (Bool.and_eq_true_iff.mp hl).1
  exact IUni.composition_eq_integer _ _ a b chartAInt chartBInt chartDenInt M _
    hp hlen integer_base_guards.1 integer_base_guards.2.2.1
    integer_base_guards.2.2.2.1 (integer_input_rows_checked k hk).1

theorem integer_outer_checked : ∀ k < N+1,
    Uni.mul (Uni.pow [qc,rq] k) (Uni.pow [1-qc,-rq] (N-k)) =
      Uni.scale ((1 : Rat)/(outerDenInt : Rat)) (IUni.castRat (outerInt.getD k [])) := by
  intro k hk
  exact IUni.outer_eq_integer N k qc rq outerQInt outerRInt outerBaseDenInt _
    (by omega) integer_base_guards.2.1 integer_base_guards.2.2.2.2.1
    integer_base_guards.2.2.2.2.2 (integer_input_rows_checked k hk).2

end Erdos993Lean.BCFG.CertData.CHeavyB3
