module

public import F4Heavy.Analysis.TailForcedEndpoints

@[expose] public section
set_option autoImplicit false

namespace F4Heavy.Analysis
open F4Unified

theorem tail_payment_positive_of_guards (r : Row) (lam Y rho u y : ℝ)
    (hdom : PairDomain r lam Y rho u y) (hx : parentX lam Y ≤ (rowData r).xMin)
    (hguards : ∀ i, 1 ≤ i → i ≤ 16 → 0 < tailGuard r lam i) :
    0 < payment r lam Y rho u y := by
  rcases hdom with ⟨hr, hY, hrho, hu, hucap, hadm⟩
  have hl := inRow_activity_pos r lam hr
  have ht := tail_mass_lower r lam Y hl hx
  have hx1 := hx.trans (tail_xMin_le_one r)
  have huq : u ≤ q lam := hucap.trans (min_le_left _ _)
  have hu1 := huq.trans_lt (q_lt_one lam hl)
  rcases hadm with hJ | ⟨_, hy⟩
  · have hup : 0 < u := by
      by_contra h
      have hz : u = 0 := le_antisymm (le_of_not_gt h) hu
      simp only [hz, childJ, ite_true] at hJ
      exact (lt_irrefl 0) hJ
    apply tail_payment_positive_of_endpoints r lam Y rho u y hr hY hrho hx1 hJ
    · exact tail_zero_endpoint_positive_of_guards r lam Y u y hr ht
        (fun i hi hj => hguards i hi (by omega)) hJ
    · exact tail_one_endpoint_positive_of_model r lam Y u y hr ht hup hu1 hJ
        (tail_childJ_constant_upper r lam u hr hu hu1)
        (fun i hi hj => hguards i hi (by omega))
        (fun z => tail_model_child_positive r lam u z hr hu huq hJ
          (fun i hi hj => hguards i (by omega) hj))
  · rw [hy]
    exact tail_forced_payment_positive r lam Y rho u hr hY hrho hx1
      (tail_zero_forced_positive_of_guards r lam Y u hr ht (fun i hi hj => hguards i hi (by omega)))
      (tail_one_forced_positive_of_guards r lam Y u hr ht hu huq hguards)

theorem tail_positive_of_guards (r : Row)
    (hguards : ∀ lam, InRow r lam → ∀ i, 1 ≤ i → i ≤ 16 → 0 < tailGuard r lam i) :
    TailPositive r := by
  intro lam Y rho u y hdom hx
  exact tail_payment_positive_of_guards r lam Y rho u y hdom hx (hguards lam hdom.1)

end F4Heavy.Analysis
