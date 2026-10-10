module

public import Erdos993Lean.Analytic.V213.ZeroTiltLaplaceRateIntervals
public import Erdos993Lean.Analytic.V213.P04Rates.Inputs
public import Erdos993Lean.Analytic.V213.P04Rates.Group00
public import Erdos993Lean.Analytic.V213.P04Rates.Group01
public import Erdos993Lean.Analytic.V213.P04Rates.Group02
public import Erdos993Lean.Analytic.V213.P04Rates.Group03
public import Erdos993Lean.Analytic.V213.P04Rates.Group04
public import Erdos993Lean.Analytic.V213.P04Rates.Group05
public import Erdos993Lean.Analytic.V213.P04Rates.Group06
public import Erdos993Lean.Analytic.V213.P04Rates.Group07
public import Erdos993Lean.Analytic.V213.P04Rates.Group08
public import Erdos993Lean.Analytic.V213.P04Rates.Group09
public import Erdos993Lean.Analytic.V213.P04Rates.Group10
public import Erdos993Lean.Analytic.V213.P04Rates.Group11
public import Erdos993Lean.Analytic.V213.P04Rates.Group12
public import Erdos993Lean.Analytic.V213.P04Rates.Group13
public import Erdos993Lean.Analytic.V213.P04Rates.Group14
public import Erdos993Lean.Analytic.V213.P04Rates.Group15
public import Erdos993Lean.Analytic.V213.P04Rates.Group16
public import Erdos993Lean.Analytic.V213.P04Rates.Group17
public import Erdos993Lean.Analytic.V213.P04Rates.Group18
public import Erdos993Lean.Analytic.V213.P04Rates.Group19
public import Erdos993Lean.Analytic.V213.P04Rates.Group20
public import Erdos993Lean.Analytic.V213.P04Rates.Group21
public import Erdos993Lean.Analytic.V213.P04Rates.Group22

/-! Current printed23 group margins and55 retained input rates.
No new numerical premise is assumed: every endpoint comparison and every
literal N44-data equality is supplied by a separately auditable finite leaf.
-/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.ZeroTiltLaplace.PrintedRates

private theorem from_low {j : Nat}
    (h : ActivityDomain (groupLo j) ∧ ActivityDomain (groupHi j) ∧
      (groupLo j:ℝ)≤groupHi j ∧ (groupHi j:ℝ)≤3/4 ∧
      (200:ℝ)<groupMargin j ∧
      (groupMargin j:ℝ)/1000000≤lowRate (q (groupLo j))-groupBar j ∧
      (groupMargin j:ℝ)/1000000≤lowRate (q (groupHi j))-groupBar j) :
    ActivityDomain (groupLo j) ∧ ActivityDomain (groupHi j) ∧ 200<groupMargin j ∧
      ∀ lam : ℝ, (groupLo j:ℝ)≤lam → lam≤groupHi j →
        (groupMargin j:ℝ)/1000000≤ellH lam-groupBar j := by
  rcases h with ⟨hl,hh,_,_,hg,hleft,hright⟩
  refine ⟨hl,hh,by exact_mod_cast hg,?_⟩
  exact fun _ hll hlh => low_group_margin hl hh hll hlh hleft hright

private theorem from_high {j : Nat}
    (h : ActivityDomain (groupLo j) ∧ ActivityDomain (groupHi j) ∧
      (groupLo j:ℝ)≤groupHi j ∧ (3/4:ℝ)≤groupLo j ∧
      (200:ℝ)<groupMargin j ∧
      (groupMargin j:ℝ)/1000000≤highRate (q (groupLo j))-groupBar j ∧
      (groupMargin j:ℝ)/1000000≤highRate (q (groupHi j))-groupBar j) :
    ActivityDomain (groupLo j) ∧ ActivityDomain (groupHi j) ∧ 200<groupMargin j ∧
      ∀ lam : ℝ, (groupLo j:ℝ)≤lam → lam≤groupHi j →
        (groupMargin j:ℝ)/1000000≤ellH lam-groupBar j := by
  rcases h with ⟨hl,hh,_,hs,hg,hleft,hright⟩
  refine ⟨hl,hh,by exact_mod_cast hg,?_⟩
  exact fun _ hll hlh => high_group_margin hl hh hs hll hlh hleft hright

/-- Full closed-interval margins, including the interval containing the
smooth maximum and the low right limit at lambda=3/4. -/
theorem all_group_facts (j : Nat) (hj : j<23) :
    ActivityDomain (groupLo j) ∧ ActivityDomain (groupHi j) ∧ 200<groupMargin j ∧
      ∀ lam : ℝ, (groupLo j:ℝ)≤lam → lam≤groupHi j →
        (groupMargin j:ℝ)/1000000≤ellH lam-groupBar j := by
  interval_cases j <;> first
  | exact from_low group_endpoints_00
  | exact from_low group_endpoints_01
  | exact from_low group_endpoints_02
  | exact from_low group_endpoints_03
  | exact from_low group_endpoints_04
  | exact from_low group_endpoints_05
  | exact from_low group_endpoints_06
  | exact from_low group_endpoints_07
  | exact from_low group_endpoints_08
  | exact from_high group_endpoints_09
  | exact from_high group_endpoints_10
  | exact from_high group_endpoints_11
  | exact from_high group_endpoints_12
  | exact from_high group_endpoints_13
  | exact from_high group_endpoints_14
  | exact from_high group_endpoints_15
  | exact from_high group_endpoints_16
  | exact from_high group_endpoints_17
  | exact from_high group_endpoints_18
  | exact from_high group_endpoints_19
  | exact from_high group_endpoints_20
  | exact from_high group_endpoints_21
  | exact from_high group_endpoints_22

theorem input_interval_domain {i : Nat} (hi : i<55) {lam : ℝ}
    (hlo : (N44.Data.pieceLo.getD i 0:ℝ)≤lam)
    (hhi : lam≤(N44.Data.pieceHi.getD i 0:ℝ)) : ActivityDomain lam := by
  rcases all_input_facts i hi with ⟨hL,hH,_,hl,hh,_,hj⟩
  have hgl : (groupLo (groupOf i):ℝ)≤lam := by
    have hc : (groupLo (groupOf i):ℝ)≤ inputLo i := by exact_mod_cast hl
    rw [hL] at hc
    exact hc.trans hlo
  have hgh : lam≤(groupHi (groupOf i):ℝ) := by
    have hc : (inputHi i:ℝ)≤groupHi (groupOf i) := by exact_mod_cast hh
    rw [hH] at hc
    exact hhi.trans hc
  have hg := all_group_facts (groupOf i) hj
  exact ⟨hg.1.1.trans hgl,hgh.trans hg.2.1.2⟩

/-- Exact input rates, not merely a reconstructed list with the same length. -/
theorem retained_input_threshold {i : Nat} (hi : i<55) {lam : ℝ}
    (hlo : (N44.Data.pieceLo.getD i 0:ℝ)≤lam)
    (hhi : lam≤(N44.Data.pieceHi.getD i 0:ℝ)) :
    ((N44.Data.rates44.getD i []).getD 0 0:ℝ)+1/5000<ellH lam := by
  rcases all_input_facts i hi with ⟨hL,hH,hR,hl,hh,hr,hj⟩
  have hgl : (groupLo (groupOf i):ℝ)≤lam := by
    have hc : (groupLo (groupOf i):ℝ)≤ inputLo i := by exact_mod_cast hl
    rw [hL] at hc
    exact hc.trans hlo
  have hgh : lam≤(groupHi (groupOf i):ℝ) := by
    have hc : (inputHi i:ℝ)≤groupHi (groupOf i) := by exact_mod_cast hh
    rw [hH] at hc
    exact hhi.trans hc
  have ht : (inputRate i:ℝ)≤groupBar (groupOf i) := by exact_mod_cast hr
  have hg := all_group_facts (groupOf i) hj
  have h := input_rate_threshold (hg.2.2.2 lam hgl hgh) ht hg.2.2.1
  rwa [hR] at h

theorem retained_input_rate_le {i : Nat} (hi : i<55) {lam : ℝ}
    (hlo : (N44.Data.pieceLo.getD i 0:ℝ)≤lam)
    (hhi : lam≤(N44.Data.pieceHi.getD i 0:ℝ)) :
    ((N44.Data.rates44.getD i []).getD 0 0:ℝ)≤ellH lam := by
  have h := retained_input_threshold hi hlo hhi
  linarith

end Erdos993Lean.Analytic.V213.ZeroTiltLaplace.PrintedRates

#check Erdos993Lean.Analytic.V213.ZeroTiltLaplace.PrintedRates.all_group_facts
#print axioms Erdos993Lean.Analytic.V213.ZeroTiltLaplace.PrintedRates.all_group_facts
#check Erdos993Lean.Analytic.V213.ZeroTiltLaplace.PrintedRates.input_interval_domain
#print axioms Erdos993Lean.Analytic.V213.ZeroTiltLaplace.PrintedRates.input_interval_domain
#check Erdos993Lean.Analytic.V213.ZeroTiltLaplace.PrintedRates.retained_input_threshold
#print axioms Erdos993Lean.Analytic.V213.ZeroTiltLaplace.PrintedRates.retained_input_threshold
#check Erdos993Lean.Analytic.V213.ZeroTiltLaplace.PrintedRates.retained_input_rate_le
#print axioms Erdos993Lean.Analytic.V213.ZeroTiltLaplace.PrintedRates.retained_input_rate_le
