module
public import Erdos993Lean.F4U.Light.Construction.SupportInterpolation
public import Erdos993Lean.F4U.Light.Construction.ContactChecks
public import Erdos993Lean.F4U.Light.Construction.ChildLower

/-! The literal two-support-line estimate, with every finite contact input
actually discharged by the exact integer certificates. -/
@[expose] public section
namespace F4Unified.LightConstruction
noncomputable section

/-- Both manuscript support lines strictly dominate the actual child J on
its original row/activity/child domain. No contact or curvature hypothesis
remains in this consumer-facing theorem. -/
theorem childJ_lt_supportLine {r : Row} {s : Support} {lam u : ℝ}
    (hlam : InRow r lam) (hu0 : 0 < u) (huq : u ≤ q lam) :
    childJ lam u < supportLine r s lam (childH u) := by
  exact supportLine_of_endpoint_contacts hlam hu0 huq
    (ContactChecks.endpointContactLo r s) (ContactChecks.endpointContactHi r s)

theorem childJ_lt_both_supportLines {r : Row} {lam u : ℝ}
    (hlam : InRow r lam) (hu0 : 0 < u) (huq : u ≤ q lam) :
    childJ lam u < min (supportLine r .first lam (childH u))
      (supportLine r .second lam (childH u)) := by
  exact lt_min (childJ_lt_supportLine (s := .first) hlam hu0 huq)
    (childJ_lt_supportLine (s := .second) hlam hu0 huq)

/-- The same actual fixed-parent light domain consumed by LightCore. -/
theorem childJ_lt_light_supportLines {r : Row} {lam Y u : ℝ}
    (hlam : InRow r lam) (hY : 0 < Y) (hcap : parentH Y ≤ q lam)
    (hu0 : q lam/2 ≤ u) (huH : u ≤ parentH Y) :
    childJ lam u < min (supportLine r .first lam (childH u))
      (supportLine r .second lam (childH u)) := by
  have hq := (inRow_q_bounds hlam).1
  have hup : 0 < u := by linarith
  exact childJ_lt_both_supportLines hlam hup (huH.trans hcap)


theorem childJ_lt_supportEnvelope {r : Row} {reg : Regime} {lam u : ℝ}
    (hlam : InRow r lam) (hu0 : 0 < u) (huq : u ≤ q lam) :
    childJ lam u < supportEnvelope r reg lam (childH u) := by
  cases reg
  · exact childJ_lt_supportLine (s := .second) hlam hu0 huq
  · exact childJ_lt_both_supportLines hlam hu0 huq

/-- Positivity is asserted only at an actual child. Artificial values such as
L1(hMinus H) remain available solely inside polynomial identities. -/
theorem supportLine_positive {r : Row} {s : Support} {lam u : ℝ}
    (hlam : InRow r lam) (hu0 : 0 < u) (huq : u ≤ q lam) :
    0 < supportLine r s lam (childH u) := by
  have hl := (inRow_lambda_bounds hlam).1
  have hq := (inRow_q_bounds hlam).2
  have hu1 : u < 1 := by linarith
  exact lt_of_le_of_lt (childJ_nonnegative hl hu0 hu1 huq)
    (childJ_lt_supportLine hlam hu0 huq)

theorem supportEnvelope_positive {r : Row} {reg : Regime} {lam u : ℝ}
    (hlam : InRow r lam) (hu0 : 0 < u) (huq : u ≤ q lam) :
    0 < supportEnvelope r reg lam (childH u) := by
  have hl := (inRow_lambda_bounds hlam).1
  have hq := (inRow_q_bounds hlam).2
  have hu1 : u < 1 := by linarith
  exact lt_of_le_of_lt (childJ_nonnegative hl hu0 hu1 huq)
    (childJ_lt_supportEnvelope hlam hu0 huq)

#print axioms childJ_lt_supportLine
#print axioms childJ_lt_both_supportLines
#print axioms childJ_lt_light_supportLines
#print axioms childJ_lt_supportEnvelope
#print axioms supportLine_positive
#print axioms supportEnvelope_positive

end
end F4Unified.LightConstruction
