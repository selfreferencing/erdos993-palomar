module

public import Erdos993Lean.BCFG.LightMass

/-! The leaf endpoint of Lemma
5.17. The zero value is handled explicitly, without dividing by Y=0. -/

@[expose] public section

set_option autoImplicit false

namespace Erdos993Lean.BCFG.Analytic

open Finset Erdos993Lean.Analytic
open Erdos993Lean.Analytic.Tail Erdos993Lean.Analytic.Reserve
open Erdos993Lean.Analytic.V213.VarianceResponse

/-- The assigned zero endpoint extends the exact light mass identity. -/
theorem messageRatio_light_mass_nonneg {Y : ℝ} (hY : 0 ≤ Y) :
    messageRatio (1-Real.exp (-Y))*Y = 1-Real.exp (-Y) := by
  rcases eq_or_lt_of_le hY with hzero | hpos
  · subst Y
    simp
  · exact messageRatio_light_mass hpos

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- Printed Lemma 5.17 on the closed light domain, including parent leaves. -/
theorem exact_light_mass_closed (hG : G.IsAcyclic) {lam : ℝ} (hl : 0 < lam)
    {s : Finset V} (hs : ConnectedIn G s) {v : V} (hv : v ∈ s)
    (hlight : 1-Real.exp (-Tmass G lam s v) ≤ actQ lam) :
    messageRatio (O2.cavH lam (rootProb G lam s v))*Tmass G lam s v =
      1-Real.exp (-Tmass G lam s v) ∧
    messageRatio (O2.cavH lam (rootProb G lam s v))*Tmass G lam s v ≤
      ∑ w ∈ nbrsIn G s v, rootProb G lam (compIn G (s.erase v) w) w := by
  have hc : O2.cavH lam (rootProb G lam s v) = 1-Real.exp (-Tmass G lam s v) := by
    rw [message_recursion hG hl hs hv]
    unfold msg
    exact cavH_light hl (Real.exp_pos _) hlight
  have hm := messageRatio_light_mass_nonneg (Tmass_nonneg hG hl hs hv)
  rw [hc]
  exact ⟨hm,hm.le.trans (children_mass_lower hG hl hs hv)⟩

end Erdos993Lean.BCFG.Analytic

#check Erdos993Lean.BCFG.Analytic.messageRatio_light_mass_nonneg
#print axioms Erdos993Lean.BCFG.Analytic.messageRatio_light_mass_nonneg
#check Erdos993Lean.BCFG.Analytic.exact_light_mass_closed
#print axioms Erdos993Lean.BCFG.Analytic.exact_light_mass_closed
