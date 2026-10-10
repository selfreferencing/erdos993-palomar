module

public import Erdos993Lean.Analytic.V213.ResponseOneVertex

/-!
Printed Lemma 5.17. The product inequality applies
also to an empty child set. The nonleaf light mass identity uses Y>0; no
division by the leaf value Y=0 is asserted.
-/

@[expose] public section

set_option autoImplicit false

namespace Erdos993Lean.BCFG.Analytic

open Finset
open Erdos993Lean.Analytic
open Erdos993Lean.Analytic.Tail Erdos993Lean.Analytic.Reserve
open Erdos993Lean.Analytic.V213.VarianceResponse

/-- The elementary product bound used in the printed proof of Lemma 5.17. -/
theorem one_sub_prod_one_sub_le_sum {I : Type*} [DecidableEq I]
    (s : Finset I) (p : I → ℝ) (hp : ∀ i ∈ s, 0 ≤ p i ∧ p i ≤ 1) :
    1 - ∏ i ∈ s, (1-p i) ≤ ∑ i ∈ s, p i := by
  revert hp
  induction s using Finset.induction_on with
  | empty => intro hp; simp
  | @insert a s ha ih =>
      intro hp
      have hs : ∀ i ∈ s, 0 ≤ p i ∧ p i ≤ 1 :=
        fun i hi => hp i (mem_insert_of_mem hi)
      have hpa := hp a (mem_insert_self a s)
      have hprod : ∏ i ∈ s, (1-p i) ≤ (1 : ℝ) :=
        Finset.prod_le_one₀ (fun i hi => sub_nonneg.mpr (hs i hi).2)
          (fun i hi => by linarith [(hs i hi).1])
      have hmul := mul_le_mul_of_nonneg_left hprod hpa.1
      have hsum := ih hs
      simp only [prod_insert ha, sum_insert ha]
      nlinarith

/-- On the light domain the cavity cap is exactly the total child vacancy loss. -/
theorem cavH_light {lam omega : ℝ} (hl : 0 < lam) (hw : 0 < omega)
    (hlight : 1-omega ≤ actQ lam) :
    O2.cavH lam (lam*omega/(1+lam*omega)) = 1-omega := by
  have hd : 1+lam*omega ≠ 0 := ne_of_gt (by positivity)
  have hsub : 1-lam*omega/(1+lam*omega) = 1/(1+lam*omega) := by
    field_simp [hd]
    ring
  have hid : (lam*omega/(1+lam*omega))/(lam*(1-lam*omega/(1+lam*omega))) = omega := by
    rw [hsub]
    field_simp [hd,hl.ne'] <;> ring
  unfold O2.cavH
  rw [hid,min_eq_right hlight]

/-- The assigned h has its exact nonleaf light mass identity. -/
theorem messageRatio_light_mass {Y : ℝ} (hY : 0 < Y) :
    messageRatio (1-Real.exp (-Y))*Y = 1-Real.exp (-Y) := by
  have he : Real.exp (-Y) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have hne : 1-Real.exp (-Y) ≠ 0 := ne_of_gt (by linarith)
  rw [messageRatio_of_ne_zero hne,
    show 1-(1-Real.exp (-Y)) = Real.exp (-Y) by ring,
    Real.log_exp,neg_neg,div_mul_cancel₀ _ hY.ne']

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- The printed lower bound for the actual children of any rooted forest. -/
theorem children_mass_lower (hG : G.IsAcyclic) {lam : ℝ} (hl : 0 < lam)
    {s : Finset V} (hs : ConnectedIn G s) {v : V} (hv : v ∈ s) :
    1-Real.exp (-Tmass G lam s v) ≤
      ∑ w ∈ nbrsIn G s v, rootProb G lam (compIn G (s.erase v) w) w := by
  rw [← O2.prod_one_sub_eq_exp hG hl.le hs hv]
  apply one_sub_prod_one_sub_le_sum
  intro w hw
  exact ⟨(rootProb_pos hl _ _).le,
    (rootProb_lt_one hl.le (self_mem_branch hw)).le⟩

/-- Exact nonleaf light mass and its actual probability-sum lower bound. -/
theorem exact_light_mass (hG : G.IsAcyclic) {lam : ℝ} (hl : 0 < lam)
    {s : Finset V} (hs : ConnectedIn G s) {v : V} (hv : v ∈ s)
    (hchild : (nbrsIn G s v).Nonempty)
    (hlight : 1-Real.exp (-Tmass G lam s v) ≤ actQ lam) :
    messageRatio (O2.cavH lam (rootProb G lam s v))*Tmass G lam s v =
      1-Real.exp (-Tmass G lam s v) ∧
    messageRatio (O2.cavH lam (rootProb G lam s v))*Tmass G lam s v ≤
      ∑ w ∈ nbrsIn G s v, rootProb G lam (compIn G (s.erase v) w) w := by
  have hc : O2.cavH lam (rootProb G lam s v) = 1-Real.exp (-Tmass G lam s v) := by
    rw [message_recursion hG hl hs hv]
    unfold msg
    exact cavH_light hl (Real.exp_pos _) hlight
  have hm := messageRatio_light_mass (Tmass_pos hG hl hs hv hchild)
  rw [hc]
  exact ⟨hm,hm.le.trans (children_mass_lower hG hl hs hv)⟩

end Erdos993Lean.BCFG.Analytic

#check Erdos993Lean.BCFG.Analytic.one_sub_prod_one_sub_le_sum
#print axioms Erdos993Lean.BCFG.Analytic.one_sub_prod_one_sub_le_sum
#check Erdos993Lean.BCFG.Analytic.cavH_light
#print axioms Erdos993Lean.BCFG.Analytic.cavH_light
#check Erdos993Lean.BCFG.Analytic.messageRatio_light_mass
#print axioms Erdos993Lean.BCFG.Analytic.messageRatio_light_mass
#check Erdos993Lean.BCFG.Analytic.children_mass_lower
#print axioms Erdos993Lean.BCFG.Analytic.children_mass_lower
#check Erdos993Lean.BCFG.Analytic.exact_light_mass
#print axioms Erdos993Lean.BCFG.Analytic.exact_light_mass
