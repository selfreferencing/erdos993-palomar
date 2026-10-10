module
public import Erdos993Lean.F4U.Light.Linking.Polynomial2
public import Mathlib.Topology.Order.IntermediateValue
public import Mathlib.Topology.Algebra.Ring.Real

/-! Orientation of an actual integer bivariate denominator on its closed
activity/chart rectangle. Polynomial continuity is proved internally; the
only sign inputs are nonvanishing throughout the stated domain and positivity
at a stated point of that same domain. -/
@[expose] public section
namespace F4Unified.LightConstruction
noncomputable section

theorem integer_eval_continuous (p : List Int) :
    Continuous (fun x : ℝ => F4U.Light.eval p x) := by
  induction p with
  | nil => exact continuous_const
  | cons a p ih =>
    exact continuous_const.add (continuous_id.mul ih)

theorem polynomial2_eval_continuous (D : F4U.Light.Linking.Polynomial2.Rows) :
    Continuous (fun z : ℝ × ℝ => F4U.Light.Linking.Polynomial2.eval D z.1 z.2) := by
  induction D with
  | nil => exact continuous_const
  | cons a D ih =>
    exact ((integer_eval_continuous a).comp continuous_fst).add (continuous_snd.mul ih)

/-- A nonzero denominator has the sign of a positive base point on the whole
closed rectangle, including its boundary and degenerate activity intervals. -/
theorem denominator_positive_of_nonzero
    (D : F4U.Light.Linking.Polynomial2.Rows) {a b x0 t0 x t : ℝ}
    (hNZ : ∀ x t, a ≤ x → x ≤ b → 0 ≤ t → t ≤ 1 →
      F4U.Light.Linking.Polynomial2.eval D x t ≠ 0)
    (hx0a : a ≤ x0) (hx0b : x0 ≤ b) (ht00 : 0 ≤ t0) (ht01 : t0 ≤ 1)
    (hbase : 0 < F4U.Light.Linking.Polynomial2.eval D x0 t0)
    (hxa : a ≤ x) (hxb : x ≤ b) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    0 < F4U.Light.Linking.Polynomial2.eval D x t := by
  by_contra hn
  have hn0 : F4U.Light.Linking.Polynomial2.eval D x t ≤ 0 := le_of_not_gt hn
  have hc : IsPreconnected (Set.Icc a b ×ˢ Set.Icc (0 : ℝ) 1) :=
    isPreconnected_Icc.prod isPreconnected_Icc
  have hx : (x,t) ∈ Set.Icc a b ×ˢ Set.Icc (0 : ℝ) 1 := ⟨⟨hxa,hxb⟩,ht0,ht1⟩
  have hx0 : (x0,t0) ∈ Set.Icc a b ×ˢ Set.Icc (0 : ℝ) 1 := ⟨⟨hx0a,hx0b⟩,ht00,ht01⟩
  obtain ⟨z,hz,heq⟩ := hc.intermediate_value hx hx0
    (polynomial2_eval_continuous D).continuousOn (show
      (0 : ℝ) ∈ Set.Icc (F4U.Light.Linking.Polynomial2.eval D x t)
        (F4U.Light.Linking.Polynomial2.eval D x0 t0) from ⟨hn0,hbase.le⟩)
  exact hNZ z.1 z.2 hz.1.1 hz.1.2 hz.2.1 hz.2.2 heq

/-- Convenient orientation from the left activity endpoint at chart t=0. -/
theorem denominator_positive_of_left_base
    (D : F4U.Light.Linking.Polynomial2.Rows) {a b x t : ℝ} (hab : a ≤ b)
    (hNZ : ∀ x t, a ≤ x → x ≤ b → 0 ≤ t → t ≤ 1 →
      F4U.Light.Linking.Polynomial2.eval D x t ≠ 0)
    (hbase : 0 < F4U.Light.Linking.Polynomial2.eval D a 0)
    (hxa : a ≤ x) (hxb : x ≤ b) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    0 < F4U.Light.Linking.Polynomial2.eval D x t := by
  exact denominator_positive_of_nonzero D hNZ le_rfl hab le_rfl (by norm_num)
    hbase hxa hxb ht0 ht1

#print axioms integer_eval_continuous
#print axioms polynomial2_eval_continuous
#print axioms denominator_positive_of_nonzero
#print axioms denominator_positive_of_left_base

end
end F4Unified.LightConstruction
