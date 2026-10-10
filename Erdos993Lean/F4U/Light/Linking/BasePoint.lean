module
public import Erdos993Lean.F4U.Light.Linking.Polynomial2
@[expose] public section
namespace F4U.Light.Linking
noncomputable section

/-- The integer homogeneous value of the actual denominator at the named base (a/b,0). -/
def checkPositiveBase (D : Polynomial2.Rows) (a b : Int) : Bool :=
  decide (0 < b) && decide (0 < (F4U.Light.shiftScale a 0 b (D.headD [])).headD 0)

 theorem eval_zero_head (p : List Int) : F4U.Light.eval p 0 = (p.headD 0 : ℝ) := by
  cases p <;> simp [F4U.Light.eval]

 theorem eval_outer_zero_head (D : Polynomial2.Rows) (x : ℝ) :
    Polynomial2.eval D x 0 = F4U.Light.eval (D.headD []) x := by
  cases D <;> simp [Polynomial2.eval]

 theorem checkPositiveBase_sound {D : Polynomial2.Rows} {a b : Int}
    (h : checkPositiveBase D a b = true) :
    0 < Polynomial2.eval D ((a:ℝ)/b) 0 := by
  have hh : 0 < b ∧ 0 < (F4U.Light.shiftScale a 0 b (D.headD [])).headD 0 := by
    simpa only [checkPositiveBase,Bool.and_eq_true_iff,decide_eq_true_eq] using h
  have hb : (0:ℝ) < b := by exact_mod_cast hh.1
  have hi : (0:ℝ) < ((F4U.Light.shiftScale a 0 b (D.headD [])).headD 0 : ℝ) := by
    exact_mod_cast hh.2
  have he := F4U.Light.eval_shiftScale a 0 b (ne_of_gt hb) (D.headD []) 0
  simp only [eval_zero_head,Int.cast_zero,zero_mul,add_zero] at he
  have hp : 0 < (b:ℝ)^((D.headD []).length-1) := pow_pos hb _
  have hm : 0 < (b:ℝ)^((D.headD []).length-1) *
      F4U.Light.eval (D.headD []) ((a:ℝ)/b) := by rw [← he]; exact hi
  rw [eval_outer_zero_head]
  exact (mul_pos_iff_of_pos_left hp).mp hm

#print axioms checkPositiveBase
#print axioms eval_zero_head
#print axioms eval_outer_zero_head
#print axioms checkPositiveBase_sound
end
end F4U.Light.Linking
