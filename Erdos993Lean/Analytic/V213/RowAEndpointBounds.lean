module

public import Erdos993Lean.Analytic.V213.RowADefinitions
public import Erdos993Lean.Analytic.V213.FreeCountRealLogEnvelopes

/-!
Row A Step 3: the two literal logarithm bounds and their endpoint substitutions.
The Simpson bound is proved by its derivative, not imported from a numerical
certificate. The resulting Q comparison has no assumed logarithm inequality.
-/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.VarianceResponse.RowA

open Set FreeCountVariance.Envelopes

noncomputable def simpsonLog (t : ℝ) : ℝ := (t-1)/6*(1+8/(t+1)+1/t)

theorem simpson_gap_hasDerivAt {z : ℝ} (hz : 0 ≤ z) :
    HasDerivAt (fun w => simpsonLog (1+w)-Real.log (1+w))
      (z^4/(6*(1+z)^2*(2+z)^2)) z := by
  have h1 : 1+z ≠ 0 := by positivity
  have h2 : 2+z ≠ 0 := by positivity
  have hA := ((hasDerivAt_id z).const_add 1)
  have hB := ((hasDerivAt_id z).const_add 2)
  have hC := (hasDerivAt_const z (8:ℝ)).div hB h2
  have hD := (hasDerivAt_const z (1:ℝ)).div hA h1
  have h := (((hasDerivAt_id z).div_const 6).mul
    ((hC.const_add 1).add hD)).sub (hA.log h1)
  convert h using 1
  · funext w
    dsimp [simpsonLog]
    ring
  · dsimp
    field_simp [h1,h2] <;> ring

theorem log_le_simpson {t : ℝ} (ht : 1 ≤ t) : Real.log t ≤ simpsonLog t := by
  have h := zero_le_value_of_nonneg_deriv (f := fun w => simpsonLog (1+w)-Real.log (1+w))
    (f' := fun w => w^4/(6*(1+w)^2*(2+w)^2))
    (show 0 ≤ t-1 by linarith) (by norm_num [simpsonLog])
    (fun w hw => simpson_gap_hasDerivAt hw.1) (fun w hw => by positivity)
  simpa only [add_sub_cancel] using (sub_nonneg.mp h)

theorem two_term_log_lower {t : ℝ} (ht : 1 ≤ t) :
    2*((t-1)/(t+1)+((t-1)/(t+1))^3/3) ≤ Real.log t := by
  have hd : 0 < t+1 := by linarith
  have hw0 : 0 ≤ (t-1)/(t+1) := div_nonneg (by linarith) hd.le
  have hw1 : (t-1)/(t+1) < 1 := (div_lt_iff₀ hd).2 (by linarith)
  have h := Real.sum_range_le_log_div hw0 hw1 2
  have hid : (1+(t-1)/(t+1))/(1-(t-1)/(t+1))=t := by
    apply (div_eq_iff (by linarith : 1-(t-1)/(t+1) ≠ 0)).2
    field_simp [hd.ne'] <;> ring
  rw [hid] at h
  norm_num [Finset.sum_range_succ] at h
  nlinarith

theorem endpoint_denominators {x : ℝ} (hx : 0 ≤ x) (hx1 : x < 1) :
    0 < 4+28*x-5*x^2 ∧ 0 < 16+88*x-29*x^2 := by
  have hs : x^2 ≤ x := by nlinarith [mul_nonneg hx (sub_nonneg.mpr hx1.le)]
  constructor <;> nlinarith

theorem kappa_pos {x : ℝ} (hx : 0 ≤ x) (hx1 : x < 1) :
    0 < kappaMinus x ∧ 0 < kappaPlus x := by
  rcases endpoint_denominators hx hx1 with ⟨hdm,hdp⟩
  have h1 : 0 < 1-x := by linarith
  have h4 : 0 < 4-x := by linarith
  have h8 : 0 < 8-3*x := by linarith
  unfold kappaMinus kappaPlus
  constructor <;> apply div_pos <;> positivity

theorem childMass_minus {x : ℝ} :
    childMass (1/3) x = Real.log ((4-x)/(3*x)) := by
  unfold childMass
  congr 1
  simp only [div_eq_mul_inv,mul_inv_rev]
  ring

theorem childMass_plus {x : ℝ} :
    childMass (3/5) x = Real.log ((8-3*x)/(5*x)) := by
  unfold childMass
  congr 1
  simp only [div_eq_mul_inv,mul_inv_rev]
  ring

theorem kappa_simpson_minus {x : ℝ} (hx : 0 < x) (hx1 : x < 1) :
    kappaMinus x * simpsonLog ((4-x)/(3*x)) = 7/(15*x) := by
  have hd := (endpoint_denominators hx.le hx1).1
  have h1 : 1-x ≠ 0 := by linarith
  have h2 : x+2 ≠ 0 := by positivity
  have h4 : 4-x ≠ 0 := by linarith
  have hsum : (4-x)/(3*x)+1 ≠ 0 := by
    have : 0 < (4-x)/(3*x) := div_pos (by linarith) (by positivity)
    positivity
  unfold kappaMinus simpsonLog
  have hP : 4+(x*28-x^2*5)≠0 := by nlinarith [hd]
  have hS : 4+x*2≠0 := by positivity
  field_simp [hx.ne',h1,h2,h4,hd.ne',hsum] <;> ring_nf
  all_goals
    field_simp [hP,hS]
    ring_nf
    linear_combination (10080-5040*x-5040*x^2)*(mul_inv_cancel₀ hP)

theorem kappa_simpson_plus {x : ℝ} (hx : 0 < x) (hx1 : x < 1) :
    kappaPlus x * simpsonLog ((8-3*x)/(5*x)) = 14/(25*x) := by
  have hd := (endpoint_denominators hx.le hx1).2
  have h1 : 1-x ≠ 0 := by linarith
  have h4 : x+4 ≠ 0 := by positivity
  have h8 : 8-3*x ≠ 0 := by linarith
  have hsum : (8-3*x)/(5*x)+1 ≠ 0 := by
    have : 0 < (8-3*x)/(5*x) := div_pos (by linarith) (by positivity)
    positivity
  unfold kappaPlus simpsonLog
  have hP : 16+(x*88-x^2*29)≠0 := by nlinarith [hd]
  have hS : 8+x*2≠0 := by positivity
  field_simp [hx.ne',h1,h4,h8,hd.ne',hsum] <;> ring_nf
  all_goals
    field_simp [hP,hS]
    ring_nf
    linear_combination (67200-50400*x-16800*x^2)*(mul_inv_cancel₀ hP)

theorem kappaMinus_le {x : ℝ} (hx : 0 < x) (hx1 : x < 1) :
    kappaMinus x ≤ 7*(1+1/3)/(20*x*childMass (1/3) x) := by
  have hy := childMass_pos (by norm_num : (0:ℝ)<1/3) hx hx1
  have hT : 1 ≤ (4-x)/(3*x) := (le_div_iff₀ (by positivity)).2 (by linarith)
  have h := mul_le_mul_of_nonneg_left (log_le_simpson hT) (kappa_pos hx.le hx1).1.le
  rw [kappa_simpson_minus hx hx1,← childMass_minus] at h
  apply (le_div_iff₀ (by positivity : 0 < 20*x*childMass (1/3) x)).2
  have he := (le_div_iff₀ (by positivity : 0 < 15*x)).mp h
  nlinarith

theorem kappaPlus_le {x : ℝ} (hx : 0 < x) (hx1 : x < 1) :
    kappaPlus x ≤ 7*(1+3/5)/(20*x*childMass (3/5) x) := by
  have hy := childMass_pos (by norm_num : (0:ℝ)<3/5) hx hx1
  have hT : 1 ≤ (8-3*x)/(5*x) := (le_div_iff₀ (by positivity)).2 (by linarith)
  have h := mul_le_mul_of_nonneg_left (log_le_simpson hT) (kappa_pos hx.le hx1).2.le
  rw [kappa_simpson_plus hx hx1,← childMass_plus] at h
  apply (le_div_iff₀ (by positivity : 0 < 20*x*childMass (3/5) x)).2
  have he := (le_div_iff₀ (by positivity : 0 < 25*x)).mp h
  nlinarith

theorem tauMinus_le {x : ℝ} (hx : 0 < x) (hx1 : x < 1) :
    tauMinus x ≤ (7/6)*(343/400)*childMass (1/3) x := by
  have hT : 1 ≤ (4-x)/(3*x) := (le_div_iff₀ (by positivity)).2 (by linarith)
  have h := two_term_log_lower hT
  have hid : (((4-x)/(3*x))-1)/(((4-x)/(3*x))+1)=2*(1-x)/(2+x) := by
    have hs : 0 < (4-x)/(3*x)+1 := by positivity
    have hS : 4+x*2≠0 := by positivity
    field_simp [hx.ne',hs.ne',show 2+x ≠ 0 by positivity] <;> ring_nf
    all_goals field_simp [hS] <;> ring
  rw [hid,← childMass_minus] at h
  unfold tauMinus
  nlinarith

theorem tauPlus_le {x : ℝ} (hx : 0 < x) (hx1 : x < 1) :
    tauPlus x ≤ (7/6)*(319/400)*childMass (3/5) x := by
  have hT : 1 ≤ (8-3*x)/(5*x) := (le_div_iff₀ (by positivity)).2 (by linarith)
  have h := two_term_log_lower hT
  have hid : (((8-3*x)/(5*x))-1)/(((8-3*x)/(5*x))+1)=4*(1-x)/(4+x) := by
    have hs : 0 < (8-3*x)/(5*x)+1 := by positivity
    have hS : 8+x*2≠0 := by positivity
    field_simp [hx.ne',hs.ne',show 4+x ≠ 0 by positivity] <;> ring_nf
    all_goals field_simp [hS] <;> ring
  rw [hid,← childMass_plus] at h
  unfold tauPlus
  nlinarith

theorem quad_le_endpoint_of_bounds (lam eta0 sigma0 kappa tau nu x r z : ℝ)
    (hr : r ≤ 1)
    (hk : kappa ≤ 7*(1+lam)/(20*x*childMass lam x))
    (ht : tau ≤ (7/6)*eta0*childMass lam x)
    (hn : nu=1-q lam*x+(7*lam/20)*(1-q lam*x/2)) :
    quad kappa tau nu sigma0 (q lam) x r z ≤ endpointPsi lam eta0 sigma0 x r z := by
  have h1 := mul_le_mul_of_nonneg_right hk (sq_nonneg (1-z))
  have h2 := mul_le_mul_of_nonneg_right ht (show 0 ≤ 1-r by linarith)
  unfold quad endpointPsi
  rw [hn]
  nlinarith

theorem quadMinus_le_endpoint {x r z : ℝ} (hx : 0 < x) (hx1 : x < 1) (hr : r ≤ 3/8) :
    quadMinus x r z ≤ endpointPsi (1/3) (343/400) (15/16) x r z := by
  have h := quad_le_endpoint_of_bounds (1/3) (343/400) (15/16)
    (kappaMinus x) (tauMinus x) (nuMinus x) x r z (by linarith)
    (kappaMinus_le hx hx1) (tauMinus_le hx hx1) (by convert nuMinus_eq x using 1 <;> norm_num [q])
  norm_num [quadMinus,q] at h ⊢
  exact h

theorem quadPlus_le_endpoint {x r z : ℝ} (hx : 0 < x) (hx1 : x < 1) (hr : r ≤ 3/8) :
    quadPlus x r z ≤ endpointPsi (3/5) (319/400) (55/64) x r z := by
  have h := quad_le_endpoint_of_bounds (3/5) (319/400) (55/64)
    (kappaPlus x) (tauPlus x) (nuPlus x) x r z (by linarith)
    (kappaPlus_le hx hx1) (tauPlus_le hx hx1) (by convert nuPlus_eq x using 1 <;> norm_num [q])
  norm_num [quadPlus,q] at h ⊢
  exact h

end Erdos993Lean.Analytic.V213.VarianceResponse.RowA

#check Erdos993Lean.Analytic.V213.VarianceResponse.RowA.simpsonLog
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.RowA.simpsonLog
#check Erdos993Lean.Analytic.V213.VarianceResponse.RowA.simpson_gap_hasDerivAt
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.RowA.simpson_gap_hasDerivAt
#check Erdos993Lean.Analytic.V213.VarianceResponse.RowA.log_le_simpson
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.RowA.log_le_simpson
#check Erdos993Lean.Analytic.V213.VarianceResponse.RowA.two_term_log_lower
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.RowA.two_term_log_lower
#check Erdos993Lean.Analytic.V213.VarianceResponse.RowA.endpoint_denominators
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.RowA.endpoint_denominators
#check Erdos993Lean.Analytic.V213.VarianceResponse.RowA.kappa_pos
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.RowA.kappa_pos
#check Erdos993Lean.Analytic.V213.VarianceResponse.RowA.childMass_minus
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.RowA.childMass_minus
#check Erdos993Lean.Analytic.V213.VarianceResponse.RowA.childMass_plus
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.RowA.childMass_plus
#check Erdos993Lean.Analytic.V213.VarianceResponse.RowA.kappa_simpson_minus
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.RowA.kappa_simpson_minus
#check Erdos993Lean.Analytic.V213.VarianceResponse.RowA.kappa_simpson_plus
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.RowA.kappa_simpson_plus
#check Erdos993Lean.Analytic.V213.VarianceResponse.RowA.kappaMinus_le
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.RowA.kappaMinus_le
#check Erdos993Lean.Analytic.V213.VarianceResponse.RowA.kappaPlus_le
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.RowA.kappaPlus_le
#check Erdos993Lean.Analytic.V213.VarianceResponse.RowA.tauMinus_le
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.RowA.tauMinus_le
#check Erdos993Lean.Analytic.V213.VarianceResponse.RowA.tauPlus_le
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.RowA.tauPlus_le
#check Erdos993Lean.Analytic.V213.VarianceResponse.RowA.quad_le_endpoint_of_bounds
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.RowA.quad_le_endpoint_of_bounds
#check Erdos993Lean.Analytic.V213.VarianceResponse.RowA.quadMinus_le_endpoint
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.RowA.quadMinus_le_endpoint
#check Erdos993Lean.Analytic.V213.VarianceResponse.RowA.quadPlus_le_endpoint
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.RowA.quadPlus_le_endpoint

-- Imported API audits.
#check Erdos993Lean.Analytic.V213.FreeCountVariance.Envelopes.zero_le_value_of_nonneg_deriv
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.Envelopes.zero_le_value_of_nonneg_deriv
#check Real.sum_range_le_log_div
#print axioms Real.sum_range_le_log_div
