module

public import Erdos993Lean.Analytic.V213.FreeCountACKActivity
public import Erdos993Lean.Analytic.V213.FreeCountACActivityMonotonicity
public import Erdos993Lean.Analytic.V213.FreeCountACCellCalculus
public import Erdos993Lean.Analytic.V213.FreeCountACT0Derivatives

/-! Closed parent rectangles: the analytic implications behind (29).
Endpoint evaluation enclosures, positive row margins and covers are not
assumed proved here. They remain separate finite-record interpretation inputs. -/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.FreeCountVariance

open Real Set

theorem K_pos {D lam : ℝ} (hD : 0<D) (hlam : 0<lam) (y : ℝ) : 0<K D lam y := by
  unfold K
  rw [h_normalized hlam]
  have hp1 := message_lt_one hlam y
  exact div_pos (add_pos (by linarith)
    (div_pos (gamma_pos hD hlam) (B_pos hlam y))) hD

theorem K_monotone_parent {D lam : ℝ} (hD : 0<D) (hlam : 0<lam) :
    Monotone (K D lam) :=
  (strictMono_of_deriv_pos (fun y => K_deriv_pos_parent hD hlam y)).monotone

theorem rho_rectangle_bounds {a b c d lam y : ℝ}
    (ha : 0<a) (hb7 : b≤7/3) (hc : 0≤c)
    (hlam : lam∈Icc a b) (hy : y∈Icc c d) :
    rho b d ≤ rho lam y ∧ rho lam y ≤ rho a c := by
  have hl : 0<lam := ha.trans_le hlam.1
  have hb : 0<b := hl.trans_le hlam.2
  have hd : 0≤d := hc.trans (hy.1.trans hy.2)
  have hyl : 0≤y := hc.trans hy.1
  constructor
  · exact (rho_antitone_activity hd ⟨hl, hlam.2.trans hb7⟩ ⟨hb, hb7⟩ hlam.2).trans
      (rho_antitone_parent hl hy.2)
  · exact (rho_antitone_parent hl hy.1).trans
      (rho_antitone_activity hc ⟨ha, hlam.1.trans (hlam.2.trans hb7)⟩
        ⟨hl, hlam.2.trans hb7⟩ hlam.1)

/-- Includes both activity and parent endpoints, with the literal 15/256
correction. This is the precise analytic premise consumed by K-plus brackets. -/
theorem K_le_rectangle_endpoints {D a b c d lam y : ℝ}
    (hD : 0<D) (ha : (1/3:ℝ)≤a) (hab : a<b) (hc : 0≤c)
    (hlam : lam∈Icc a b) (hy : y∈Icc c d) :
    K D lam y ≤ max (K D a d) (K D b d)+(15/256:ℝ)*(b-a)^2 := by
  have hd : 0≤d := hc.trans (hy.1.trans hy.2)
  have hl : 0<lam := by linarith [hlam.1]
  have hparent := K_monotone_parent hD hl hy.2
  have hs := Real.exp_pos (-d)
  have hcell := second_lower_endpoint_upper (f := fun z => K D z d)
    (f' := KActivitySlope D (exp (-d)))
    (f'' := KActivityCurvature D (exp (-d))) hab (by norm_num : (0:ℝ)≤15/32)
    (fun z hz => K_hasDerivAt_activity hD (by linarith [hz.1]) d)
    (fun z hz => KActivitySlope_hasDerivAt hD hs (by linarith [hz.1]))
    (fun z hz => KActivityCurvature_lower_fifteen_thirtytwo hD (ha.trans hz.1) hd) hlam
  have hi : (15/32:ℝ)*(b-a)^2/8 = (15/256:ℝ)*(b-a)^2 := by ring
  rw [hi] at hcell
  exact hparent.trans hcell

theorem W_ge_rectangle_lower {D b c d lam y kbar : ℝ}
    (hD : 0<D) (hlam : 0<lam) (hlamb : lam≤b) (hc : 0≤c)
    (hy : y∈Icc c d) (hK : K D lam y≤kbar) :
    (5/12:ℝ)*(logActivity b*exp c/b+2*betaRatio b)-d*kbar ≤ W D lam y := by
  have hb : 0<b := hlam.trans_le hlamb
  have hyl : 0≤y := hc.trans hy.1
  have hd : 0≤d := hyl.trans hy.2
  have hratio := beta_div_activity_antitone hlam hb hlamb
  have hr0 : 0≤logActivity lam/lam := (div_pos (logActivity_pos hlam) hlam).le
  have hexp := Real.exp_le_exp.mpr hy.1
  have hfirst := mul_le_mul hratio hexp (Real.exp_pos c).le hr0
  have hsecond := betaRatio_antitone hlam hb hlamb
  have hlast := mul_le_mul hy.2 hK (K_pos hD hlam y).le hd
  unfold W betaRatio at *
  have hi1 : logActivity b*exp c/b = (logActivity b/b)*exp c := by ring
  have hi2 : logActivity lam*exp y/lam = (logActivity lam/lam)*exp y := by ring
  rw [hi1, hi2]
  dsimp only at hfirst
  ring_nf at hfirst hsecond hlast ⊢
  linarith only [hfirst, hsecond, hlast]

/-- The activity comparison is already discharged. Only the actual fixed-b
curvature/basepoint/slope enclosures remain explicit finite inputs. -/
theorem T0_ge_rectangle_cell_lower {D a b c d lam y y0 M j w lower : ℝ}
    (hD : (6/5:ℝ)≤D) (ha : 0<a) (hb7 : b≤7/3) (hc : 0≤c)
    (hlam : lam∈Icc a b) (hy : y∈Icc c d) (hy0 : y0∈Icc c d)
    (hM : 0<M) (hj : 0≤j) (hw : 0≤w) (hwidth : |y-y0|≤w)
    (hcurv : ∀ z∈Icc c d, M≤T0Curvature D b z)
    (hbase : lower≤T0 D b y0) (hslope : |T0Slope D b y0|≤j) :
    lower-quadraticLoss M j w ≤ T0 D lam y := by
  have hl : 0<lam := ha.trans_le hlam.1
  have hb : 0<b := hl.trans_le hlam.2
  have hactivity := T0_antitone_activity hD (hc.trans hy.1)
    ⟨hl, hlam.2.trans hb7⟩ ⟨hb, hb7⟩ hlam.2
  have hcell := second_lower_cell_value
    (f := T0 D b) (f' := T0Slope D b) (f'' := T0Curvature D b)
    (fun z _ => T0_hasDerivAt_parent (by linarith) hb z)
    (fun z _ => T0Slope_hasDerivAt_parent (by linarith) hb z)
    hcurv hy hy0 hM hj hw hwidth hbase hslope
  exact hcell.trans hactivity

end Erdos993Lean.Analytic.V213.FreeCountVariance

#check Erdos993Lean.Analytic.V213.FreeCountVariance.K_pos
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.K_pos
#check Erdos993Lean.Analytic.V213.FreeCountVariance.K_monotone_parent
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.K_monotone_parent
#check Erdos993Lean.Analytic.V213.FreeCountVariance.rho_rectangle_bounds
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.rho_rectangle_bounds
#check Erdos993Lean.Analytic.V213.FreeCountVariance.K_le_rectangle_endpoints
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.K_le_rectangle_endpoints
#check Erdos993Lean.Analytic.V213.FreeCountVariance.W_ge_rectangle_lower
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.W_ge_rectangle_lower
#check Erdos993Lean.Analytic.V213.FreeCountVariance.T0_ge_rectangle_cell_lower
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.T0_ge_rectangle_cell_lower
