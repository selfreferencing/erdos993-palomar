module

public import Erdos993Lean.Analytic.V213.FreeCountVarianceRowBounds
public import Erdos993Lean.Analytic.V213.FreeCountCAFeasibleFace

/-!
Interpretation of the literal C-row face worksheet. The local
ell lower bound is an explicit premise until activity monotonicity and the
parent curvature argument supply it. Every other endpoint substitution in
the C-row formula is proved from its PointFacts. Type L and type C margins
remain separate; no concrete record/list, cover or completed CA domain is
asserted here. On the face, positive activity forces y>0 automatically.
-/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.FreeCountVariance.Certificates

open Real Set Erdos993Lean.ExactComparisons.F3All

theorem jCap_positive (D : Rat) : (0:ℝ)<jCap D := by
  unfold jCap
  split <;> norm_num

theorem CRowFacts.cap_domain {r : CRow} (hr : CRowFacts r) :
    (0:ℝ)<r.D ∧ (0:ℝ)<r.left.b.lam ∧ (r.left.b.lam : ℝ)≤7/3 := by
  have h := capRightOK_positive (cRowOK_parts hr.checked).2.2.1
  exact ⟨h.1, by linarith [h.2.1], h.2.2⟩

theorem CRowFacts.message_upper {r : CRow} (hr : CRowFacts r) {lam y : ℝ}
    (hlam : 0<lam) (hlamu : lam≤(r.left.b.lam : ℝ))
    (hy : (r.left.e.y : ℝ)≤y) : message lam y≤pPlusR r.left := by
  have hu := hr.cap_domain.2.1
  have he := hr.left.exp_bounds
  have hex : (r.left.e.lo : ℝ)≤exp y :=
    he.2.1.trans (Real.exp_le_exp.mpr hy)
  rw [message_eq_exp_quotient hlam]
  unfold pPlusR
  apply (div_le_div_iff₀ (add_pos (exp_pos y) hlam) (add_pos he.1 hu)).2
  have hh := mul_le_mul hlamu hex he.1.le hu.le
  nlinarith only [hh]

theorem CRowFacts.beta_upper {r : CRow} (hr : CRowFacts r) {lam : ℝ}
    (hlam : 0<lam) (hlamu : lam≤(r.left.b.lam : ℝ)) :
    logActivity lam≤(r.left.b.hi : ℝ) := by
  have hh : logActivity lam≤logActivity (r.left.b.lam : ℝ) := by
    unfold logActivity
    exact Real.log_le_log (by linarith) (add_le_add (le_rfl : (1:ℝ) ≤ 1) hlamu)
  exact hh.trans hr.left.beta_bounds.2.2.le

theorem child_message_on_face {lam t y : ℝ} (hlam : 0<lam)
    (hface : y=logMass lam t) : message lam t=1-exp (-y) := by
  rw [hface, logMass_eq_neg_log hlam t, neg_neg,
    Real.exp_log (sub_pos.mpr (message_lt_one hlam t))]
  ring

theorem CRowFacts.signed_gap_lower {r : CRow} (hr : CRowFacts r) {lam t y : ℝ}
    (hlam : 0<lam) (hlamu : lam≤(r.left.b.lam : ℝ))
    (hy : (r.left.e.y : ℝ)≤y) (hface : y=logMass lam t) :
    1-1/(r.left.e.lo : ℝ)-pPlusR r.left ≤ message lam t-message lam y := by
  have he := hr.left.exp_bounds
  have hex : (r.left.e.lo : ℝ)≤exp y :=
    he.2.1.trans (Real.exp_le_exp.mpr hy)
  have hinv : 1/exp y≤1/(r.left.e.lo : ℝ) := by
    apply (div_le_div_iff₀ (exp_pos y) he.1).2
    simpa only [one_mul] using hex
  have hp := hr.message_upper hlam hlamu hy
  rw [child_message_on_face hlam hface, Real.exp_neg, ← one_div]
  linarith only [hinv, hp]

private theorem positive_part_sq_le_sq {a b : ℝ} (hab : a≤b) :
    (max 0 a)^2≤b^2 := by
  by_cases ha : a≤0
  · rw [max_eq_left ha]
    simpa using sq_nonneg b
  · have ha0 : 0≤a := le_of_lt (lt_of_not_ge ha)
    have hb0 : 0≤b := ha0.trans hab
    have hh := mul_nonneg (sub_nonneg.mpr hab) (add_nonneg hb0 ha0)
    rw [max_eq_right ha0]
    nlinarith only [hh]

theorem CRowFacts.gap_square_lower {r : CRow} (hr : CRowFacts r) {lam t y : ℝ}
    (hlam : 0<lam) (hlamu : lam≤(r.left.b.lam : ℝ))
    (hy : (r.left.e.y : ℝ)≤y) (hface : y=logMass lam t) :
    (faceS0R r)^2≤(message lam y-message lam t)^2 := by
  have hh := positive_part_sq_le_sq (hr.signed_gap_lower hlam hlamu hy hface)
  unfold faceS0R
  nlinarith only [hh]

/-- For a nonpositive ell, both changes have a fixed direction: decreasing
ell decreases ell/(1+j ell), and increasing its positive coefficient also
decreases the resulting nonpositive term. -/
theorem CRowFacts.correction_lower {r : CRow} (hr : CRowFacts r) {lam y : ℝ}
    (hlam : 0<lam) (hlamu : lam≤(r.left.b.lam : ℝ))
    (hy : (r.left.e.y : ℝ)≤y)
    (hEll : faceEllR r≤ell (r.D : ℝ) lam y)
    (hell : ell (r.D : ℝ) lam y≤0) (hd0 : 0<faceDenR r) :
    0<1+(jCap r.D : ℝ)*ell (r.D : ℝ) lam y ∧
    (5/7:ℝ)*(r.left.b.hi : ℝ)*pPlusR r.left*faceL0R r/faceDenR r≤
      (5/7:ℝ)*logActivity lam*message lam y*ell (r.D : ℝ) lam y/
        (1+(jCap r.D : ℝ)*ell (r.D : ℝ) lam y) := by
  have hj := jCap_positive r.D
  have hl0 : faceL0R r≤0 := min_le_left _ _
  have hl : faceL0R r≤ell (r.D : ℝ) lam y := (min_le_right _ _).trans hEll
  have hden : faceDenR r≤1+(jCap r.D : ℝ)*ell (r.D : ℝ) lam y := by
    unfold faceDenR
    exact add_le_add (le_rfl : (1:ℝ) ≤ 1) (mul_le_mul_of_nonneg_left hl hj.le)
  have hd := hd0.trans_le hden
  have hratio : faceL0R r/faceDenR r≤ell (r.D : ℝ) lam y/
      (1+(jCap r.D : ℝ)*ell (r.D : ℝ) lam y) := by
    apply (div_le_div_iff₀ hd0 hd).2
    unfold faceDenR
    nlinarith only [hl]
  have hratio0 : faceL0R r/faceDenR r≤0 :=
    div_nonpos_of_nonpos_of_nonneg hl0 hd0.le
  have hp := hr.message_upper hlam hlamu hy
  have hb := hr.beta_upper hlam hlamu
  have hbhi : (0:ℝ)<r.left.b.hi :=
    (logActivity_pos hr.cap_domain.2.1).trans hr.left.beta_bounds.2.2
  have hcoef := mul_le_mul_of_nonneg_left
    (mul_le_mul hb hp (message_pos hlam y).le hbhi.le)
    (by norm_num : (0:ℝ)≤5/7)
  have hfirst := mul_le_mul_of_nonpos_right hcoef hratio0
  have hsecond := mul_le_mul_of_nonneg_left hratio
    (mul_nonneg (by norm_num : (0:ℝ) ≤ 5/7)
      (mul_nonneg (logActivity_pos hlam).le (message_pos hlam y).le))
  refine ⟨hd, ?_⟩
  convert hfirst.trans hsecond using 1 <;> ring

/-- Type L has no face restriction: a positive local ell bound already
implies CA>0 at every feasible child. The calculus modules supply hEll. -/
theorem CRowFacts.CA_positive_of_L {r : CRow} (hr : CRowFacts r)
    (hmargin : 0<faceEllR r) {lam t y : ℝ}
    (hlam : 0<lam) (ht : 0≤t) (hfeasible : logMass lam t≤y)
    (hEll : faceEllR r≤ell (r.D : ℝ) lam y) :
    0<CA (r.D : ℝ) lam t y :=
  CA_pos_of_ell_pos hr.cap_domain.1 hlam ht hfeasible (hmargin.trans_le hEll)

/-- Literal type C face implication, including ell=0. No global ell lower
bound is assumed; only its explicit local interpolation consequence hEll. -/
theorem CRowFacts.CA_face_positive {r : CRow} (hr : CRowFacts r)
    (hd0 : 0<faceDenR r) (hmargin : 0<faceBalanceR r)
    {lam t y : ℝ} (hlam : 0<lam) (hlamu : lam≤(r.left.b.lam : ℝ))
    (ht : 0≤t) (hy : (r.left.e.y : ℝ)≤y) (hface : y=logMass lam t)
    (hEll : faceEllR r≤ell (r.D : ℝ) lam y)
    (hJ : J lam t<(jCap r.D : ℝ)) : 0<CA (r.D : ℝ) lam t y := by
  have hD := hr.cap_domain.1
  have hfeasible : logMass lam t≤y := by rw [hface]
  by_cases hell : ell (r.D : ℝ) lam y≤0
  · have hc := hr.correction_lower hlam hlamu hy hEll hell hd0
    have hs := hr.gap_square_lower hlam hlamu hy hface
    have hb := CA_feasible_face_lower hD hlam (hlamu.trans hr.cap_domain.2.2)
      ht hface hell hJ hc.1
    have hm : 0<y*CA (r.D : ℝ) lam t y/alpha (r.D : ℝ) lam := by
      have hmargin' : 0<2*(faceS0R r)^2+
          (5/7:ℝ)*(r.left.b.hi : ℝ)*pPlusR r.left*faceL0R r/faceDenR r := hmargin
      linarith only [hmargin', hc.2, hs, hb]
    have ha := alpha_pos hD hlam
    have hyp : 0<y := by rw [hface]; exact logMass_pos hlam t
    have hprod := (lt_div_iff₀ ha).1 hm
    nlinarith only [hprod, hyp]
  · exact CA_pos_of_ell_pos hD hlam ht hfeasible (lt_of_not_ge hell)

end Erdos993Lean.Analytic.V213.FreeCountVariance.Certificates

-- Audit commands.
#check Erdos993Lean.Analytic.V213.FreeCountVariance.Certificates.jCap_positive
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.Certificates.jCap_positive
#check Erdos993Lean.Analytic.V213.FreeCountVariance.Certificates.CRowFacts.cap_domain
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.Certificates.CRowFacts.cap_domain
#check Erdos993Lean.Analytic.V213.FreeCountVariance.Certificates.CRowFacts.message_upper
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.Certificates.CRowFacts.message_upper
#check Erdos993Lean.Analytic.V213.FreeCountVariance.Certificates.CRowFacts.beta_upper
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.Certificates.CRowFacts.beta_upper
#check Erdos993Lean.Analytic.V213.FreeCountVariance.Certificates.child_message_on_face
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.Certificates.child_message_on_face
#check Erdos993Lean.Analytic.V213.FreeCountVariance.Certificates.CRowFacts.signed_gap_lower
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.Certificates.CRowFacts.signed_gap_lower
#check Erdos993Lean.Analytic.V213.FreeCountVariance.Certificates.CRowFacts.gap_square_lower
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.Certificates.CRowFacts.gap_square_lower
#check Erdos993Lean.Analytic.V213.FreeCountVariance.Certificates.CRowFacts.correction_lower
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.Certificates.CRowFacts.correction_lower
#check Erdos993Lean.Analytic.V213.FreeCountVariance.Certificates.CRowFacts.CA_positive_of_L
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.Certificates.CRowFacts.CA_positive_of_L
#check Erdos993Lean.Analytic.V213.FreeCountVariance.Certificates.CRowFacts.CA_face_positive
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.Certificates.CRowFacts.CA_face_positive
