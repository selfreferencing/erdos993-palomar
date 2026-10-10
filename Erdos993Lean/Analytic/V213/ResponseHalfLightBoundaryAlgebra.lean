module

public import Erdos993Lean.Analytic.V213.ResponseHalfLightScalarBounds

/-! Exact Eq17 and the lower-bound gap underlying Eq18. Every discarded term
is displayed; the H.1 correction retains its signed physical-domain factor.
The source-chord inequality is an explicit intermediate premise here, to be
discharged by the separate phase-source theorem before a boundary conclusion. -/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLight

open FreeCountVariance.Envelopes

theorem boundary_scaled_identity {i : Fin 4} {lam H rho y : ℝ}
    (hl : 0 < lam) (hH : 0 < H) (hcap : H ≤ childQ lam/2) :
    let p := halfParent lam H
    let Y := parentY H
    let z := Y*y/H
    Y*parentPayment i lam H rho H y/p =
      price i lam*rho*O2.src lam p rho+alpha i lam*(1-rho)+beta i lam*rho*H-
      (alpha i lam+beta i lam)*H*z-parentP i lam H rho*(1-H*z)^2+
      capitalGamma i lam/p*(H^2/Y)*z^2+delta i lam/(p*childLog lam H)*(1-z)^2 := by
  have hp := halfParent_bounds hl hH.le hcap
  have hc := half_child_bounds hl hH hcap
  have hY : 0 < parentY H := scalarLog_pos hH (by linarith [hp.1])
  have hh : messageRatio H=H/parentY H := by
    rw [messageRatio_eq_scalarH hH.ne']
    rfl
  dsimp only
  unfold parentPayment responseQuadratic parentA parentB parentC parentD capitalGamma childJ
  rw [hh]
  field_simp [hp.2.1.ne',hY.ne',hH.ne',hc.2.2.1.ne']
  ring

theorem boundary_lower_gap {i : Fin 4} {phase : ℕ} {lam H rho y : ℝ}
    (hl : 0 < lam) (hH : 0 < H) (hcap : H ≤ childQ lam/2) :
    let p := halfParent lam H
    let Y := parentY H
    let z := Y*y/H
    Y*parentPayment i lam H rho H y/p-jointQuadratic i phase lam H rho z =
      price i lam*rho*(O2.src lam p rho-(sourceChordA phase lam H*rho+sourceChordB phase lam H))+
      gamma i lam*(upperRatio p-messageRatio p)*(1-H*z)^2+
      capitalGamma i lam/p*H*(H/Y-lowerChildRatio H)*z^2+
      (delta i lam/(p*childLog lam H)-H*responseFactor i lam H)*(1-z)^2+
      H^2*(1-rho)*(1-p)*z^2-
      phaseCorrection i phase lam H*(rho-rhoStar lam p) := by
  dsimp only
  rw [boundary_scaled_identity hl hH hcap]
  unfold jointQuadratic quadraticA2 quadraticA1 quadraticA0 quadraticB1 quadraticB0 quadraticK parentP
  ring

theorem boundary_quadratic_lower_of_source_chord {i : Fin 4} {phase : ℕ} {lam H rho y : ℝ}
    (hrow : inRow i lam) (hH : 0 < H) (hcap : H ≤ childQ lam/2)
    (hrho : rhoMin lam (halfParent lam H) ≤ rho) (hrho1 : rho ≤ 1)
    (hphase : phaseDomain phase lam H rho)
    (hsource : sourceChordA phase lam H*rho+sourceChordB phase lam H ≤
      O2.src lam (halfParent lam H) rho) :
    jointQuadratic i phase lam H rho (parentY H*y/H) ≤
      parentY H*parentPayment i lam H rho H y/halfParent lam H := by
  have hl := (row_activity_bounds hrow).1
  have hp := halfParent_bounds hl hH.le hcap
  have hr := half_rho_pos hl hH.le hcap hrho
  have hprice := row_price_pos hrow
  have hg := (all_rows_fields_positive hrow).2.2.1
  have hGamma := row_Gamma_pos hrow
  have hup := parent_ratio_upper hrow hH.le hcap
  have hlo := boundary_child_ratio_lower hH (show H<1 by linarith [hp.1])
  have hresp := boundary_response_lower hrow hH hcap
  have hcorr := phaseCorrection_product_nonpos (i:=i) hl hH.le hcap hphase
  have hp0 := hp.2.1
  have hp1 : 0 ≤ 1-halfParent lam H := by linarith [hp.2.2.1]
  have hr1 : 0 ≤ 1-rho := by linarith
  have hupper : 0 ≤ upperRatio (halfParent lam H)-messageRatio (halfParent lam H) := sub_nonneg.mpr hup
  have hlower : 0 ≤ H/parentY H-lowerChildRatio H := sub_nonneg.mpr hlo
  have hresponse : 0 ≤ delta i lam/(halfParent lam H*childLog lam H)-H*responseFactor i lam H := sub_nonneg.mpr hresp
  have h1 : 0 ≤ price i lam*rho*
      (O2.src lam (halfParent lam H) rho-(sourceChordA phase lam H*rho+sourceChordB phase lam H)) :=
    mul_nonneg (mul_nonneg hprice.le hr.le) (sub_nonneg.mpr hsource)
  have h2 : 0 ≤ gamma i lam*(upperRatio (halfParent lam H)-messageRatio (halfParent lam H))*
      (1-H*(parentY H*y/H))^2 := by positivity
  have h3 : 0 ≤ capitalGamma i lam/halfParent lam H*H*(H/parentY H-lowerChildRatio H)*
      (parentY H*y/H)^2 := by positivity
  have h4 : 0 ≤ (delta i lam/(halfParent lam H*childLog lam H)-H*responseFactor i lam H)*
      (1-parentY H*y/H)^2 := by positivity
  have h5 : 0 ≤ H^2*(1-rho)*(1-halfParent lam H)*(parentY H*y/H)^2 := by positivity
  have hid := boundary_lower_gap (i:=i) (phase:=phase) (rho:=rho) (y:=y) hl hH hcap
  dsimp only at hid
  linarith

end Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLight

#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLight.boundary_scaled_identity
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLight.boundary_scaled_identity
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLight.boundary_lower_gap
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLight.boundary_lower_gap
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLight.boundary_quadratic_lower_of_source_chord
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLight.boundary_quadratic_lower_of_source_chord
