module

public import Erdos993Lean.Analytic.V213.FreeCountVarianceRowTaylor
public import Erdos993Lean.Analytic.V213.FreeCountACCellTransfer

/-!
Complete A-row implication after its point facts and three
scalar worksheet margins are supplied. The actual global ell/denominator
bounds remain explicit; they are not smuggled in as a named paper theorem.
The row m-range is also a separate checked guard. Closed rectangle endpoints
are allowed, but the physical AC evaluation requires y>0. No finite-family
statement or aggregate variance theorem is claimed here.
-/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.FreeCountVariance.Certificates

open Real Set Erdos993Lean.ExactComparisons.F3All

theorem ARowFacts.activity_floor_bounds {r : ARow} (hr : ARowFacts r) {lam : ℝ}
    (hlam : lam∈Icc (r.ac.b.lam : ℝ) (r.bd.b.lam : ℝ)) :
    (r.ac.b.lo : ℝ) ≤ logActivity lam ∧ qAtR r.ac.b.lam ≤ q lam := by
  have ha : (0:ℝ)<r.ac.b.lam := by exact_mod_cast hr.ac.activity_pos
  have hl : 0<lam := ha.trans_le hlam.1
  constructor
  · have hb : logActivity (r.ac.b.lam : ℝ)≤logActivity lam := by
      unfold logActivity
      exact Real.log_le_log (by linarith) (add_le_add (le_rfl : (1:ℝ) ≤ 1) hlam.1)
    exact hr.ac.beta_bounds.2.1.le.trans hb
  · change (r.ac.b.lam : ℝ)/(1+(r.ac.b.lam : ℝ))≤lam/(1+lam)
    apply (div_le_div_iff₀ (by linarith) (by linarith)).2
    nlinarith only [hlam.1]

/-- All analytic endpoint and Taylor estimates are discharged by ARowFacts.
Only the stated global scalar bounds and the actual checked row margins
remain, exactly where the printed argument consumes them. -/
theorem ARowFacts.AC_positive {r : ARow} (hr : ARowFacts r)
    (hD : (6/5:ℝ)≤r.D)
    (hm : decide (0≤r.m ∧ r.m≤49/100)=true)
    (hM : 0<cellM0R r) (hdw : 0<cellDeltaR r) (hbalance : 0<cellBalanceR r)
    {lam t y : ℝ}
    (hlam : lam∈Icc (r.ac.b.lam : ℝ) (r.bd.b.lam : ℝ))
    (hycell : y∈Icc (r.ac.e.y : ℝ) (r.bd.e.y : ℝ))
    (ht : 0≤t) (hy : 0<y) (hfeasible : logMass lam t≤y)
    (hell : -(3/4:ℝ)<ell (r.D : ℝ) lam y)
    (hden : 0<1+ell (r.D : ℝ) lam y*J lam t) :
    0<AC (r.D : ℝ) lam t y := by
  rcases aRowOK_domain_real hr.checked with
    ⟨hD0, ha, hab, hb7, had, hyd, hc, hcd, hd3, hmid⟩
  have hl : 0<lam := by linarith [hlam.1]
  have hrho := hr.rho_bounds hlam hycell
  have hmR := m_range_real hm
  have hfloor := hr.activity_floor_bounds hlam
  have hqa : 0<qAtR r.ac.b.lam :=
    q_pos (by exact_mod_cast hr.ac.activity_pos)
  have heps : epsilon (r.m : ℝ)=cellEpsilonR r := by
    unfold epsilon cellEpsilonR
    ring
  have hrow : 0 < min (omega (rhoMinusR r.bd)) (omega (rhoPlusR r.ac))+
      cellTR r-cellPsiR r+
      epsilon (r.m : ℝ)*max 0 (1-(r.bd.e.y : ℝ)/(r.ac.b.lo : ℝ))-
      ((r.bd.e.y : ℝ)/qAtR r.ac.b.lam)*
        (max 0 (cellKR r-(r.m : ℝ)))^2/cellDeltaR r := by
    rw [heps]
    exact hbalance
  exact AC_positive_of_cell_bounds hD0 hl (hlam.2.trans hb7) ht hy hfeasible
    hmR.1 hmR.2 hell hden hr.bd.rho_lower_positive hrho.1 hrho.2
    (hr.K_upper hlam hycell) hdw (hr.W_lower hlam hycell)
    (hr.T_lower hD hM hlam hycell) hr.ac.beta_bounds.1 hfloor.1
    hqa hfloor.2 hycell.2 hrow

end Erdos993Lean.Analytic.V213.FreeCountVariance.Certificates

-- Audit commands.
#check Erdos993Lean.Analytic.V213.FreeCountVariance.Certificates.ARowFacts.activity_floor_bounds
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.Certificates.ARowFacts.activity_floor_bounds
#check Erdos993Lean.Analytic.V213.FreeCountVariance.Certificates.ARowFacts.AC_positive
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.Certificates.ARowFacts.AC_positive
