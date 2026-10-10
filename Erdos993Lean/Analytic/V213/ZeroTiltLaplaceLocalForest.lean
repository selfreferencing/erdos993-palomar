module

public import Erdos993Lean.Analytic.V213.ZeroTiltLaplaceTelescope
public import Erdos993Lean.Analytic.V213.ZeroTiltLaplacePartition

/-!
This discharges the actual local, selected-vertex and
root hypotheses of the single telescoping sum. The only unproved analytic
input is the literal current `UnitNonnegative`; neither potential_induction
nor a historical completed forest rate theorem is applied.
-/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.ZeroTiltLaplace

open Finset

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- The paper's actual outside factor, assigned value one at selected vertices. -/
noncomputable def currentFactor (G : SimpleGraph V) [DecidableRel G.Adj]
    (A : Finset V) (lam : ℝ) (s : Finset V) (r : V) : ℝ :=
  if r ∈ A then 1 else Tail.rootProb G lam s r+
    (1-Tail.rootProb G lam s r)*Real.exp (-Tail.unitY G A lam s r)

theorem currentFactor_eq_toyLocal (A : Finset V) {lam : ℝ} (hlam : 0 ≤ lam)
    (s : Finset V) (r : V) : currentFactor G A lam s r = Tail.toyLocal G A lam 0 s r := by
  unfold currentFactor Tail.toyLocal Tail.tauC
  rw [Tail.exp_neg_unitY hlam]
  simp only [Tail.betaB, sub_zero, one_mul]

/-- This is precisely sigma from the displayed single-sum argument. -/
noncomputable def currentSigma (G : SimpleGraph V) [DecidableRel G.Adj]
    (A : Finset V) (lam : ℝ) (s : Finset V) (r : V) : ℝ :=
  -Real.log (currentFactor G A lam s r)-
    E lam (Y lam (Tail.rootProb G lam s r))*Tail.sB G A lam s r

theorem currentSigma_eq_sigmaU (A : Finset V) {lam : ℝ} (hlam : 0 < lam)
    {s : Finset V} {r : V} (hr : r ∈ s) :
    currentSigma G A lam s r = Tail.sigmaU G A lam 0 (ellH lam) s r := by
  have hpr : Tail.rootProb G lam s r =
      Tail.pC lam (Y lam (Tail.rootProb G lam s r)) :=
    Tail.eq_pC_of_Tf hlam (Tail.rootProb_pos hlam s r)
      (Tail.rootProb_lt_one hlam.le hr) rfl
  unfold currentSigma
  rw [currentFactor_eq_toyLocal A hlam.le, current_E_eq_T3c hlam]
  unfold Tail.T3c Tail.sigmaU
  rw [← hpr]
  ring

theorem currentSigma_selected_zero {A : Finset V} (hA : IsIndepFinset G A)
    (lam : ℝ) (s : Finset V) {r : V} (hrA : r ∈ A) :
    currentSigma G A lam s r = 0 := by
  simp [currentSigma, currentFactor, hrA, Tail.sB_eq_zero hA hrA]

theorem root_Psi_nonnegative {lam : ℝ} (hd : ActivityDomain lam)
    {s : Finset V} {r : V} (hr : r ∈ s) :
    0 ≤ Psi lam (Tail.rootProb G lam s r) := by
  have hlam : 0 < lam := by linarith [hd.1]
  have ha : 0 ≤ a lam := by linarith [(a_bounds hd).1]
  have hw : 0 ≤ w lam := (w_pos_lt_one hlam).1.le
  have hb := Tail.Lf_nonneg (Tail.rootProb_nonneg (G := G) hlam.le s r)
    (Tail.rootProb_lt_one hlam.le hr)
  have hY := Tail.Tf_nonneg hlam (Tail.rootProb_pos (G := G) hlam s r)
    (Tail.rootProb_le_actQ hlam.le hr)
  exact add_nonneg (mul_nonneg ha hb) (mul_nonneg (mul_nonneg ha hw) hY)

/-- At a selected vertex every child is outside. The selected leaf has H(q)=0. -/
theorem selectedSurplus_nonnegative (hG : G.IsAcyclic) {A : Finset V}
    (hA : IsIndepFinset G A) {lam : ℝ} (hd : ActivityDomain lam)
    {s : Finset V} (hs : ConnectedIn G s) {r : V} (hr : r ∈ s) :
    0 ≤ selectedSurplus G A lam s r := by
  by_cases hrA : r ∈ A
  · have hlam : 0 < lam := by linarith [hd.1]
    have ha : 0 ≤ a lam := by linarith [(a_bounds hd).1]
    have haw : 0 ≤ a lam*w lam := mul_nonneg ha (w_pos_lt_one hlam).1.le
    have hk : ∀ v ∈ nbrsIn G s r, v ∉ A :=
      fun v hv hvA => hA r hrA v hvA (mem_nbrsIn.mp hv).2
    have hsum : (∑ v ∈ nbrsIn G s r,
        vertexPotential G A lam (compIn G (s.erase r) v) v) =
        a lam*Y lam (Tail.rootProb G lam s r)+
          (a lam*w lam)*∑ v ∈ nbrsIn G s r,
            Y lam (Tail.rootProb G lam (compIn G (s.erase r) v) v) := by
      calc
        _ = ∑ v ∈ nbrsIn G s r,
            Psi lam (Tail.rootProb G lam (compIn G (s.erase r) v) v) := by
          apply Finset.sum_congr rfl
          intro v hv
          simp only [vertexPotential, if_neg (hk v hv)]
        _ = _ := by
          have hmass : (∑ v ∈ nbrsIn G s r,
              b (Tail.rootProb G lam (compIn G (s.erase r) v) v)) =
              Y lam (Tail.rootProb G lam s r) :=
            Tail.lemmaC_exact hG hlam hs hr
          simp only [Psi, Finset.sum_add_distrib, ← Finset.mul_sum]
          rw [hmass]
    rw [selectedSurplus, if_pos hrA, hsum, vertexPotential, if_pos hrA]
    rcases (nbrsIn G s r).eq_empty_or_nonempty with hnil | hne
    · have hpq := Tail.rootProb_eq_actQ (G := G) hlam.le hr hnil
      have hH : H lam (actQ lam) = 0 := H_leaf lam
      have hY : Y lam (actQ lam) = 0 := Tail.Tf_actQ hlam
      rw [hpq,hH,hY,hnil]
      simp
    · have hp := Tail.rootProb_pos (G := G) hlam s r
      have hpq := Tail.rootProb_le_actQ (G := G) hlam.le hr
      have hlt := Tail.rootProb_lt_actQ (G := G) hlam hr hne
      rw [current_child_potential hlam hp hpq, if_pos hlt]
      have hchild := Tail.lemmaC_tree hG hlam hs hr hne
      have hh := mul_le_mul_of_nonneg_left hchild haw
      change 0 ≤ a lam*Tail.Tf lam (Tail.rootProb G lam s r)+
        (a lam*w lam)*∑ v ∈ nbrsIn G s r,
          Tail.Tf lam (Tail.rootProb G lam (compIn G (s.erase r) v) v)-
        (a lam*Tail.Tf lam (Tail.rootProb G lam s r)+
          (a lam*w lam)*Tail.ThatPlus lam (Tail.Tf lam (Tail.rootProb G lam s r)))
      linarith
  · simp [selectedSurplus, hrA]

/-- The printed local outside inequality (35), on its actual branch domain. -/
theorem outsideDefect_le_currentSigma (hG : G.IsAcyclic) (A : Finset V)
    {lam : ℝ} (hd : ActivityDomain lam) (hU : UnitNonnegative lam)
    {s : Finset V} (hs : ConnectedIn G s) {r : V} (hr : r ∈ s)
    (hC : Tail.HasChildren G A s r) :
    outsideDefect G A lam s r ≤ if r ∈ A then 0 else currentSigma G A lam s r := by
  by_cases hrA : r ∈ A
  · simp [outsideDefect, hrA]
  · have hlam : 0 < lam := by linarith [hd.1]
    let I := (nbrsIn G s r).filter (· ∈ A)
    let J := (nbrsIn G s r).filter (· ∉ A)
    let p : V → ℝ := fun v => Tail.rootProb G lam (compIn G (s.erase r) v) v
    have hp : ∀ v ∈ nbrsIn G s r, 0 < p v :=
      fun v _ => Tail.rootProb_pos hlam _ v
    have hpq : ∀ v ∈ nbrsIn G s r, p v ≤ q lam :=
      fun v hv => Tail.rootProb_le_actQ hlam.le (self_mem_branch hv)
    have hsum : (∑ i ∈ I, b (p i))+(∑ j ∈ J, b (p j)) =
        Y lam (Tail.rootProb G lam s r) := by
      dsimp only [I, J]
      rw [Finset.sum_filter_add_sum_filter_not]
      exact Tail.lemmaC_exact hG hlam hs hr
    have hpr : Tail.rootProb G lam s r =
        Tail.pC lam ((∑ i ∈ I, b (p i))+(∑ j ∈ J, b (p j))) := by
      rw [hsum]
      exact Tail.eq_pC_of_Tf hlam (Tail.rootProb_pos hlam s r)
        (Tail.rootProb_lt_one hlam.le hr) rfl
    have hne : I.Nonempty ∨ J.Nonempty := by
      obtain ⟨v, hv⟩ := hC.1 hrA
      by_cases hvA : v ∈ A
      · exact Or.inl ⟨v, Finset.mem_filter.mpr ⟨hv, hvA⟩⟩
      · exact Or.inr ⟨v, Finset.mem_filter.mpr ⟨hv, hvA⟩⟩
    have hY : Tail.unitY G A lam s r = ∑ i ∈ I, b (p i) := by
      dsimp only [I]
      rw [Finset.sum_filter]
      rfl
    have hsB : Tail.sB G A lam s r = ∑ i ∈ I, p i := by
      dsimp only [I]
      rw [Finset.sum_filter]
      rfl
    have htau : 0 < currentFactor G A lam s r := by
      rw [currentFactor_eq_toyLocal A hlam.le]
      exact Tail.toyLocal_pos hlam le_rfl zero_le_one hr
    have hgain : currentFactor G A lam s r ≤ Tail.rootProb G lam s r+
        (1-Tail.rootProb G lam s r)*Real.exp (-(∑ i ∈ I, b (p i))) := by
      simp only [currentFactor, if_neg hrA, hY, le_refl]
    have hstep := local_potential_step hd hU I J p
      (fun i hi => hp i (Finset.mem_filter.mp hi).1)
      (fun i hi => hpq i (Finset.mem_filter.mp hi).1)
      (fun j hj => hp j (Finset.mem_filter.mp hj).1)
      (fun j hj => hpq j (Finset.mem_filter.mp hj).1) hne hpr htau hgain
    have hkids : (∑ i ∈ I, a lam*H lam (p i))+(∑ j ∈ J, Psi lam (p j)) =
        ∑ v ∈ nbrsIn G s r, vertexPotential G A lam (compIn G (s.erase r) v) v := by
      rw [← Finset.sum_filter_add_sum_filter_not (nbrsIn G s r) (· ∈ A)]
      apply congrArg₂ (· + ·)
      · apply Finset.sum_congr rfl
        intro v hv
        simp only [vertexPotential, if_pos (Finset.mem_filter.mp hv).2]
        rfl
      · apply Finset.sum_congr rfl
        intro v hv
        simp only [vertexPotential, if_neg (Finset.mem_filter.mp hv).2]
        rfl
    rw [hsum, ← hsB] at hstep
    have hroot : vertexPotential G A lam s r = Psi lam (Tail.rootProb G lam s r) := by
      simp only [vertexPotential, if_neg hrA]
    simp only [outsideDefect, if_neg hrA, hroot]
    change _ ≤ -Real.log (currentFactor G A lam s r)-
      E lam (Y lam (Tail.rootProb G lam s r))*Tail.sB G A lam s r
    linarith [hkids]

/-- The single telescope now has no undischarged graph-local hypotheses. -/
theorem currentSigma_sum_nonnegative (hG : G.IsAcyclic) {A : Finset V}
    (hA : IsIndepFinset G A) {lam : ℝ} (hd : ActivityDomain lam)
    (hU : UnitNonnegative lam) {s : Finset V} (hs : ConnectedIn G s)
    {r : V} (hr : r ∈ s) (hrA : r ∉ A) (hC : Tail.HasChildren G A s r) :
    0 ≤ Tail.treeSum G (currentSigma G A lam) s r := by
  have h := outside_sigma_nonnegative hG A lam (currentSigma G A lam)
    (Tail.HasChildren G A)
    (fun s r _ _ hC w hw => Tail.hasChildren_branch hG hw hC)
    (fun s r hs hr hC => outsideDefect_le_currentSigma hG A hd hU hs hr hC)
    (fun s r hs hr => selectedSurplus_nonnegative hG hA hd hs hr)
    hs hr hrA hC (root_Psi_nonnegative hd hr)
  have heq : ∀ s r, ConnectedIn G s → r ∈ s →
      (if r ∈ A then 0 else currentSigma G A lam s r) = currentSigma G A lam s r := by
    intro s r _ _
    by_cases h : r ∈ A
    · simp only [if_pos h, currentSigma_selected_zero hA lam s h]
    · simp only [if_neg h]
  rwa [rooted_sum_congr hG heq hs hr] at h

/-- Eq33's exact cavity identity, prior to the pointwise minimum replacement. -/
theorem selected_marginal_identity (hG : G.IsAcyclic) (A : Finset V)
    {lam : ℝ} (hlam : 0 ≤ lam) {s : Finset V} (hs : ConnectedIn G s)
    {r : V} (hr : r ∈ s) (hrA : r ∉ A) :
    (∑ v ∈ s.filter (· ∈ A), Tail.marg G lam s v) = Tail.mSum G A lam s r 1 :=
  Tail.lemmaB_component hG hlam hs hr hrA

theorem selected_marginal_le_minimum_sum (hG : G.IsAcyclic) (A : Finset V)
    {lam : ℝ} (hlam : 0 < lam) {s : Finset V} (hs : ConnectedIn G s)
    {r : V} (hr : r ∈ s) (hrA : r ∉ A) :
    (∑ v ∈ s.filter (· ∈ A), Tail.marg G lam s v) ≤ Tail.mSumMax G A lam s r := by
  rw [selected_marginal_identity hG A hlam.le hs hr hrA]
  exact Tail.mSum_le_max hG hlam hs hr
    (Tail.one_div_le_one_of_rootProb hlam.le hr) le_rfl

/-- The product bound and actual single telescope imply the rooted-component bound. -/
theorem rooted_partition_bound (hG : G.IsAcyclic) {A : Finset V}
    (hA : IsIndepFinset G A) {lam : ℝ} (hd : ActivityDomain lam)
    (hU : UnitNonnegative lam) {s : Finset V} (hs : ConnectedIn G s)
    {r : V} (hr : r ∈ s) (hrA : r ∉ A) (hC : Tail.HasChildren G A s r) :
    partitionRatio G A lam s ≤
      Real.exp (-(ellH lam/q lam)*(∑ v ∈ s.filter (· ∈ A), Tail.marg G lam s v)) := by
  have hlam : 0 < lam := by linarith [hd.1]
  have hsum := currentSigma_sum_nonnegative hG hA hd hU hs hr hrA hC
  have heq : ∀ s r, ConnectedIn G s → r ∈ s → currentSigma G A lam s r =
      Tail.sigmaU G A lam 0 (ellH lam) s r :=
    fun s r _ hr => currentSigma_eq_sigmaU A hlam hr
  rw [rooted_sum_congr hG heq hs hr] at hsum
  change 0 ≤ Tail.surplus G A lam 0 (ellH lam) s r at hsum
  rw [Tail.surplus_eq, ← q_eq_actQ lam] at hsum
  have hmean := selected_marginal_le_minimum_sum hG A hlam hs hr hrA
  have hcoef : 0 ≤ ellH lam/q lam :=
    div_nonneg (activity_rate_bounds hd).1.le (q_pos hlam).le
  apply (partitionRatio_le_product hG hA hlam.le hs hr).trans
  rw [Tail.toy_eq_exp hG hlam le_rfl zero_le_one hs hr]
  apply Real.exp_le_exp.mpr
  nlinarith [mul_le_mul_of_nonneg_left hmean hcoef]

end Erdos993Lean.Analytic.V213.ZeroTiltLaplace

-- Audit commands.
#check Erdos993Lean.Analytic.V213.ZeroTiltLaplace.currentFactor_eq_toyLocal
#print axioms Erdos993Lean.Analytic.V213.ZeroTiltLaplace.currentFactor_eq_toyLocal
#check Erdos993Lean.Analytic.V213.ZeroTiltLaplace.currentSigma_eq_sigmaU
#print axioms Erdos993Lean.Analytic.V213.ZeroTiltLaplace.currentSigma_eq_sigmaU
#check Erdos993Lean.Analytic.V213.ZeroTiltLaplace.currentSigma_selected_zero
#print axioms Erdos993Lean.Analytic.V213.ZeroTiltLaplace.currentSigma_selected_zero
#check Erdos993Lean.Analytic.V213.ZeroTiltLaplace.root_Psi_nonnegative
#print axioms Erdos993Lean.Analytic.V213.ZeroTiltLaplace.root_Psi_nonnegative
#check Erdos993Lean.Analytic.V213.ZeroTiltLaplace.selectedSurplus_nonnegative
#print axioms Erdos993Lean.Analytic.V213.ZeroTiltLaplace.selectedSurplus_nonnegative
#check Erdos993Lean.Analytic.V213.ZeroTiltLaplace.outsideDefect_le_currentSigma
#print axioms Erdos993Lean.Analytic.V213.ZeroTiltLaplace.outsideDefect_le_currentSigma
#check Erdos993Lean.Analytic.V213.ZeroTiltLaplace.currentSigma_sum_nonnegative
#print axioms Erdos993Lean.Analytic.V213.ZeroTiltLaplace.currentSigma_sum_nonnegative
#check Erdos993Lean.Analytic.V213.ZeroTiltLaplace.selected_marginal_identity
#print axioms Erdos993Lean.Analytic.V213.ZeroTiltLaplace.selected_marginal_identity
#check Erdos993Lean.Analytic.V213.ZeroTiltLaplace.selected_marginal_le_minimum_sum
#print axioms Erdos993Lean.Analytic.V213.ZeroTiltLaplace.selected_marginal_le_minimum_sum
#check Erdos993Lean.Analytic.V213.ZeroTiltLaplace.rooted_partition_bound
#print axioms Erdos993Lean.Analytic.V213.ZeroTiltLaplace.rooted_partition_bound
