module

public import Erdos993Lean.Analytic.V213.LowMeanSeedAll
public import Erdos993Lean.Analytic.V213.LowMeanEquationSixty

/-!
Concrete equation-60 and seven extra-anchor assertions. Complete core
coverage and all checker premises are discharged by the reviewed families.
-/

@[expose] public section

namespace Erdos993Lean.Analytic.V213

theorem lowMean_seedChoice_checked (i : ℕ) (hi : i < 564) (w : LowMeanSeedBudgetChoice)
    (hw : w ∈ (lowMeanSeedAt i).positions) : lowMeanSeedChoiceCheck (lowMeanCoreFiberAt i) w = true := by
  have hs := lowMean_seedAt_checked i hi
  simp only [lowMeanDirectSeedCheck, Bool.and_eq_true] at hs
  have hb := hs.1
  simp only [lowMeanFiberBudgetCheck, Bool.and_eq_true, decide_eq_true_eq] at hb
  exact List.all_eq_true.mp hb.2 w hw

theorem lowMean_core_position_choice (i : ℕ) (hi : i < 564) (j : ℤ)
    (hj : j ∈ (lowMeanCoreFiberAt i).core) :
    ∃ w ∈ (lowMeanSeedAt i).positions, w.j = j := by
  have hs := lowMean_seedAt_checked i hi
  simp only [lowMeanDirectSeedCheck, Bool.and_eq_true] at hs
  have hb := hs.1
  simp only [lowMeanFiberBudgetCheck, Bool.and_eq_true, decide_eq_true_eq] at hb
  have hm : j ∈ (lowMeanSeedAt i).positions.map LowMeanSeedBudgetChoice.j := by
    rw [hb.1]; exact hj
  exact List.mem_map.mp hm

theorem lowMean_all_core_eq60 (i : ℕ) (hi : i < 564) (w : LowMeanSeedBudgetChoice)
    (hw : w ∈ (lowMeanSeedAt i).positions) (hn : w.mode ≠ 2) :
    let f := lowMeanCoreFiberAt i
    let l := lowMeanFractionReal (lowMeanFiberCertificate f).l
    let h := lowMeanFractionReal (lowMeanFiberCertificate f).h
    (1 / 50000 : ℝ) < max (lowMeanPositionR f w l h)
      (min (lowMeanPositionR f w l ((l + h) / 2)) (lowMeanPositionR f w ((l + h) / 2) h)) :=
  lowMean_seedChoice_eq60 _ w (lowMean_seedChoice_checked i hi w hw) hn

theorem lowMean_specialTargets_kernel : (List.range 564).all (fun i =>
    (lowMeanSeedAt i).positions.all (fun w => decide (w.mode = 2 →
      (lowMeanCoreFiberAt i).certificate = 1 ∧ (lowMeanCoreFiberAt i).zeta = (1, 100000) ∧
      (lowMeanSeedAt i).target.R = (lowMeanCoreFiberAt i).M))) = true := by decide +kernel

theorem lowMean_all_special_targets (i : ℕ) (hi : i < 564) (w : LowMeanSeedBudgetChoice)
    (hw : w ∈ (lowMeanSeedAt i).positions) (hm : w.mode = 2) :
    (lowMeanCoreFiberAt i).certificate = 1 ∧ (lowMeanCoreFiberAt i).zeta = (1, 100000) ∧
      (lowMeanSeedAt i).target.R = (lowMeanCoreFiberAt i).M :=
  (of_decide_eq_true (List.all_eq_true.mp
    (Erdos993Lean.F4Fast.forall_lt_of_range_all lowMean_specialTargets_kernel i hi) w hw)) hm

theorem lowMean_all_special_minima (i : ℕ) (hi : i < 564) (w : LowMeanSeedBudgetChoice)
    (hw : w ∈ (lowMeanSeedAt i).positions) (hm : w.mode = 2) :
    let f := lowMeanCoreFiberAt i
    let c := lowMeanFiberCertificate f
    let tau := lowMeanFractionReal (lowMeanSpecialBudgetTau f.M w.j)
    lowMeanFractionReal (lowMeanSpecialBudgetBound f.M w.j) <
      lowMeanBudgetMinimumAt (lowMeanBudgetInputTerms (lowMeanBudgetAt w.left).input) f.M w.j
        (lowMeanFractionReal c.eta) (lowMeanFractionReal c.xi) (lowMeanFractionReal c.alpha)
        (lowMeanFractionReal c.beta) (lowMeanFractionReal c.gamma) (lowMeanFractionReal c.m0)
        (1 / 100000) (lowMeanFractionReal c.l) (lowMeanFractionReal c.h) tau ∧
      tau ∈ Set.Icc (lowMeanFractionReal c.l) (lowMeanFractionReal c.h) := by
  have hz := (lowMean_all_special_targets i hi w hw hm).2.1
  have hp := lowMean_seedChoice_special_minimum (lowMeanCoreFiberAt i) w
    (lowMean_seedChoice_checked i hi w hw) hm
  have he : lowMeanFractionReal (1, 100000) = (1 / 100000 : ℝ) := by norm_num [lowMeanFractionReal]
  simpa only [hz, he] using hp

noncomputable def lowMeanCorePositionPairs : List (ℕ × ℕ × ℤ) :=
  lowMeanCoreFibers.flatMap fun f => f.core.map fun j => (f.certificate, f.M, j)

theorem lowMean_corePositionPairs_nodup : lowMeanCorePositionPairs.Nodup := by
  have hp := lowMean_core_keys_distinct
  simp only [List.Nodup, List.pairwise_map] at hp
  apply List.nodup_flatMap.mpr
  constructor
  · intro f hf
    have h := List.all_eq_true.mp lowMean_cores_kernel f hf
    simp only [lowMeanFiberCheck, Bool.and_eq_true] at h
    have hm := h.1.1
    simp only [lowMeanFiberMetaCheck, Bool.and_eq_true, decide_eq_true_eq] at hm
    rcases hm.1 with ⟨_, _, _, _, _, _, _, hn⟩
    exact hn.map (fun _ _ h => congrArg (fun x : ℕ × ℕ × ℤ => x.2.2) h)
  · exact hp.imp fun {f g} hfg x hfx hgx => by
      rcases List.mem_map.mp hfx with ⟨j, _, hj⟩
      rcases List.mem_map.mp hgx with ⟨k, _, hk⟩
      exact hfg (congrArg (fun x : ℕ × ℕ × ℤ => (x.1, x.2.1)) (hj.trans hk.symm))

theorem lowMean_corePositionPairs_length : lowMeanCorePositionPairs.length = 1057 := by decide +kernel

theorem lowMean_corePositionPairs_card : lowMeanCorePositionPairs.toFinset.card = 1057 := by
  rw [List.toFinset_card_of_nodup lowMean_corePositionPairs_nodup, lowMean_corePositionPairs_length]

end Erdos993Lean.Analytic.V213

#print axioms Erdos993Lean.Analytic.V213.lowMean_all_core_eq60
#print axioms Erdos993Lean.Analytic.V213.lowMean_all_special_minima
