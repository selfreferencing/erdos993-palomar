module

public import Erdos993Lean.Analytic.V213.LowMeanCoverage

/-! The printed group maxima are attained maxima of the exact paper rows. -/

@[expose] public section

namespace Erdos993Lean.Analytic.V213

noncomputable def lowMeanFiniteMaximum (xs : List ℕ) (f : ℕ → ℝ) : ℝ :=
  xs.foldr (fun i m => max (f i) m) 0

theorem lowMean_finiteMaximum_le {xs : List ℕ} {f : ℕ → ℝ} {d : ℝ}
    (hd : 0 ≤ d) (h : ∀ i ∈ xs, f i ≤ d) : lowMeanFiniteMaximum xs f ≤ d := by
  induction xs with
  | nil => exact hd
  | cons i xs ih =>
    change max (f i) (lowMeanFiniteMaximum xs f) ≤ d
    exact max_le (h i (by simp)) (ih (fun j hj => h j (by simp [hj])))

theorem lowMean_le_finiteMaximum {xs : List ℕ} {f : ℕ → ℝ} {i : ℕ}
    (hi : i ∈ xs) : f i ≤ lowMeanFiniteMaximum xs f := by
  induction xs with
  | nil => simp at hi
  | cons j xs ih =>
    change f i ≤ max (f j) (lowMeanFiniteMaximum xs f)
    rcases List.mem_cons.mp hi with rfl | hi
    · exact le_max_left _ _
    · exact le_trans (ih hi) (le_max_right _ _)

theorem lowMean_finiteMaximum_eq {xs : List ℕ} {f : ℕ → ℝ} {d : ℝ}
    (hd : 0 ≤ d) (h : ∀ i ∈ xs, f i ≤ d) (i : ℕ) (hi : i ∈ xs) (he : f i = d) :
    lowMeanFiniteMaximum xs f = d := by
  apply le_antisymm (lowMean_finiteMaximum_le hd h)
  rw [← he]
  exact lowMean_le_finiteMaximum hi

def lowMeanGroupIndices (k : ℕ) : List ℕ :=
  (List.range ((lowMeanGroupAt k).iotaHi - (lowMeanGroupAt k).iotaLo + 1)).map
    (fun j => (lowMeanGroupAt k).iotaLo + j)
noncomputable def lowMeanGroupDbar (k : ℕ) : ℝ :=
  lowMeanFiniteMaximum (lowMeanGroupIndices k) (fun i => lowMeanFractionReal (lowMeanInputRowAt i).D)
noncomputable def lowMeanGroupThetaBar (k : ℕ) : ℝ :=
  lowMeanFiniteMaximum (lowMeanGroupIndices k) (fun i => lowMeanFractionReal (lowMeanInputRowAt i).theta)
noncomputable def lowMeanGroupVQ (k : ℕ) : ℝ :=
  lowMeanVarianceMaximum (lowMeanFractionReal (lowMeanGroupAt k).l) (lowMeanFractionReal (lowMeanGroupAt k).h)

theorem lowMean_group_indices_mem (k i : ℕ) (hk : k < 11) :
    i ∈ lowMeanGroupIndices k ↔ (lowMeanGroupAt k).iotaLo ≤ i ∧ i ≤ (lowMeanGroupAt k).iotaHi := by
  have hb := (lowMean_group_bounds k hk).1
  constructor
  · intro h
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp h
    have hj' := List.mem_range.mp hj
    omega
  · intro h
    apply List.mem_map.mpr
    refine ⟨i - (lowMeanGroupAt k).iotaLo, List.mem_range.mpr (by omega), ?_⟩
    omega

theorem lowMean_group_Dbar_value (k : ℕ) (hk : k < 11) :
    lowMeanGroupDbar k = lowMeanFractionReal (lowMeanGroupAt k).D := by
  have hb := lowMean_group_bounds k hk
  have hg := (lowMean_group_checked k hk).1
  rcases hg with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hdlo, hdhi, _, _, _, _, hdeq, _⟩
  obtain ⟨_, _, _, _, _, _, _, _, hdpos, _⟩ := lowMean_group_real_facts k hk
  apply lowMean_finiteMaximum_eq hdpos.le ?_ (lowMeanGroupAt k).dWitness
    ((lowMean_group_indices_mem k _ hk).mpr ⟨hdlo, hdhi⟩) (congrArg lowMeanFractionReal hdeq)
  intro i hi
  have hib := (lowMean_group_indices_mem k i hk).mp hi
  have hi55 : i < 55 := lt_of_le_of_lt hib.2 hb.2.1
  have hmember := lowMean_group_input_member k i hk hib
  have h := (lowMean_input_real_caps i hi55).2.1
  simpa only [hmember] using h

theorem lowMean_group_thetaBar_value (k : ℕ) (hk : k < 11) :
    lowMeanGroupThetaBar k = lowMeanFractionReal (lowMeanGroupAt k).theta := by
  have hb := lowMean_group_bounds k hk
  have hg := (lowMean_group_checked k hk).1
  rcases hg with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, htlo, hthi, _, _, _, hteq, _⟩
  obtain ⟨_, _, _, _, _, _, _, _, _, htpos, _⟩ := lowMean_group_real_facts k hk
  apply lowMean_finiteMaximum_eq htpos.le ?_ (lowMeanGroupAt k).thetaWitness
    ((lowMean_group_indices_mem k _ hk).mpr ⟨htlo, hthi⟩) (congrArg lowMeanFractionReal hteq)
  intro i hi
  have hib := (lowMean_group_indices_mem k i hk).mp hi
  have hi55 : i < 55 := lt_of_le_of_lt hib.2 hb.2.1
  have hmember := lowMean_group_input_member k i hk hib
  have h := (lowMean_input_real_caps i hi55).2.2.1
  simpa only [hmember] using h

theorem lowMean_group_vQ_exact (k : ℕ) (hk : k < 11) :
    IsGreatest ((fun q : ℝ => q * (1 - q)) '' Set.Icc
      (lowMeanFractionReal (lowMeanGroupAt k).l) (lowMeanFractionReal (lowMeanGroupAt k).h))
      (lowMeanGroupVQ k) := by
  have hb := lowMean_group_bounds k hk
  have hc := lowMean_group_certificate_fields k (lowMeanGroupAt k).certLo hk ⟨le_rfl, hb.2.2.1⟩
  have h := lowMean_certificate_interval_facts _ hc.1
  dsimp only at h
  rw [hc.2.1, hc.2.2.1] at h
  exact lowMean_varianceMaximum_exact h.2.2.le


noncomputable def lowMeanGroupMeanCap (k : ℕ) : ℝ :=
  lowMeanFiniteMaximum (lowMeanGroupIndices k) (fun i => lowMeanFractionReal (lowMeanInputRowAt i).mu0)

theorem lowMean_group_meanCap_value (k : ℕ) (hk : k < 11) :
    lowMeanGroupMeanCap k = lowMeanFractionReal (lowMeanGroupAt k).muHi := by
  have hb := lowMean_group_bounds k hk
  have hg := (lowMean_group_checked k hk).1
  rcases hg with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hmlo, hmhi, _, _, hmeq, _⟩
  have hc := lowMean_group_certificate_fields k (lowMeanGroupAt k).certHi hk ⟨hb.2.2.1, le_rfl⟩
  have hmpos := (lowMean_certificate_signs _ hc.1).2.2.2.2.2.2.2.2
  rw [hc.2.2.2.2.2.2.1 rfl] at hmpos
  apply lowMean_finiteMaximum_eq hmpos ?_ (lowMeanGroupAt k).meanWitness
    ((lowMean_group_indices_mem k _ hk).mpr ⟨hmlo, hmhi⟩) (congrArg lowMeanFractionReal hmeq)
  intro i hi
  have hib := (lowMean_group_indices_mem k i hk).mp hi
  have hi55 : i < 55 := lt_of_le_of_lt hib.2 hb.2.1
  have hmember := lowMean_group_input_member k i hk hib
  have h := (lowMean_input_real_caps i hi55).2.2.2
  simpa only [hmember] using h

theorem lowMean_finiteMaximum_isGreatest {xs : List ℕ} {f : ℕ → ℝ} {i : ℕ}
    (hi : i ∈ xs) (he : f i = lowMeanFiniteMaximum xs f) :
    IsGreatest (f '' {i | i ∈ xs}) (lowMeanFiniteMaximum xs f) := by
  refine ⟨⟨i, hi, he⟩, ?_⟩
  rintro x ⟨j, hj, rfl⟩
  exact lowMean_le_finiteMaximum hj

theorem lowMean_group_Dbar_exact (k : ℕ) (hk : k < 11) :
    IsGreatest ((fun i => lowMeanFractionReal (lowMeanInputRowAt i).D) ''
      {i | i ∈ lowMeanGroupIndices k}) (lowMeanGroupDbar k) := by
  have h := (lowMean_group_checked k hk).1
  rcases h with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hl, hh, _, _, _, _, he, _⟩
  exact lowMean_finiteMaximum_isGreatest
    ((lowMean_group_indices_mem k _ hk).mpr ⟨hl, hh⟩)
    ((congrArg lowMeanFractionReal he).trans (lowMean_group_Dbar_value k hk).symm)

theorem lowMean_group_thetaBar_exact (k : ℕ) (hk : k < 11) :
    IsGreatest ((fun i => lowMeanFractionReal (lowMeanInputRowAt i).theta) ''
      {i | i ∈ lowMeanGroupIndices k}) (lowMeanGroupThetaBar k) := by
  have h := (lowMean_group_checked k hk).1
  rcases h with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hl, hh, _, _, _, he, _⟩
  exact lowMean_finiteMaximum_isGreatest
    ((lowMean_group_indices_mem k _ hk).mpr ⟨hl, hh⟩)
    ((congrArg lowMeanFractionReal he).trans (lowMean_group_thetaBar_value k hk).symm)

theorem lowMean_group_meanCap_exact (k : ℕ) (hk : k < 11) :
    IsGreatest ((fun i => lowMeanFractionReal (lowMeanInputRowAt i).mu0) ''
      {i | i ∈ lowMeanGroupIndices k}) (lowMeanGroupMeanCap k) := by
  have h := (lowMean_group_checked k hk).1
  rcases h with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hl, hh, _, _, he, _⟩
  exact lowMean_finiteMaximum_isGreatest
    ((lowMean_group_indices_mem k _ hk).mpr ⟨hl, hh⟩)
    ((congrArg lowMeanFractionReal he).trans (lowMean_group_meanCap_value k hk).symm)

end Erdos993Lean.Analytic.V213
