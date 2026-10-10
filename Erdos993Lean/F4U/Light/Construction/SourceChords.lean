module

public import Erdos993Lean.F4U.Light.Construction.SourceCharts
public import Mathlib.Analysis.Convex.Function

@[expose] public section


namespace F4Unified.LightConstruction
noncomputable section

theorem source_f_chart (lam t : ℝ) (hq : q lam ≠ 0) :
    f lam t = max (sourceSlopeA lam * t) (sourceSlopeB lam * t + sourceIntercept lam) := by
  simp only [f, sourceSlopeB, sourceSlopeA, sourceIntercept]
  congr 1
  field_simp [hq] <;> ring

theorem source_slopes_positive {r : Row} {lam : ℝ} (hlam : InRow r lam) :
    0 < sourceSlopeA lam ∧ 0 < sourceSlopeB lam := by
  have hq := (inRow_q_bounds hlam).1
  constructor
  · unfold sourceSlopeA
    positivity
  · unfold sourceSlopeB sourceSlopeA
    positivity

theorem source_affine_mix (c d x y a b : ℝ) (hab : a + b = 1) :
    c * (a * x + b * y) + d = a * (c * x + d) + b * (c * y + d) := by
  nlinarith [congrArg (fun z : ℝ => z * d) hab]

theorem source_affine_convex (c d : ℝ) :
    ConvexOn ℝ Set.univ (fun x : ℝ => c * x + d) := by
  constructor
  · exact convex_univ
  · intro x hx y hy a b ha hb hab
    simp only [smul_eq_mul]
    exact (source_affine_mix c d x y a b hab).le

theorem source_affine_concave (c d : ℝ) :
    ConcaveOn ℝ Set.univ (fun x : ℝ => c * x + d) := by
  constructor
  · exact convex_univ
  · intro x hx y hy a b ha hb hab
    simp only [smul_eq_mul]
    exact (source_affine_mix c d x y a b hab).symm.le

/-- Four actual affine source-neighbor pieces, with the parent frozen. -/
noncomputable def sourceNeighbor (lam H rho : ℝ) : ℝ :=
  f lam (max (1 - rho) ((1 - pH lam H * rho) * H))

theorem sourceNeighbor_convex {r : Row} {lam : ℝ} (hlam : InRow r lam) (H : ℝ) :
    ConvexOn ℝ Set.univ (sourceNeighbor lam H) := by
  have hs := source_slopes_positive hlam
  have hq := (inRow_q_bounds hlam).1.ne'
  let A := sourceSlopeA lam
  let B := sourceSlopeB lam
  let C := sourceIntercept lam
  let P := pH lam H
  have he : sourceNeighbor lam H = fun rho : ℝ =>
      max (max ((-A) * rho + A) ((-A * P * H) * rho + A * H))
        (max ((-B) * rho + (B + C)) ((-B * P * H) * rho + (B * H + C))) := by
    ext rho
    unfold sourceNeighbor
    rw [source_f_chart lam _ hq, mul_max_of_nonneg _ _ hs.1.le,
      mul_max_of_nonneg _ _ hs.2.le, ← max_add_add_right]
    dsimp [A, B, C, P]
    congr 2 <;> ring
  rw [he]
  exact ((source_affine_convex (-A) A).sup (source_affine_convex (-A * P * H) (A * H))).sup
    ((source_affine_convex (-B) (B + C)).sup (source_affine_convex (-B * P * H) (B * H + C)))


theorem source_slope_gap (lam t : ℝ) (hq : q lam ≠ 0) :
    sourceSlopeA lam * t - (sourceSlopeB lam * t + sourceIntercept lam) =
      (1-q lam) * (q lam-(1+q lam)*t) / (2*(q lam)^2) := by
  simp only [sourceSlopeB, sourceSlopeA, sourceIntercept]
  field_simp [hq] <;> ring

theorem source_f_first {r : Row} {lam t : ℝ} (hlam : InRow r lam)
    (ht : t ≤ q lam/(1+q lam)) : f lam t = sourceSlopeA lam*t := by
  have hq := inRow_q_bounds hlam
  have hp : 0 < 1+q lam := by linarith
  have ht' : (1+q lam)*t ≤ q lam := by
    have := (le_div_iff₀ hp).mp ht
    nlinarith
  have hgap : 0 ≤ sourceSlopeA lam*t-(sourceSlopeB lam*t+sourceIntercept lam) := by
    rw [source_slope_gap lam t hq.1.ne']
    have h1 : 0 ≤ 1-q lam := by linarith
    have h2 : 0 ≤ q lam-(1+q lam)*t := by linarith
    positivity
  rw [source_f_chart lam t hq.1.ne', max_eq_left (by linarith)]

theorem source_f_second {r : Row} {lam t : ℝ} (hlam : InRow r lam)
    (ht : q lam/(1+q lam) ≤ t) :
    f lam t = sourceSlopeB lam*t+sourceIntercept lam := by
  have hq := inRow_q_bounds hlam
  have hp : 0 < 1+q lam := by linarith
  have ht' : q lam ≤ (1+q lam)*t := by
    have := (div_le_iff₀ hp).mp ht
    nlinarith
  have hgap : sourceSlopeA lam*t-(sourceSlopeB lam*t+sourceIntercept lam) ≤ 0 := by
    rw [source_slope_gap lam t hq.1.ne']
    have h1 : 0 ≤ 1-q lam := by linarith
    have h2 : q lam-(1+q lam)*t ≤ 0 := by linarith
    exact div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos h1 h2) (by positivity)
  rw [source_f_chart lam t hq.1.ne', max_eq_right (by linarith)]

theorem pH_mul_switch {r : Row} {lam H : ℝ} (hlam : InRow r lam)
    (hH0 : 0 ≤ H) (hHq : H ≤ q lam) :
    pH lam H*vacancySwitch lam H = q lam/(1+q lam) := by
  have hd := light_rational_denominators hlam hH0 hHq
  rcases hd with ⟨_,_,_,_,hqplus,_,_,_,_,_,_,hp,_,_⟩
  unfold vacancySwitch
  field_simp [hqplus.ne', hp.ne']


theorem source_endpoint_geometry {r : Row} {lam H : ℝ} (hlam : InRow r lam)
    (hH0 : 0 ≤ H) (hHq : H ≤ q lam) :
    pH lam H*vacancyLo lam H ≤ q lam/(1+q lam) ∧
    q lam/(1+q lam) ≤ 1-vacancyLo lam H ∧
    (1-pH lam H*vacancyLo lam H)*H ≤ 1-vacancyLo lam H ∧
    q lam/(1+q lam) ≤ pH lam H ∧
    (1-pH lam H)*H ≤ q lam/(1+q lam) ∧
    0 ≤ (1-pH lam H)*H ∧
    1-vacancySwitch lam H ≤ q lam/(1+q lam) ∧
    (1-pH lam H*vacancySwitch lam H)*H ≤ q lam/(1+q lam) := by
  have hd := light_rational_denominators hlam hH0 hHq
  rcases hd with ⟨_,_,hq0,_,hqplus,_,hH1,_,hk,hd,_,_,hp1,_⟩
  have hqH : 0 ≤ q lam-H := by linarith
  have hq1 : 0 ≤ 1-q lam := by linarith [(inRow_q_bounds hlam).2]
  have he1 : q lam/(1+q lam)-pH lam H*vacancyLo lam H =
      q lam*H/((1+q lam)*(1+q lam-q lam*H)) := by
    rw [pH_q_chart hlam hH0 hHq, vacancyLo_q_chart hlam hH0 hHq]
    field_simp [hqplus.ne', hk.ne', hd.ne'] <;> ring
  have he2 : 1-vacancyLo lam H-q lam/(1+q lam) =
      (q lam)^2*H/((1+q lam)*(1+q lam-q lam*H)) := by
    rw [vacancyLo_q_chart hlam hH0 hHq]
    field_simp [hqplus.ne', hd.ne'] <;> ring
  have he3 : 1-vacancyLo lam H-(1-pH lam H*vacancyLo lam H)*H =
      (q lam-H)/(1+q lam-q lam*H) := by
    rw [pH_q_chart hlam hH0 hHq, vacancyLo_q_chart hlam hH0 hHq]
    field_simp [hk.ne', hd.ne'] <;> ring
  have he4 : pH lam H-q lam/(1+q lam) =
      q lam*(q lam-H)/((1+q lam)*(1-q lam*H)) := by
    rw [pH_q_chart hlam hH0 hHq]
    field_simp [hqplus.ne', hk.ne'] <;> ring
  have he5 : q lam/(1+q lam)-(1-pH lam H)*H =
      (q lam-H)/((1+q lam)*(1-q lam*H)) := by
    rw [pH_q_chart hlam hH0 hHq]
    field_simp [hqplus.ne', hk.ne'] <;> ring
  have he7 : q lam/(1+q lam)-(1-vacancySwitch lam H) =
      H*(1-q lam)/((1+q lam)*(1-H)) := by
    rw [vacancySwitch_q_chart hlam hH0 hHq]
    field_simp [hqplus.ne', hH1.ne'] <;> ring
  have he8 : q lam/(1+q lam)-(1-pH lam H*vacancySwitch lam H)*H =
      (q lam-H)/(1+q lam) := by
    rw [pH_mul_switch hlam hH0 hHq]
    field_simp [hqplus.ne'] <;> ring
  have h1 : 0 ≤ q lam*H/((1+q lam)*(1+q lam-q lam*H)) := by positivity
  have h2 : 0 ≤ (q lam)^2*H/((1+q lam)*(1+q lam-q lam*H)) := by positivity
  have h3 : 0 ≤ (q lam-H)/(1+q lam-q lam*H) := by positivity
  have h4 : 0 ≤ q lam*(q lam-H)/((1+q lam)*(1-q lam*H)) := by positivity
  have h5 : 0 ≤ (q lam-H)/((1+q lam)*(1-q lam*H)) := by positivity
  have h7 : 0 ≤ H*(1-q lam)/((1+q lam)*(1-H)) := by positivity
  have h8 : 0 ≤ (q lam-H)/(1+q lam) := by positivity
  refine ⟨by linarith, by linarith, by linarith, by linarith, by linarith,
    mul_nonneg hp1.le hH0, by linarith, by linarith⟩

theorem sourceH_at_lo {r : Row} {lam H : ℝ} (hlam : InRow r lam)
    (hH0 : 0 ≤ H) (hHq : H ≤ q lam) :
    sourceH lam H (vacancyLo lam H) = sourceAtLo lam H := by
  have hg := source_endpoint_geometry hlam hH0 hHq
  have hd := light_rational_denominators hlam hH0 hHq
  rcases hd with ⟨_,hl1,hq,_,hqp,_,hH1,_,hk,hd,_,_,_,_⟩
  unfold sourceH
  rw [max_eq_left hg.2.2.1, source_f_first hlam hg.1, source_f_second hlam hg.2.1]
  simp only [sourceAtLo, sourceSlopeB, sourceSlopeA, sourceIntercept]
  rw [pH_q_chart hlam hH0 hHq, vacancyLo_q_chart hlam hH0 hHq]
  field_simp [hq.ne', hqp.ne', hk.ne', hd.ne'] <;> ring

theorem sourceH_at_hi {r : Row} {lam H : ℝ} (hlam : InRow r lam)
    (hH0 : 0 ≤ H) (hHq : H ≤ q lam) :
    sourceH lam H 1 = sourceAtHi lam H := by
  have hg := source_endpoint_geometry hlam hH0 hHq
  have hd := light_rational_denominators hlam hH0 hHq
  rcases hd with ⟨_,_,hq,_,hqp,_,_,_,hk,_,_,_,_,_⟩
  unfold sourceH
  simp only [mul_one, sub_self, max_eq_right hg.2.2.2.2.2.1]
  rw [source_f_second hlam hg.2.2.2.1, source_f_first hlam hg.2.2.2.2.1]
  simp only [sourceAtHi, sourceSlopeB, sourceSlopeA, sourceIntercept]
  rw [pH_q_chart hlam hH0 hHq]
  field_simp [hq.ne', hqp.ne', hk.ne'] <;> ring


theorem sourceH_at_switch_lower {r : Row} {lam H : ℝ} (hlam : InRow r lam)
    (hHlo : q lam/2 ≤ H) (hHq : H ≤ q lam) :
    sourceAtSwitchLower lam H ≤ sourceH lam H (vacancySwitch lam H) := by
  have hq := inRow_q_bounds hlam
  have hH0 : 0 ≤ H := by linarith
  have hg := source_endpoint_geometry hlam hH0 hHq
  have hd := light_rational_denominators hlam hH0 hHq
  rcases hd with ⟨_,_,hq0,_,hqp,hq2,hH1,_,_,_,_,_,_,_⟩
  have hfac : 0 ≤ -H^2+2*H*q lam-3*q lam+2 := by
    have hp : 0 ≤ (H-q lam/2)*(3*q lam/2-H) :=
      mul_nonneg (by linarith) (by linarith)
    have ht : 0 ≤ (7/10-q lam)*(3-3/4*(q lam+7/10)) :=
      mul_nonneg (by linarith) (by linarith)
    nlinarith
  let X := 1-vacancySwitch lam H
  let Z := (1-pH lam H*vacancySwitch lam H)*H
  have hx : sourceAtSwitchLower lam H ≤
      (1+sourceSlopeA lam*(q lam/(1+q lam))-sourceSlopeA lam*X)/2 := by
    have he : (1+sourceSlopeA lam*(q lam/(1+q lam))-sourceSlopeA lam*X)/2 -
        sourceAtSwitchLower lam H =
        (2*H-q lam)*(-H^2+2*H*q lam-3*q lam+2)/(4*q lam*(1-H)*(2-q lam)) := by
      dsimp [X, sourceAtSwitchLower, sourceSlopeA]
      rw [vacancySwitch_q_chart hlam hH0 hHq]
      field_simp [hq0.ne', hqp.ne', hH1.ne', hq2.ne'] <;> ring
    have hepos : 0 ≤ (2*H-q lam)*(-H^2+2*H*q lam-3*q lam+2)/
        (4*q lam*(1-H)*(2-q lam)) := by
      have h2H : 0 ≤ 2*H-q lam := by linarith
      positivity
    linarith
  have hz : sourceAtSwitchLower lam H ≤
      (1+sourceSlopeA lam*(q lam/(1+q lam))-sourceSlopeA lam*Z)/2 := by
    have he : (1+sourceSlopeA lam*(q lam/(1+q lam))-sourceSlopeA lam*Z)/2 -
        sourceAtSwitchLower lam H = (q lam-H)^2/(2*q lam*(2-q lam)) := by
      dsimp [Z]
      rw [pH_mul_switch hlam hH0 hHq]
      simp only [sourceAtSwitchLower, sourceSlopeA]
      field_simp [hq0.ne', hqp.ne', hq2.ne'] <;> ring
    have hepos : 0 ≤ (q lam-H)^2/(2*q lam*(2-q lam)) := by positivity
    linarith
  unfold sourceH
  rw [source_f_first hlam (max_le hg.2.2.2.2.2.2.1 hg.2.2.2.2.2.2.2)]
  rw [show f lam (pH lam H*vacancySwitch lam H) = sourceSlopeA lam*(q lam/(1+q lam)) by
    rw [pH_mul_switch hlam hH0 hHq, source_f_first hlam le_rfl]]
  rcases le_total X Z with h | h
  · rw [max_eq_right h]
    exact hz
  · rw [max_eq_left h]
    exact hx

theorem second_chord_at_switch {r : Row} {lam H : ℝ} (hlam : InRow r lam)
    (hH0 : 0 ≤ H) (hHq : H ≤ q lam) :
    sourceChord .second lam H (vacancySwitch lam H) = sourceAtSwitchLower lam H := by
  have hd := light_rational_denominators hlam hH0 hHq
  rcases hd with ⟨_,_,hq0,_,hqp,hq2,hH1,_,hk,_,_,_,_,_⟩
  simp only [sourceChord, chordIntercept, chordSlope, sourceAtHi,
    sourceSlopeB, sourceSlopeA, sourceIntercept, sourceAtSwitchLower]
  rw [pH_q_chart hlam hH0 hHq, vacancySwitch_q_chart hlam hH0 hHq]
  have hkh : 1-H*q lam ≠ 0 := by nlinarith
  field_simp [hq0.ne', hqp.ne', hq2.ne', hH1.ne', hk.ne', hkh] <;> ring

def sourceParentPiece (phase : SourcePhase) (lam H rho : ℝ) : ℝ :=
  match phase with
  | .first => sourceSlopeA lam*pH lam H*rho
  | .second => sourceSlopeB lam*pH lam H*rho+sourceIntercept lam

theorem source_parent_piece {r : Row} {lam H rho : ℝ} (hlam : InRow r lam)
    (hH0 : 0 ≤ H) (hHq : H ≤ q lam) (phase : SourcePhase)
    (hphase : PhaseDomain phase lam H rho) :
    f lam (pH lam H*rho) = sourceParentPiece phase lam H rho := by
  have hd := light_rational_denominators hlam hH0 hHq
  rcases hd with ⟨_,_,_,_,_,_,_,_,_,_,_,hp,_,_⟩
  have hs := pH_mul_switch hlam hH0 hHq
  cases phase
  · simp only [PhaseDomain] at hphase
    have ht : pH lam H*rho ≤ q lam/(1+q lam) := by
      rw [← hs]
      exact mul_le_mul_of_nonneg_left hphase.2 hp.le
    rw [source_f_first hlam ht]
    simp only [sourceParentPiece, mul_assoc]
  · simp only [PhaseDomain] at hphase
    have ht : q lam/(1+q lam) ≤ pH lam H*rho := by
      rw [← hs]
      exact mul_le_mul_of_nonneg_left hphase.1 hp.le
    rw [source_f_second hlam ht]
    simp only [sourceParentPiece, mul_assoc]

theorem source_parent_piece_affine (phase : SourcePhase) (lam H x y a b : ℝ)
    (hab : a+b=1) :
    sourceParentPiece phase lam H (a*x+b*y) =
      a*sourceParentPiece phase lam H x+b*sourceParentPiece phase lam H y := by
  cases phase <;> simp only [sourceParentPiece]
  · ring
  · exact source_affine_mix (sourceSlopeB lam*pH lam H) (sourceIntercept lam) x y a b hab

theorem phaseDomain_eq_Icc (phase : SourcePhase) (lam H rho : ℝ) :
    PhaseDomain phase lam H rho ↔ rho ∈ Set.Icc (phaseLo phase lam H) (phaseHi phase lam H) := by
  cases phase <;> rfl

theorem sourceH_phase_concave {r : Row} {lam H : ℝ} (hlam : InRow r lam)
    (hH0 : 0 ≤ H) (hHq : H ≤ q lam) (phase : SourcePhase) :
    ConcaveOn ℝ (Set.Icc (phaseLo phase lam H) (phaseHi phase lam H)) (sourceH lam H) := by
  refine ⟨convex_Icc _ _, ?_⟩
  intro x hx y hy a b ha hb hab
  have hm := convex_Icc (phaseLo phase lam H) (phaseHi phase lam H) hx hy ha hb hab
  have hn := (sourceNeighbor_convex hlam H).2 (Set.mem_univ x) (Set.mem_univ y) ha hb hab
  simp only [smul_eq_mul] at hn hm ⊢
  have hfx := source_parent_piece hlam hH0 hHq phase ((phaseDomain_eq_Icc phase lam H x).mpr hx)
  have hfy := source_parent_piece hlam hH0 hHq phase ((phaseDomain_eq_Icc phase lam H y).mpr hy)
  have hfm := source_parent_piece hlam hH0 hHq phase ((phaseDomain_eq_Icc phase lam H (a*x+b*y)).mpr hm)
  unfold sourceH
  rw [hfx, hfy, hfm, source_parent_piece_affine phase lam H x y a b hab]
  unfold sourceNeighbor at hn
  nlinarith


theorem affine_le_concave_on_Icc {g : ℝ → ℝ} {lo hi rho c d : ℝ}
    (hg : ConcaveOn ℝ (Set.Icc lo hi) g) (hlo : c*lo+d ≤ g lo)
    (hhi : c*hi+d ≤ g hi) (hrho : rho ∈ Set.Icc lo hi) : c*rho+d ≤ g rho := by
  have hlh : lo ≤ hi := hrho.1.trans hrho.2
  rcases eq_or_lt_of_le hlh with heq | hlt
  · have he : rho = lo := by linarith [hrho.1, hrho.2]
    simpa only [he] using hlo
  · let w := (rho-lo)/(hi-lo)
    have hd : 0 < hi-lo := by linarith
    have hw0 : 0 ≤ w := div_nonneg (by linarith [hrho.1]) hd.le
    have hw1 : w ≤ 1 := (div_le_one hd).mpr (by linarith [hrho.2])
    have hmix : (1-w)*lo+w*hi = rho := by
      dsimp [w]
      field_simp [hd.ne'] <;> ring
    have hn := hg.2 (show lo ∈ Set.Icc lo hi from ⟨le_rfl, hlh⟩)
      (show hi ∈ Set.Icc lo hi from ⟨hlh, le_rfl⟩)
      (show 0 ≤ 1-w by linarith) hw0 (by ring : (1-w)+w=1)
    simp only [smul_eq_mul, hmix] at hn
    have hm := add_le_add (mul_le_mul_of_nonneg_left hlo (by linarith : 0 ≤ 1-w))
      (mul_le_mul_of_nonneg_left hhi hw0)
    have ha := source_affine_mix c d lo hi (1-w) w (by ring)
    rw [hmix] at ha
    linarith

/-- The manuscript's two literal source chords lie below the frozen-parent source.
The interval argument also covers the collapsed second phase H=q. -/
theorem sourceChord_le_sourceH {r : Row} {lam H rho : ℝ} (hlam : InRow r lam)
    (hHlo : q lam/2 ≤ H) (hHq : H ≤ q lam) (phase : SourcePhase)
    (hphase : PhaseDomain phase lam H rho) :
    sourceChord phase lam H rho ≤ sourceH lam H rho := by
  have hq := inRow_q_bounds hlam
  have hH0 : 0 ≤ H := by linarith
  have hHpos : 0 < H := by linarith
  apply affine_le_concave_on_Icc (g := sourceH lam H)
    (lo := phaseLo phase lam H) (hi := phaseHi phase lam H)
    (c := chordSlope phase lam H) (d := chordIntercept phase lam H)
    (sourceH_phase_concave hlam hH0 hHq phase)
  · change sourceChord phase lam H (phaseLo phase lam H) ≤ _
    cases phase
    · simp only [phaseLo]
      rw [first_chord_at_lo, sourceH_at_lo hlam hH0 hHq]
    · simp only [phaseLo]
      rw [second_chord_at_switch hlam hH0 hHq]
      exact sourceH_at_switch_lower hlam hHlo hHq
  · change sourceChord phase lam H (phaseHi phase lam H) ≤ _
    cases phase
    · simp only [phaseHi]
      rw [first_chord_at_switch hlam hHpos hHq]
      exact sourceH_at_switch_lower hlam hHlo hHq
    · simp only [phaseHi]
      rw [second_chord_at_hi, sourceH_at_hi hlam hH0 hHq]
  · exact (phaseDomain_eq_Icc phase lam H rho).mp hphase

end
end F4Unified.LightConstruction
