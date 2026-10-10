module

public import Erdos993Lean.Analytic.V213.FiberCornerCheck

/-!
Real consumers of the complete checked corner/logarithm trees. All13
actual logarithm bounds, six actual coupled-rate lower bounds, ten
positive corners, and eight strict weighted-window exponent tests are
obtained from the whole-number checks.
-/

@[expose] public section
namespace Erdos993Lean.Analytic.V213

theorem fiber_corner_log_upper (id : FiberCornerLogIdentity) :
    Real.log (lowMeanFractionReal (fiberCornerLogById id).y) ≤
      lowMeanFractionReal (fiberCornerLogById id).L := by
  rcases fiber_corner_log_facts id true with ⟨hpr,hy,hL,hg,hlo,hhi,hgp,hgap⟩
  have h := fiber_corner_log_checked id true
  simp only [fiberCornerLogCheck,Bool.and_eq_true] at h
  have hs := lowMean_integerShape_sound h.1
  rw [fiber_corner_log_shape_real] at hs
  have hb := (lowMean_fraction_le_iff hg hs.1).mp hgap
  have hpos := (lowMean_fraction_lt_iff (by decide +kernel : lowMeanFractionValid (0,1)) hg).mp hgp
  have hzero : lowMeanFractionReal (0,1) = 0 := by norm_num [lowMeanFractionReal]
  rw [hzero] at hpos
  have hd := (lowMean_fraction_le_iff (by norm_num [lowMeanFractionValid]) hy).mp hlo
  simp only [lowMeanFractionReal,Int.cast_pow,Int.cast_ofNat,Nat.cast_one,div_one] at hd
  change (2 : ℝ)^(fiberCornerLogById id).n ≤ lowMeanFractionReal (fiberCornerLogById id).y at hd
  have hl := fiber_dyadic_log_bound (fiberCornerLogById id).n hd
  rw [← hs.2] at hb
  dsimp [fiberCornerLogValue] at hb
  linarith only [hl,hb,hpos]

theorem fiber_corner_rate_bound (id : FiberCornerRateIdentity) :
    let r := fiberCornerRateById id
    lowMeanFractionReal r.base + lowMeanFractionReal r.slope * lowMeanFractionReal (fiberInputHiFraction r.input) <
      lowMeanFractionReal (fiberInputRouteById r.input).ell0 := by
  rcases fiber_corner_rate_facts id with ⟨hpr,hi,he,hhi,hb,hs,heV,hhV,hpos,hval⟩
  have h := fiber_corner_rate_checked id
  simp only [fiberCornerRateCheck,Bool.and_eq_true] at h
  have hv := fiber_corner_equality_real h.1 hval
  rw [fiber_corner_rate_shape_real] at hv
  have hp := (lowMean_fraction_lt_iff (by decide +kernel : lowMeanFractionValid (0,1)) hval.1).mp hpos
  have hzero : lowMeanFractionReal (0,1) = 0 := by norm_num [lowMeanFractionReal]
  rw [hzero] at hp
  dsimp [fiberCornerRateValue] at hv
  linarith only [hv,hp]

theorem fiber_rate_corner_positive (id : FiberRateCornerIdentity) :
    let r := fiberRateCornerById id
    0 < lowMeanFractionReal r.ell - lowMeanFractionReal r.L * lowMeanFractionReal r.ts := by
  rcases fiber_rate_corner_facts id with ⟨hpr,he,hL,ht,hpos,hval⟩
  have h := fiber_rate_corner_checked id
  simp only [fiberRateCornerCheck,Bool.and_eq_true] at h
  have hv := fiber_corner_equality_real h.1 hval
  rw [fiber_rate_corner_shape_real] at hv
  have hp := (lowMean_fraction_lt_iff (by decide +kernel : lowMeanFractionValid (0,1)) hval.1).mp hpos
  have hzero : lowMeanFractionReal (0,1) = 0 := by norm_num [lowMeanFractionReal]
  rw [hzero] at hp
  change 0 < fiberRateCornerValue id
  rw [hv]
  exact hp

theorem fiber_window_weight_value (id : FiberWindowWeightIdentity) (gap : Bool) :
    fiberWindowWeightValue id gap = lowMeanFractionReal
      (if gap then (fiberWindowWeightById id).gap else (fiberWindowWeightById id).upper) := by
  rcases fiber_window_weight_facts id gap with
    ⟨hpr,hi,hc,hcp,hLW,hh,hm,he,hL,hZ,hy,heps,heqy,hlo,hhi,hZp,hep,hee,hval,hcmp⟩
  have h := fiber_window_weight_checked id gap
  simp only [fiberWindowWeightCheck,Bool.and_eq_true] at h
  have hv := fiber_corner_equality_real h.1 hval
  rw [fiber_window_weight_shape_real] at hv
  exact hv

theorem fiber_window_weight_log_upper (id : FiberWindowWeightIdentity) :
    let r := fiberWindowWeightById id
    let w := fiberWindowById r.window
    let c := fiberWindowCornerById r.corner
    Real.log (lowMeanFractionReal w.L_W / lowMeanFractionReal c.Z_W) ≤ fiberWindowWeightValue id false := by
  rcases fiber_window_weight_facts id false with
    ⟨hpr,hi,hc,hcp,hLW,hh,hm,he,hL,hZ,hy,heps,heqy,hlo,hhi,hZp,hep,hee,hval,hcmp⟩
  have hZpos := (lowMean_fraction_lt_iff (by decide +kernel : lowMeanFractionValid (0,1)) hZ).mp hZp
  have hzero : lowMeanFractionReal (0,1) = 0 := by norm_num [lowMeanFractionReal]
  rw [hzero] at hZpos
  have hmV : lowMeanFractionValid (lowMeanFractionMul (fiberWindowWeightById id).y
      (fiberWindowCornerById (fiberWindowWeightById id).corner).Z_W) := Nat.mul_pos hy hZ
  have heq := (lowMean_fraction_eq_iff hmV hLW).mp heqy
  rw [lowMean_fraction_mul] at heq
  have hyEq : lowMeanFractionReal (fiberWindowWeightById id).y =
      lowMeanFractionReal (fiberWindowById (fiberWindowWeightById id).window).L_W /
        lowMeanFractionReal (fiberWindowCornerById (fiberWindowWeightById id).corner).Z_W :=
    (eq_div_iff hZpos.ne').mpr heq
  have hd := (lowMean_fraction_le_iff (by norm_num [lowMeanFractionValid]) hy).mp hlo
  simp only [lowMeanFractionReal,Int.cast_pow,Int.cast_ofNat,Nat.cast_one,div_one] at hd
  change (2 : ℝ)^(fiberWindowWeightById id).n ≤ lowMeanFractionReal (fiberWindowWeightById id).y at hd
  rw [hyEq] at hd
  exact fiber_dyadic_log_bound _ hd

theorem fiber_window_weight_strict_gap (id : FiberWindowWeightIdentity) :
    let r := fiberWindowWeightById id
    let w := fiberWindowById r.window
    let c := fiberWindowCornerById r.corner
    Real.log (lowMeanFractionReal w.L_W / lowMeanFractionReal c.Z_W) <
      lowMeanFractionReal c.mu_c *
        (lowMeanFractionReal c.ell_c - lowMeanFractionReal c.L_c * lowMeanFractionReal w.h) := by
  rcases fiber_window_weight_facts id true with
    ⟨hpr,hi,hc,hcp,hLW,hh,hm,he,hL,hZ,hy,heps,heqy,hlo,hhi,hZp,hep,hee,hval,hcmp⟩
  have hgapV : lowMeanFractionValid (fiberWindowWeightById id).gap := hval.1
  have hg := (lowMean_fraction_le_iff heps hgapV).mp (hcmp rfl)
  have hp := (lowMean_fraction_lt_iff (by decide +kernel : lowMeanFractionValid (0,1)) heps).mp hep
  have hzero : lowMeanFractionReal (0,1) = 0 := by norm_num [lowMeanFractionReal]
  rw [hzero] at hp
  have hv := fiber_window_weight_value id true
  dsimp [fiberWindowWeightValue] at hv
  have hl := fiber_window_weight_log_upper id
  dsimp [fiberWindowWeightValue] at hl
  linarith only [hv,hl,hg,hp]

end Erdos993Lean.Analytic.V213
