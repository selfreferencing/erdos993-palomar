module

public import Erdos993Lean.F4U.Light.Soundness.Geometry
public import Erdos993Lean.F4U.Light.Soundness.Quadratic
public import Erdos993Lean.F4U.Light.Soundness.BernsteinBridge
public import Erdos993Lean.F4U.Light.Soundness.Parent

@[expose] public section


namespace F4U.Light

theorem positive_of_centered {F : Fn} (hg : GeometryFacts F) (B : List Int)
    {x : ℝ} (hx : ActivityInterval F x)
    (hpos : ∀ u : ℝ, |u| ≤ 1 →
      0 < eval (shiftScale (Int.ofNat F.c) (Int.ofNat F.rad) (Int.ofNat F.D) B) u) :
    0 < eval B x := by
  let u := ((F.D : ℝ) * x - F.c) / F.rad
  have hc := centered_coordinate hg hx
  have h := hpos u hc.1
  have hD : ((Int.ofNat F.D : Int) : ℝ) ≠ 0 := by
    simpa only [Int.ofNat_eq_natCast, Int.cast_natCast] using ne_of_gt hg.D_pos
  have he := eval_shiftScale (Int.ofNat F.c) (Int.ofNat F.rad) (Int.ofNat F.D) hD B u
  simp only [Int.ofNat_eq_natCast, Int.cast_natCast] at he
  rw [hc.2] at he
  simp only [Int.ofNat_eq_natCast] at h
  rw [he] at h
  exact (mul_pos_iff_of_pos_left (pow_pos hg.D_pos _)).mp h

theorem positive_of_interval_expansion {F : Fn} (hg : GeometryFacts F) (B : List Int)
    {x : ℝ} (hx : ActivityInterval F x)
    (hpos : ∀ u : ℝ, 0 ≤ u ∧ u ≤ 1 →
      0 < eval (shiftScale (Int.ofNat F.c - Int.ofNat F.rad)
        (2 * Int.ofNat F.rad) (Int.ofNat F.D) B) u) : 0 < eval B x := by
  let u := ((F.D : ℝ) * x - ((F.c : ℝ) - F.rad)) / (2 * F.rad)
  have hc := interval_coordinate hg hx
  have h := hpos u hc.1
  have hD : ((Int.ofNat F.D : Int) : ℝ) ≠ 0 := by
    simpa only [Int.ofNat_eq_natCast, Int.cast_natCast] using ne_of_gt hg.D_pos
  have he := eval_shiftScale (Int.ofNat F.c - Int.ofNat F.rad)
    (2 * Int.ofNat F.rad) (Int.ofNat F.D) hD B u
  simp only [Int.ofNat_eq_natCast, Int.cast_natCast, Int.cast_sub, Int.cast_mul,
    Int.cast_ofNat] at he
  rw [hc.2] at he
  simp only [Int.ofNat_eq_natCast] at h
  rw [he] at h
  exact (mul_pos_iff_of_pos_left (pow_pos hg.D_pos _)).mp h

theorem control_positive {F : Fn} {C : Ctl} (hg : GeometryFacts F)
    (hcheck : checkCtl F C = true) {x : ℝ} (hx : ActivityInterval F x) :
    0 < eval (control F C.s) x := by
  cases C with
  | mk s rule =>
    cases rule with
    | norm =>
      apply positive_of_centered hg (control F s) hx
      intro u hu
      apply normOK_sound _ hu
      exact hcheck
    | quad =>
      apply positive_of_centered hg (control F s) hx
      intro u hu
      apply quadOK_sound _ hu
      exact hcheck
    | bern =>
      have hp : 0 < eval (trimZ (control F s)) x := by
        apply positive_of_interval_expansion hg (trimZ (control F s)) hx
        intro u hu
        apply bernOK_sound _ hu
        exact hcheck
      simpa only [eval_trimZ] using hp

/-- Every accepted control certifies its actual parent polynomial at the correct base activity.
For q-coordinate E records that base activity is x/(1-x), not x. -/
theorem checkCtl_sound {F : Fn} {C : Ctl} (hgeom : geomOK F = true)
    (hcheck : checkCtl F C = true) {x : ℝ} (hx : ActivityInterval F x) :
    0 < eval (parent F.m C.s F.rows) (activityArg F x) := by
  have hg := geomOK_sound hgeom
  have hp := control_positive hg hcheck hx
  cases htoq : F.toQ with
  | false => simpa [control, activityArg, htoq] using hp
  | true =>
    have hx1 : x < 1 := lt_of_le_of_lt hx.2 (hg.q_upper htoq)
    have he := eval_toQ (parent F.m C.s F.rows) (ne_of_lt hx1)
    have hpos : 0 < (1 - x) ^ ((trimZ (parent F.m C.s F.rows)).length - 1) *
        eval (parent F.m C.s F.rows) (x / (1 - x)) := by
      rw [← he]
      simpa [control, htoq] using hp
    have hpow : 0 < (1 - x) ^ ((trimZ (parent F.m C.s F.rows)).length - 1) :=
      pow_pos (sub_pos.mpr hx1) _
    simpa [activityArg, htoq] using (mul_pos_iff_of_pos_left hpow).mp hpos

/-- Actual normalized C_s, on the manuscript's closed interval. -/
theorem checkCtl_bernsteinControl_pos {F : Fn} {C : Ctl} (hgeom : geomOK F = true)
    (hcheck : checkCtl F C = true) (hlen : F.rows.length ≤ F.m + 1) (hs : C.s ≤ F.m)
    {x : ℝ} (hx : ActivityInterval F x) :
    0 < parentBernsteinCoefficient F.m C.s
      (fun j => eval (F.rows.getD j []) (activityArg F x)) := by
  apply parentBernsteinCoefficient_pos_of_scaled hs
  rw [← eval_parent F.m C.s F.rows hlen]
  exact checkCtl_sound hgeom hcheck hx

end F4U.Light
