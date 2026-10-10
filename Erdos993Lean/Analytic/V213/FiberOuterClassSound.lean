module

public import Erdos993Lean.Analytic.V213.FiberOuterClassCheck

/-!
Real soundness of all eight identity-bound outer class checks.
Every width, skew, threshold and target association is obtained from
positive-denominator Int/Nat relations. The exact class minimum width is
mu_D*tau+2; no artificial width or endpoint assumption is introduced.
-/

@[expose] public section

namespace Erdos993Lean.Analytic.V213

theorem fiber_outer_class_field_valid (id : FiberOuterClassIdentity) (x : lowMeanFraction)
    (hx : x ∈ fiberOuterClassFields (fiberOuterClassById id)) : lowMeanFractionValid x := by
  have h := fiber_outer_class_named id
  simp only [fiberOuterClassCheck,Bool.and_eq_true] at h
  have hd := of_decide_eq_true h.2
  exact of_decide_eq_true (List.all_eq_true.mp hd.2.2.2.2.2.2.1 x hx)

theorem fiber_outer_class_controls (id : FiberOuterClassIdentity) :
    let r := fiberOuterClassById id
    (4 / 25 : ℝ) ≤ lowMeanFractionReal r.skew_lower ∧
    lowMeanFractionReal r.skew_upper ≤ 1 / 2 ∧
    0 ≤ lowMeanFractionReal r.b ∧ lowMeanFractionReal r.b ≤ 2 / 5 ∧
    0 ≤ lowMeanFractionReal r.beta_prime ∧ lowMeanFractionReal r.beta_prime ≤ 1 ∧
    40 ≤ lowMeanFractionReal r.mu_D ∧ 0 < lowMeanFractionReal r.tau ∧
    lowMeanFractionReal r.required_N ≤ lowMeanFractionReal r.mu_D * lowMeanFractionReal r.tau + 2 ∧
    lowMeanFractionReal r.required_skew_lower ≤ lowMeanFractionReal r.skew_lower ∧
    lowMeanFractionReal r.skew_upper ≤ lowMeanFractionReal r.required_skew_upper ∧
    lowMeanFractionReal r.required_tau ≤ lowMeanFractionReal r.tau := by
  let r := fiberOuterClassById id
  have h := fiber_outer_class_named id
  simp only [fiberOuterClassCheck,Bool.and_eq_true] at h
  have hd := of_decide_eq_true h.2
  rcases hd with ⟨hprint,hlo,hhi,hfields,hroute,hroutefields,hvalid,hmin,hN,ha,hr,ht,
    hra,hrb,hb0,hb1,hbeta0,hbeta1,hmu,ht0,htarget⟩
  have valid (x : lowMeanFraction) (hx : x ∈ fiberOuterClassFields r) : lowMeanFractionValid x :=
    fiber_outer_class_field_valid id x hx
  have hn := valid r.minimum_N (by simp [fiberOuterClassFields])
  have hmuV := valid r.mu_D (by simp [fiberOuterClassFields])
  have htV := valid r.tau (by simp [fiberOuterClassFields])
  have hcanonical := (lowMean_fraction_eq_iff hn
    (show lowMeanFractionValid (lowMeanFractionAdd (lowMeanFractionMul r.mu_D r.tau) (2,1)) from
      Nat.mul_pos (Nat.mul_pos hmuV htV) (by decide +kernel))).mp hmin
  rw [lowMean_fraction_add (x := lowMeanFractionMul r.mu_D r.tau) (y := (2,1))
    (Nat.mul_pos hmuV htV) (by decide +kernel),lowMean_fraction_mul] at hcanonical
  have htwo : lowMeanFractionReal (2,1) = (2 : ℝ) := by norm_num [lowMeanFractionReal]
  rw [htwo] at hcanonical
  have hwidth := (lowMean_fraction_le_iff
    (valid r.required_N (by simp [fiberOuterClassFields])) hn).mp hN
  rw [hcanonical] at hwidth
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,hwidth,?_,?_,?_⟩
  · have hc := (lowMean_fraction_le_iff (by decide +kernel) (valid r.skew_lower (by simp [fiberOuterClassFields]))).mp hra
    norm_num only [lowMeanFractionReal,Int.cast_ofNat,Nat.cast_ofNat,Int.cast_zero,Int.cast_one,Nat.cast_one,zero_div,div_one] at hc
    exact hc
  · have hc := (lowMean_fraction_le_iff (valid r.skew_upper (by simp [fiberOuterClassFields])) (by decide +kernel)).mp hrb
    norm_num only [lowMeanFractionReal,Int.cast_ofNat,Nat.cast_ofNat,Int.cast_zero,Int.cast_one,Nat.cast_one,zero_div,div_one] at hc
    exact hc
  · have hc := (lowMean_fraction_le_iff (by decide +kernel) (valid r.b (by simp [fiberOuterClassFields]))).mp hb0
    norm_num only [lowMeanFractionReal,Int.cast_ofNat,Nat.cast_ofNat,Int.cast_zero,Int.cast_one,Nat.cast_one,zero_div,div_one] at hc
    exact hc
  · have hc := (lowMean_fraction_le_iff (valid r.b (by simp [fiberOuterClassFields])) (by decide +kernel)).mp hb1
    norm_num only [lowMeanFractionReal,Int.cast_ofNat,Nat.cast_ofNat,Int.cast_zero,Int.cast_one,Nat.cast_one,zero_div,div_one] at hc
    exact hc
  · have hc := (lowMean_fraction_le_iff (by decide +kernel) (valid r.beta_prime (by simp [fiberOuterClassFields]))).mp hbeta0
    norm_num only [lowMeanFractionReal,Int.cast_ofNat,Nat.cast_ofNat,Int.cast_zero,Int.cast_one,Nat.cast_one,zero_div,div_one] at hc
    exact hc
  · have hc := (lowMean_fraction_le_iff (valid r.beta_prime (by simp [fiberOuterClassFields])) (by decide +kernel)).mp hbeta1
    norm_num only [lowMeanFractionReal,Int.cast_ofNat,Nat.cast_ofNat,Int.cast_zero,Int.cast_one,Nat.cast_one,zero_div,div_one] at hc
    exact hc
  · have hc := (lowMean_fraction_le_iff (by decide +kernel) (valid r.mu_D (by simp [fiberOuterClassFields]))).mp hmu
    norm_num only [lowMeanFractionReal,Int.cast_ofNat,Nat.cast_ofNat,Int.cast_zero,Int.cast_one,Nat.cast_one,zero_div,div_one] at hc
    exact hc
  · have hc := (lowMean_fraction_lt_iff (by decide +kernel) (valid r.tau (by simp [fiberOuterClassFields]))).mp ht0
    norm_num only [lowMeanFractionReal,Int.cast_ofNat,Nat.cast_ofNat,Int.cast_zero,Int.cast_one,Nat.cast_one,zero_div,div_one] at hc
    exact hc
  · have hc := (lowMean_fraction_le_iff (valid r.required_skew_lower (by simp [fiberOuterClassFields])) (valid r.skew_lower (by simp [fiberOuterClassFields]))).mp ha
    norm_num only [lowMeanFractionReal,Int.cast_ofNat,Nat.cast_ofNat,Int.cast_zero,Int.cast_one,Nat.cast_one,zero_div,div_one] at hc
    exact hc
  · have hc := (lowMean_fraction_le_iff (valid r.skew_upper (by simp [fiberOuterClassFields])) (valid r.required_skew_upper (by simp [fiberOuterClassFields]))).mp hr
    norm_num only [lowMeanFractionReal,Int.cast_ofNat,Nat.cast_ofNat,Int.cast_zero,Int.cast_one,Nat.cast_one,zero_div,div_one] at hc
    exact hc
  · have hc := (lowMean_fraction_le_iff (valid r.required_tau (by simp [fiberOuterClassFields])) (valid r.tau (by simp [fiberOuterClassFields]))).mp ht
    norm_num only [lowMeanFractionReal,Int.cast_ofNat,Nat.cast_ofNat,Int.cast_zero,Int.cast_one,Nat.cast_one,zero_div,div_one] at hc
    exact hc

noncomputable def fiberOuterClassRouteMeaning (id : FiberOuterClassIdentity) : Prop :=
  let r := fiberOuterClassById id
  match r.start with
  | none => lowMeanFractionReal r.required_N = 26 ∧
      lowMeanFractionReal r.required_skew_lower = 1 / 4 ∧
      lowMeanFractionReal r.required_skew_upper = 1 / 2 ∧
      lowMeanFractionReal r.required_tau = 3 / 5
  | some k => lowMeanFractionReal r.required_N = lowMeanFractionReal (fiberOuterStartById k).n ∧
      lowMeanFractionReal r.required_skew_lower = lowMeanFractionReal (fiberOuterStartById k).a ∧
      lowMeanFractionReal r.required_skew_upper = 2 / 5 ∧
      lowMeanFractionReal r.required_tau = lowMeanFractionReal (fiberOuterStartById k).sigma ∧
      lowMeanFractionReal r.b ≤ lowMeanFractionReal (fiberOuterStartById k).b0 ∧
      lowMeanFractionReal (fiberOuterStartById k).beta0 ≤ lowMeanFractionReal r.beta_prime

theorem fiber_outer_class_route_sound (id : FiberOuterClassIdentity) : fiberOuterClassRouteMeaning id := by
  have h := fiber_outer_class_named id
  simp only [fiberOuterClassCheck,Bool.and_eq_true] at h
  have hd := of_decide_eq_true h.2
  rcases hd with ⟨hprint,hlo,hhi,hfields,hroute,hroutefields,hvalid,hmin,hN,ha,hr,ht,
    hra,hrb,hb0,hb1,hbeta0,hbeta1,hmu,ht0,htarget⟩
  cases id <;> simp only [fiberOuterClassById,fiberOuterClassRouteMeaning,
    fiberOuterClassActualRouteFields,fiberOuterClassRouteFields,fiberOuterClassTargetGuard,
    fiberOuterUniversal,List.cons.injEq] at hroutefields htarget ⊢
    <;> norm_num only [lowMeanFractionReal,Int.cast_ofNat,Nat.cast_ofNat,Nat.cast_one,div_one]
    <;> first
      | exact ⟨congrArg lowMeanFractionReal hroutefields.1,congrArg lowMeanFractionReal hroutefields.2.1,
          by norm_num,congrArg lowMeanFractionReal hroutefields.2.2.2.1,
          (lowMean_fraction_le_iff (by decide +kernel) (by decide +kernel)).mp htarget.1,
          (lowMean_fraction_le_iff (by decide +kernel) (by decide +kernel)).mp htarget.2⟩
      | norm_num [fiberOuterStartById,lowMeanFractionReal]

end Erdos993Lean.Analytic.V213
