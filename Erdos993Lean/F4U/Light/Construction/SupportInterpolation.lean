module
public import Erdos993Lean.F4U.Light.Construction.SupportDomination
public import Mathlib.Analysis.Convex.Deriv

/-! Activity interpolation and the literal D/E error corrections. Intermediate
convexity hypotheses are discharged by the actual logarithm derivatives. -/
@[expose] public section
namespace F4Unified.LightConstruction
noncomputable section

def supportLogit (x : ℝ) : ℝ := Real.log (x/(1-x))

theorem supportLogit_hasDerivAt {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    HasDerivAt supportLogit (1/(x*(1-x))) x := by
  have hid := hasDerivAt_id x
  have h1 : 1-x ≠ 0 := by linarith
  have hd := (hid.div ((hasDerivAt_const x (1 : ℝ)).sub hid) h1).log
    (show x/(1-x) ≠ 0 by positivity)
  convert hd using 1
  · rfl
  · dsimp
    field_simp [hx0.ne', h1] <;> ring

theorem supportLogit_derivative_hasDerivAt {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    HasDerivAt (fun v : ℝ => 1/(v*(1-v)))
      ((2*x-1)/(x^2*(1-x)^2)) x := by
  have hid := hasDerivAt_id x
  have hd := (hasDerivAt_const x (1 : ℝ)).div
    (hid.mul ((hasDerivAt_const x (1 : ℝ)).sub hid))
      (show x*(1-x) ≠ 0 from mul_ne_zero hx0.ne' (by linarith))
  convert hd using 1
  · rfl
  · dsimp
    have h1 : 1-x ≠ 0 := by linarith
    field_simp [hx0.ne', h1] <;> ring

theorem supportLogit_corrected_convex {a b K : ℝ} (ha0 : 0 < a) (hb1 : b < 1)
    (hsecond : ∀ x ∈ Set.Icc a b, 0 ≤ (2*x-1)/(x^2*(1-x)^2)+K) :
    ConvexOn ℝ (Set.Icc a b) (fun x : ℝ => supportLogit x+K/2*x^2) := by
  have hd : ∀ x ∈ Set.Icc a b, HasDerivAt
      (fun x : ℝ => supportLogit x+K/2*x^2) (1/(x*(1-x))+K*x) x := by
    intro x hx
    convert (supportLogit_hasDerivAt (ha0.trans_le hx.1) (hx.2.trans_lt hb1)).add
      (((hasDerivAt_id x).pow 2).const_mul (K/2)) using 1
    · rfl
    · (try dsimp) <;> ring
  have hdd : ∀ x ∈ Set.Icc a b, HasDerivAt
      (fun x : ℝ => 1/(x*(1-x))+K*x) ((2*x-1)/(x^2*(1-x)^2)+K) x := by
    intro x hx
    convert (supportLogit_derivative_hasDerivAt (ha0.trans_le hx.1) (hx.2.trans_lt hb1)).add
      ((hasDerivAt_id x).const_mul K) using 1
    · rfl
    · (try dsimp) <;> ring
  apply convexOn_of_hasDerivWithinAt2_nonneg (convex_Icc a b)
    (fun x hx => (hd x hx).continuousAt.continuousWithinAt)
  · intro x hx
    exact (hd x (interior_subset hx)).hasDerivWithinAt
  · intro x hx
    exact (hdd x (interior_subset hx)).hasDerivWithinAt
  · intro x hx
    exact hsecond x (interior_subset hx)

theorem supportLogit_D_corrected_convex :
    ConvexOn ℝ (Set.Icc ((4 : ℝ)/9) (13/23))
      (fun x : ℝ => supportLogit x+(729/800)*x^2) := by
  rw [show (729 : ℝ)/800=(729/400)/2 by norm_num]
  apply supportLogit_corrected_convex (K := (729 : ℝ)/400) (by norm_num) (by norm_num)
  intro x hx
  have hx0 : 0 < x := by linarith [hx.1]
  have hx1 : x < 1 := by linarith [hx.2]
  have he : (2*x-1)/(x^2*(1-x)^2)+729/400 =
      (9*x-4)*(81*x^3-126*x^2+25*x+100)/(400*x^2*(1-x)^2) := by
    have h1 : 1-x ≠ 0 := by linarith
    field_simp [hx0.ne', h1] <;> ring
  rw [he]
  have hfirst : 0 ≤ 9*x-4 := by linarith [hx.1]
  have hp : 0 ≤ 81*x^3-126*x^2+25*x+100 := by
    have hx7 : x ≤ 7/10 := by linarith [hx.2]
    have hs := mul_le_mul hx7 hx7 hx0.le (by norm_num : 0 ≤ (7 : ℝ)/10)
    nlinarith [pow_nonneg hx0.le 3]
  positivity

theorem supportLogit_H_convex : ConvexOn ℝ (Set.Icc ((7 : ℝ)/11) (7/10)) supportLogit := by
  have h := supportLogit_corrected_convex (K := (0 : ℝ)) (by norm_num : 0 < (7 : ℝ)/11)
    (by norm_num : (7 : ℝ)/10 < 1) (by
      intro x hx
      have ht : 0 ≤ 2*x-1 := by linarith [hx.1]
      positivity)
  simpa only [zero_div, zero_mul, add_zero] using h

theorem support_log_corrected_convex {a b : ℝ} (ha0 : 0 < a) :
    ConvexOn ℝ (Set.Icc a b) (fun x : ℝ => Real.log x+x^2/(2*a^2)) := by
  have hd : ∀ x ∈ Set.Icc a b, HasDerivAt
      (fun x : ℝ => Real.log x+x^2/(2*a^2)) (1/x+x/a^2) x := by
    intro x hx
    have hxp : 0 < x := ha0.trans_le hx.1
    convert (Real.hasDerivAt_log hxp.ne').add
      (((hasDerivAt_id x).pow 2).div_const (2*a^2)) using 1
    · rfl
    · (try dsimp) <;> ring
  have hdd : ∀ x ∈ Set.Icc a b, HasDerivAt
      (fun x : ℝ => 1/x+x/a^2) (-1/x^2+1/a^2) x := by
    intro x hx
    have hxp : 0 < x := ha0.trans_le hx.1
    convert ((hasDerivAt_const x (1 : ℝ)).div (hasDerivAt_id x) hxp.ne').add
      ((hasDerivAt_id x).div_const (a^2)) using 1
    · rfl
    · (try dsimp) <;> ring
  apply convexOn_of_hasDerivWithinAt2_nonneg (convex_Icc a b)
    (fun x hx => (hd x hx).continuousAt.continuousWithinAt)
  · intro x hx
    exact (hd x (interior_subset hx)).hasDerivWithinAt
  · intro x hx
    exact (hdd x (interior_subset hx)).hasDerivWithinAt
  · intro x hx
    have hxm := interior_subset hx
    have hxp : 0 < x := ha0.trans_le hxm.1
    have hs : a^2 ≤ x^2 := pow_le_pow_left₀ ha0.le hxm.1 2
    have hi : 1/x^2 ≤ 1/a^2 := one_div_le_one_div_of_le (pow_pos ha0 2) hs
    simp only [neg_div]
    linarith

theorem corrected_convex_chord_upper {F : ℝ → ℝ} {a b x K : ℝ}
    (hab : a < b) (hx : x ∈ Set.Icc a b)
    (hconv : ConvexOn ℝ (Set.Icc a b) (fun x => F x+K/2*x^2)) :
    F x ≤ (1-(x-a)/(b-a))*F a+((x-a)/(b-a))*F b+K/2*(x-a)*(b-x) := by
  let w := (x-a)/(b-a)
  have hd : 0 < b-a := by linarith
  have hw0 : 0 ≤ w := div_nonneg (by linarith [hx.1]) hd.le
  have hw1 : w ≤ 1 := (div_le_one hd).mpr (by linarith [hx.2])
  have he : (1-w)*a+w*b = x := by dsimp [w]; field_simp [hd.ne'] <;> ring
  have hs : (1-w)*a^2+w*b^2-x^2 = (x-a)*(b-x) := by
    dsimp [w]
    field_simp [hd.ne'] <;> ring
  have h := hconv.2 (show a ∈ Set.Icc a b from ⟨le_rfl,hab.le⟩)
    (show b ∈ Set.Icc a b from ⟨hab.le,le_rfl⟩)
    (show 0 ≤ 1-w by linarith) hw0 (by ring : (1-w)+w=1)
  simp only [smul_eq_mul, he] at h
  change F x ≤ (1-w)*F a+w*F b+K/2*(x-a)*(b-x)
  rw [mul_assoc (K/2) (x-a) (b-x), ← hs]
  nlinarith

theorem support_log_chord_upper {a b x : ℝ} (ha0 : 0 < a) (hab : a < b)
    (hx : x ∈ Set.Icc a b) :
    Real.log x ≤ (1-(x-a)/(b-a))*Real.log a+((x-a)/(b-a))*Real.log b+
      (b-a)^2/(8*a^2) := by
  have hc := support_log_corrected_convex (b := b) ha0
  have hc' : ConvexOn ℝ (Set.Icc a b) (fun x : ℝ => Real.log x+(1/a^2)/2*x^2) := by
    convert hc using 1 <;> ext y <;> ring
  have hh := corrected_convex_chord_upper hab hx hc'
  have hm : (x-a)*(b-x) ≤ (b-a)^2/4 := by nlinarith [sq_nonneg (x-(a+b)/2)]
  have hp := mul_le_mul_of_nonneg_left hm (show 0 ≤ (1/a^2)/2 by positivity)
  have ht : (1/a^2)/2*(x-a)*(b-x) ≤ (b-a)^2/(8*a^2) := by
    convert hp using 1 <;> ring
  have ht' := add_le_add_left ht ((1-(x-a)/(b-a))*Real.log a+((x-a)/(b-a))*Real.log b)
  linarith only [hh, ht']

theorem support_logit_q {lam : ℝ} (hlam : 0 < lam) : supportLogit (q lam) = Real.log lam := by
  have h1 : 1+lam ≠ 0 := by positivity
  have he : q lam/(1-q lam) = lam := by
    unfold q
    field_simp [h1] <;> ring
  exact congrArg Real.log he

theorem childJ_activity_mix {a b lam u w : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hlam : 0 < lam) (hu0 : 0 < u) (hu1 : u < 1) :
    childJ lam u = (1-w)*childJ a u+w*childJ b u+
      u*childH u*(Real.log lam-(1-w)*Real.log a-w*Real.log b) := by
  have hratio : (1-u)/u ≠ 0 := by positivity
  have hcanon (e : ℝ) (he : 0 < e) :
      Real.log (e*(1-u)/u) = Real.log e+Real.log ((1-u)/u) := by
    rw [show e*(1-u)/u=e*((1-u)/u) by ring, Real.log_mul he.ne' hratio]
  simp only [childJ, ite_eq_right hu0.ne', hcanon lam hlam, hcanon a ha, hcanon b hb]
  ring

theorem support_mass_bound {u b : ℝ} (hu0 : 0 ≤ u) (hub : u ≤ b) (hb1 : b < 1) :
    u*childH u ≤ b*(1-b/2) := by
  have hu1 : u < 1 := hub.trans_lt hb1
  have hh := childH_le_parentHBound hu0 hu1
  have hh' : childH u ≤ 1-u/2 := by unfold parentHBound at hh; nlinarith [sq_nonneg u]
  have hm := mul_le_mul_of_nonneg_left hh' hu0
  have he : 0 ≤ (b-u)*(1-(b+u)/2) :=
    mul_nonneg (sub_nonneg.mpr hub) (by linarith)
  nlinarith


def supportInterpolationWeight (r : Row) (lam : ℝ) : ℝ :=
  match r with
  | .D | .H => (q lam-q (rowData r).lo)/(q (rowData r).hi-q (rowData r).lo)
  | .E1 | .E2 => (lam-(rowData r).lo)/((rowData r).hi-(rowData r).lo)

def supportLogError (r : Row) (lam : ℝ) : ℝ :=
  match r with
  | .D => (729/800)*(q lam-q (rowData r).lo)*(q (rowData r).hi-q lam)
  | .H => 0
  | .E1 | .E2 => ((rowData r).hi-(rowData r).lo)^2/(8*((rowData r).lo)^2)

theorem support_row_endpoints (r : Row) :
    0 < (rowData r).lo ∧ (rowData r).lo < (rowData r).hi := by
  cases r <;> norm_num [rowData]

theorem support_q_mono {a b : ℝ} (ha0 : 0 < a) (hab : a ≤ b) : q a ≤ q b := by
  have ha : 0 < 1+a := by linarith
  have hb : 0 < 1+b := by linarith
  have he : q b-q a=(b-a)/((1+a)*(1+b)) := by
    unfold q
    field_simp [ha.ne', hb.ne'] <;> ring
  have hp : 0 ≤ (b-a)/((1+a)*(1+b)) := by positivity
  linarith

theorem support_q_strict {a b : ℝ} (ha0 : 0 < a) (hab : a < b) : q a < q b := by
  have ha : 0 < 1+a := by linarith
  have hb : 0 < 1+b := by linarith
  have he : q b-q a=(b-a)/((1+a)*(1+b)) := by
    unfold q
    field_simp [ha.ne', hb.ne'] <;> ring
  have hp : 0 < (b-a)/((1+a)*(1+b)) := by positivity
  linarith

theorem support_q_interval {r : Row} {lam : ℝ} (hlam : InRow r lam) :
    q (rowData r).lo ≤ q lam ∧ q lam ≤ q (rowData r).hi := by
  have he := support_row_endpoints r
  exact ⟨support_q_mono he.1 hlam.1,
    support_q_mono (he.1.trans_le hlam.1) hlam.2⟩

theorem supportInterpolationWeight_bounds {r : Row} {lam : ℝ} (hlam : InRow r lam) :
    0 ≤ supportInterpolationWeight r lam ∧ supportInterpolationWeight r lam ≤ 1 := by
  have he := support_row_endpoints r
  have hq := support_q_interval hlam
  have hqab := support_q_strict he.1 he.2
  have hqwidth : 0 < q (rowData r).hi-q (rowData r).lo := by linarith
  have hwidth : 0 < (rowData r).hi-(rowData r).lo := by linarith
  cases r <;> simp only [supportInterpolationWeight]
  all_goals constructor
  all_goals first
    | exact div_nonneg (by linarith [hq.1]) hqwidth.le
    | exact (div_le_one hqwidth).mpr (by linarith [hq.2])
    | exact div_nonneg (by linarith [hlam.1]) hwidth.le
    | exact (div_le_one hwidth).mpr (by linarith [hlam.2])

theorem supportLogError_nonneg {r : Row} {lam : ℝ} (hlam : InRow r lam) :
    0 ≤ supportLogError r lam := by
  have hq := support_q_interval hlam
  cases r <;> simp only [supportLogError]
  · exact mul_nonneg (mul_nonneg (by norm_num) (sub_nonneg.mpr hq.1)) (sub_nonneg.mpr hq.2)
  · positivity
  · positivity
  · exact le_rfl

theorem support_activity_log_bound {r : Row} {lam : ℝ} (hlam : InRow r lam) :
    Real.log lam ≤ (1-supportInterpolationWeight r lam)*Real.log (rowData r).lo+
      supportInterpolationWeight r lam*Real.log (rowData r).hi+supportLogError r lam := by
  have he := support_row_endpoints r
  have hl := inRow_lambda_bounds hlam
  have hq := support_q_interval hlam
  cases r
  · have hconv : ConvexOn ℝ (Set.Icc ((4 : ℝ)/9) (13/23))
        (fun x : ℝ => supportLogit x+((729 : ℝ)/400)/2*x^2) := by
      norm_num
      exact supportLogit_D_corrected_convex
    have hh := corrected_convex_chord_upper (F := supportLogit) (K := (729 : ℝ)/400)
      (by norm_num : (4 : ℝ)/9 < 13/23)
      (show q lam ∈ Set.Icc ((4 : ℝ)/9) (13/23) by
        norm_num [rowData, q] at hq ⊢
        exact hq) hconv
    have hqa : supportLogit ((4 : ℝ)/9) = Real.log ((4 : ℝ)/5) := by
      convert support_logit_q (by norm_num : 0 < (4 : ℝ)/5) using 1 <;> norm_num [q]
    have hqb : supportLogit ((13 : ℝ)/23) = Real.log ((13 : ℝ)/10) := by
      convert support_logit_q (by norm_num : 0 < (13 : ℝ)/10) using 1 <;> norm_num [q]
    rw [support_logit_q hl.1, hqa, hqb] at hh
    norm_num [supportInterpolationWeight, supportLogError, rowData, q] at hh ⊢
    exact hh
  · have hh := support_log_chord_upper he.1 he.2 hlam
    simpa only [supportInterpolationWeight, supportLogError] using hh
  · have hh := support_log_chord_upper he.1 he.2 hlam
    simpa only [supportInterpolationWeight, supportLogError] using hh
  · have hc : ConvexOn ℝ (Set.Icc ((7 : ℝ)/11) (7/10))
        (fun x : ℝ => supportLogit x+(0 : ℝ)/2*x^2) := by
      simpa only [zero_div, zero_mul, add_zero] using supportLogit_H_convex
    have hh := corrected_convex_chord_upper (by norm_num : (7 : ℝ)/11 < 7/10)
      (show q lam ∈ Set.Icc ((7 : ℝ)/11) (7/10) by
        norm_num [rowData, q] at hq ⊢
        exact hq) hc
    have hqa : supportLogit ((7 : ℝ)/11) = Real.log ((7 : ℝ)/4) := by
      convert support_logit_q (by norm_num : 0 < (7 : ℝ)/4) using 1 <;> norm_num [q]
    have hqb : supportLogit ((7 : ℝ)/10) = Real.log ((7 : ℝ)/3) := by
      convert support_logit_q (by norm_num : 0 < (7 : ℝ)/3) using 1 <;> norm_num [q]
    rw [support_logit_q hl.1, hqa, hqb] at hh
    norm_num [supportInterpolationWeight, supportLogError, rowData, q] at hh ⊢
    exact hh

theorem support_intercept_identity (r : Row) (s : Support) (lam : ℝ) :
    intercept r s lam = (1-supportInterpolationWeight r lam)*endpointInterceptLo r s+
      supportInterpolationWeight r lam*endpointInterceptHi r s+interceptError r lam := by
  cases r <;> simp only [intercept, supportInterpolationWeight] <;> norm_num only [rowData] <;> ring

theorem support_intercept_error_identity (r : Row) (lam : ℝ) :
    interceptError r lam = q (rowData r).hi*(1-q (rowData r).hi/2)*supportLogError r lam := by
  cases r <;> simp only [interceptError, supportLogError] <;> ring

theorem support_u_upper {r : Row} {lam u : ℝ} (hlam : InRow r lam) (huq : u ≤ q lam) :
    u ≤ supportUpper r := by
  have hq := support_q_interval hlam
  have h := huq.trans hq.2
  cases r <;> norm_num [rowData, q, supportUpper] at h ⊢ <;> linarith

theorem support_contacts_domain (r : Row) (s : Support) :
    (0 < contactLo r s ∧ contactLo r s ≤ supportUpper r) ∧
    (0 < contactHi r s ∧ contactHi r s ≤ supportUpper r) := by
  cases r <;> cases s <;> norm_num [contactLo, contactHi, supportUpper]

/-- Both literal contact comparisons imply the actual interpolated support.
The two contact hypotheses are the finite logarithm checks discharged by
ContactChecks; no support theorem is assumed here. -/
theorem supportLine_of_endpoint_contacts {r : Row} {s : Support} {lam u : ℝ}
    (hlam : InRow r lam) (hu0 : 0 < u) (huq : u ≤ q lam)
    (hlo : supportContactValue r s (rowData r).lo (contactLo r s) < endpointInterceptLo r s)
    (hhi : supportContactValue r s (rowData r).hi (contactHi r s) < endpointInterceptHi r s) :
    childJ lam u < supportLine r s lam (childH u) := by
  have he := support_row_endpoints r
  have hl := inRow_lambda_bounds hlam
  have huhi := support_u_upper hlam huq
  have hu1 := huhi.trans_lt (support_upper_lt_one r)
  have hc := support_contacts_domain r s
  have hJa := endpoint_support_of_contact (lam := (rowData r).lo) le_rfl
    hc.1.1 hc.1.2 hu0 huhi hlo
  have hJb := endpoint_support_of_contact (lam := (rowData r).hi) he.2.le
    hc.2.1 hc.2.2 hu0 huhi hhi
  have hw := supportInterpolationWeight_bounds hlam
  have hlog := support_activity_log_bound hlam
  have herr := supportLogError_nonneg hlam
  have hmpos : 0 ≤ u*childH u := mul_nonneg hu0.le (support_childH_pos hu0 hu1).le
  have hm := mul_le_mul_of_nonneg_left hlog hmpos
  have hb1 : q (rowData r).hi < 1 := by
    have hp : 0 < 1+(rowData r).hi := by linarith
    unfold q
    rw [div_lt_one hp]
    linarith
  have hmass := support_mass_bound hu0.le (huq.trans (support_q_interval hlam).2) hb1
  have hmass' := mul_le_mul_of_nonneg_right hmass herr
  have hmix := childJ_activity_mix he.1 (he.1.trans he.2) hl.1 hu0 hu1
    (w := supportInterpolationWeight r lam)
  have hend : (1-supportInterpolationWeight r lam)*childJ (rowData r).lo u+
      supportInterpolationWeight r lam*childJ (rowData r).hi u <
      slope r s*childH u+(1-supportInterpolationWeight r lam)*endpointInterceptLo r s+
      supportInterpolationWeight r lam*endpointInterceptHi r s := by
    rcases lt_or_eq_of_le hw.1 with hwpos | hwzero
    · have hm1 := mul_le_mul_of_nonneg_left hJa.le (sub_nonneg.mpr hw.2)
      have hm2 := mul_lt_mul_of_pos_left hJb hwpos
      nlinarith
    · simp only [← hwzero, zero_mul, sub_zero, one_mul, add_zero]
      exact hJa
  unfold supportLine
  rw [support_intercept_identity, support_intercept_error_identity]
  nlinarith

end
end F4Unified.LightConstruction
