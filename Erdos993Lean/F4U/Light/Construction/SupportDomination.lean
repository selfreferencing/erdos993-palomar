module
public import Erdos993Lean.F4U.Light.Construction.SupportCurvature

/-! Global tangent domination on the actual child parameter, without an
unproved inverse h chart. Curvature makes dJ/dh+κh increase with u because
h decreases. The corresponding contact remainder is maximal at contact. -/
@[expose] public section
namespace F4Unified.LightConstruction
noncomputable section

def supportShift (lam K u : ℝ) : ℝ := supportDerivative lam u+K*childH u

def supportRemainder (lam K u0 u : ℝ) : ℝ :=
  childJ lam u-childJ lam u0-supportDerivative lam u0*(childH u-childH u0)+
    K/2*(childH u-childH u0)^2

theorem support_curvature_positive (r : Row) : 0 < curvature r := by
  cases r <;> norm_num [curvature]

theorem support_upper_lt_one (r : Row) : supportUpper r < 1 := by
  cases r <;> norm_num [supportUpper]

theorem support_row_lower_positive {r : Row} {lam : ℝ}
    (hlam : (rowData r).lo ≤ lam) : 0 < lam := by
  cases r <;> simp only [rowData] at hlam <;> linarith

theorem support_childH_derivative_neg {u : ℝ} (hu0 : 0 < u) (hu1 : u < 1) :
    -supportW u/((1-u)*phi u) < 0 := by
  have hw := support_w_pos hu0 hu1
  have hp := support_phi_pos hu0 hu1
  have h1 : 0 < 1-u := by linarith
  exact div_neg_of_neg_of_pos (neg_neg_of_pos hw) (mul_pos h1 hp)

theorem supportShift_hasDerivAt {lam K u : ℝ} (hlam : 0 < lam)
    (hu0 : 0 < u) (hu1 : u < 1) :
    HasDerivAt (supportShift lam K)
      ((-supportW u/((1-u)*phi u))*(supportSecond lam u+K)) u := by
  have hd := (supportDerivative_hasDerivAt hlam hu0 hu1).add
    ((childH_support_hasDerivAt hu0 hu1).const_mul K)
  convert hd using 1
  · rfl
  · ring

theorem supportShift_monotoneOn {r : Row} {lam : ℝ}
    (hlam : (rowData r).lo ≤ lam) :
    MonotoneOn (supportShift lam (curvature r)) (Set.Ioc 0 (supportUpper r)) := by
  have hl := support_row_lower_positive hlam
  have hder : ∀ u ∈ Set.Ioc 0 (supportUpper r),
      HasDerivAt (supportShift lam (curvature r))
        ((-supportW u/((1-u)*phi u))*(supportSecond lam u+curvature r)) u := by
    intro u hu
    exact supportShift_hasDerivAt hl hu.1 (lt_of_le_of_lt hu.2 (support_upper_lt_one r))
  apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ioc 0 (supportUpper r))
    (fun u hu => (hder u hu).continuousAt.continuousWithinAt)
  · intro u hu
    exact (hder u (interior_subset hu)).hasDerivWithinAt
  · intro u hu
    have hum := interior_subset hu
    have hd := support_childH_derivative_neg hum.1
      (lt_of_le_of_lt hum.2 (support_upper_lt_one r))
    have hc := endpoint_support_curvature hlam hum.1 hum.2
    exact mul_nonneg_of_nonpos_of_nonpos hd.le (by linarith)

theorem supportRemainder_hasDerivAt {lam K u0 u : ℝ} (hlam : 0 < lam)
    (hu0 : 0 < u) (hu1 : u < 1) :
    HasDerivAt (supportRemainder lam K u0)
      ((-supportW u/((1-u)*phi u))*(supportShift lam K u-supportShift lam K u0)) u := by
  have hj := childJ_support_hasDerivAt hlam hu0 hu1
  have hh := childH_support_hasDerivAt hu0 hu1
  have hd := ((hj.sub_const (childJ lam u0)).sub
      ((hh.sub_const (childH u0)).const_mul (supportDerivative lam u0))).add
      (((hh.sub_const (childH u0)).pow 2).const_mul (K/2))
  convert hd using 1
  · ext v
    unfold supportRemainder
    dsimp <;> ring
  · unfold supportShift
    dsimp <;> ring

theorem supportRemainder_nonpos {r : Row} {lam u0 u : ℝ}
    (hlam : (rowData r).lo ≤ lam)
    (hu00 : 0 < u0) (hu0hi : u0 ≤ supportUpper r)
    (hu0 : 0 < u) (huhi : u ≤ supportUpper r) :
    supportRemainder lam (curvature r) u0 u ≤ 0 := by
  have hl := support_row_lower_positive hlam
  have hm := supportShift_monotoneOn hlam
  have hzero : supportRemainder lam (curvature r) u0 u0 = 0 := by simp [supportRemainder]
  rcases le_total u u0 with hle | hle
  · have hdom : ∀ v ∈ Set.Icc u u0, 0 < v ∧ v ≤ supportUpper r := by
      intro v hv
      exact ⟨lt_of_lt_of_le hu0 hv.1, hv.2.trans hu0hi⟩
    have hd : ∀ v ∈ Set.Icc u u0,
        HasDerivAt (supportRemainder lam (curvature r) u0)
          ((-supportW v/((1-v)*phi v))*(supportShift lam (curvature r) v-
            supportShift lam (curvature r) u0)) v := by
      intro v hv
      exact supportRemainder_hasDerivAt hl (hdom v hv).1
        (lt_of_le_of_lt (hdom v hv).2 (support_upper_lt_one r))
    have hmon : MonotoneOn (supportRemainder lam (curvature r) u0) (Set.Icc u u0) := by
      apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc u u0)
        (fun v hv => (hd v hv).continuousAt.continuousWithinAt)
      · intro v hv
        exact (hd v (interior_subset hv)).hasDerivWithinAt
      · intro v hv
        have hv' := interior_subset hv
        have hvd := hdom v hv'
        have hk := hm hvd ⟨hu00,hu0hi⟩ hv'.2
        have hneg := support_childH_derivative_neg hvd.1
          (lt_of_le_of_lt hvd.2 (support_upper_lt_one r))
        exact mul_nonneg_of_nonpos_of_nonpos hneg.le (sub_nonpos.mpr hk)
    have hh := hmon ⟨le_rfl,hle⟩ ⟨hle,le_rfl⟩ hle
    simpa only [hzero] using hh
  · have hdom : ∀ v ∈ Set.Icc u0 u, 0 < v ∧ v ≤ supportUpper r := by
      intro v hv
      exact ⟨lt_of_lt_of_le hu00 hv.1, hv.2.trans huhi⟩
    have hd : ∀ v ∈ Set.Icc u0 u,
        HasDerivAt (supportRemainder lam (curvature r) u0)
          ((-supportW v/((1-v)*phi v))*(supportShift lam (curvature r) v-
            supportShift lam (curvature r) u0)) v := by
      intro v hv
      exact supportRemainder_hasDerivAt hl (hdom v hv).1
        (lt_of_le_of_lt (hdom v hv).2 (support_upper_lt_one r))
    have hmon : AntitoneOn (supportRemainder lam (curvature r) u0) (Set.Icc u0 u) := by
      apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc u0 u)
        (fun v hv => (hd v hv).continuousAt.continuousWithinAt)
      · intro v hv
        exact (hd v (interior_subset hv)).hasDerivWithinAt
      · intro v hv
        have hv' := interior_subset hv
        have hvd := hdom v hv'
        have hk := hm ⟨hu00,hu0hi⟩ hvd hv'.1
        have hneg := support_childH_derivative_neg hvd.1
          (lt_of_le_of_lt hvd.2 (support_upper_lt_one r))
        exact mul_nonpos_of_nonpos_of_nonneg hneg.le (sub_nonneg.mpr hk)
    have hh := hmon ⟨le_rfl,hle⟩ ⟨hle,le_rfl⟩ hle
    simpa only [hzero] using hh

/-- Curvature converts the actual contact value into a global support bound. -/
theorem endpoint_support_of_contact {r : Row} {s : Support} {lam u0 u c : ℝ}
    (hlam : (rowData r).lo ≤ lam)
    (hu00 : 0 < u0) (hu0hi : u0 ≤ supportUpper r)
    (hu0 : 0 < u) (huhi : u ≤ supportUpper r)
    (hcontact : supportContactValue r s lam u0 < c) :
    childJ lam u < slope r s*childH u+c := by
  have hr := supportRemainder_nonpos hlam hu00 hu0hi hu0 huhi
  have hK := support_curvature_positive r
  have hs := sq_nonneg ((childH u-childH u0)-
      (supportDerivative lam u0-slope r s)/curvature r)
  have hm := mul_nonneg (show 0 ≤ curvature r/2 by positivity) hs
  have he : curvature r/2*((childH u-childH u0)-
      (supportDerivative lam u0-slope r s)/curvature r)^2 =
      curvature r/2*(childH u-childH u0)^2-
      (supportDerivative lam u0-slope r s)*(childH u-childH u0)+
      (supportDerivative lam u0-slope r s)^2/(2*curvature r) := by
    field_simp [hK.ne'] <;> ring
  rw [he] at hm
  unfold supportRemainder at hr
  unfold supportContactValue at hcontact
  nlinarith

end
end F4Unified.LightConstruction
