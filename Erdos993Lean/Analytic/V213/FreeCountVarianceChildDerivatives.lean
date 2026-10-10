module

public import Erdos993Lean.Analytic.V213.FreeCountVarianceDerivatives

/-!+# Child-coordinate derivatives for CA

Source: current Section 3, the paragraph following equation (19).
The two rate comparisons are stated after multiplication by the positive
dr/dt; consequently no inverse-coordinate or endpoint differentiability is
assumed. The hc-square comparison explicitly requires the printed scalar
bound hc <= 1-u/2. Proving that bound, the cap-dependent positive derivative
budget and the least-feasible-child reduction remains separate work.
-/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.FreeCountVariance

noncomputable def childRatio (lam t : ℝ) : ℝ := t / logMass lam t
noncomputable def childH (lam t : ℝ) : ℝ := message lam t / logMass lam t

theorem childH_pos {lam : ℝ} (hlam : 0 < lam) (t : ℝ) : 0 < childH lam t :=
  div_pos (message_pos hlam t) (logMass_pos hlam t)

theorem childRatio_nonneg {lam t : ℝ} (hlam : 0 < lam) (ht : 0 ≤ t) :
    0 ≤ childRatio lam t := div_nonneg ht (logMass_pos hlam t).le

theorem childRatio_hasDerivAt {lam : ℝ} (hlam : 0 < lam) (t : ℝ) :
    HasDerivAt (childRatio lam)
      ((logMass lam t + t * message lam t) / logMass lam t ^ 2) t := by
  have hf := (logMass_pos hlam t).ne'
  change HasDerivAt (fun s => s / logMass lam s) _ t
  apply ((hasDerivAt_id t).div (logMass_hasDerivAt hlam t) hf).congr_deriv
  (try simp only [id_eq, Pi.pow_apply]) <;> ring

theorem childRatio_deriv_pos {lam t : ℝ} (hlam : 0 < lam) (ht : 0 ≤ t) :
    0 < deriv (childRatio lam) t := by
  rw [(childRatio_hasDerivAt hlam t).deriv]
  have hf := logMass_pos hlam t
  have hu := message_pos hlam t
  positivity

theorem childH_hasDerivAt {lam : ℝ} (hlam : 0 < lam) (t : ℝ) :
    HasDerivAt (childH lam)
      (childH lam t * (childH lam t - (1 - message lam t))) t := by
  have hf := (logMass_pos hlam t).ne'
  change HasDerivAt (fun s => message lam s / logMass lam s) _ t
  apply ((message_hasDerivAt hlam t).div (logMass_hasDerivAt hlam t) hf).congr_deriv
  unfold childH
  (try simp only [id_eq, Pi.pow_apply]) <;> field_simp [hf] <;> ring

theorem childH_sq_hasDerivAt {lam : ℝ} (hlam : 0 < lam) (t : ℝ) :
    HasDerivAt (fun s => childH lam s ^ 2)
      (2 * childH lam t ^ 2 * (childH lam t - (1 - message lam t))) t := by
  apply ((childH_hasDerivAt hlam t).pow 2).congr_deriv
  (try simp only [id_eq, Pi.pow_apply]) <;> ring

theorem J_hasDerivAt {lam : ℝ} (hlam : 0 < lam) (t : ℝ) :
    HasDerivAt (J lam)
      (message lam t ^ 2 *
          ((logMass lam t + t * message lam t) / logMass lam t ^ 2) -
        2 * message lam t ^ 2 * (1 - message lam t) * childRatio lam t) t := by
  have hr : J lam = fun s => message lam s ^ 2 * childRatio lam s := by
    funext s
    unfold J childRatio
    ring
  rw [hr]
  apply (((message_hasDerivAt hlam t).pow 2).mul
    (childRatio_hasDerivAt hlam t)).congr_deriv
  (try simp only [id_eq, Pi.pow_apply]) <;> ring

/-- Equivalent to dJ/dr <= u^2 because dr/dt is strictly positive. -/
theorem J_deriv_le_childRatio {lam t : ℝ} (hlam : 0 < lam) (ht : 0 ≤ t) :
    deriv (J lam) t ≤ message lam t ^ 2 * deriv (childRatio lam) t := by
  rw [(J_hasDerivAt hlam t).deriv, (childRatio_hasDerivAt hlam t).deriv]
  have hk : 0 ≤ 1 - message lam t := (sub_pos.mpr (message_lt_one hlam t)).le
  have hr := childRatio_nonneg hlam ht
  have hx : 0 ≤ 2 * message lam t ^ 2 * (1 - message lam t) * childRatio lam t := by
    positivity
  linarith

/-- The precise dependency on the printed upper bound for h0 is visible here. -/
theorem childH_sq_deriv_le_childRatio {lam t : ℝ}
    (hlam : 0 < lam) (ht : 0 ≤ t)
    (hupper : childH lam t ≤ 1 - message lam t / 2) :
    deriv (fun s => childH lam s ^ 2) t ≤
      message lam t ^ 2 * childH lam t * deriv (childRatio lam) t := by
  rw [(childH_sq_hasDerivAt hlam t).deriv, (childRatio_hasDerivAt hlam t).deriv]
  have hf := (logMass_pos hlam t).ne'
  have hu := message_pos hlam t
  have hhc := childH_pos hlam t
  have hterm : 0 ≤ t * message lam t * childH lam t := by positivity
  have hbracket : 0 ≤ message lam t -
      2 * (childH lam t - (1 - message lam t)) +
      t * message lam t * childH lam t := by linarith
  have hnonneg := mul_nonneg (sq_nonneg (childH lam t)) hbracket
  have hid : message lam t ^ 2 * childH lam t *
        ((logMass lam t + t * message lam t) / logMass lam t ^ 2) -
      2 * childH lam t ^ 2 * (childH lam t - (1 - message lam t)) =
      childH lam t ^ 2 * (message lam t -
        2 * (childH lam t - (1 - message lam t)) +
        t * message lam t * childH lam t) := by
    unfold childH
    field_simp [hf]
    ring
  linarith

/-- Exact normalized CA, valid even when its common total-division denominator
vanishes. Denominator positivity is required by the later comparison, not
silently assumed by this identity. -/
theorem CA_div_message {D lam y : ℝ} (hD : 0 < D) (hlam : 0 < lam)
    (hy : 0 < y) (t : ℝ) :
    CA D lam t y / message lam y =
      alpha D lam * (childRatio lam t + bp lam y) +
        gamma D lam * ell D lam y * childH lam t ^ 2 /
          (1 + ell D lam y * J lam t) := by
  have hp := (message_pos hlam y).ne'
  have hg := (gamma_pos hD hlam).ne'
  have hL : L D lam y = message lam y * gamma D lam * ell D lam y := by
    unfold ell
    field_simp [hp, hg]
  unfold CA
  rw [E_normalized hlam hy, Z_normalized hD hlam, hL]
  by_cases hz : 1 + ell D lam y * J lam t = 0
  · simp only [hz, mul_zero, div_zero, add_zero]
    unfold childRatio
    field_simp [hp] <;> ring
  · unfold childRatio childH
    field_simp [hp, hg, hz] <;> ring

/-- Exact ordinary t derivative. The positive dr/dt from above can be used to
turn this into the printed r derivative without an inverse-function theorem. -/
theorem CA_div_message_hasDerivAt {D lam y : ℝ}
    (hD : 0 < D) (hlam : 0 < lam) (hy : 0 < y) (t : ℝ)
    (hz : 1 + ell D lam y * J lam t ≠ 0) :
    HasDerivAt (fun s => CA D lam s y / message lam y)
      (alpha D lam * deriv (childRatio lam) t +
        gamma D lam * ell D lam y *
          (deriv (fun s => childH lam s ^ 2) t * (1 + ell D lam y * J lam t) -
            childH lam t ^ 2 * ell D lam y * deriv (J lam) t) /
              (1 + ell D lam y * J lam t) ^ 2) t := by
  have hr : (fun s => CA D lam s y / message lam y) =
      fun s => alpha D lam * (childRatio lam s + bp lam y) +
        gamma D lam * ell D lam y * childH lam s ^ 2 /
          (1 + ell D lam y * J lam s) := by
    funext s
    exact CA_div_message hD hlam hy s
  rw [hr]
  have hrd := (childRatio_hasDerivAt hlam t).differentiableAt.hasDerivAt
  have hsd := (childH_sq_hasDerivAt hlam t).differentiableAt.hasDerivAt
  have hjd := (J_hasDerivAt hlam t).differentiableAt.hasDerivAt
  apply (((hrd.add_const (bp lam y)).const_mul (alpha D lam)).add
    ((hsd.const_mul (gamma D lam * ell D lam y)).div
      ((hjd.const_mul (ell D lam y)).const_add 1) hz)).congr_deriv
  (try simp only [id_eq, Pi.pow_apply]) <;> ring

/-- One scalar conversion produces both printed coefficient budgets:
eta=delta=3/4 gives c=1; eta=1/2, delta=3/4 gives c=2/3. -/
theorem negative_child_weight_le {ellValue JValue eta delta c : ℝ}
    (hell : ellValue ≤ 0) (hellLower : -eta ≤ ellValue)
    (hdelta : 0 < delta) (hc : 0 ≤ c) (heta : eta = c * delta)
    (hden : delta ≤ 1 + ellValue * JValue) :
    0 ≤ -ellValue / (1 + ellValue * JValue) ∧
      -ellValue / (1 + ellValue * JValue) ≤ c := by
  have hd : 0 < 1 + ellValue * JValue := lt_of_lt_of_le hdelta hden
  constructor
  · exact div_nonneg (neg_nonneg.mpr hell) hd.le
  · apply (div_le_iff₀ hd).2
    have hm := mul_le_mul_of_nonneg_left hden hc
    rw [← heta] at hm
    linarith

/-- A conditional analytic reduction, not the completed cap theorem. The
three substantive later premises are the h0 upper bound, the normalized
negative weight bound, and the strict alpha/gamma budget. -/
theorem CA_deriv_pos_of_child_budget {D lam t y c : ℝ}
    (hD : 0 < D) (hlam : 0 < lam) (ht : 0 ≤ t) (hy : 0 < y)
    (hell : ell D lam y ≤ 0) (hden : 0 < 1 + ell D lam y * J lam t)
    (hc : 0 ≤ c)
    (hweight : -ell D lam y / (1 + ell D lam y * J lam t) ≤ c)
    (hupper : childH lam t ≤ 1 - message lam t / 2)
    (hbudget : gamma D lam * message lam t ^ 2 *
        (c * childH lam t + c ^ 2 * childH lam t ^ 2) < alpha D lam) :
    0 < deriv (fun s => CA D lam s y / message lam y) t := by
  let w := -ell D lam y / (1 + ell D lam y * J lam t)
  have hw0 : 0 ≤ w := div_nonneg (neg_nonneg.mpr hell) hden.le
  have hwc : w ≤ c := hweight
  have hw2 : w ^ 2 ≤ c ^ 2 := by nlinarith
  have hr := childRatio_deriv_pos hlam ht
  have hh := childH_pos hlam t
  have hs := childH_sq_deriv_le_childRatio hlam ht hupper
  have hj := J_deriv_le_childRatio hlam ht
  have hfac1 : 0 ≤ message lam t ^ 2 * childH lam t * deriv (childRatio lam) t := by
    positivity
  have hfac2 : 0 ≤ childH lam t ^ 2 * message lam t ^ 2 *
      deriv (childRatio lam) t := by positivity
  have hcost : w * deriv (fun s => childH lam s ^ 2) t +
      (w ^ 2 * childH lam t ^ 2) * deriv (J lam) t ≤
      message lam t ^ 2 * (c * childH lam t + c ^ 2 * childH lam t ^ 2) *
        deriv (childRatio lam) t := by
    calc
      _ ≤ w * (message lam t ^ 2 * childH lam t * deriv (childRatio lam) t) +
          (w ^ 2 * childH lam t ^ 2) * (message lam t ^ 2 * deriv (childRatio lam) t) :=
        add_le_add (mul_le_mul_of_nonneg_left hs hw0)
          (mul_le_mul_of_nonneg_left hj (mul_nonneg (sq_nonneg w) (sq_nonneg _)))
      _ = w * (message lam t ^ 2 * childH lam t * deriv (childRatio lam) t) +
          w ^ 2 * (childH lam t ^ 2 * message lam t ^ 2 * deriv (childRatio lam) t) := by ring
      _ ≤ c * (message lam t ^ 2 * childH lam t * deriv (childRatio lam) t) +
          c ^ 2 * (childH lam t ^ 2 * message lam t ^ 2 * deriv (childRatio lam) t) :=
        add_le_add (mul_le_mul_of_nonneg_right hwc hfac1)
          (mul_le_mul_of_nonneg_right hw2 hfac2)
      _ = _ := by ring
  have hid : deriv (fun s => CA D lam s y / message lam y) t =
      alpha D lam * deriv (childRatio lam) t - gamma D lam *
        (w * deriv (fun s => childH lam s ^ 2) t +
          (w ^ 2 * childH lam t ^ 2) * deriv (J lam) t) := by
    rw [(CA_div_message_hasDerivAt hD hlam hy t hden.ne').deriv]
    dsimp only [w]
    field_simp [hden.ne']
    ring
  have hg := gamma_pos hD hlam
  have hcost' := mul_le_mul_of_nonneg_left hcost hg.le
  calc
    0 < (alpha D lam - gamma D lam * message lam t ^ 2 *
        (c * childH lam t + c ^ 2 * childH lam t ^ 2)) * deriv (childRatio lam) t :=
      mul_pos (sub_pos.mpr hbudget) hr
    _ ≤ deriv (fun s => CA D lam s y / message lam y) t := by
      rw [hid]
      nlinarith only [hcost']

end Erdos993Lean.Analytic.V213.FreeCountVariance

#check Erdos993Lean.Analytic.V213.FreeCountVariance.childH_pos
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.childH_pos
#check Erdos993Lean.Analytic.V213.FreeCountVariance.childRatio_nonneg
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.childRatio_nonneg
#check Erdos993Lean.Analytic.V213.FreeCountVariance.childRatio_hasDerivAt
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.childRatio_hasDerivAt
#check Erdos993Lean.Analytic.V213.FreeCountVariance.childRatio_deriv_pos
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.childRatio_deriv_pos
#check Erdos993Lean.Analytic.V213.FreeCountVariance.childH_hasDerivAt
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.childH_hasDerivAt
#check Erdos993Lean.Analytic.V213.FreeCountVariance.childH_sq_hasDerivAt
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.childH_sq_hasDerivAt
#check Erdos993Lean.Analytic.V213.FreeCountVariance.J_hasDerivAt
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.J_hasDerivAt
#check Erdos993Lean.Analytic.V213.FreeCountVariance.J_deriv_le_childRatio
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.J_deriv_le_childRatio
#check Erdos993Lean.Analytic.V213.FreeCountVariance.childH_sq_deriv_le_childRatio
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.childH_sq_deriv_le_childRatio
#check Erdos993Lean.Analytic.V213.FreeCountVariance.CA_div_message
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.CA_div_message
#check Erdos993Lean.Analytic.V213.FreeCountVariance.CA_div_message_hasDerivAt
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.CA_div_message_hasDerivAt
#check Erdos993Lean.Analytic.V213.FreeCountVariance.negative_child_weight_le
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.negative_child_weight_le
#check Erdos993Lean.Analytic.V213.FreeCountVariance.CA_deriv_pos_of_child_budget
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.CA_deriv_pos_of_child_budget
