module

public import Erdos993Lean.Analytic.V213.ZeroTiltLaplaceDefs
public import Erdos993Lean.Analytic.Tail.Boundary

/-!
Mobius/boundary part of current Lemma 4.2. The old
generic Boundary theorem has exactly the current w and the same printed
one-variable derivative proof; only its scalar a=1 instance is reused.
No old rate, cap, profile, or finite data is imported or substituted.

-/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.ZeroTiltLaplace

open Real Set

noncomputable def mobius (q p : ℝ) : ℝ := q*(1-p)/(1-q*p)
noncomputable def p0 (q : ℝ) : ℝ := q/(1+q)
noncomputable def wMinus (q : ℝ) : ℝ := q*(1+q)/(1+2*q)
noncomputable def wPlus (q : ℝ) : ℝ := q/(1+q-q^2)

theorem kappa_facts {lam : ℝ} (hlam : 0 < lam) :
    1 < kappa lam ∧ (kappa lam)^2-kappa lam = lam ∧ w lam = 1-1/kappa lam := by
  obtain ⟨h1, h2, hw, _⟩ := Tail.alpha_facts hlam
  exact ⟨h1, h2, hw⟩

theorem w_pos_lt_one {lam : ℝ} (hlam : 0 < lam) : 0 < w lam ∧ w lam < 1 := by
  obtain ⟨hk, _, hw⟩ := kappa_facts hlam
  have hk0 : 0 < kappa lam := by linarith
  have hi : 0 < 1/kappa lam := div_pos (by norm_num) hk0
  have hi1 : 1/kappa lam < 1 := (div_lt_one hk0).2 hk
  rw [hw]
  constructor <;> linarith

theorem w_quadratic {lam : ℝ} (hlam : 0 < lam) : lam*(1-w lam)^2 = w lam := by
  obtain ⟨hk, he, hw⟩ := kappa_facts hlam
  have hk0 : kappa lam ≠ 0 := by linarith
  rw [hw]
  field_simp [hk0]
  nlinarith [he]

theorem w_mobius_equation {lam : ℝ} (hlam : 0 < lam) :
    q lam*(1-w lam+(w lam)^2) = w lam := by
  have hh := w_quadratic hlam
  have hd : 1+lam ≠ 0 := by positivity
  unfold q
  field_simp [hd]
  nlinarith

theorem w_le_q {lam : ℝ} (hlam : 0 < lam) : w lam ≤ q lam := by
  have hw := w_pos_lt_one hlam
  have hq := q_pos hlam
  have he := w_mobius_equation hlam
  have hh : 0 ≤ q lam*w lam*(1-w lam) :=
    mul_nonneg (mul_nonneg hq.le hw.1.le) (sub_nonneg.mpr hw.2.le)
  nlinarith

theorem mobius_den_pos {q x : ℝ} (hq0 : 0 < q) (hq1 : q < 1)
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1) : 0 < 1-q*x := by
  have hh := mul_le_mul_of_nonneg_left hx1 hq0.le
  linarith

theorem mobius_antitone {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) :
    AntitoneOn (mobius q) (Icc 0 1) := by
  intro x hx y hy hxy
  unfold mobius
  apply (div_le_div_iff₀ (mobius_den_pos hq0 hq1 hy.1 hy.2)
    (mobius_den_pos hq0 hq1 hx.1 hx.2)).2
  have hh : 0 ≤ q*(1-q)*(y-x) := by
    exact mul_nonneg (mul_nonneg hq0.le (by linarith)) (sub_nonneg.mpr hxy)
  nlinarith

theorem mobius_w {lam : ℝ} (hlam : 0 < lam) : mobius (q lam) (w lam) = w lam := by
  have hw := w_pos_lt_one hlam
  have he := w_mobius_equation hlam
  have hd := mobius_den_pos (q_pos hlam) (q_lt_one hlam) hw.1.le hw.2.le
  unfold mobius
  apply (div_eq_iff hd.ne').2
  nlinarith

theorem p0_domain {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) : 0 < p0 q ∧ p0 q < 1 := by
  unfold p0
  refine ⟨by positivity, (div_lt_one (by positivity)).2 ?_⟩
  linarith

theorem wPlus_domain {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) :
    0 < wPlus q ∧ wPlus q < 1 := by
  have hs : 0 < q*(1-q) := mul_pos hq0 (by linarith)
  have hd : 0 < 1+q-q^2 := by nlinarith
  have hsq : q^2 < 1 := by
    nlinarith [mul_pos (show 0 < 1-q by linarith) (show 0 < 1+q by linarith)]
  unfold wPlus
  refine ⟨div_pos hq0 hd, (div_lt_one hd).2 ?_⟩
  linarith

theorem mobius_q {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) : mobius q q = p0 q := by
  have hd := (mobius_den_pos hq0 hq1 hq0.le hq1.le).ne'
  have hp : 1+q ≠ 0 := by positivity
  unfold mobius p0
  apply (div_eq_div_iff hd hp).2
  ring

theorem mobius_p0 {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) : mobius q (p0 q) = wPlus q := by
  have hp := p0_domain hq0 hq1
  have hd := (mobius_den_pos hq0 hq1 hp.1.le hp.2.le).ne'
  have hq : 1+q ≠ 0 := by positivity
  have hh : 1+q-q^2 ≠ 0 := by
    have := mul_pos hq0 (show 0 < 1-q by linarith)
    nlinarith
  unfold mobius p0 wPlus at *
  field_simp [hd, hq, hh] <;> ring

theorem mobius_wPlus {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) : mobius q (wPlus q) = wMinus q := by
  have hp := wPlus_domain hq0 hq1
  have hd := (mobius_den_pos hq0 hq1 hp.1.le hp.2.le).ne'
  have hq : 1+2*q ≠ 0 := by positivity
  have hh : 1+q-q^2 ≠ 0 := by
    have := mul_pos hq0 (show 0 < 1-q by linarith)
    nlinarith
  unfold mobius wPlus wMinus at *
  apply (div_eq_div_iff hd hq).2
  field_simp [hh] <;> ring

theorem w_mobius_bounds {lam : ℝ} (hlam : 0 < lam) :
    p0 (q lam) ≤ w lam ∧ wMinus (q lam) ≤ w lam ∧ w lam ≤ wPlus (q lam) := by
  have hq0 := q_pos hlam
  have hq1 := q_lt_one hlam
  have hw := w_pos_lt_one hlam
  have hwq := w_le_q hlam
  have hp0 := p0_domain hq0 hq1
  have hp1 := wPlus_domain hq0 hq1
  have hanti := mobius_antitone hq0 hq1
  have hlo := hanti ⟨hw.1.le, hw.2.le⟩ ⟨hq0.le, hq1.le⟩ hwq
  rw [mobius_q hq0 hq1, mobius_w hlam] at hlo
  have hhi := hanti ⟨hp0.1.le, hp0.2.le⟩ ⟨hw.1.le, hw.2.le⟩ hlo
  rw [mobius_p0 hq0 hq1, mobius_w hlam] at hhi
  have hl2 := hanti ⟨hw.1.le, hw.2.le⟩ ⟨hp1.1.le, hp1.2.le⟩ hhi
  rw [mobius_wPlus hq0 hq1, mobius_w hlam] at hl2
  exact ⟨hlo, hl2, hhi⟩

theorem wPlus_lt_three_fifths {q : ℝ} (hq : QDomain q) : wPlus q < 3/5 := by
  have hq0 : 0 < q := by linarith [hq.1]
  have hq1 : q < 1 := by linarith [hq.2]
  have hs := pow_le_pow_left₀ hq0.le hq.2 2
  have hd : 0 < 1+q-q^2 := by
    have := mul_pos hq0 (show 0 < 1-q by linarith)
    nlinarith
  unfold wPlus
  apply (div_lt_iff₀ hd).2
  nlinarith [hq.2]

theorem Bplus_eq_ThatPlus {lam t : ℝ} (hlam : 0 < lam) (ht : 0 < t) :
    Bplus lam t = Tail.ThatPlus lam t := by
  rw [Tail.ThatPlus, Tail.That_eq hlam ht]
  rfl

/-- Generic boundary lemma, specialized at its scalar a=1.
This theorem deliberately excludes t=0, where the current Pi is assigned0. -/
theorem Pi_ge_f {lam t : ℝ} (h : ActivityDomain lam) (ht : 0 < t) : f lam t ≤ Pi lam t := by
  have hlam : 0 < lam := by linarith [h.1]
  have hh := Tail.boundary_lemma (a := 1) hlam (by linarith [h.2]) (by norm_num) ht
  rw [Tail.Lf_pC hlam] at hh
  rw [Pi_positive_argument ht, Bplus_eq_ThatPlus hlam ht]
  change log (1+lam*exp (-t)) ≤ (1-Tail.rK lam)*t+Tail.rK lam*Tail.ThatPlus lam t
  nlinarith

/-- Nonleaf statement only; no conclusion H(q)>=b(q) is asserted or needed. -/
theorem H_ge_b {lam p : ℝ} (h : ActivityDomain lam) (hp : 0 < p) (hpq : p < q lam) :
    b p ≤ H lam p := by
  have hlam : 0 < lam := by linarith [h.1]
  have hY := Y_positive hlam hp hpq
  have hw := w_pos_lt_one hlam
  have hh := Pi_ge_f h hY
  rw [f_Y_eq_b hlam hp hpq] at hh
  rw [H_eq_Pi_add hlam hp hpq]
  have hn : 0 ≤ w lam*Y lam p := mul_nonneg hw.1.le hY.le
  linarith

end Erdos993Lean.Analytic.V213.ZeroTiltLaplace

-- Audit commands.
#check Erdos993Lean.Analytic.V213.ZeroTiltLaplace.kappa_facts
#print axioms Erdos993Lean.Analytic.V213.ZeroTiltLaplace.kappa_facts
#check Erdos993Lean.Analytic.V213.ZeroTiltLaplace.w_pos_lt_one
#print axioms Erdos993Lean.Analytic.V213.ZeroTiltLaplace.w_pos_lt_one
#check Erdos993Lean.Analytic.V213.ZeroTiltLaplace.w_quadratic
#print axioms Erdos993Lean.Analytic.V213.ZeroTiltLaplace.w_quadratic
#check Erdos993Lean.Analytic.V213.ZeroTiltLaplace.w_mobius_equation
#print axioms Erdos993Lean.Analytic.V213.ZeroTiltLaplace.w_mobius_equation
#check Erdos993Lean.Analytic.V213.ZeroTiltLaplace.w_le_q
#print axioms Erdos993Lean.Analytic.V213.ZeroTiltLaplace.w_le_q
#check Erdos993Lean.Analytic.V213.ZeroTiltLaplace.mobius_den_pos
#print axioms Erdos993Lean.Analytic.V213.ZeroTiltLaplace.mobius_den_pos
#check Erdos993Lean.Analytic.V213.ZeroTiltLaplace.mobius_antitone
#print axioms Erdos993Lean.Analytic.V213.ZeroTiltLaplace.mobius_antitone
#check Erdos993Lean.Analytic.V213.ZeroTiltLaplace.mobius_w
#print axioms Erdos993Lean.Analytic.V213.ZeroTiltLaplace.mobius_w
#check Erdos993Lean.Analytic.V213.ZeroTiltLaplace.p0_domain
#print axioms Erdos993Lean.Analytic.V213.ZeroTiltLaplace.p0_domain
#check Erdos993Lean.Analytic.V213.ZeroTiltLaplace.wPlus_domain
#print axioms Erdos993Lean.Analytic.V213.ZeroTiltLaplace.wPlus_domain
#check Erdos993Lean.Analytic.V213.ZeroTiltLaplace.mobius_q
#print axioms Erdos993Lean.Analytic.V213.ZeroTiltLaplace.mobius_q
#check Erdos993Lean.Analytic.V213.ZeroTiltLaplace.mobius_p0
#print axioms Erdos993Lean.Analytic.V213.ZeroTiltLaplace.mobius_p0
#check Erdos993Lean.Analytic.V213.ZeroTiltLaplace.mobius_wPlus
#print axioms Erdos993Lean.Analytic.V213.ZeroTiltLaplace.mobius_wPlus
#check Erdos993Lean.Analytic.V213.ZeroTiltLaplace.w_mobius_bounds
#print axioms Erdos993Lean.Analytic.V213.ZeroTiltLaplace.w_mobius_bounds
#check Erdos993Lean.Analytic.V213.ZeroTiltLaplace.wPlus_lt_three_fifths
#print axioms Erdos993Lean.Analytic.V213.ZeroTiltLaplace.wPlus_lt_three_fifths
#check Erdos993Lean.Analytic.V213.ZeroTiltLaplace.Bplus_eq_ThatPlus
#print axioms Erdos993Lean.Analytic.V213.ZeroTiltLaplace.Bplus_eq_ThatPlus
#check Erdos993Lean.Analytic.V213.ZeroTiltLaplace.Pi_ge_f
#print axioms Erdos993Lean.Analytic.V213.ZeroTiltLaplace.Pi_ge_f
#check Erdos993Lean.Analytic.V213.ZeroTiltLaplace.H_ge_b
#print axioms Erdos993Lean.Analytic.V213.ZeroTiltLaplace.H_ge_b
