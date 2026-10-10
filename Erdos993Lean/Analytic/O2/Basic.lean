module

public import Erdos993Lean.Analytic.O2.Defs

/-!
# O2: basic facts about the interface

Source: the O2 proof, §5 (the local
payment (11)), §6 (roots: "the test at `r = 1, t = 0` is conservative: it includes extra
nonpositive terms `−u(0)h z₋² − v(0)h z₊²`"), §7–§8 (the small-message and leaf cases).

* sign facts from `BandData.Guards` on the band: `uF`, `vF`, `sF`, `wF`, `ellF`, `price ≥ 0`;
  `hFun ≥ 0`;
* `phiRoot_eq`: `PhiRoot = Φ(r = 1, t = 0) + u(0) h z₋² + v(0) h z₊²`, hence `phiRoot_ge`;
* **`BandData.OK.phi_nonneg`**: from the three band propositions, `Φ ≥ 0` at every physical record
  (every real `z` if `p < q`, and `z = 1` at the leaf `p = q`); **`BandData.OK.phiRoot_nonneg`**.
-/

@[expose] public section

namespace Erdos993Lean.Analytic.O2

theorem hat_nonneg (y : ℝ) : 0 ≤ hat y := le_max_left _ _

theorem pwLin_nonneg {f : Fin 9 → ℝ} (hf : ∀ j, 0 ≤ f j) (x : ℝ) : 0 ≤ pwLin f x :=
  Finset.sum_nonneg fun j _ => mul_nonneg (hf j) (hat_nonneg _)

theorem lerp_nonneg {lo hi a b : ℚ} {lam : ℝ} (hlo : (lo : ℝ) ≤ lam) (hhi : lam ≤ hi)
    (ha : 0 ≤ a) (hb : 0 ≤ b) : 0 ≤ lerp lo hi a b lam := by
  have ha' : (0 : ℝ) ≤ a := by exact_mod_cast ha
  have hb' : (0 : ℝ) ≤ b := by exact_mod_cast hb
  unfold lerp
  rcases eq_or_lt_of_le (hlo.trans hhi) with heq | hlt
  · rw [← heq, sub_self, div_zero, zero_mul, add_zero]
    exact ha'
  · have hθ0 : 0 ≤ (lam - lo) / ((hi : ℝ) - lo) := div_nonneg (by linarith) (by linarith)
    have hθ1 : (lam - lo) / ((hi : ℝ) - lo) ≤ 1 := by
      rw [div_le_one (by linarith)]
      linarith
    nlinarith [mul_nonneg (sub_nonneg.2 hθ1) ha', mul_nonneg hθ0 hb']

theorem hFun_nonneg {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p < 1) : 0 ≤ hFun p := by
  unfold hFun
  refine div_nonneg hp0 ?_
  have := Real.log_nonpos (by linarith : (0 : ℝ) ≤ 1 - p) (by linarith)
  linarith

namespace BandData

variable {b : BandData} {lam : ℝ}

theorem Guards.lo_pos (hg : b.Guards) : 0 < b.lo := hg.1

theorem Guards.gamma_nonneg (hg : b.Guards) : 0 ≤ b.gamma := hg.2.2.1

theorem Guards.xmin_pos (hg : b.Guards) : 0 < b.xmin := hg.2.2.2.1

theorem InBand.pos (hg : b.Guards) (hlam : b.InBand lam) : 0 < lam :=
  lt_of_lt_of_le (by exact_mod_cast hg.lo_pos) hlam.1

theorem uF_nonneg (hg : b.Guards) (hlam : b.InBand lam) (p : ℝ) : 0 ≤ b.uF lam p := by
  obtain ⟨-, -, -, -, -, hl, hr, -⟩ := hg
  exact pwLin_nonneg (fun j => lerp_nonneg hlam.1 hlam.2 (hl j) (hr j)) _

theorem vF_nonneg (hg : b.Guards) (hlam : b.InBand lam) (p : ℝ) : 0 ≤ b.vF lam p := by
  obtain ⟨-, -, -, -, -, -, -, hl, hr, -⟩ := hg
  exact pwLin_nonneg (fun j => lerp_nonneg hlam.1 hlam.2 (hl j) (hr j)) _

theorem sF_nonneg (hg : b.Guards) (hlam : b.InBand lam) (p : ℝ) : 0 ≤ b.sF lam p := by
  obtain ⟨-, -, -, -, -, -, -, -, -, hl, hr, -⟩ := hg
  exact pwLin_nonneg (fun j => lerp_nonneg hlam.1 hlam.2 (hl j) (hr j)) _

theorem wF_nonneg (hg : b.Guards) (hlam : b.InBand lam) : 0 ≤ b.wF lam := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hl, hr, -⟩ := hg
  exact lerp_nonneg hlam.1 hlam.2 hl hr

theorem ellF_nonneg (hg : b.Guards) (hlam : b.InBand lam) : 0 ≤ b.ellF lam := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, hl, hr⟩ := hg
  exact lerp_nonneg hlam.1 hlam.2 hl hr

theorem price_nonneg (hg : b.Guards) (hlam : b.InBand lam) : 0 ≤ b.price lam := by
  unfold price
  have := hlam.pos hg
  exact div_nonneg (by exact_mod_cast hg.gamma_nonneg) (by linarith)

/-- The root payment is `Φ` at `r = 1`, `t = 0` plus the fictitious root test charges. -/
theorem phiRoot_eq (b : BandData) (lam p z : ℝ) :
    b.PhiRoot lam p z = b.Phi lam p 1 0 z + b.uF lam 0 * hFun p * (max (-z) 0) ^ 2 +
      b.vF lam 0 * hFun p * (max z 0) ^ 2 := by
  unfold PhiRoot Phi Ru Rv Rs Rtau
  ring

/-- **The root test at `r = 1, t = 0` is conservative**: `PhiRoot ≥ Φ(r = 1, t = 0)`. -/
theorem phiRoot_ge (hg : b.Guards) (hlam : b.InBand lam) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p < 1)
    (z : ℝ) : b.Phi lam p 1 0 z ≤ b.PhiRoot lam p z := by
  rw [phiRoot_eq]
  have h1 := mul_nonneg (mul_nonneg (b.uF_nonneg hg hlam 0) (hFun_nonneg hp0 hp1))
    (sq_nonneg (max (-z) 0))
  have h2 := mul_nonneg (mul_nonneg (b.vF_nonneg hg hlam 0) (hFun_nonneg hp0 hp1))
    (sq_nonneg (max z 0))
  linarith

/-- **The local payment is nonnegative at every physical record**, from the three band
propositions: the certified cover (`xmin·q ≤ p < q`), the small messages (`p < xmin·q`), and the
leaf (`p = q`, where only `z = 1` is physical). -/
theorem OK.phi_nonneg (hok : b.OK) (hlam : b.InBand lam) {p r t z : ℝ}
    (hrec : PhysRecord lam p r t) (hz : p = actQ lam → z = 1) : 0 ≤ b.Phi lam p r t z := by
  rcases lt_or_eq_of_le hrec.2.1 with hp | hp
  · by_cases hs : p < b.xmin * actQ lam
    · exact hok.small lam hlam p r t z hrec hs
    · exact hok.pay lam hlam p r t z hrec (not_lt.mp hs) hp
  · have hz1 := hz hp
    subst hz1
    rw [hp] at hrec ⊢
    exact hok.leaf lam hlam r t hrec

/-- **The root payment is nonnegative** at every root record `(p, z)` (`0 < p ≤ q`, and `z = 1`
if `p = q`). -/
theorem OK.phiRoot_nonneg (hok : b.OK) (hlam : b.InBand lam) {p z : ℝ} (hp0 : 0 < p)
    (hpq : p ≤ actQ lam) (hz : p = actQ lam → z = 1) : 0 ≤ b.PhiRoot lam p z := by
  have hl := hlam.pos hok.guards
  have hq1 : actQ lam < 1 := by unfold actQ; rw [div_lt_one (by linarith)]; linarith
  have hrec : PhysRecord lam p 1 0 := by
    refine ⟨hp0, hpq, le_rfl, by norm_num, ?_, by norm_num⟩
    have h1p : 0 < 1 - p := by linarith
    exact div_nonneg (mul_nonneg hl.le h1p.le) (by nlinarith)
  exact le_trans (hok.phi_nonneg hlam hrec hz) (phiRoot_ge hok.guards hlam hp0.le (by linarith) z)

end BandData

end Erdos993Lean.Analytic.O2
