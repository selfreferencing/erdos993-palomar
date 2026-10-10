module

public import Erdos993Lean.Analytic.V213.FiberRaySupportingLine
public import Erdos993Lean.Analytic.V213.FiberRayLoss
public import Erdos993Lean.Analytic.V213.FiberRayDefinitions

/-!
Transport of the actual negative upper-offset supporting line to
H_r(N). The reciprocal loss, N Delta bonus and signed combined loss
remain separate until each literal Eq93 bound has been applied.
-/

@[expose] public section
namespace Erdos993Lean.Analytic.V213
open Erdos993Lean.Analytic.V22 Erdos993Lean.Analytic.V22.Analysis

theorem fiber_ray_negative_transport (id : FiberRayIdentity) {M : ℕ} {q mu ra : ℝ}
    (hMf : lowMeanFractionReal (fiberRayById id).m_f ≤ (M : ℝ))
    (hq0 : 1 / 2 ≤ q) (hqh : q ≤ 3 / 4) (hmu : 0 < mu)
    (hra : 0 ≤ ra) (har : ra ≤ fiberSkew q)
    (hrR : fiberSkew q ≤ lowMeanFractionReal (fiberRayById id).R)
    (ht0 : 1 / 3 ≤ (M : ℝ) / mu) (ht1 : (M : ℝ) / mu ≤ 3 / 5)
    (j : ℤ) (hw : fiberBonus q M ≤ fiberSquareOffset q M j)
    (hω : fiberUpperOmega mu (fiberSkew q) (M + 2) < 0) :
    mu * (fiberF q mu M j - fiberPsi ((M : ℝ) / mu)) ≥
      (M : ℝ) * fiberTaylorS ((M : ℝ) / mu) -
        fiberRayH id ((M : ℝ) / mu) ra (fiberSkew q) ((M : ℝ) + 2) := by
  let N : ℝ := (M : ℝ) + 2
  let r := fiberSkew q
  let t := (M : ℝ) / mu
  let R := lowMeanFractionReal (fiberRayById id).R
  let rf := lowMeanFractionReal (fiberRayById id).rho_f
  let kf := lowMeanFractionReal (fiberRayById id).k_f
  let df := lowMeanFractionReal (fiberRayById id).d_f
  let mf := lowMeanFractionReal (fiberRayById id).m_f
  let ωt := 5 / 2 * Real.log t
  let ωT := fiberTemplateOmega mu (M + 2) (fiberUpperPrefactor (M + 2))
  let ωU := fiberUpperOmega mu r (M + 2)
  let ζ := r * Real.sqrt N
  have hg := fiber_ray_record_guards id
  dsimp at hg
  rcases hg with ⟨hR,hRh,hNf,hNeq,hcap,hrf,hbf,hdf,hs0,hv0,hgap0⟩
  have hmf : 8 ≤ mf := by dsimp [mf]; linarith only [hNf,hNeq]
  have hM8 : (8 : ℝ) ≤ M := hmf.trans hMf
  have hM : 8 ≤ M := by exact_mod_cast hM8
  have hNf' : mf + 2 ≤ N := by dsimp [mf,N]; linarith only [hMf]
  have hc := fiber_ray_records_all_real id hNf'
  dsimp at hc
  have hN : 10 ≤ N := by dsimp [N]; linarith only [hM8]
  have hNp : 0 < N := by linarith only [hN]
  have ht : 0 < t := by dsimp [t]; linarith only [ht0]
  have hth : t < 1 := by dsimp [t]; linarith only [ht1]
  have hr : 0 ≤ r := by dsimp [r,fiberSkew]; linarith only [hq0]
  have hrh : r ≤ 1 / 2 := by dsimp [r,fiberSkew]; linarith only [hqh]
  have hRh' : R ≤ 1 / 2 := by dsimp [R]; linarith only [hRh]
  have hρs : 0 < rhoStar N R := hrf.trans_le hc.1
  have hkf : 0 ≤ kf := by cases id <;> norm_num [kf,fiberRayById,lowMeanFractionReal]
  have hζ : 0 ≤ ζ := by dsimp [ζ]; positivity
  have hζ6 : ζ ≤ 6 := by
    by_contra h
    have hp := fiber_large_activity_upper_omega_pos hmu hM hr hrh
      (le_of_lt (lt_of_not_ge h)) (by linarith only [ht0])
    exact (not_lt_of_ge hp.le) hω
  have hTpl := fiber_ray_template_negative hM hmu ht1
  change ωt ≤ ωT ∧ ωT < 0 at hTpl
  have hGU : ωt < ωU := fiber_uniform_upper_omega_strict hmu hM hr hrh
  have hGT : G ωT ≤ G ωt := shared_G_antitoneOn_nonpos
    (by exact le_trans hTpl.1 hTpl.2.le) hTpl.2.le hTpl.1
  have hσ : |G1 ωU| ≤ |G1 ωt| := by
    have hu := shared_G1_strictMono hω
    have ht' := shared_G1_strictMono (hGU.trans hω)
    have hm := shared_G1_monotone hGU.le
    rw [shared_G1_zero] at hu ht'
    rw [abs_of_nonpos hu.le,abs_of_nonpos ht'.le]
    linarith only [hm]
  have hrec := fiber_upper_reciprocal_loss hN hr hrR hRh' hρs
  have hκ := mul_le_mul_of_nonneg_right hc.2.2.1 (sq_nonneg ζ)
  have hnum : 0 ≤ 4 * ζ + kf * ζ ^ 2 := by positivity
  have hcoef : 2 * N * ((rhoU r N)⁻¹ - (rho N)⁻¹) ≤
      (4 * ζ + kf * ζ ^ 2) / rf := by
    exact hrec.trans ((div_le_div_of_nonneg_right
      (add_le_add (le_refl (4 * ζ)) hκ) hρs.le).trans
      (div_le_div_of_nonneg_left hnum hrf hc.1))
  have hrecG : 2 * N * ((rhoU r N)⁻¹ - (rho N)⁻¹) * G ωT ≤
      (4 * ζ + kf * ζ ^ 2) * G ωt / rf := by
    have h := (mul_le_mul_of_nonneg_right hcoef (shared_G_nonneg ωT)).trans
      (mul_le_mul_of_nonneg_left hGT (div_nonneg hnum hrf.le))
    convert h using 1 <;> ring
  have hbonus := fiber_activity_interval_bonus hN hra har hrh
  have hbonus' : fiberRayDelta ra * (N - 1) * ζ ^ 2 ≤ N * Delta r N := by
    convert hbonus using 1 <;> simp only [fiberRayDelta,div_eq_mul_inv] <;> ring
  have hL := fiber_ray_combined_loss_bound id hNf' hr hrR hζ6
  have hloss : |G1 ωU| * (2 * N * eU r N / rhoU r N - N * Delta r N) ≤
      df * |G1 ωt| := by
    calc
      _ ≤ |G1 ωU| * df := mul_le_mul_of_nonneg_left hL (abs_nonneg _)
      _ ≤ _ := by simpa only [mul_comm] using mul_le_mul_of_nonneg_left hσ hdf.le
  have hT := fiber_ray_taylor_bound ht hth hmf hMf
  have hbase := fiber_ray_supporting_line hM hq0 hqh hmu j hw hω
  dsimp at hbase
  have hroot := fiber_ray_root_identity ht hth
  have hsq := Real.sq_sqrt hNp.le
  have hid : (M : ℝ) * fiberTaylorS t + 2 - 6 * G ωt + 71 / 10 * |G1 ωt| -
      fiberRayCF mf * G2 ωt - (4 * ζ + kf * ζ ^ 2) * G ωt / rf +
      fiberRayDelta ra * (N - 1) * ζ ^ 2 - df * |G1 ωt| =
      (M : ℝ) * fiberTaylorS t - fiberRayH id t ra r N := by
    unfold fiberRayH fiberRayHPolynomial fiberRayC fiberRayA fiberRayK
    change _ = _
    dsimp [ζ,rf,kf,df,mf,ωt]
    simp only [mul_pow,hsq]
    linear_combination hroot
  have hfin : (M : ℝ) * fiberTaylorS t - fiberRayH id t ra r N ≤
      mu * (fiberF q mu M j - fiberPsi t) := by
    linarith only [hbase,hT,hrecG,hbonus',hloss,hid]
  exact hfin

end Erdos993Lean.Analytic.V213
