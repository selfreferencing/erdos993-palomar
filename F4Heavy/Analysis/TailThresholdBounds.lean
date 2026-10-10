module

public import F4Heavy.Analysis.TailDomain
public import F4Heavy.Analysis.TailFixedLogs
public import F4Heavy.Analysis.TailLogApproximation

@[expose] public section
set_option autoImplicit false

namespace F4Heavy.Analysis
open F4Unified

theorem tail_radius_parameters (r : Row) :
    0 ≤ tailRadius r ∧ tailRadius r < 1 ∧
      tailRadius r / (3 * (1 - tailRadius r)) ≤ tailEpsilon r := by
  cases r <;> norm_num [tailRadius, tailMid, tailEpsilon, rowData]

theorem tail_coordinate_bounds (r : Row) (lam : ℝ) (hr : InRow r lam) :
    -tailRadius r ≤ tailCoordinate r lam ∧ tailCoordinate r lam ≤ tailRadius r := by
  cases r <;> norm_num [InRow, rowData] at hr <;>
    norm_num [tailRadius, tailCoordinate, tailMid, rowData] <;>
    constructor <;> linarith only [hr.1, hr.2]

theorem tail_threshold_log_identity (r : Row) (lam : ℝ) (hr : InRow r lam) :
    tailTau r lam = Real.log (tailScale r * (1 + tailMid r)) + Real.log (1 + tailCoordinate r lam) := by
  have hm : 0 < 1 + tailMid r := by cases r <;> norm_num [tailMid, rowData]
  have hs := tail_scale_positive r
  have hv := tail_coordinate_bounds r lam hr
  have hrad := tail_radius_parameters r
  have hvp : 0 < 1 + tailCoordinate r lam := by linarith only [hv.1, hrad.2.1]
  unfold tailTau
  rw [show tailScale r * (1 + lam) = tailScale r * (1 + tailMid r) * (1 + tailCoordinate r lam) by
    unfold tailCoordinate
    field_simp
    <;> ring]
  exact Real.log_mul (ne_of_gt (mul_pos hs hm)) (ne_of_gt hvp)

theorem tail_threshold_bounds (r : Row) (lam : ℝ) (hr : InRow r lam) :
    tailTauLo r lam ≤ tailTau r lam ∧ tailTau r lam ≤ tailTauHi r lam := by
  have hp := tail_radius_parameters r
  have h := tail_log_quadratic_enclosure (tailRadius r) (tailEpsilon r) (tailCoordinate r lam)
    hp.1 hp.2.1 hp.2.2 (tail_coordinate_bounds r lam hr)
  have hm := tail_fixed_log_bracket r
  rw [tail_threshold_log_identity r lam hr]
  unfold tailTauLo tailTauHi
  constructor <;> linarith only [h.1, h.2, hm.1, hm.2]

end F4Heavy.Analysis
