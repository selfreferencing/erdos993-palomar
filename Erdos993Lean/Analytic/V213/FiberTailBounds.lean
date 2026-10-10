module

public import Erdos993Lean.Analytic.V213.FiberTailCheck
public import Erdos993Lean.Analytic.V213.FiberWindowWeightPrice

/-!
Actual strict tail prices from all thirteen Eq104 rows.
The complete log trees feed positive gap consumers, then actual exp/log
identities turn squared rational arguments into the printed prices.
Full input routing remains separate.
-/

@[expose] public section
namespace Erdos993Lean.Analytic.V213

theorem fiber_tail_scalar_identities (id : FiberTailIdentity) :
    let r := fiberTailById id
    fiberTailA id = lowMeanFractionReal r.A_t ∧
    fiberTailB id = lowMeanFractionReal r.B_t ∧
    fiberTailXA id = lowMeanFractionReal r.x_a ∧
    fiberTailXS id = lowMeanFractionReal r.x_s ∧
    fiberTailYA id = lowMeanFractionReal r.y_a ∧
    fiberTailYS id = lowMeanFractionReal r.y_s := by
  cases id <;> norm_num [fiberTailA,fiberTailB,fiberTailXA,fiberTailXS,fiberTailYA,fiberTailYS,
    fiberTailById,fiberWeightById,lowMeanFractionReal]

theorem fiber_tail_positive_parameters (id : FiberTailIdentity) :
    let r := fiberTailById id
    0 < fiberTailA id ∧ 0 < fiberTailB id ∧ 0 < lowMeanFractionReal r.mu ∧
      0 < lowMeanFractionReal r.m ∧ 0 < lowMeanFractionReal r.Z_a ∧
      0 < lowMeanFractionReal r.Z_small := by
  have h := fiber_tail_scalar_identities id
  rw [h.1,h.2.1]
  cases id <;> norm_num [fiberTailById,lowMeanFractionReal]

theorem fiber_tail_small_log_strict (id : FiberTailIdentity) :
    Real.log (fiberTailYA id) < 2*fiberTailXA id := by
  have hf := fiber_tail_facts id .smallLog
  rcases hf.1 with ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,heps,_,hgap,_,_⟩
  rw [heps] at hgap
  have hvalid : lowMeanFractionValid (fiberTailById id).gap_a := by cases id <;> decide +kernel
  have hg := (lowMean_fraction_le_iff (by decide +kernel : lowMeanFractionValid (1,100)) hvalid).mp hgap
  have hv := fiber_tail_value_recorded id .smallGap
  dsimp [fiberTailValue,fiberTailRecordedValue] at hv
  have hy : lowMeanFractionValid (fiberTailById id).y_a := by cases id <;> decide +kernel
  have hd := (lowMean_fraction_le_iff (by norm_num [lowMeanFractionValid]) hy).mp hf.2.1
  simp only [lowMeanFractionReal,Int.cast_pow,Int.cast_ofNat,Nat.cast_one,div_one] at hd
  change (2 : ℝ)^(fiberTailById id).n_a ≤ lowMeanFractionReal (fiberTailById id).y_a at hd
  rw [← (fiber_tail_scalar_identities id).2.2.2.2.1] at hd
  have hl := fiber_dyadic_log_bound (fiberTailById id).n_a hd
  rw [show lowMeanFractionReal (1,100) = (1/100 : ℝ) by norm_num [lowMeanFractionReal]] at hg
  linarith only [hg,hv,hl]

theorem fiber_tail_large_log_strict (id : FiberTailIdentity) :
    Real.log (fiberTailYS id) < 2*fiberTailXS id := by
  have hf := fiber_tail_facts id .largeLog
  rcases hf.1 with ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,heps,_,hgap,_⟩
  rw [heps] at hgap
  have hvalid : lowMeanFractionValid (fiberTailById id).gap_s := by cases id <;> decide +kernel
  have hg := (lowMean_fraction_le_iff (by decide +kernel : lowMeanFractionValid (1,1000)) hvalid).mp hgap
  have hv := fiber_tail_value_recorded id .largeGap
  dsimp [fiberTailValue,fiberTailRecordedValue] at hv
  have hy : lowMeanFractionValid (fiberTailById id).y_s := by cases id <;> decide +kernel
  have hd := (lowMean_fraction_le_iff (by norm_num [lowMeanFractionValid]) hy).mp hf.2.2.2.1
  simp only [lowMeanFractionReal,Int.cast_pow,Int.cast_ofNat,Nat.cast_one,div_one] at hd
  change (2 : ℝ)^(fiberTailById id).n_s ≤ lowMeanFractionReal (fiberTailById id).y_s at hd
  rw [← (fiber_tail_scalar_identities id).2.2.2.2.2] at hd
  have hl := fiber_dyadic_log_bound (fiberTailById id).n_s hd
  rw [show lowMeanFractionReal (1,1000) = (1/1000 : ℝ) by norm_num [lowMeanFractionReal]] at hg
  linarith only [hg,hv,hl]

theorem fiber_tail_squared_log_price {A mu Z x : ℝ}
    (hA : 0 < A) (hmu : 0 < mu) (hZ : 0 < Z)
    (h : Real.log (A^2*mu^3/Z^2) < 2*x) :
    A*mu^(3/2 : ℝ)*Real.exp (-x) < Z := by
  have hp := Real.rpow_pos_of_pos hmu (3/2 : ℝ)
  have hl : Real.log (A*mu^(3/2 : ℝ)/Z) < x := by
    rw [Real.log_div (mul_ne_zero hA.ne' hp.ne') hZ.ne',Real.log_mul hA.ne' hp.ne',Real.log_rpow hmu]
    rw [Real.log_div (mul_ne_zero (pow_ne_zero _ hA.ne') (pow_ne_zero _ hmu.ne'))
      (pow_ne_zero _ hZ.ne'),Real.log_mul (pow_ne_zero _ hA.ne') (pow_ne_zero _ hmu.ne'),
      Real.log_pow,Real.log_pow,Real.log_pow] at h
    norm_num at h ⊢
    linarith only [h]
  have hh := fiber_discount_log_lt (mul_pos hA hp) hZ hl
  nlinarith only [hh]

theorem fiber_tail_printed_prices (id : FiberTailIdentity) :
    let r := fiberTailById id
    fiberTailA id*(lowMeanFractionReal r.mu)^(3/2 : ℝ)*Real.exp (-fiberTailXA id) <
      lowMeanFractionReal r.Z_a ∧
    fiberTailB id*(lowMeanFractionReal r.m)^(3/2 : ℝ)*Real.exp (-fiberTailXS id) <
      lowMeanFractionReal r.Z_small := by
  have hp := fiber_tail_positive_parameters id
  exact ⟨fiber_tail_squared_log_price hp.1 hp.2.2.1 hp.2.2.2.2.1 (fiber_tail_small_log_strict id),
    fiber_tail_squared_log_price hp.2.1 hp.2.2.2.1 hp.2.2.2.2.2 (fiber_tail_large_log_strict id)⟩

end Erdos993Lean.Analytic.V213
