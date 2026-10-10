module

public import Erdos993Lean.Analytic.V213.FiberWindowInputGuards
public import Erdos993Lean.Analytic.V213.FiberCornerBounds

/-!
Actual seventeen-input window associations and five ordinary class
corner transfers. All endpoints/rates/means come from the actual F06
interface. The finite comparisons feed whole-interval logarithm bounds.
C1/C2 are deliberately left to the coupled-rate theorem.

-/

@[expose] public section
namespace Erdos993Lean.Analytic.V213

def fiberWindowInputRoutingTests (id : FiberWindowInputIdentity) : Prop :=
  let r := fiberInputRouteById (fiberWindowInput id)
  fiberInputOuterClass r.kind = some (fiberWindowInputClass id) ∧
  r.windows = (fiberWindowInputWindows id).map (fun wid => fiberWindowIndex wid+1)

instance fiberWindowInputRoutingTestsDecidable (id : FiberWindowInputIdentity) :
    Decidable (fiberWindowInputRoutingTests id) := by unfold fiberWindowInputRoutingTests; infer_instance

def fiberWindowInputCornerTests (id : FiberWindowInputIdentity) : Prop :=
  match fiberWindowInputCorner id with
  | none => True
  | some cid =>
    let c := fiberWindowCornerById cid
    let r := fiberInputRouteById (fiberWindowInput id)
    let log := fiberCornerLogById (fiberWindowInputLog id)
    c.outerClass = fiberWindowInputClass id ∧
    lowMeanFractionValid c.mu_c ∧ lowMeanFractionValid c.ell_c ∧ lowMeanFractionValid c.L_c ∧
    lowMeanFractionValid r.mu0 ∧ lowMeanFractionValid r.ell0 ∧
    lowMeanFractionValid (fiberInputHiFraction (fiberWindowInput id)) ∧ lowMeanFractionValid log.y ∧
    c.L_c = log.L ∧ lowMeanFractionLE c.mu_c r.mu0 ∧ lowMeanFractionLE c.ell_c r.ell0 ∧
    lowMeanFractionLE (lowMeanFractionAdd (1,1) (fiberInputHiFraction (fiberWindowInput id))) log.y

instance fiberWindowInputCornerTestsDecidable (id : FiberWindowInputIdentity) :
    Decidable (fiberWindowInputCornerTests id) := by
  unfold fiberWindowInputCornerTests
  split <;> infer_instance

theorem fiber_window_input_corner_checks :
    (List.range 17).all (fun k => decide
      (fiberWindowInputRoutingTests (fiberWindowInputIdentityAt k) ∧
        fiberWindowInputCornerTests (fiberWindowInputIdentityAt k))) = true := by
  decide +kernel

theorem fiber_window_input_corner_facts (id : FiberWindowInputIdentity) :
    fiberWindowInputRoutingTests id ∧ fiberWindowInputCornerTests id := by
  have hk : fiberWindowInputIndex id < 17 := by cases id <;> decide +kernel
  have hi : fiberWindowInputIdentityAt (fiberWindowInputIndex id) = id := by cases id <;> rfl
  have h := Erdos993Lean.F4Fast.forall_lt_of_range_all fiber_window_input_corner_checks _ hk
  rw [hi] at h
  exact of_decide_eq_true h

theorem fiber_window_input_corner (id : FiberWindowInputIdentity) (cid : FiberWindowCornerIdentity)
    (hc : fiberWindowInputCorner id = some cid) {lambda mu : ℝ}
    (hlambda : 0 ≤ lambda) (hh : lambda ≤ lowMeanFractionReal (fiberInputHiFraction (fiberWindowInput id)))
    (hmu : lowMeanFractionReal (fiberInputRouteById (fiberWindowInput id)).mu0 ≤ mu) :
    lowMeanFractionReal (fiberWindowCornerById cid).mu_c ≤ mu ∧
      lowMeanFractionReal (fiberWindowCornerById cid).ell_c ≤
        lowMeanFractionReal (fiberInputRouteById (fiberWindowInput id)).ell0 ∧
      Real.log (1+lambda) ≤ lowMeanFractionReal (fiberWindowCornerById cid).L_c := by
  have h := (fiber_window_input_corner_facts id).2
  simp only [fiberWindowInputCornerTests,hc] at h
  rcases h with ⟨hclass,hm,he,hL,hm0,he0,hhi,hy,hLid,hmean,hell,hendpoint⟩
  have hmr := (lowMean_fraction_le_iff hm hm0).mp hmean
  have her := (lowMean_fraction_le_iff he he0).mp hell
  have hsum : lowMeanFractionValid (lowMeanFractionAdd (1,1) (fiberInputHiFraction (fiberWindowInput id))) :=
    Nat.mul_pos (by norm_num [lowMeanFractionValid]) hhi
  have hep := (lowMean_fraction_le_iff hsum hy).mp hendpoint
  rw [lowMean_fraction_add (by norm_num [lowMeanFractionValid]) hhi] at hep
  have hone : lowMeanFractionReal (1,1) = (1 : ℝ) := by norm_num [lowMeanFractionReal]
  rw [hone] at hep
  have hlog := Real.log_le_log (by linarith only [hlambda] : 0 < 1+lambda)
    (show 1+lambda ≤ lowMeanFractionReal (fiberCornerLogById (fiberWindowInputLog id)).y by linarith only [hh,hep])
  have hbound := fiber_corner_log_upper (fiberWindowInputLog id)
  rw [← hLid] at hbound
  exact ⟨hmr.trans hmu,her,hlog.trans hbound⟩

end Erdos993Lean.Analytic.V213
