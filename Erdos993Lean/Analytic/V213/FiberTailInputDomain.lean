module

public import Erdos993Lean.Analytic.V213.FiberInputHighDomain
public import Erdos993Lean.Analytic.V213.FiberTailBounds
public import Erdos993Lean.Analytic.V213.FiberCornerBounds

/-!
Actual55 input-to-tail identities and closed-domain guards.
All fields are selected from existing accepted F06/F11/F14/F15 records;
no numerical endpoint/rate table is duplicated. The weighted small
endpoint is7/least-mu, separately from shifted m. Exact ranges include
all closed activity endpoints and the natural-width zero case later.

-/

@[expose] public section
namespace Erdos993Lean.Analytic.V213

def fiberInputTailIdentity : FiberInputTail → FiberTailIdentity
  | .c1 => .c1
  | .c2 => .c2
  | .a => .a
  | .b10 => .b10
  | .b19 => .b19
  | .c => .c
  | .def => .defGroup
  | .g => .g
  | .h40 => .h40
  | .h45 => .h45
  | .c5 => .c5
  | .c6 => .c6
  | .c78 => .c78

def fiberInputTail (id : FiberInputIdentity) : FiberTailIdentity :=
  fiberInputTailIdentity (fiberInputRouteById id).tail

def fiberTailSkewCapFraction : FiberTailIdentity → lowMeanFraction
  | .a | .b10 | .b19 | .c | .defGroup => (1,4)
  | _ => (1,2)

def fiberTailOrdinaryLog : FiberTailIdentity → Option FiberCornerLogIdentity
  | .defGroup => some .y12_5
  | .g => some .y13_5
  | .h40 | .h45 => some .y11_4
  | .c5 => some .y29_10
  | .c6 => some .y61_20
  | .c78 => some .y10_3
  | _ => none

def fiberInputAnalyticOption : FiberInputIdentity → Option FiberAnalyticInputIdentity
  | .iota_6 => some .iota_6
  | .iota_7 => some .iota_7
  | .iota_8 => some .iota_8
  | .iota_9 => some .iota_9
  | .iota_10 => some .iota_10
  | .iota_11 => some .iota_11
  | .iota_12 => some .iota_12
  | .iota_13 => some .iota_13
  | .iota_14 => some .iota_14
  | .iota_15 => some .iota_15
  | .iota_16 => some .iota_16
  | .iota_17 => some .iota_17
  | .iota_18 => some .iota_18
  | .iota_19 => some .iota_19
  | .iota_20 => some .iota_20
  | .iota_21 => some .iota_21
  | .iota_22 => some .iota_22
  | .iota_23 => some .iota_23
  | .iota_24 => some .iota_24
  | .iota_25 => some .iota_25
  | .iota_26 => some .iota_26
  | .iota_27 => some .iota_27
  | .iota_28 => some .iota_28
  | .iota_29 => some .iota_29
  | .iota_30 => some .iota_30
  | .iota_31 => some .iota_31
  | .iota_32 => some .iota_32
  | .iota_33 => some .iota_33
  | .iota_34 => some .iota_34
  | .iota_35 => some .iota_35
  | .iota_36 => some .iota_36
  | .iota_37 => some .iota_37
  | .iota_38 => some .iota_38
  | .iota_39 => some .iota_39
  | .iota_40 => some .iota_40
  | .iota_41 => some .iota_41
  | .iota_42 => some .iota_42
  | .iota_43 => some .iota_43
  | .iota_44 => some .iota_44
  | .iota_45 => some .iota_45
  | .iota_46 => some .iota_46
  | _ => none

def fiberTailInputTests (id : FiberInputIdentity) : Prop :=
  let input := fiberInputRouteById id
  let tid := fiberInputTail id
  let r := fiberTailById tid
  let cap := fiberTailSkewCapFraction tid
  let lo := fiberInputSignedSkewFraction (fiberInputQloFraction id)
  let hi := fiberInputSignedSkewFraction (fiberInputQhiFraction id)
  lowMeanFractionValid cap ∧ lowMeanFractionLE r.mu input.mu0 ∧ r.c = input.c ∧
  lowMeanFractionLE (lowMeanFractionAbs lo) cap ∧ lowMeanFractionLE (lowMeanFractionAbs hi) cap ∧
  lowMeanFractionLE (fiberInputClassB input.kind) (2,5) ∧
  lowMeanFractionLE (0,1) (fiberInputClassBeta input.kind) ∧
  (match r.weight with
    | none =>
      lowMeanFractionLE r.ell input.ell0 ∧
      lowMeanFractionValid (r.h_i.getD (1,1)) ∧
      lowMeanFractionLE (1,1) (r.h_i.getD (1,1)) ∧
      lowMeanFractionLE (lowMeanFractionAdd (1,1) (fiberInputHiFraction id)) (r.h_i.getD (1,1))
    | some wid =>
      lowMeanFractionLE (3,5) (fiberInputLoFraction id) ∧
      (match fiberInputAnalyticOption id with
        | none => False
        | some aid =>
          fiberInputIndex (fiberAnalyticInput aid) = fiberInputIndex id ∧ fiberAnalyticWeight aid = wid ∧
          lowMeanFractionLE (fiberWeightById wid).guard_lo (r.smallGuard.getD (0,1)) ∧
          lowMeanFractionLE (r.smallGuard.getD (0,1)) (fiberWeightById wid).guard_hi ∧
          lowMeanFractionLE (fiberWeightById wid).guard_lo r.c ∧
          lowMeanFractionLE r.c (fiberWeightById wid).guard_hi ∧
          lowMeanFractionEq r.d (fiberFractionSub (fiberWeightById wid).ell_w
            (lowMeanFractionMul r.c (fiberWeightById wid).L_w)))) ∧
  (match fiberTailOrdinaryLog tid with
    | none => True
    | some lid =>
      r.h_i = some (fiberCornerLogById lid).y ∧
      lowMeanFractionEq r.d (fiberFractionSub r.ell (lowMeanFractionMul r.c (fiberCornerLogById lid).L)))

instance fiberTailInputTestsDecidable (id : FiberInputIdentity) :
    Decidable (fiberTailInputTests id) := by
  unfold fiberTailInputTests
  dsimp only
  cases hw : (fiberTailById (fiberInputTail id)).weight <;>
    cases ha : fiberInputAnalyticOption id <;>
      cases hlog : fiberTailOrdinaryLog (fiberInputTail id) <;>
        simp only [hw, ha, hlog] <;> infer_instance

theorem fiber_tail_input_checks :
    (List.range 55).all (fun k => decide (fiberTailInputTests (fiberInputIdentityAt k))) = true := by
  decide +kernel

theorem fiber_tail_input_facts (id : FiberInputIdentity) : fiberTailInputTests id := by
  have hk : fiberInputIndex id < 55 := by cases id <;> decide +kernel
  have hi : fiberInputIdentityAt (fiberInputIndex id) = id := by cases id <;> rfl
  have h := Erdos993Lean.F4Fast.forall_lt_of_range_all fiber_tail_input_checks (fiberInputIndex id) hk
  rw [hi] at h
  exact of_decide_eq_true h

end Erdos993Lean.Analytic.V213
