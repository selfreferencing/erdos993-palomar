module

public import Erdos993Lean.ExactComparisons.F3All.Data

/-! Generated from the F3 text of version 2.10 of the manuscript.
No Python certificate evaluation is used; the checks are done by the Lean kernel. -/

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 400000
namespace Erdos993Lean.ExactComparisons.F3All.Validity013

def records : List Bool := [
  -- A099.domain
  aRowOK a099,
  -- A099.positive_M0
  decide (0 < cellM0 a099),
  -- A099.band
  decide (a099.D = (6/5 : Rat) ∧ a099.ac.b.lam = (28/25 : Rat) ∧ a099.bd.b.lam = (263/200 : Rat)),
  -- A100.domain
  aRowOK a100,
  -- A100.positive_M0
  decide (0 < cellM0 a100),
  -- A100.band
  decide (a100.D = (6/5 : Rat) ∧ a100.ac.b.lam = (28/25 : Rat) ∧ a100.bd.b.lam = (263/200 : Rat)),
  -- A101.domain
  aRowOK a101,
  -- A101.positive_M0
  decide (0 < cellM0 a101),
  -- A101.band
  decide (a101.D = (6/5 : Rat) ∧ a101.ac.b.lam = (28/25 : Rat) ∧ a101.bd.b.lam = (263/200 : Rat)),
  -- A102.domain
  aRowOK a102,
  -- A102.positive_M0
  decide (0 < cellM0 a102),
  -- A102.band
  decide (a102.D = (6/5 : Rat) ∧ a102.ac.b.lam = (28/25 : Rat) ∧ a102.bd.b.lam = (263/200 : Rat)),
  -- A103.domain
  aRowOK a103,
  -- A103.positive_M0
  decide (0 < cellM0 a103),
  -- A103.band
  decide (a103.D = (6/5 : Rat) ∧ a103.ac.b.lam = (28/25 : Rat) ∧ a103.bd.b.lam = (263/200 : Rat)),
  -- A104.domain
  aRowOK a104,
  -- A104.positive_M0
  decide (0 < cellM0 a104),
  -- A104.band
  decide (a104.D = (6/5 : Rat) ∧ a104.ac.b.lam = (28/25 : Rat) ∧ a104.bd.b.lam = (263/200 : Rat)),
  -- A105.domain
  aRowOK a105,
  -- A105.positive_M0
  decide (0 < cellM0 a105),
  -- A105.band
  decide (a105.D = (7/5 : Rat) ∧ a105.ac.b.lam = (263/200 : Rat) ∧ a105.bd.b.lam = (3/2 : Rat)),
  -- A106.domain
  aRowOK a106,
  -- A106.positive_M0
  decide (0 < cellM0 a106),
  -- A106.band
  decide (a106.D = (7/5 : Rat) ∧ a106.ac.b.lam = (263/200 : Rat) ∧ a106.bd.b.lam = (3/2 : Rat)),
  -- A107.domain
  aRowOK a107,
  -- A107.positive_M0
  decide (0 < cellM0 a107),
  -- A107.band
  decide (a107.D = (7/5 : Rat) ∧ a107.ac.b.lam = (263/200 : Rat) ∧ a107.bd.b.lam = (3/2 : Rat)),
  -- A108.domain
  aRowOK a108,
  -- A108.positive_M0
  decide (0 < cellM0 a108),
  -- A108.band
  decide (a108.D = (7/5 : Rat) ∧ a108.ac.b.lam = (263/200 : Rat) ∧ a108.bd.b.lam = (3/2 : Rat)),
  -- A109.domain
  aRowOK a109,
  -- A109.positive_M0
  decide (0 < cellM0 a109),
  -- A109.band
  decide (a109.D = (7/5 : Rat) ∧ a109.ac.b.lam = (263/200 : Rat) ∧ a109.bd.b.lam = (3/2 : Rat)),
  -- A110.domain
  aRowOK a110,
  -- A110.positive_M0
  decide (0 < cellM0 a110),
  -- A110.band
  decide (a110.D = (7/5 : Rat) ∧ a110.ac.b.lam = (263/200 : Rat) ∧ a110.bd.b.lam = (3/2 : Rat)),
  -- A111.domain
  aRowOK a111,
  -- A111.positive_M0
  decide (0 < cellM0 a111),
  -- A111.band
  decide (a111.D = (7/5 : Rat) ∧ a111.ac.b.lam = (263/200 : Rat) ∧ a111.bd.b.lam = (3/2 : Rat)),
  -- A112.domain
  aRowOK a112,
  -- A112.positive_M0
  decide (0 < cellM0 a112),
  -- A112.band
  decide (a112.D = (7/5 : Rat) ∧ a112.ac.b.lam = (263/200 : Rat) ∧ a112.bd.b.lam = (3/2 : Rat)),
  -- A113.domain
  aRowOK a113,
  -- A113.positive_M0
  decide (0 < cellM0 a113),
  -- A113.band
  decide (a113.D = (7/5 : Rat) ∧ a113.ac.b.lam = (263/200 : Rat) ∧ a113.bd.b.lam = (3/2 : Rat)),
  -- A114.domain
  aRowOK a114,
  -- A114.positive_M0
  decide (0 < cellM0 a114),
  -- A114.band
  decide (a114.D = (7/5 : Rat) ∧ a114.ac.b.lam = (263/200 : Rat) ∧ a114.bd.b.lam = (3/2 : Rat)),
  -- A115.domain
  aRowOK a115,
  -- A115.positive_M0
  decide (0 < cellM0 a115),
  -- A115.band
  decide (a115.D = (7/5 : Rat) ∧ a115.ac.b.lam = (263/200 : Rat) ∧ a115.bd.b.lam = (3/2 : Rat)),
  -- A116.domain
  aRowOK a116,
  -- A116.positive_M0
  decide (0 < cellM0 a116),
  -- A116.band
  decide (a116.D = (7/5 : Rat) ∧ a116.ac.b.lam = (263/200 : Rat) ∧ a116.bd.b.lam = (3/2 : Rat)),
  -- A117.domain
  aRowOK a117,
  -- A117.positive_M0
  decide (0 < cellM0 a117),
  -- A117.band
  decide (a117.D = (7/5 : Rat) ∧ a117.ac.b.lam = (263/200 : Rat) ∧ a117.bd.b.lam = (3/2 : Rat)),
  -- A118.domain
  aRowOK a118,
  -- A118.positive_M0
  decide (0 < cellM0 a118),
  -- A118.band
  decide (a118.D = (7/5 : Rat) ∧ a118.ac.b.lam = (263/200 : Rat) ∧ a118.bd.b.lam = (3/2 : Rat)),
  -- A119.domain
  aRowOK a119,
  -- A119.positive_M0
  decide (0 < cellM0 a119),
  -- A119.band
  decide (a119.D = (7/5 : Rat) ∧ a119.ac.b.lam = (263/200 : Rat) ∧ a119.bd.b.lam = (3/2 : Rat)),
  -- A120.domain
  aRowOK a120
]
theorem checked : records.all id = true := by decide +kernel
theorem record_count : records.length = 64 := by decide +kernel
end Erdos993Lean.ExactComparisons.F3All.Validity013
