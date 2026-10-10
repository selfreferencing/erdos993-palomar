module

public import Erdos993Lean.ExactComparisons.F3All.Data

/-! Generated from the F3 text of version 2.10 of the manuscript.
No Python certificate evaluation is used; the checks are done by the Lean kernel. -/

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 400000
namespace Erdos993Lean.ExactComparisons.F3All.Validity012

def records : List Bool := [
  -- A077.band
  decide (a077.D = (6/5 : Rat) ∧ a077.ac.b.lam = (28/25 : Rat) ∧ a077.bd.b.lam = (263/200 : Rat)),
  -- A078.domain
  aRowOK a078,
  -- A078.positive_M0
  decide (0 < cellM0 a078),
  -- A078.band
  decide (a078.D = (6/5 : Rat) ∧ a078.ac.b.lam = (28/25 : Rat) ∧ a078.bd.b.lam = (263/200 : Rat)),
  -- A079.domain
  aRowOK a079,
  -- A079.positive_M0
  decide (0 < cellM0 a079),
  -- A079.band
  decide (a079.D = (6/5 : Rat) ∧ a079.ac.b.lam = (28/25 : Rat) ∧ a079.bd.b.lam = (263/200 : Rat)),
  -- A080.domain
  aRowOK a080,
  -- A080.positive_M0
  decide (0 < cellM0 a080),
  -- A080.band
  decide (a080.D = (6/5 : Rat) ∧ a080.ac.b.lam = (28/25 : Rat) ∧ a080.bd.b.lam = (263/200 : Rat)),
  -- A081.domain
  aRowOK a081,
  -- A081.positive_M0
  decide (0 < cellM0 a081),
  -- A081.band
  decide (a081.D = (6/5 : Rat) ∧ a081.ac.b.lam = (28/25 : Rat) ∧ a081.bd.b.lam = (263/200 : Rat)),
  -- A082.domain
  aRowOK a082,
  -- A082.positive_M0
  decide (0 < cellM0 a082),
  -- A082.band
  decide (a082.D = (6/5 : Rat) ∧ a082.ac.b.lam = (28/25 : Rat) ∧ a082.bd.b.lam = (263/200 : Rat)),
  -- A083.domain
  aRowOK a083,
  -- A083.positive_M0
  decide (0 < cellM0 a083),
  -- A083.band
  decide (a083.D = (6/5 : Rat) ∧ a083.ac.b.lam = (28/25 : Rat) ∧ a083.bd.b.lam = (263/200 : Rat)),
  -- A084.domain
  aRowOK a084,
  -- A084.positive_M0
  decide (0 < cellM0 a084),
  -- A084.band
  decide (a084.D = (6/5 : Rat) ∧ a084.ac.b.lam = (28/25 : Rat) ∧ a084.bd.b.lam = (263/200 : Rat)),
  -- A085.domain
  aRowOK a085,
  -- A085.positive_M0
  decide (0 < cellM0 a085),
  -- A085.band
  decide (a085.D = (6/5 : Rat) ∧ a085.ac.b.lam = (28/25 : Rat) ∧ a085.bd.b.lam = (263/200 : Rat)),
  -- A086.domain
  aRowOK a086,
  -- A086.positive_M0
  decide (0 < cellM0 a086),
  -- A086.band
  decide (a086.D = (6/5 : Rat) ∧ a086.ac.b.lam = (28/25 : Rat) ∧ a086.bd.b.lam = (263/200 : Rat)),
  -- A087.domain
  aRowOK a087,
  -- A087.positive_M0
  decide (0 < cellM0 a087),
  -- A087.band
  decide (a087.D = (6/5 : Rat) ∧ a087.ac.b.lam = (28/25 : Rat) ∧ a087.bd.b.lam = (263/200 : Rat)),
  -- A088.domain
  aRowOK a088,
  -- A088.positive_M0
  decide (0 < cellM0 a088),
  -- A088.band
  decide (a088.D = (6/5 : Rat) ∧ a088.ac.b.lam = (28/25 : Rat) ∧ a088.bd.b.lam = (263/200 : Rat)),
  -- A089.domain
  aRowOK a089,
  -- A089.positive_M0
  decide (0 < cellM0 a089),
  -- A089.band
  decide (a089.D = (6/5 : Rat) ∧ a089.ac.b.lam = (28/25 : Rat) ∧ a089.bd.b.lam = (263/200 : Rat)),
  -- A090.domain
  aRowOK a090,
  -- A090.positive_M0
  decide (0 < cellM0 a090),
  -- A090.band
  decide (a090.D = (6/5 : Rat) ∧ a090.ac.b.lam = (28/25 : Rat) ∧ a090.bd.b.lam = (263/200 : Rat)),
  -- A091.domain
  aRowOK a091,
  -- A091.positive_M0
  decide (0 < cellM0 a091),
  -- A091.band
  decide (a091.D = (6/5 : Rat) ∧ a091.ac.b.lam = (28/25 : Rat) ∧ a091.bd.b.lam = (263/200 : Rat)),
  -- A092.domain
  aRowOK a092,
  -- A092.positive_M0
  decide (0 < cellM0 a092),
  -- A092.band
  decide (a092.D = (6/5 : Rat) ∧ a092.ac.b.lam = (28/25 : Rat) ∧ a092.bd.b.lam = (263/200 : Rat)),
  -- A093.domain
  aRowOK a093,
  -- A093.positive_M0
  decide (0 < cellM0 a093),
  -- A093.band
  decide (a093.D = (6/5 : Rat) ∧ a093.ac.b.lam = (28/25 : Rat) ∧ a093.bd.b.lam = (263/200 : Rat)),
  -- A094.domain
  aRowOK a094,
  -- A094.positive_M0
  decide (0 < cellM0 a094),
  -- A094.band
  decide (a094.D = (6/5 : Rat) ∧ a094.ac.b.lam = (28/25 : Rat) ∧ a094.bd.b.lam = (263/200 : Rat)),
  -- A095.domain
  aRowOK a095,
  -- A095.positive_M0
  decide (0 < cellM0 a095),
  -- A095.band
  decide (a095.D = (6/5 : Rat) ∧ a095.ac.b.lam = (28/25 : Rat) ∧ a095.bd.b.lam = (263/200 : Rat)),
  -- A096.domain
  aRowOK a096,
  -- A096.positive_M0
  decide (0 < cellM0 a096),
  -- A096.band
  decide (a096.D = (6/5 : Rat) ∧ a096.ac.b.lam = (28/25 : Rat) ∧ a096.bd.b.lam = (263/200 : Rat)),
  -- A097.domain
  aRowOK a097,
  -- A097.positive_M0
  decide (0 < cellM0 a097),
  -- A097.band
  decide (a097.D = (6/5 : Rat) ∧ a097.ac.b.lam = (28/25 : Rat) ∧ a097.bd.b.lam = (263/200 : Rat)),
  -- A098.domain
  aRowOK a098,
  -- A098.positive_M0
  decide (0 < cellM0 a098),
  -- A098.band
  decide (a098.D = (6/5 : Rat) ∧ a098.ac.b.lam = (28/25 : Rat) ∧ a098.bd.b.lam = (263/200 : Rat))
]
theorem checked : records.all id = true := by decide +kernel
theorem record_count : records.length = 64 := by decide +kernel
end Erdos993Lean.ExactComparisons.F3All.Validity012
