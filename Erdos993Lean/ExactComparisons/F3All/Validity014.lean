module

public import Erdos993Lean.ExactComparisons.F3All.Data

/-! Generated from the F3 text of version 2.10 of the manuscript.
No Python certificate evaluation is used; the checks are done by the Lean kernel. -/

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 400000
namespace Erdos993Lean.ExactComparisons.F3All.Validity014

def records : List Bool := [
  -- A120.positive_M0
  decide (0 < cellM0 a120),
  -- A120.band
  decide (a120.D = (7/5 : Rat) ∧ a120.ac.b.lam = (263/200 : Rat) ∧ a120.bd.b.lam = (3/2 : Rat)),
  -- A121.domain
  aRowOK a121,
  -- A121.positive_M0
  decide (0 < cellM0 a121),
  -- A121.band
  decide (a121.D = (7/5 : Rat) ∧ a121.ac.b.lam = (263/200 : Rat) ∧ a121.bd.b.lam = (3/2 : Rat)),
  -- A122.domain
  aRowOK a122,
  -- A122.positive_M0
  decide (0 < cellM0 a122),
  -- A122.band
  decide (a122.D = (7/5 : Rat) ∧ a122.ac.b.lam = (263/200 : Rat) ∧ a122.bd.b.lam = (3/2 : Rat)),
  -- A123.domain
  aRowOK a123,
  -- A123.positive_M0
  decide (0 < cellM0 a123),
  -- A123.band
  decide (a123.D = (8/5 : Rat) ∧ a123.ac.b.lam = (3/2 : Rat) ∧ a123.bd.b.lam = (7/4 : Rat)),
  -- A124.domain
  aRowOK a124,
  -- A124.positive_M0
  decide (0 < cellM0 a124),
  -- A124.band
  decide (a124.D = (8/5 : Rat) ∧ a124.ac.b.lam = (3/2 : Rat) ∧ a124.bd.b.lam = (7/4 : Rat)),
  -- A125.domain
  aRowOK a125,
  -- A125.positive_M0
  decide (0 < cellM0 a125),
  -- A125.band
  decide (a125.D = (8/5 : Rat) ∧ a125.ac.b.lam = (3/2 : Rat) ∧ a125.bd.b.lam = (7/4 : Rat)),
  -- A126.domain
  aRowOK a126,
  -- A126.positive_M0
  decide (0 < cellM0 a126),
  -- A126.band
  decide (a126.D = (8/5 : Rat) ∧ a126.ac.b.lam = (3/2 : Rat) ∧ a126.bd.b.lam = (7/4 : Rat)),
  -- A127.domain
  aRowOK a127,
  -- A127.positive_M0
  decide (0 < cellM0 a127),
  -- A127.band
  decide (a127.D = (8/5 : Rat) ∧ a127.ac.b.lam = (3/2 : Rat) ∧ a127.bd.b.lam = (7/4 : Rat)),
  -- A128.domain
  aRowOK a128,
  -- A128.positive_M0
  decide (0 < cellM0 a128),
  -- A128.band
  decide (a128.D = (8/5 : Rat) ∧ a128.ac.b.lam = (3/2 : Rat) ∧ a128.bd.b.lam = (7/4 : Rat)),
  -- A129.domain
  aRowOK a129,
  -- A129.positive_M0
  decide (0 < cellM0 a129),
  -- A129.band
  decide (a129.D = (8/5 : Rat) ∧ a129.ac.b.lam = (3/2 : Rat) ∧ a129.bd.b.lam = (7/4 : Rat)),
  -- A130.domain
  aRowOK a130,
  -- A130.positive_M0
  decide (0 < cellM0 a130),
  -- A130.band
  decide (a130.D = (8/5 : Rat) ∧ a130.ac.b.lam = (3/2 : Rat) ∧ a130.bd.b.lam = (7/4 : Rat)),
  -- A131.domain
  aRowOK a131,
  -- A131.positive_M0
  decide (0 < cellM0 a131),
  -- A131.band
  decide (a131.D = (8/5 : Rat) ∧ a131.ac.b.lam = (3/2 : Rat) ∧ a131.bd.b.lam = (7/4 : Rat)),
  -- A132.domain
  aRowOK a132,
  -- A132.positive_M0
  decide (0 < cellM0 a132),
  -- A132.band
  decide (a132.D = (8/5 : Rat) ∧ a132.ac.b.lam = (3/2 : Rat) ∧ a132.bd.b.lam = (7/4 : Rat)),
  -- A133.domain
  aRowOK a133,
  -- A133.positive_M0
  decide (0 < cellM0 a133),
  -- A133.band
  decide (a133.D = (8/5 : Rat) ∧ a133.ac.b.lam = (3/2 : Rat) ∧ a133.bd.b.lam = (7/4 : Rat)),
  -- A134.domain
  aRowOK a134,
  -- A134.positive_M0
  decide (0 < cellM0 a134),
  -- A134.band
  decide (a134.D = (8/5 : Rat) ∧ a134.ac.b.lam = (3/2 : Rat) ∧ a134.bd.b.lam = (7/4 : Rat)),
  -- A135.domain
  aRowOK a135,
  -- A135.positive_M0
  decide (0 < cellM0 a135),
  -- A135.band
  decide (a135.D = (8/5 : Rat) ∧ a135.ac.b.lam = (3/2 : Rat) ∧ a135.bd.b.lam = (7/4 : Rat)),
  -- A136.domain
  aRowOK a136,
  -- A136.positive_M0
  decide (0 < cellM0 a136),
  -- A136.band
  decide (a136.D = (9/5 : Rat) ∧ a136.ac.b.lam = (7/4 : Rat) ∧ a136.bd.b.lam = (2 : Rat)),
  -- A137.domain
  aRowOK a137,
  -- A137.positive_M0
  decide (0 < cellM0 a137),
  -- A137.band
  decide (a137.D = (9/5 : Rat) ∧ a137.ac.b.lam = (7/4 : Rat) ∧ a137.bd.b.lam = (2 : Rat)),
  -- A138.domain
  aRowOK a138,
  -- A138.positive_M0
  decide (0 < cellM0 a138),
  -- A138.band
  decide (a138.D = (9/5 : Rat) ∧ a138.ac.b.lam = (7/4 : Rat) ∧ a138.bd.b.lam = (2 : Rat)),
  -- A139.domain
  aRowOK a139,
  -- A139.positive_M0
  decide (0 < cellM0 a139),
  -- A139.band
  decide (a139.D = (9/5 : Rat) ∧ a139.ac.b.lam = (7/4 : Rat) ∧ a139.bd.b.lam = (2 : Rat)),
  -- A140.domain
  aRowOK a140,
  -- A140.positive_M0
  decide (0 < cellM0 a140),
  -- A140.band
  decide (a140.D = (9/5 : Rat) ∧ a140.ac.b.lam = (7/4 : Rat) ∧ a140.bd.b.lam = (2 : Rat)),
  -- A141.domain
  aRowOK a141,
  -- A141.positive_M0
  decide (0 < cellM0 a141)
]
theorem checked : records.all id = true := by decide +kernel
theorem record_count : records.length = 64 := by decide +kernel
end Erdos993Lean.ExactComparisons.F3All.Validity014
