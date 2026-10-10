module

public import Erdos993Lean.ExactComparisons.F3All.Data

/-! Generated from the F3 text of version 2.10 of the manuscript.
No Python certificate evaluation is used; the checks are done by the Lean kernel. -/

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 400000
namespace Erdos993Lean.ExactComparisons.F3All.Validity008

def records : List Bool := [
  -- C018.domain
  cRowOK c018,
  -- C019.domain
  cRowOK c019,
  -- C020.domain
  cRowOK c020,
  -- C021.domain
  cRowOK c021,
  -- C022.domain
  cRowOK c022,
  -- C023.domain
  cRowOK c023,
  -- C024.domain
  cRowOK c024,
  -- C025.domain
  cRowOK c025,
  -- C026.domain
  cRowOK c026,
  -- C027.domain
  cRowOK c027,
  -- C028.domain
  cRowOK c028,
  -- C029.domain
  cRowOK c029,
  -- C030.domain
  cRowOK c030,
  -- C031.domain
  cRowOK c031,
  -- C032.domain
  cRowOK c032,
  -- C033.domain
  cRowOK c033,
  -- C034.domain
  cRowOK c034,
  -- C035.domain
  cRowOK c035,
  -- C036.domain
  cRowOK c036,
  -- C037.domain
  cRowOK c037,
  -- C038.domain
  cRowOK c038,
  -- C039.domain
  cRowOK c039,
  -- C040.domain
  cRowOK c040,
  -- C041.domain
  cRowOK c041,
  -- C042.domain
  cRowOK c042,
  -- C043.domain
  cRowOK c043,
  -- A001.domain
  aRowOK a001,
  -- A001.positive_M0
  decide (0 < cellM0 a001),
  -- A001.band
  decide (a001.D = (6/5 : Rat) ∧ a001.ac.b.lam = (1/3 : Rat) ∧ a001.bd.b.lam = (3/5 : Rat)),
  -- A002.domain
  aRowOK a002,
  -- A002.positive_M0
  decide (0 < cellM0 a002),
  -- A002.band
  decide (a002.D = (6/5 : Rat) ∧ a002.ac.b.lam = (1/3 : Rat) ∧ a002.bd.b.lam = (3/5 : Rat)),
  -- A003.domain
  aRowOK a003,
  -- A003.positive_M0
  decide (0 < cellM0 a003),
  -- A003.band
  decide (a003.D = (6/5 : Rat) ∧ a003.ac.b.lam = (1/3 : Rat) ∧ a003.bd.b.lam = (3/5 : Rat)),
  -- A004.domain
  aRowOK a004,
  -- A004.positive_M0
  decide (0 < cellM0 a004),
  -- A004.band
  decide (a004.D = (6/5 : Rat) ∧ a004.ac.b.lam = (1/3 : Rat) ∧ a004.bd.b.lam = (3/5 : Rat)),
  -- A005.domain
  aRowOK a005,
  -- A005.positive_M0
  decide (0 < cellM0 a005),
  -- A005.band
  decide (a005.D = (6/5 : Rat) ∧ a005.ac.b.lam = (1/3 : Rat) ∧ a005.bd.b.lam = (3/5 : Rat)),
  -- A006.domain
  aRowOK a006,
  -- A006.positive_M0
  decide (0 < cellM0 a006),
  -- A006.band
  decide (a006.D = (6/5 : Rat) ∧ a006.ac.b.lam = (1/3 : Rat) ∧ a006.bd.b.lam = (3/5 : Rat)),
  -- A007.domain
  aRowOK a007,
  -- A007.positive_M0
  decide (0 < cellM0 a007),
  -- A007.band
  decide (a007.D = (6/5 : Rat) ∧ a007.ac.b.lam = (1/3 : Rat) ∧ a007.bd.b.lam = (3/5 : Rat)),
  -- A008.domain
  aRowOK a008,
  -- A008.positive_M0
  decide (0 < cellM0 a008),
  -- A008.band
  decide (a008.D = (6/5 : Rat) ∧ a008.ac.b.lam = (1/3 : Rat) ∧ a008.bd.b.lam = (3/5 : Rat)),
  -- A009.domain
  aRowOK a009,
  -- A009.positive_M0
  decide (0 < cellM0 a009),
  -- A009.band
  decide (a009.D = (6/5 : Rat) ∧ a009.ac.b.lam = (1/3 : Rat) ∧ a009.bd.b.lam = (3/5 : Rat)),
  -- A010.domain
  aRowOK a010,
  -- A010.positive_M0
  decide (0 < cellM0 a010),
  -- A010.band
  decide (a010.D = (6/5 : Rat) ∧ a010.ac.b.lam = (1/3 : Rat) ∧ a010.bd.b.lam = (3/5 : Rat)),
  -- A011.domain
  aRowOK a011,
  -- A011.positive_M0
  decide (0 < cellM0 a011),
  -- A011.band
  decide (a011.D = (6/5 : Rat) ∧ a011.ac.b.lam = (1/3 : Rat) ∧ a011.bd.b.lam = (3/5 : Rat)),
  -- A012.domain
  aRowOK a012,
  -- A012.positive_M0
  decide (0 < cellM0 a012),
  -- A012.band
  decide (a012.D = (6/5 : Rat) ∧ a012.ac.b.lam = (1/3 : Rat) ∧ a012.bd.b.lam = (3/5 : Rat)),
  -- A013.domain
  aRowOK a013,
  -- A013.positive_M0
  decide (0 < cellM0 a013)
]
theorem checked : records.all id = true := by decide +kernel
theorem record_count : records.length = 64 := by decide +kernel
end Erdos993Lean.ExactComparisons.F3All.Validity008
