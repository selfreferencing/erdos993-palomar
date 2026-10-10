module

public import Erdos993Lean.ExactComparisons.F3All.Data

/-! Generated from the F3 text of version 2.10 of the manuscript.
No Python certificate evaluation is used; the checks are done by the Lean kernel. -/

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 400000
namespace Erdos993Lean.ExactComparisons.F3All.Validity009

def records : List Bool := [
  -- A013.band
  decide (a013.D = (6/5 : Rat) ∧ a013.ac.b.lam = (1/3 : Rat) ∧ a013.bd.b.lam = (3/5 : Rat)),
  -- A014.domain
  aRowOK a014,
  -- A014.positive_M0
  decide (0 < cellM0 a014),
  -- A014.band
  decide (a014.D = (6/5 : Rat) ∧ a014.ac.b.lam = (1/3 : Rat) ∧ a014.bd.b.lam = (3/5 : Rat)),
  -- A015.domain
  aRowOK a015,
  -- A015.positive_M0
  decide (0 < cellM0 a015),
  -- A015.band
  decide (a015.D = (6/5 : Rat) ∧ a015.ac.b.lam = (1/3 : Rat) ∧ a015.bd.b.lam = (3/5 : Rat)),
  -- A016.domain
  aRowOK a016,
  -- A016.positive_M0
  decide (0 < cellM0 a016),
  -- A016.band
  decide (a016.D = (6/5 : Rat) ∧ a016.ac.b.lam = (3/5 : Rat) ∧ a016.bd.b.lam = (7/8 : Rat)),
  -- A017.domain
  aRowOK a017,
  -- A017.positive_M0
  decide (0 < cellM0 a017),
  -- A017.band
  decide (a017.D = (6/5 : Rat) ∧ a017.ac.b.lam = (3/5 : Rat) ∧ a017.bd.b.lam = (7/8 : Rat)),
  -- A018.domain
  aRowOK a018,
  -- A018.positive_M0
  decide (0 < cellM0 a018),
  -- A018.band
  decide (a018.D = (6/5 : Rat) ∧ a018.ac.b.lam = (3/5 : Rat) ∧ a018.bd.b.lam = (7/8 : Rat)),
  -- A019.domain
  aRowOK a019,
  -- A019.positive_M0
  decide (0 < cellM0 a019),
  -- A019.band
  decide (a019.D = (6/5 : Rat) ∧ a019.ac.b.lam = (3/5 : Rat) ∧ a019.bd.b.lam = (7/8 : Rat)),
  -- A020.domain
  aRowOK a020,
  -- A020.positive_M0
  decide (0 < cellM0 a020),
  -- A020.band
  decide (a020.D = (6/5 : Rat) ∧ a020.ac.b.lam = (3/5 : Rat) ∧ a020.bd.b.lam = (7/8 : Rat)),
  -- A021.domain
  aRowOK a021,
  -- A021.positive_M0
  decide (0 < cellM0 a021),
  -- A021.band
  decide (a021.D = (6/5 : Rat) ∧ a021.ac.b.lam = (3/5 : Rat) ∧ a021.bd.b.lam = (7/8 : Rat)),
  -- A022.domain
  aRowOK a022,
  -- A022.positive_M0
  decide (0 < cellM0 a022),
  -- A022.band
  decide (a022.D = (6/5 : Rat) ∧ a022.ac.b.lam = (3/5 : Rat) ∧ a022.bd.b.lam = (7/8 : Rat)),
  -- A023.domain
  aRowOK a023,
  -- A023.positive_M0
  decide (0 < cellM0 a023),
  -- A023.band
  decide (a023.D = (6/5 : Rat) ∧ a023.ac.b.lam = (3/5 : Rat) ∧ a023.bd.b.lam = (7/8 : Rat)),
  -- A024.domain
  aRowOK a024,
  -- A024.positive_M0
  decide (0 < cellM0 a024),
  -- A024.band
  decide (a024.D = (6/5 : Rat) ∧ a024.ac.b.lam = (3/5 : Rat) ∧ a024.bd.b.lam = (7/8 : Rat)),
  -- A025.domain
  aRowOK a025,
  -- A025.positive_M0
  decide (0 < cellM0 a025),
  -- A025.band
  decide (a025.D = (6/5 : Rat) ∧ a025.ac.b.lam = (3/5 : Rat) ∧ a025.bd.b.lam = (7/8 : Rat)),
  -- A026.domain
  aRowOK a026,
  -- A026.positive_M0
  decide (0 < cellM0 a026),
  -- A026.band
  decide (a026.D = (6/5 : Rat) ∧ a026.ac.b.lam = (3/5 : Rat) ∧ a026.bd.b.lam = (7/8 : Rat)),
  -- A027.domain
  aRowOK a027,
  -- A027.positive_M0
  decide (0 < cellM0 a027),
  -- A027.band
  decide (a027.D = (6/5 : Rat) ∧ a027.ac.b.lam = (3/5 : Rat) ∧ a027.bd.b.lam = (7/8 : Rat)),
  -- A028.domain
  aRowOK a028,
  -- A028.positive_M0
  decide (0 < cellM0 a028),
  -- A028.band
  decide (a028.D = (6/5 : Rat) ∧ a028.ac.b.lam = (3/5 : Rat) ∧ a028.bd.b.lam = (7/8 : Rat)),
  -- A029.domain
  aRowOK a029,
  -- A029.positive_M0
  decide (0 < cellM0 a029),
  -- A029.band
  decide (a029.D = (6/5 : Rat) ∧ a029.ac.b.lam = (3/5 : Rat) ∧ a029.bd.b.lam = (7/8 : Rat)),
  -- A030.domain
  aRowOK a030,
  -- A030.positive_M0
  decide (0 < cellM0 a030),
  -- A030.band
  decide (a030.D = (6/5 : Rat) ∧ a030.ac.b.lam = (3/5 : Rat) ∧ a030.bd.b.lam = (7/8 : Rat)),
  -- A031.domain
  aRowOK a031,
  -- A031.positive_M0
  decide (0 < cellM0 a031),
  -- A031.band
  decide (a031.D = (6/5 : Rat) ∧ a031.ac.b.lam = (3/5 : Rat) ∧ a031.bd.b.lam = (7/8 : Rat)),
  -- A032.domain
  aRowOK a032,
  -- A032.positive_M0
  decide (0 < cellM0 a032),
  -- A032.band
  decide (a032.D = (6/5 : Rat) ∧ a032.ac.b.lam = (3/5 : Rat) ∧ a032.bd.b.lam = (7/8 : Rat)),
  -- A033.domain
  aRowOK a033,
  -- A033.positive_M0
  decide (0 < cellM0 a033),
  -- A033.band
  decide (a033.D = (6/5 : Rat) ∧ a033.ac.b.lam = (3/5 : Rat) ∧ a033.bd.b.lam = (7/8 : Rat)),
  -- A034.domain
  aRowOK a034,
  -- A034.positive_M0
  decide (0 < cellM0 a034),
  -- A034.band
  decide (a034.D = (6/5 : Rat) ∧ a034.ac.b.lam = (7/8 : Rat) ∧ a034.bd.b.lam = (28/25 : Rat))
]
theorem checked : records.all id = true := by decide +kernel
theorem record_count : records.length = 64 := by decide +kernel
end Erdos993Lean.ExactComparisons.F3All.Validity009
