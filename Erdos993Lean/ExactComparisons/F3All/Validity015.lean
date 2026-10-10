module

public import Erdos993Lean.ExactComparisons.F3All.Data

/-! Generated from the F3 text of version 2.10 of the manuscript.
No Python certificate evaluation is used; the checks are done by the Lean kernel. -/

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 400000
namespace Erdos993Lean.ExactComparisons.F3All.Validity015

def records : List Bool := [
  -- A141.band
  decide (a141.D = (9/5 : Rat) ∧ a141.ac.b.lam = (7/4 : Rat) ∧ a141.bd.b.lam = (2 : Rat)),
  -- A142.domain
  aRowOK a142,
  -- A142.positive_M0
  decide (0 < cellM0 a142),
  -- A142.band
  decide (a142.D = (9/5 : Rat) ∧ a142.ac.b.lam = (7/4 : Rat) ∧ a142.bd.b.lam = (2 : Rat)),
  -- A143.domain
  aRowOK a143,
  -- A143.positive_M0
  decide (0 < cellM0 a143),
  -- A143.band
  decide (a143.D = (9/5 : Rat) ∧ a143.ac.b.lam = (7/4 : Rat) ∧ a143.bd.b.lam = (2 : Rat)),
  -- A144.domain
  aRowOK a144,
  -- A144.positive_M0
  decide (0 < cellM0 a144),
  -- A144.band
  decide (a144.D = (9/5 : Rat) ∧ a144.ac.b.lam = (7/4 : Rat) ∧ a144.bd.b.lam = (2 : Rat)),
  -- A145.domain
  aRowOK a145,
  -- A145.positive_M0
  decide (0 < cellM0 a145),
  -- A145.band
  decide (a145.D = (9/5 : Rat) ∧ a145.ac.b.lam = (7/4 : Rat) ∧ a145.bd.b.lam = (2 : Rat)),
  -- A146.domain
  aRowOK a146,
  -- A146.positive_M0
  decide (0 < cellM0 a146),
  -- A146.band
  decide (a146.D = (9/5 : Rat) ∧ a146.ac.b.lam = (7/4 : Rat) ∧ a146.bd.b.lam = (2 : Rat)),
  -- A147.domain
  aRowOK a147,
  -- A147.positive_M0
  decide (0 < cellM0 a147),
  -- A147.band
  decide (a147.D = (9/5 : Rat) ∧ a147.ac.b.lam = (7/4 : Rat) ∧ a147.bd.b.lam = (2 : Rat)),
  -- A148.domain
  aRowOK a148,
  -- A148.positive_M0
  decide (0 < cellM0 a148),
  -- A148.band
  decide (a148.D = (9/5 : Rat) ∧ a148.ac.b.lam = (7/4 : Rat) ∧ a148.bd.b.lam = (2 : Rat)),
  -- A149.domain
  aRowOK a149,
  -- A149.positive_M0
  decide (0 < cellM0 a149),
  -- A149.band
  decide (a149.D = (21/10 : Rat) ∧ a149.ac.b.lam = (2 : Rat) ∧ a149.bd.b.lam = (7/3 : Rat)),
  -- A150.domain
  aRowOK a150,
  -- A150.positive_M0
  decide (0 < cellM0 a150),
  -- A150.band
  decide (a150.D = (21/10 : Rat) ∧ a150.ac.b.lam = (2 : Rat) ∧ a150.bd.b.lam = (7/3 : Rat)),
  -- A151.domain
  aRowOK a151,
  -- A151.positive_M0
  decide (0 < cellM0 a151),
  -- A151.band
  decide (a151.D = (21/10 : Rat) ∧ a151.ac.b.lam = (2 : Rat) ∧ a151.bd.b.lam = (7/3 : Rat)),
  -- A152.domain
  aRowOK a152,
  -- A152.positive_M0
  decide (0 < cellM0 a152),
  -- A152.band
  decide (a152.D = (21/10 : Rat) ∧ a152.ac.b.lam = (2 : Rat) ∧ a152.bd.b.lam = (7/3 : Rat)),
  -- A153.domain
  aRowOK a153,
  -- A153.positive_M0
  decide (0 < cellM0 a153),
  -- A153.band
  decide (a153.D = (21/10 : Rat) ∧ a153.ac.b.lam = (2 : Rat) ∧ a153.bd.b.lam = (7/3 : Rat)),
  -- A154.domain
  aRowOK a154,
  -- A154.positive_M0
  decide (0 < cellM0 a154),
  -- A154.band
  decide (a154.D = (21/10 : Rat) ∧ a154.ac.b.lam = (2 : Rat) ∧ a154.bd.b.lam = (7/3 : Rat)),
  -- A155.domain
  aRowOK a155,
  -- A155.positive_M0
  decide (0 < cellM0 a155),
  -- A155.band
  decide (a155.D = (21/10 : Rat) ∧ a155.ac.b.lam = (2 : Rat) ∧ a155.bd.b.lam = (7/3 : Rat)),
  -- A156.domain
  aRowOK a156,
  -- A156.positive_M0
  decide (0 < cellM0 a156),
  -- A156.band
  decide (a156.D = (21/10 : Rat) ∧ a156.ac.b.lam = (2 : Rat) ∧ a156.bd.b.lam = (7/3 : Rat)),
  -- A157.domain
  aRowOK a157,
  -- A157.positive_M0
  decide (0 < cellM0 a157),
  -- A157.band
  decide (a157.D = (21/10 : Rat) ∧ a157.ac.b.lam = (2 : Rat) ∧ a157.bd.b.lam = (7/3 : Rat)),
  -- A158.domain
  aRowOK a158,
  -- A158.positive_M0
  decide (0 < cellM0 a158),
  -- A158.band
  decide (a158.D = (21/10 : Rat) ∧ a158.ac.b.lam = (2 : Rat) ∧ a158.bd.b.lam = (7/3 : Rat)),
  -- A159.domain
  aRowOK a159,
  -- A159.positive_M0
  decide (0 < cellM0 a159),
  -- A159.band
  decide (a159.D = (21/10 : Rat) ∧ a159.ac.b.lam = (2 : Rat) ∧ a159.bd.b.lam = (7/3 : Rat)),
  -- log.domain0001
  logUseOK (((10 : Rat) / (3 : Rat))),
  -- log.domain0002
  logUseOK (((369 : Rat) / (80 : Rat))),
  -- log.domain0003
  logUseOK (((463 : Rat) / (200 : Rat))),
  -- log.domain0004
  logUseOK (((1 : Rat) + ((1 : Rat) / (3 : Rat)))),
  -- log.domain0006
  logUseOK (((1 : Rat) + ((3 : Rat) / (5 : Rat)))),
  -- log.domain0008
  logUseOK (((1 : Rat) + ((7 : Rat) / (8 : Rat)))),
  -- log.domain0010
  logUseOK (((1 : Rat) + ((28 : Rat) / (25 : Rat)))),
  -- log.domain0012
  logUseOK (((1 : Rat) + ((263 : Rat) / (200 : Rat)))),
  -- log.domain0014
  logUseOK (((1 : Rat) + ((3 : Rat) / (2 : Rat))))
]
theorem checked : records.all id = true := by decide +kernel
theorem record_count : records.length = 64 := by decide +kernel
end Erdos993Lean.ExactComparisons.F3All.Validity015
