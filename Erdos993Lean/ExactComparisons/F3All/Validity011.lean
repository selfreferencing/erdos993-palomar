module

public import Erdos993Lean.ExactComparisons.F3All.Data

/-! Generated from the F3 text of version 2.10 of the manuscript.
No Python certificate evaluation is used; the checks are done by the Lean kernel. -/

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 400000
namespace Erdos993Lean.ExactComparisons.F3All.Validity011

def records : List Bool := [
  -- A056.positive_M0
  decide (0 < cellM0 a056),
  -- A056.band
  decide (a056.D = (6/5 : Rat) ∧ a056.ac.b.lam = (7/8 : Rat) ∧ a056.bd.b.lam = (28/25 : Rat)),
  -- A057.domain
  aRowOK a057,
  -- A057.positive_M0
  decide (0 < cellM0 a057),
  -- A057.band
  decide (a057.D = (6/5 : Rat) ∧ a057.ac.b.lam = (7/8 : Rat) ∧ a057.bd.b.lam = (28/25 : Rat)),
  -- A058.domain
  aRowOK a058,
  -- A058.positive_M0
  decide (0 < cellM0 a058),
  -- A058.band
  decide (a058.D = (6/5 : Rat) ∧ a058.ac.b.lam = (7/8 : Rat) ∧ a058.bd.b.lam = (28/25 : Rat)),
  -- A059.domain
  aRowOK a059,
  -- A059.positive_M0
  decide (0 < cellM0 a059),
  -- A059.band
  decide (a059.D = (6/5 : Rat) ∧ a059.ac.b.lam = (7/8 : Rat) ∧ a059.bd.b.lam = (28/25 : Rat)),
  -- A060.domain
  aRowOK a060,
  -- A060.positive_M0
  decide (0 < cellM0 a060),
  -- A060.band
  decide (a060.D = (6/5 : Rat) ∧ a060.ac.b.lam = (7/8 : Rat) ∧ a060.bd.b.lam = (28/25 : Rat)),
  -- A061.domain
  aRowOK a061,
  -- A061.positive_M0
  decide (0 < cellM0 a061),
  -- A061.band
  decide (a061.D = (6/5 : Rat) ∧ a061.ac.b.lam = (28/25 : Rat) ∧ a061.bd.b.lam = (263/200 : Rat)),
  -- A062.domain
  aRowOK a062,
  -- A062.positive_M0
  decide (0 < cellM0 a062),
  -- A062.band
  decide (a062.D = (6/5 : Rat) ∧ a062.ac.b.lam = (28/25 : Rat) ∧ a062.bd.b.lam = (263/200 : Rat)),
  -- A063.domain
  aRowOK a063,
  -- A063.positive_M0
  decide (0 < cellM0 a063),
  -- A063.band
  decide (a063.D = (6/5 : Rat) ∧ a063.ac.b.lam = (28/25 : Rat) ∧ a063.bd.b.lam = (263/200 : Rat)),
  -- A064.domain
  aRowOK a064,
  -- A064.positive_M0
  decide (0 < cellM0 a064),
  -- A064.band
  decide (a064.D = (6/5 : Rat) ∧ a064.ac.b.lam = (28/25 : Rat) ∧ a064.bd.b.lam = (263/200 : Rat)),
  -- A065.domain
  aRowOK a065,
  -- A065.positive_M0
  decide (0 < cellM0 a065),
  -- A065.band
  decide (a065.D = (6/5 : Rat) ∧ a065.ac.b.lam = (28/25 : Rat) ∧ a065.bd.b.lam = (263/200 : Rat)),
  -- A066.domain
  aRowOK a066,
  -- A066.positive_M0
  decide (0 < cellM0 a066),
  -- A066.band
  decide (a066.D = (6/5 : Rat) ∧ a066.ac.b.lam = (28/25 : Rat) ∧ a066.bd.b.lam = (263/200 : Rat)),
  -- A067.domain
  aRowOK a067,
  -- A067.positive_M0
  decide (0 < cellM0 a067),
  -- A067.band
  decide (a067.D = (6/5 : Rat) ∧ a067.ac.b.lam = (28/25 : Rat) ∧ a067.bd.b.lam = (263/200 : Rat)),
  -- A068.domain
  aRowOK a068,
  -- A068.positive_M0
  decide (0 < cellM0 a068),
  -- A068.band
  decide (a068.D = (6/5 : Rat) ∧ a068.ac.b.lam = (28/25 : Rat) ∧ a068.bd.b.lam = (263/200 : Rat)),
  -- A069.domain
  aRowOK a069,
  -- A069.positive_M0
  decide (0 < cellM0 a069),
  -- A069.band
  decide (a069.D = (6/5 : Rat) ∧ a069.ac.b.lam = (28/25 : Rat) ∧ a069.bd.b.lam = (263/200 : Rat)),
  -- A070.domain
  aRowOK a070,
  -- A070.positive_M0
  decide (0 < cellM0 a070),
  -- A070.band
  decide (a070.D = (6/5 : Rat) ∧ a070.ac.b.lam = (28/25 : Rat) ∧ a070.bd.b.lam = (263/200 : Rat)),
  -- A071.domain
  aRowOK a071,
  -- A071.positive_M0
  decide (0 < cellM0 a071),
  -- A071.band
  decide (a071.D = (6/5 : Rat) ∧ a071.ac.b.lam = (28/25 : Rat) ∧ a071.bd.b.lam = (263/200 : Rat)),
  -- A072.domain
  aRowOK a072,
  -- A072.positive_M0
  decide (0 < cellM0 a072),
  -- A072.band
  decide (a072.D = (6/5 : Rat) ∧ a072.ac.b.lam = (28/25 : Rat) ∧ a072.bd.b.lam = (263/200 : Rat)),
  -- A073.domain
  aRowOK a073,
  -- A073.positive_M0
  decide (0 < cellM0 a073),
  -- A073.band
  decide (a073.D = (6/5 : Rat) ∧ a073.ac.b.lam = (28/25 : Rat) ∧ a073.bd.b.lam = (263/200 : Rat)),
  -- A074.domain
  aRowOK a074,
  -- A074.positive_M0
  decide (0 < cellM0 a074),
  -- A074.band
  decide (a074.D = (6/5 : Rat) ∧ a074.ac.b.lam = (28/25 : Rat) ∧ a074.bd.b.lam = (263/200 : Rat)),
  -- A075.domain
  aRowOK a075,
  -- A075.positive_M0
  decide (0 < cellM0 a075),
  -- A075.band
  decide (a075.D = (6/5 : Rat) ∧ a075.ac.b.lam = (28/25 : Rat) ∧ a075.bd.b.lam = (263/200 : Rat)),
  -- A076.domain
  aRowOK a076,
  -- A076.positive_M0
  decide (0 < cellM0 a076),
  -- A076.band
  decide (a076.D = (6/5 : Rat) ∧ a076.ac.b.lam = (28/25 : Rat) ∧ a076.bd.b.lam = (263/200 : Rat)),
  -- A077.domain
  aRowOK a077,
  -- A077.positive_M0
  decide (0 < cellM0 a077)
]
theorem checked : records.all id = true := by decide +kernel
theorem record_count : records.length = 64 := by decide +kernel
end Erdos993Lean.ExactComparisons.F3All.Validity011
