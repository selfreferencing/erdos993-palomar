module

public import Erdos993Lean.ExactComparisons.F3All.Data

/-! Generated from the F3 text of version 2.10 of the manuscript.
No Python certificate evaluation is used; the checks are done by the Lean kernel. -/

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 400000
namespace Erdos993Lean.ExactComparisons.F3All.Validity010

def records : List Bool := [
  -- A035.domain
  aRowOK a035,
  -- A035.positive_M0
  decide (0 < cellM0 a035),
  -- A035.band
  decide (a035.D = (6/5 : Rat) ∧ a035.ac.b.lam = (7/8 : Rat) ∧ a035.bd.b.lam = (28/25 : Rat)),
  -- A036.domain
  aRowOK a036,
  -- A036.positive_M0
  decide (0 < cellM0 a036),
  -- A036.band
  decide (a036.D = (6/5 : Rat) ∧ a036.ac.b.lam = (7/8 : Rat) ∧ a036.bd.b.lam = (28/25 : Rat)),
  -- A037.domain
  aRowOK a037,
  -- A037.positive_M0
  decide (0 < cellM0 a037),
  -- A037.band
  decide (a037.D = (6/5 : Rat) ∧ a037.ac.b.lam = (7/8 : Rat) ∧ a037.bd.b.lam = (28/25 : Rat)),
  -- A038.domain
  aRowOK a038,
  -- A038.positive_M0
  decide (0 < cellM0 a038),
  -- A038.band
  decide (a038.D = (6/5 : Rat) ∧ a038.ac.b.lam = (7/8 : Rat) ∧ a038.bd.b.lam = (28/25 : Rat)),
  -- A039.domain
  aRowOK a039,
  -- A039.positive_M0
  decide (0 < cellM0 a039),
  -- A039.band
  decide (a039.D = (6/5 : Rat) ∧ a039.ac.b.lam = (7/8 : Rat) ∧ a039.bd.b.lam = (28/25 : Rat)),
  -- A040.domain
  aRowOK a040,
  -- A040.positive_M0
  decide (0 < cellM0 a040),
  -- A040.band
  decide (a040.D = (6/5 : Rat) ∧ a040.ac.b.lam = (7/8 : Rat) ∧ a040.bd.b.lam = (28/25 : Rat)),
  -- A041.domain
  aRowOK a041,
  -- A041.positive_M0
  decide (0 < cellM0 a041),
  -- A041.band
  decide (a041.D = (6/5 : Rat) ∧ a041.ac.b.lam = (7/8 : Rat) ∧ a041.bd.b.lam = (28/25 : Rat)),
  -- A042.domain
  aRowOK a042,
  -- A042.positive_M0
  decide (0 < cellM0 a042),
  -- A042.band
  decide (a042.D = (6/5 : Rat) ∧ a042.ac.b.lam = (7/8 : Rat) ∧ a042.bd.b.lam = (28/25 : Rat)),
  -- A043.domain
  aRowOK a043,
  -- A043.positive_M0
  decide (0 < cellM0 a043),
  -- A043.band
  decide (a043.D = (6/5 : Rat) ∧ a043.ac.b.lam = (7/8 : Rat) ∧ a043.bd.b.lam = (28/25 : Rat)),
  -- A044.domain
  aRowOK a044,
  -- A044.positive_M0
  decide (0 < cellM0 a044),
  -- A044.band
  decide (a044.D = (6/5 : Rat) ∧ a044.ac.b.lam = (7/8 : Rat) ∧ a044.bd.b.lam = (28/25 : Rat)),
  -- A045.domain
  aRowOK a045,
  -- A045.positive_M0
  decide (0 < cellM0 a045),
  -- A045.band
  decide (a045.D = (6/5 : Rat) ∧ a045.ac.b.lam = (7/8 : Rat) ∧ a045.bd.b.lam = (28/25 : Rat)),
  -- A046.domain
  aRowOK a046,
  -- A046.positive_M0
  decide (0 < cellM0 a046),
  -- A046.band
  decide (a046.D = (6/5 : Rat) ∧ a046.ac.b.lam = (7/8 : Rat) ∧ a046.bd.b.lam = (28/25 : Rat)),
  -- A047.domain
  aRowOK a047,
  -- A047.positive_M0
  decide (0 < cellM0 a047),
  -- A047.band
  decide (a047.D = (6/5 : Rat) ∧ a047.ac.b.lam = (7/8 : Rat) ∧ a047.bd.b.lam = (28/25 : Rat)),
  -- A048.domain
  aRowOK a048,
  -- A048.positive_M0
  decide (0 < cellM0 a048),
  -- A048.band
  decide (a048.D = (6/5 : Rat) ∧ a048.ac.b.lam = (7/8 : Rat) ∧ a048.bd.b.lam = (28/25 : Rat)),
  -- A049.domain
  aRowOK a049,
  -- A049.positive_M0
  decide (0 < cellM0 a049),
  -- A049.band
  decide (a049.D = (6/5 : Rat) ∧ a049.ac.b.lam = (7/8 : Rat) ∧ a049.bd.b.lam = (28/25 : Rat)),
  -- A050.domain
  aRowOK a050,
  -- A050.positive_M0
  decide (0 < cellM0 a050),
  -- A050.band
  decide (a050.D = (6/5 : Rat) ∧ a050.ac.b.lam = (7/8 : Rat) ∧ a050.bd.b.lam = (28/25 : Rat)),
  -- A051.domain
  aRowOK a051,
  -- A051.positive_M0
  decide (0 < cellM0 a051),
  -- A051.band
  decide (a051.D = (6/5 : Rat) ∧ a051.ac.b.lam = (7/8 : Rat) ∧ a051.bd.b.lam = (28/25 : Rat)),
  -- A052.domain
  aRowOK a052,
  -- A052.positive_M0
  decide (0 < cellM0 a052),
  -- A052.band
  decide (a052.D = (6/5 : Rat) ∧ a052.ac.b.lam = (7/8 : Rat) ∧ a052.bd.b.lam = (28/25 : Rat)),
  -- A053.domain
  aRowOK a053,
  -- A053.positive_M0
  decide (0 < cellM0 a053),
  -- A053.band
  decide (a053.D = (6/5 : Rat) ∧ a053.ac.b.lam = (7/8 : Rat) ∧ a053.bd.b.lam = (28/25 : Rat)),
  -- A054.domain
  aRowOK a054,
  -- A054.positive_M0
  decide (0 < cellM0 a054),
  -- A054.band
  decide (a054.D = (6/5 : Rat) ∧ a054.ac.b.lam = (7/8 : Rat) ∧ a054.bd.b.lam = (28/25 : Rat)),
  -- A055.domain
  aRowOK a055,
  -- A055.positive_M0
  decide (0 < cellM0 a055),
  -- A055.band
  decide (a055.D = (6/5 : Rat) ∧ a055.ac.b.lam = (7/8 : Rat) ∧ a055.bd.b.lam = (28/25 : Rat)),
  -- A056.domain
  aRowOK a056
]
theorem checked : records.all id = true := by decide +kernel
theorem record_count : records.length = 64 := by decide +kernel
end Erdos993Lean.ExactComparisons.F3All.Validity010
