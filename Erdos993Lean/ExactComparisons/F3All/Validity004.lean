module

public import Erdos993Lean.ExactComparisons.F3All.Data

/-! Generated from the F3 text of version 2.10 of the manuscript.
No Python certificate evaluation is used; the checks are done by the Lean kernel. -/

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 400000
namespace Erdos993Lean.ExactComparisons.F3All.Validity004

def records : List Bool := [
  -- pt022.coordinates
  pointOK pt022,
  -- pt023.coordinates
  pointOK pt023,
  -- pt024.coordinates
  pointOK pt024,
  -- pt025.coordinates
  pointOK pt025,
  -- pt026.coordinates
  pointOK pt026,
  -- pt027.coordinates
  pointOK pt027,
  -- pt028.coordinates
  pointOK pt028,
  -- pt029.coordinates
  pointOK pt029,
  -- pt030.coordinates
  pointOK pt030,
  -- pt031.coordinates
  pointOK pt031,
  -- pt032.coordinates
  pointOK pt032,
  -- pt033.coordinates
  pointOK pt033,
  -- pt034.coordinates
  pointOK pt034,
  -- pt035.coordinates
  pointOK pt035,
  -- pt036.coordinates
  pointOK pt036,
  -- pt037.coordinates
  pointOK pt037,
  -- pt038.coordinates
  pointOK pt038,
  -- pt039.coordinates
  pointOK pt039,
  -- pt040.coordinates
  pointOK pt040,
  -- pt041.coordinates
  pointOK pt041,
  -- pt042.coordinates
  pointOK pt042,
  -- pt043.coordinates
  pointOK pt043,
  -- pt044.coordinates
  pointOK pt044,
  -- pt045.coordinates
  pointOK pt045,
  -- pt046.coordinates
  pointOK pt046,
  -- pt047.coordinates
  pointOK pt047,
  -- pt048.coordinates
  pointOK pt048,
  -- pt049.coordinates
  pointOK pt049,
  -- pt050.coordinates
  pointOK pt050,
  -- pt051.coordinates
  pointOK pt051,
  -- pt052.coordinates
  pointOK pt052,
  -- pt053.coordinates
  pointOK pt053,
  -- pt054.coordinates
  pointOK pt054,
  -- pt055.coordinates
  pointOK pt055,
  -- pt056.coordinates
  pointOK pt056,
  -- pt057.coordinates
  pointOK pt057,
  -- pt058.coordinates
  pointOK pt058,
  -- pt059.coordinates
  pointOK pt059,
  -- pt060.coordinates
  pointOK pt060,
  -- pt061.coordinates
  pointOK pt061,
  -- pt062.coordinates
  pointOK pt062,
  -- pt063.coordinates
  pointOK pt063,
  -- pt064.coordinates
  pointOK pt064,
  -- pt065.coordinates
  pointOK pt065,
  -- pt066.coordinates
  pointOK pt066,
  -- pt067.coordinates
  pointOK pt067,
  -- pt068.coordinates
  pointOK pt068,
  -- pt069.coordinates
  pointOK pt069,
  -- pt070.coordinates
  pointOK pt070,
  -- pt071.coordinates
  pointOK pt071,
  -- pt072.coordinates
  pointOK pt072,
  -- pt073.coordinates
  pointOK pt073,
  -- pt074.coordinates
  pointOK pt074,
  -- pt075.coordinates
  pointOK pt075,
  -- pt076.coordinates
  pointOK pt076,
  -- pt077.coordinates
  pointOK pt077,
  -- pt078.coordinates
  pointOK pt078,
  -- pt079.coordinates
  pointOK pt079,
  -- pt080.coordinates
  pointOK pt080,
  -- pt081.coordinates
  pointOK pt081,
  -- pt082.coordinates
  pointOK pt082,
  -- pt083.coordinates
  pointOK pt083,
  -- pt084.coordinates
  pointOK pt084,
  -- pt085.coordinates
  pointOK pt085
]
theorem checked : records.all id = true := by decide +kernel
theorem record_count : records.length = 64 := by decide +kernel
end Erdos993Lean.ExactComparisons.F3All.Validity004
