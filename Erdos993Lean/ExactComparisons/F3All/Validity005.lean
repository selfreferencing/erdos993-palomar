module

public import Erdos993Lean.ExactComparisons.F3All.Data

/-! Generated from the F3 text of version 2.10 of the manuscript.
No Python certificate evaluation is used; the checks are done by the Lean kernel. -/

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 400000
namespace Erdos993Lean.ExactComparisons.F3All.Validity005

def records : List Bool := [
  -- pt086.coordinates
  pointOK pt086,
  -- pt087.coordinates
  pointOK pt087,
  -- pt088.coordinates
  pointOK pt088,
  -- pt089.coordinates
  pointOK pt089,
  -- pt090.coordinates
  pointOK pt090,
  -- pt091.coordinates
  pointOK pt091,
  -- pt092.coordinates
  pointOK pt092,
  -- pt093.coordinates
  pointOK pt093,
  -- pt094.coordinates
  pointOK pt094,
  -- pt095.coordinates
  pointOK pt095,
  -- pt096.coordinates
  pointOK pt096,
  -- pt097.coordinates
  pointOK pt097,
  -- pt098.coordinates
  pointOK pt098,
  -- pt099.coordinates
  pointOK pt099,
  -- pt100.coordinates
  pointOK pt100,
  -- pt101.coordinates
  pointOK pt101,
  -- pt102.coordinates
  pointOK pt102,
  -- pt103.coordinates
  pointOK pt103,
  -- pt104.coordinates
  pointOK pt104,
  -- pt105.coordinates
  pointOK pt105,
  -- pt106.coordinates
  pointOK pt106,
  -- pt107.coordinates
  pointOK pt107,
  -- pt108.coordinates
  pointOK pt108,
  -- pt109.coordinates
  pointOK pt109,
  -- pt110.coordinates
  pointOK pt110,
  -- pt111.coordinates
  pointOK pt111,
  -- pt112.coordinates
  pointOK pt112,
  -- pt113.coordinates
  pointOK pt113,
  -- pt114.coordinates
  pointOK pt114,
  -- pt115.coordinates
  pointOK pt115,
  -- pt116.coordinates
  pointOK pt116,
  -- pt117.coordinates
  pointOK pt117,
  -- pt118.coordinates
  pointOK pt118,
  -- pt119.coordinates
  pointOK pt119,
  -- pt120.coordinates
  pointOK pt120,
  -- pt121.coordinates
  pointOK pt121,
  -- pt122.coordinates
  pointOK pt122,
  -- pt123.coordinates
  pointOK pt123,
  -- pt124.coordinates
  pointOK pt124,
  -- pt125.coordinates
  pointOK pt125,
  -- pt126.coordinates
  pointOK pt126,
  -- pt127.coordinates
  pointOK pt127,
  -- pt128.coordinates
  pointOK pt128,
  -- pt129.coordinates
  pointOK pt129,
  -- pt130.coordinates
  pointOK pt130,
  -- pt131.coordinates
  pointOK pt131,
  -- pt132.coordinates
  pointOK pt132,
  -- pt133.coordinates
  pointOK pt133,
  -- pt134.coordinates
  pointOK pt134,
  -- pt135.coordinates
  pointOK pt135,
  -- pt136.coordinates
  pointOK pt136,
  -- pt137.coordinates
  pointOK pt137,
  -- pt138.coordinates
  pointOK pt138,
  -- pt139.coordinates
  pointOK pt139,
  -- pt140.coordinates
  pointOK pt140,
  -- pt141.coordinates
  pointOK pt141,
  -- pt142.coordinates
  pointOK pt142,
  -- pt143.coordinates
  pointOK pt143,
  -- pt144.coordinates
  pointOK pt144,
  -- pt145.coordinates
  pointOK pt145,
  -- pt146.coordinates
  pointOK pt146,
  -- pt147.coordinates
  pointOK pt147,
  -- pt148.coordinates
  pointOK pt148,
  -- pt149.coordinates
  pointOK pt149
]
theorem checked : records.all id = true := by decide +kernel
theorem record_count : records.length = 64 := by decide +kernel
end Erdos993Lean.ExactComparisons.F3All.Validity005
