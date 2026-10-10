module

public import Erdos993Lean.ExactComparisons.F3All.Data

/-! Generated from the F3 text of version 2.10 of the manuscript.
No Python certificate evaluation is used; the checks are done by the Lean kernel. -/

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 400000
namespace Erdos993Lean.ExactComparisons.F3All.Validity006

def records : List Bool := [
  -- pt150.coordinates
  pointOK pt150,
  -- pt151.coordinates
  pointOK pt151,
  -- pt152.coordinates
  pointOK pt152,
  -- pt153.coordinates
  pointOK pt153,
  -- pt154.coordinates
  pointOK pt154,
  -- pt155.coordinates
  pointOK pt155,
  -- pt156.coordinates
  pointOK pt156,
  -- pt157.coordinates
  pointOK pt157,
  -- pt158.coordinates
  pointOK pt158,
  -- pt159.coordinates
  pointOK pt159,
  -- pt160.coordinates
  pointOK pt160,
  -- pt161.coordinates
  pointOK pt161,
  -- pt162.coordinates
  pointOK pt162,
  -- pt163.coordinates
  pointOK pt163,
  -- pt164.coordinates
  pointOK pt164,
  -- pt165.coordinates
  pointOK pt165,
  -- pt166.coordinates
  pointOK pt166,
  -- pt167.coordinates
  pointOK pt167,
  -- pt168.coordinates
  pointOK pt168,
  -- pt169.coordinates
  pointOK pt169,
  -- pt170.coordinates
  pointOK pt170,
  -- pt171.coordinates
  pointOK pt171,
  -- pt172.coordinates
  pointOK pt172,
  -- pt173.coordinates
  pointOK pt173,
  -- pt174.coordinates
  pointOK pt174,
  -- pt175.coordinates
  pointOK pt175,
  -- pt176.coordinates
  pointOK pt176,
  -- pt177.coordinates
  pointOK pt177,
  -- pt178.coordinates
  pointOK pt178,
  -- pt179.coordinates
  pointOK pt179,
  -- pt180.coordinates
  pointOK pt180,
  -- pt181.coordinates
  pointOK pt181,
  -- pt182.coordinates
  pointOK pt182,
  -- pt183.coordinates
  pointOK pt183,
  -- pt184.coordinates
  pointOK pt184,
  -- pt185.coordinates
  pointOK pt185,
  -- pt186.coordinates
  pointOK pt186,
  -- pt187.coordinates
  pointOK pt187,
  -- pt188.coordinates
  pointOK pt188,
  -- pt189.coordinates
  pointOK pt189,
  -- pt190.coordinates
  pointOK pt190,
  -- pt191.coordinates
  pointOK pt191,
  -- pt192.coordinates
  pointOK pt192,
  -- pt193.coordinates
  pointOK pt193,
  -- pt194.coordinates
  pointOK pt194,
  -- pt195.coordinates
  pointOK pt195,
  -- pt196.coordinates
  pointOK pt196,
  -- pt197.coordinates
  pointOK pt197,
  -- pt198.coordinates
  pointOK pt198,
  -- pt199.coordinates
  pointOK pt199,
  -- pt200.coordinates
  pointOK pt200,
  -- pt201.coordinates
  pointOK pt201,
  -- pt202.coordinates
  pointOK pt202,
  -- pt203.coordinates
  pointOK pt203,
  -- pt204.coordinates
  pointOK pt204,
  -- pt205.coordinates
  pointOK pt205,
  -- pt206.coordinates
  pointOK pt206,
  -- pt207.coordinates
  pointOK pt207,
  -- pt208.coordinates
  pointOK pt208,
  -- pt209.coordinates
  pointOK pt209,
  -- pt210.coordinates
  pointOK pt210,
  -- pt211.coordinates
  pointOK pt211,
  -- pt212.coordinates
  pointOK pt212,
  -- pt213.coordinates
  pointOK pt213
]
theorem checked : records.all id = true := by decide +kernel
theorem record_count : records.length = 64 := by decide +kernel
end Erdos993Lean.ExactComparisons.F3All.Validity006
