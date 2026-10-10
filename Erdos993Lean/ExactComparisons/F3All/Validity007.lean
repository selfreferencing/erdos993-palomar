module

public import Erdos993Lean.ExactComparisons.F3All.Data

/-! Generated from the F3 text of version 2.10 of the manuscript.
No Python certificate evaluation is used; the checks are done by the Lean kernel. -/

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 400000
namespace Erdos993Lean.ExactComparisons.F3All.Validity007

def records : List Bool := [
  -- pt214.coordinates
  pointOK pt214,
  -- pt215.coordinates
  pointOK pt215,
  -- pt216.coordinates
  pointOK pt216,
  -- pt217.coordinates
  pointOK pt217,
  -- pt218.coordinates
  pointOK pt218,
  -- pt219.coordinates
  pointOK pt219,
  -- pt220.coordinates
  pointOK pt220,
  -- pt221.coordinates
  pointOK pt221,
  -- pt222.coordinates
  pointOK pt222,
  -- pt223.coordinates
  pointOK pt223,
  -- pt224.coordinates
  pointOK pt224,
  -- pt225.coordinates
  pointOK pt225,
  -- pt226.coordinates
  pointOK pt226,
  -- pt227.coordinates
  pointOK pt227,
  -- pt228.coordinates
  pointOK pt228,
  -- pt229.coordinates
  pointOK pt229,
  -- pt230.coordinates
  pointOK pt230,
  -- pt231.coordinates
  pointOK pt231,
  -- pt232.coordinates
  pointOK pt232,
  -- pt233.coordinates
  pointOK pt233,
  -- pt234.coordinates
  pointOK pt234,
  -- pt235.coordinates
  pointOK pt235,
  -- pt236.coordinates
  pointOK pt236,
  -- pt237.coordinates
  pointOK pt237,
  -- pt238.coordinates
  pointOK pt238,
  -- pt239.coordinates
  pointOK pt239,
  -- pt240.coordinates
  pointOK pt240,
  -- pt241.coordinates
  pointOK pt241,
  -- pt242.coordinates
  pointOK pt242,
  -- pt243.coordinates
  pointOK pt243,
  -- pt244.coordinates
  pointOK pt244,
  -- pt245.coordinates
  pointOK pt245,
  -- pt246.coordinates
  pointOK pt246,
  -- pt247.coordinates
  pointOK pt247,
  -- pt248.coordinates
  pointOK pt248,
  -- pt249.coordinates
  pointOK pt249,
  -- pt250.coordinates
  pointOK pt250,
  -- pt251.coordinates
  pointOK pt251,
  -- pt252.coordinates
  pointOK pt252,
  -- pt253.coordinates
  pointOK pt253,
  -- pt254.coordinates
  pointOK pt254,
  -- pt255.coordinates
  pointOK pt255,
  -- pt256.coordinates
  pointOK pt256,
  -- pt257.coordinates
  pointOK pt257,
  -- pt258.coordinates
  pointOK pt258,
  -- pt259.coordinates
  pointOK pt259,
  -- pt260.coordinates
  pointOK pt260,
  -- C001.domain
  cRowOK c001,
  -- C002.domain
  cRowOK c002,
  -- C003.domain
  cRowOK c003,
  -- C004.domain
  cRowOK c004,
  -- C005.domain
  cRowOK c005,
  -- C006.domain
  cRowOK c006,
  -- C007.domain
  cRowOK c007,
  -- C008.domain
  cRowOK c008,
  -- C009.domain
  cRowOK c009,
  -- C010.domain
  cRowOK c010,
  -- C011.domain
  cRowOK c011,
  -- C012.domain
  cRowOK c012,
  -- C013.domain
  cRowOK c013,
  -- C014.domain
  cRowOK c014,
  -- C015.domain
  cRowOK c015,
  -- C016.domain
  cRowOK c016,
  -- C017.domain
  cRowOK c017
]
theorem checked : records.all id = true := by decide +kernel
theorem record_count : records.length = 64 := by decide +kernel
end Erdos993Lean.ExactComparisons.F3All.Validity007
