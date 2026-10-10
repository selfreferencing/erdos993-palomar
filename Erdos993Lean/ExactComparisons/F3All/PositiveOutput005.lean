module

public import Erdos993Lean.ExactComparisons.F3All.Data

/-! Generated from the F3 text of version 2.10 of the manuscript.
No Python certificate evaluation is used; the checks are done by the Lean kernel. -/

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 400000
namespace Erdos993Lean.ExactComparisons.F3All.PositiveOutput005

def records : List Comparison := [
  -- A094.positive_gp; A094: D=6/5, lambda in [28/25,263/200], y in [93/64,3/2], m=49/100: delta > 491137/1000000 > 0; B_balance > 136972/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((491137 : Rat)) .lt,
  -- A094.positive_g; A094: D=6/5, lambda in [28/25,263/200], y in [93/64,3/2], m=49/100: delta > 491137/1000000 > 0; B_balance > 136972/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((136972 : Rat)) .lt,
  -- A095.positive_gp; A095: D=6/5, lambda in [28/25,263/200], y in [3/2,99/64], m=49/100: delta > 488107/1000000 > 0; B_balance > 183050/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((488107 : Rat)) .lt,
  -- A095.positive_g; A095: D=6/5, lambda in [28/25,263/200], y in [3/2,99/64], m=49/100: delta > 488107/1000000 > 0; B_balance > 183050/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((183050 : Rat)) .lt,
  -- A096.positive_gp; A096: D=6/5, lambda in [28/25,263/200], y in [99/64,51/32], m=49/100: delta > 487272/1000000 > 0; B_balance > 242707/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((487272 : Rat)) .lt,
  -- A096.positive_g; A096: D=6/5, lambda in [28/25,263/200], y in [99/64,51/32], m=49/100: delta > 487272/1000000 > 0; B_balance > 242707/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((242707 : Rat)) .lt,
  -- A097.positive_gp; A097: D=6/5, lambda in [28/25,263/200], y in [51/32,27/16], m=49/100: delta > 429985/1000000 > 0; B_balance > 4245/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((429985 : Rat)) .lt,
  -- A097.positive_g; A097: D=6/5, lambda in [28/25,263/200], y in [51/32,27/16], m=49/100: delta > 429985/1000000 > 0; B_balance > 4245/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((4245 : Rat)) .lt,
  -- A098.positive_gp; A098: D=6/5, lambda in [28/25,263/200], y in [27/16,57/32], m=49/100: delta > 440072/1000000 > 0; B_balance > 193971/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((440072 : Rat)) .lt,
  -- A098.positive_g; A098: D=6/5, lambda in [28/25,263/200], y in [27/16,57/32], m=49/100: delta > 440072/1000000 > 0; B_balance > 193971/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((193971 : Rat)) .lt,
  -- A099.positive_gp; A099: D=6/5, lambda in [28/25,263/200], y in [57/32,15/8], m=49/100: delta > 461680/1000000 > 0; B_balance > 491647/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((461680 : Rat)) .lt,
  -- A099.positive_g; A099: D=6/5, lambda in [28/25,263/200], y in [57/32,15/8], m=49/100: delta > 461680/1000000 > 0; B_balance > 491647/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((491647 : Rat)) .lt,
  -- A100.positive_gp; A100: D=6/5, lambda in [28/25,263/200], y in [15/8,63/32], m=49/100: delta > 496256/1000000 > 0; B_balance > 912229/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((496256 : Rat)) .lt,
  -- A100.positive_g; A100: D=6/5, lambda in [28/25,263/200], y in [15/8,63/32], m=49/100: delta > 496256/1000000 > 0; B_balance > 912229/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((912229 : Rat)) .lt,
  -- A101.positive_gp; A101: D=6/5, lambda in [28/25,263/200], y in [63/32,33/16], m=49/100: delta > 545355/1000000 > 0; B_balance > 1462111/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((545355 : Rat)) .lt,
  -- A101.positive_g; A101: D=6/5, lambda in [28/25,263/200], y in [63/32,33/16], m=49/100: delta > 545355/1000000 > 0; B_balance > 1462111/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((1462111 : Rat)) .lt,
  -- A102.positive_gp; A102: D=6/5, lambda in [28/25,263/200], y in [33/16,9/4], m=49/100: delta > 488316/1000000 > 0; B_balance > 1389088/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((488316 : Rat)) .lt,
  -- A102.positive_g; A102: D=6/5, lambda in [28/25,263/200], y in [33/16,9/4], m=49/100: delta > 488316/1000000 > 0; B_balance > 1389088/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((1389088 : Rat)) .lt,
  -- A103.positive_gp; A103: D=6/5, lambda in [28/25,263/200], y in [9/4,21/8], m=49/100: delta > 428874/1000000 > 0; B_balance > 1438246/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((428874 : Rat)) .lt,
  -- A103.positive_g; A103: D=6/5, lambda in [28/25,263/200], y in [9/4,21/8], m=49/100: delta > 428874/1000000 > 0; B_balance > 1438246/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((1438246 : Rat)) .lt,
  -- A104.positive_gp; A104: D=6/5, lambda in [28/25,263/200], y in [21/8,3], m=49/100: delta > 1087949/1000000 > 0; B_balance > 8016025/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((1087949 : Rat)) .lt,
  -- A104.positive_g; A104: D=6/5, lambda in [28/25,263/200], y in [21/8,3], m=49/100: delta > 1087949/1000000 > 0; B_balance > 8016025/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((8016025 : Rat)) .lt,
  -- A105.positive_gp; A105: D=7/5, lambda in [263/200,3/2], y in [0,3/8], m=1/3: delta > 793753/1000000 > 0; B_balance > 96522/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((793753 : Rat)) .lt,
  -- A105.positive_g; A105: D=7/5, lambda in [263/200,3/2], y in [0,3/8], m=1/3: delta > 793753/1000000 > 0; B_balance > 96522/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((96522 : Rat)) .lt,
  -- A106.positive_gp; A106: D=7/5, lambda in [263/200,3/2], y in [3/8,9/16], m=2/5: delta > 766204/1000000 > 0; B_balance > 4465/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((766204 : Rat)) .lt,
  -- A106.positive_g; A106: D=7/5, lambda in [263/200,3/2], y in [3/8,9/16], m=2/5: delta > 766204/1000000 > 0; B_balance > 4465/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((4465 : Rat)) .lt,
  -- A107.positive_gp; A107: D=7/5, lambda in [263/200,3/2], y in [9/16,21/32], m=49/100: delta > 765155/1000000 > 0; B_balance > 33905/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((765155 : Rat)) .lt,
  -- A107.positive_g; A107: D=7/5, lambda in [263/200,3/2], y in [9/16,21/32], m=49/100: delta > 765155/1000000 > 0; B_balance > 33905/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((33905 : Rat)) .lt,
  -- A108.positive_gp; A108: D=7/5, lambda in [263/200,3/2], y in [21/32,3/4], m=49/100: delta > 728010/1000000 > 0; B_balance > 47067/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((728010 : Rat)) .lt,
  -- A108.positive_g; A108: D=7/5, lambda in [263/200,3/2], y in [21/32,3/4], m=49/100: delta > 728010/1000000 > 0; B_balance > 47067/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((47067 : Rat)) .lt,
  -- A109.positive_gp; A109: D=7/5, lambda in [263/200,3/2], y in [3/4,27/32], m=49/100: delta > 691734/1000000 > 0; B_balance > 62995/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((691734 : Rat)) .lt,
  -- A109.positive_g; A109: D=7/5, lambda in [263/200,3/2], y in [3/4,27/32], m=49/100: delta > 691734/1000000 > 0; B_balance > 62995/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((62995 : Rat)) .lt,
  -- A110.positive_gp; A110: D=7/5, lambda in [263/200,3/2], y in [27/32,15/16], m=49/100: delta > 656955/1000000 > 0; B_balance > 82571/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((656955 : Rat)) .lt,
  -- A110.positive_g; A110: D=7/5, lambda in [263/200,3/2], y in [27/32,15/16], m=49/100: delta > 656955/1000000 > 0; B_balance > 82571/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((82571 : Rat)) .lt,
  -- A111.positive_gp; A111: D=7/5, lambda in [263/200,3/2], y in [15/16,33/32], m=49/100: delta > 624356/1000000 > 0; B_balance > 106135/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((624356 : Rat)) .lt,
  -- A111.positive_g; A111: D=7/5, lambda in [263/200,3/2], y in [15/16,33/32], m=49/100: delta > 624356/1000000 > 0; B_balance > 106135/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((106135 : Rat)) .lt,
  -- A112.positive_gp; A112: D=7/5, lambda in [263/200,3/2], y in [33/32,9/8], m=49/100: delta > 594015/1000000 > 0; B_balance > 133466/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((594015 : Rat)) .lt,
  -- A112.positive_g; A112: D=7/5, lambda in [263/200,3/2], y in [33/32,9/8], m=49/100: delta > 594015/1000000 > 0; B_balance > 133466/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((133466 : Rat)) .lt,
  -- A113.positive_gp; A113: D=7/5, lambda in [263/200,3/2], y in [9/8,39/32], m=49/100: delta > 566344/1000000 > 0; B_balance > 165026/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((566344 : Rat)) .lt,
  -- A113.positive_g; A113: D=7/5, lambda in [263/200,3/2], y in [9/8,39/32], m=49/100: delta > 566344/1000000 > 0; B_balance > 165026/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((165026 : Rat)) .lt,
  -- A114.positive_gp; A114: D=7/5, lambda in [263/200,3/2], y in [39/32,21/16], m=49/100: delta > 542959/1000000 > 0; B_balance > 205461/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((542959 : Rat)) .lt,
  -- A114.positive_g; A114: D=7/5, lambda in [263/200,3/2], y in [39/32,21/16], m=49/100: delta > 542959/1000000 > 0; B_balance > 205461/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((205461 : Rat)) .lt,
  -- A115.positive_gp; A115: D=7/5, lambda in [263/200,3/2], y in [21/16,45/32], m=49/100: delta > 524786/1000000 > 0; B_balance > 259771/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((524786 : Rat)) .lt,
  -- A115.positive_g; A115: D=7/5, lambda in [263/200,3/2], y in [21/16,45/32], m=49/100: delta > 524786/1000000 > 0; B_balance > 259771/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((259771 : Rat)) .lt,
  -- A116.positive_gp; A116: D=7/5, lambda in [263/200,3/2], y in [45/32,3/2], m=49/100: delta > 512819/1000000 > 0; B_balance > 335286/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((512819 : Rat)) .lt,
  -- A116.positive_g; A116: D=7/5, lambda in [263/200,3/2], y in [45/32,3/2], m=49/100: delta > 512819/1000000 > 0; B_balance > 335286/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((335286 : Rat)) .lt,
  -- A117.positive_gp; A117: D=7/5, lambda in [263/200,3/2], y in [3/2,27/16], m=49/100: delta > 399708/1000000 > 0; B_balance > 50669/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((399708 : Rat)) .lt,
  -- A117.positive_g; A117: D=7/5, lambda in [263/200,3/2], y in [3/2,27/16], m=49/100: delta > 399708/1000000 > 0; B_balance > 50669/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((50669 : Rat)) .lt,
  -- A118.positive_gp; A118: D=7/5, lambda in [263/200,3/2], y in [27/16,15/8], m=49/100: delta > 414145/1000000 > 0; B_balance > 340900/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((414145 : Rat)) .lt,
  -- A118.positive_g; A118: D=7/5, lambda in [263/200,3/2], y in [27/16,15/8], m=49/100: delta > 414145/1000000 > 0; B_balance > 340900/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((340900 : Rat)) .lt,
  -- A119.positive_gp; A119: D=7/5, lambda in [263/200,3/2], y in [15/8,33/16], m=49/100: delta > 473150/1000000 > 0; B_balance > 978955/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((473150 : Rat)) .lt,
  -- A119.positive_g; A119: D=7/5, lambda in [263/200,3/2], y in [15/8,33/16], m=49/100: delta > 473150/1000000 > 0; B_balance > 978955/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((978955 : Rat)) .lt,
  -- A120.positive_gp; A120: D=7/5, lambda in [263/200,3/2], y in [33/16,9/4], m=49/100: delta > 588170/1000000 > 0; B_balance > 2024459/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((588170 : Rat)) .lt,
  -- A120.positive_g; A120: D=7/5, lambda in [263/200,3/2], y in [33/16,9/4], m=49/100: delta > 588170/1000000 > 0; B_balance > 2024459/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((2024459 : Rat)) .lt,
  -- A121.positive_gp; A121: D=7/5, lambda in [263/200,3/2], y in [9/4,21/8], m=49/100: delta > 543517/1000000 > 0; B_balance > 2553388/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((543517 : Rat)) .lt,
  -- A121.positive_g; A121: D=7/5, lambda in [263/200,3/2], y in [9/4,21/8], m=49/100: delta > 543517/1000000 > 0; B_balance > 2553388/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((2553388 : Rat)) .lt,
  -- A122.positive_gp; A122: D=7/5, lambda in [263/200,3/2], y in [21/8,3], m=49/100: delta > 1185938/1000000 > 0; B_balance > 7247053/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((1185938 : Rat)) .lt,
  -- A122.positive_g; A122: D=7/5, lambda in [263/200,3/2], y in [21/8,3], m=49/100: delta > 1185938/1000000 > 0; B_balance > 7247053/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((7247053 : Rat)) .lt,
  -- A123.positive_gp; A123: D=8/5, lambda in [3/2,7/4], y in [0,3/8], m=1/3: delta > 787254/1000000 > 0; B_balance > 134400/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((787254 : Rat)) .lt,
  -- A123.positive_g; A123: D=8/5, lambda in [3/2,7/4], y in [0,3/8], m=1/3: delta > 787254/1000000 > 0; B_balance > 134400/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((134400 : Rat)) .lt,
  -- A124.positive_gp; A124: D=8/5, lambda in [3/2,7/4], y in [3/8,9/16], m=1/3: delta > 764369/1000000 > 0; B_balance > 53565/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((764369 : Rat)) .lt,
  -- A124.positive_g; A124: D=8/5, lambda in [3/2,7/4], y in [3/8,9/16], m=1/3: delta > 764369/1000000 > 0; B_balance > 53565/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((53565 : Rat)) .lt,
  -- A125.positive_gp; A125: D=8/5, lambda in [3/2,7/4], y in [9/16,3/4], m=49/100: delta > 689674/1000000 > 0; B_balance > 30535/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((689674 : Rat)) .lt,
  -- A125.positive_g; A125: D=8/5, lambda in [3/2,7/4], y in [9/16,3/4], m=49/100: delta > 689674/1000000 > 0; B_balance > 30535/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((30535 : Rat)) .lt
]

theorem checked : check records = true := by decide +kernel
theorem sound : ∀ c ∈ records, c.rationalHolds := check_sound records checked
theorem record_count : records.length = 64 := by decide +kernel

end Erdos993Lean.ExactComparisons.F3All.PositiveOutput005
