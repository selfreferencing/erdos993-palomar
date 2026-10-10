module

public import Erdos993Lean.ExactComparisons.F3All.Data

/-! Generated from the F3 text of version 2.10 of the manuscript.
No Python certificate evaluation is used; the checks are done by the Lean kernel. -/

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 400000
namespace Erdos993Lean.ExactComparisons.F3All.Validity016

def records : List Bool := [
  -- log.domain0016
  logUseOK (((1 : Rat) + ((7 : Rat) / (4 : Rat)))),
  -- log.domain0018
  logUseOK (((1 : Rat) + (2 : Rat))),
  -- log.domain0020
  logUseOK (((1 : Rat) + ((7 : Rat) / (3 : Rat)))),
  -- log.domain0022
  logUseOK (((1 : Rat) + (((1 : Rat) / (3 : Rat)) / ((10982853 : Rat) / (10000000 : Rat))))),
  -- log.domain0023
  logUseOK (((1 : Rat) + (((1 : Rat) / (3 : Rat)) / ((219657 : Rat) / (200000 : Rat))))),
  -- log.domain0024
  logUseOK (((1 : Rat) + (((1 : Rat) / (3 : Rat)) / ((376947 : Rat) / (312500 : Rat))))),
  -- log.domain0025
  logUseOK (((1 : Rat) + (((1 : Rat) / (3 : Rat)) / ((12062301 : Rat) / (10000000 : Rat))))),
  -- log.domain0026
  logUseOK (((1 : Rat) + (((1 : Rat) / (3 : Rat)) / ((6320593 : Rat) / (5000000 : Rat))))),
  -- log.domain0027
  logUseOK (((1 : Rat) + (((1 : Rat) / (3 : Rat)) / ((12641183 : Rat) / (10000000 : Rat))))),
  -- log.domain0028
  logUseOK (((1 : Rat) + (((1 : Rat) / (3 : Rat)) / ((13247849 : Rat) / (10000000 : Rat))))),
  -- log.domain0029
  logUseOK (((1 : Rat) + (((1 : Rat) / (3 : Rat)) / ((6623923 : Rat) / (5000000 : Rat))))),
  -- log.domain0030
  logUseOK (((1 : Rat) + (((1 : Rat) / (3 : Rat)) / ((3637479 : Rat) / (2500000 : Rat))))),
  -- log.domain0031
  logUseOK (((1 : Rat) + (((1 : Rat) / (3 : Rat)) / ((14549913 : Rat) / (10000000 : Rat))))),
  -- log.domain0032
  logUseOK (((1 : Rat) + (((1 : Rat) / (3 : Rat)) / ((3994989 : Rat) / (2500000 : Rat))))),
  -- log.domain0033
  logUseOK (((1 : Rat) + (((1 : Rat) / (3 : Rat)) / ((15979953 : Rat) / (10000000 : Rat))))),
  -- log.domain0034
  logUseOK (((1 : Rat) + (((1 : Rat) / (3 : Rat)) / ((4387637 : Rat) / (2500000 : Rat))))),
  -- log.domain0035
  logUseOK (((1 : Rat) + (((1 : Rat) / (3 : Rat)) / ((3510109 : Rat) / (2000000 : Rat))))),
  -- log.domain0036
  logUseOK (((1 : Rat) + (((1 : Rat) / (3 : Rat)) / ((10585001 : Rat) / (5000000 : Rat))))),
  -- log.domain0037
  logUseOK (((1 : Rat) + (((1 : Rat) / (3 : Rat)) / ((21169999 : Rat) / (10000000 : Rat))))),
  -- log.domain0038
  logUseOK (((1 : Rat) + (((1 : Rat) / (3 : Rat)) / ((3191987 : Rat) / (1250000 : Rat))))),
  -- log.domain0039
  logUseOK (((1 : Rat) + (((1 : Rat) / (3 : Rat)) / ((25535893 : Rat) / (10000000 : Rat))))),
  -- log.domain0040
  logUseOK (((1 : Rat) + (((1 : Rat) / (3 : Rat)) / ((3080217 : Rat) / (1000000 : Rat))))),
  -- log.domain0041
  logUseOK (((1 : Rat) + (((1 : Rat) / (3 : Rat)) / ((30802167 : Rat) / (10000000 : Rat))))),
  -- log.domain0042
  logUseOK (((1 : Rat) + (((1 : Rat) / (3 : Rat)) / ((37154509 : Rat) / (10000000 : Rat))))),
  -- log.domain0043
  logUseOK (((1 : Rat) + (((1 : Rat) / (3 : Rat)) / ((18577253 : Rat) / (5000000 : Rat))))),
  -- log.domain0044
  logUseOK (((1 : Rat) + (((1 : Rat) / (3 : Rat)) / ((22408447 : Rat) / (5000000 : Rat))))),
  -- log.domain0045
  logUseOK (((1 : Rat) + (((1 : Rat) / (3 : Rat)) / ((44816889 : Rat) / (10000000 : Rat))))),
  -- log.domain0046
  logUseOK (((1 : Rat) + (((1 : Rat) / (3 : Rat)) / ((32604103 : Rat) / (5000000 : Rat))))),
  -- log.domain0047
  logUseOK (((1 : Rat) + (((1 : Rat) / (3 : Rat)) / ((6520819 : Rat) / (1000000 : Rat))))),
  -- log.domain0048
  logUseOK (((1 : Rat) + (((1 : Rat) / (3 : Rat)) / ((23719357 : Rat) / (2500000 : Rat))))),
  -- log.domain0049
  logUseOK (((1 : Rat) + (((1 : Rat) / (3 : Rat)) / ((94877357 : Rat) / (10000000 : Rat))))),
  -- log.domain0050
  logUseOK (((1 : Rat) + (((1 : Rat) / (3 : Rat)) / ((100428229 : Rat) / (5000000 : Rat))))),
  -- log.domain0051
  logUseOK (((1 : Rat) + (((1 : Rat) / (3 : Rat)) / ((40171073 : Rat) / (2000000 : Rat))))),
  -- log.domain0052
  logUseOK (((1 : Rat) + (((3 : Rat) / (5 : Rat)) / ((10982853 : Rat) / (10000000 : Rat))))),
  -- log.domain0053
  logUseOK (((1 : Rat) + (((3 : Rat) / (5 : Rat)) / ((219657 : Rat) / (200000 : Rat))))),
  -- log.domain0054
  logUseOK (((1 : Rat) + (((3 : Rat) / (5 : Rat)) / ((376947 : Rat) / (312500 : Rat))))),
  -- log.domain0055
  logUseOK (((1 : Rat) + (((3 : Rat) / (5 : Rat)) / ((12062301 : Rat) / (10000000 : Rat))))),
  -- log.domain0056
  logUseOK (((1 : Rat) + (((3 : Rat) / (5 : Rat)) / ((6320593 : Rat) / (5000000 : Rat))))),
  -- log.domain0057
  logUseOK (((1 : Rat) + (((3 : Rat) / (5 : Rat)) / ((12641183 : Rat) / (10000000 : Rat))))),
  -- log.domain0058
  logUseOK (((1 : Rat) + (((3 : Rat) / (5 : Rat)) / ((13247849 : Rat) / (10000000 : Rat))))),
  -- log.domain0059
  logUseOK (((1 : Rat) + (((3 : Rat) / (5 : Rat)) / ((6623923 : Rat) / (5000000 : Rat))))),
  -- log.domain0060
  logUseOK (((1 : Rat) + (((3 : Rat) / (5 : Rat)) / ((13883627 : Rat) / (10000000 : Rat))))),
  -- log.domain0061
  logUseOK (((1 : Rat) + (((3 : Rat) / (5 : Rat)) / ((1735453 : Rat) / (1250000 : Rat))))),
  -- log.domain0062
  logUseOK (((1 : Rat) + (((3 : Rat) / (5 : Rat)) / ((3637479 : Rat) / (2500000 : Rat))))),
  -- log.domain0063
  logUseOK (((1 : Rat) + (((3 : Rat) / (5 : Rat)) / ((14549913 : Rat) / (10000000 : Rat))))),
  -- log.domain0064
  logUseOK (((1 : Rat) + (((3 : Rat) / (5 : Rat)) / ((15248181 : Rat) / (10000000 : Rat))))),
  -- log.domain0065
  logUseOK (((1 : Rat) + (((3 : Rat) / (5 : Rat)) / ((7624089 : Rat) / (5000000 : Rat))))),
  -- log.domain0066
  logUseOK (((1 : Rat) + (((3 : Rat) / (5 : Rat)) / ((3994989 : Rat) / (2500000 : Rat))))),
  -- log.domain0067
  logUseOK (((1 : Rat) + (((3 : Rat) / (5 : Rat)) / ((15979953 : Rat) / (10000000 : Rat))))),
  -- log.domain0068
  logUseOK (((1 : Rat) + (((3 : Rat) / (5 : Rat)) / ((4387637 : Rat) / (2500000 : Rat))))),
  -- log.domain0069
  logUseOK (((1 : Rat) + (((3 : Rat) / (5 : Rat)) / ((3510109 : Rat) / (2000000 : Rat))))),
  -- log.domain0070
  logUseOK (((1 : Rat) + (((3 : Rat) / (5 : Rat)) / ((9637753 : Rat) / (5000000 : Rat))))),
  -- log.domain0071
  logUseOK (((1 : Rat) + (((3 : Rat) / (5 : Rat)) / ((19275503 : Rat) / (10000000 : Rat))))),
  -- log.domain0072
  logUseOK (((1 : Rat) + (((3 : Rat) / (5 : Rat)) / ((10585001 : Rat) / (5000000 : Rat))))),
  -- log.domain0073
  logUseOK (((1 : Rat) + (((3 : Rat) / (5 : Rat)) / ((21169999 : Rat) / (10000000 : Rat))))),
  -- log.domain0074
  logUseOK (((1 : Rat) + (((3 : Rat) / (5 : Rat)) / ((11625349 : Rat) / (5000000 : Rat))))),
  -- log.domain0075
  logUseOK (((1 : Rat) + (((3 : Rat) / (5 : Rat)) / ((4650139 : Rat) / (2000000 : Rat))))),
  -- log.domain0076
  logUseOK (((1 : Rat) + (((3 : Rat) / (5 : Rat)) / ((3191987 : Rat) / (1250000 : Rat))))),
  -- log.domain0077
  logUseOK (((1 : Rat) + (((3 : Rat) / (5 : Rat)) / ((25535893 : Rat) / (10000000 : Rat))))),
  -- log.domain0078
  logUseOK (((1 : Rat) + (((3 : Rat) / (5 : Rat)) / ((3080217 : Rat) / (1000000 : Rat))))),
  -- log.domain0079
  logUseOK (((1 : Rat) + (((3 : Rat) / (5 : Rat)) / ((30802167 : Rat) / (10000000 : Rat))))),
  -- log.domain0080
  logUseOK (((1 : Rat) + (((3 : Rat) / (5 : Rat)) / ((37154509 : Rat) / (10000000 : Rat))))),
  -- log.domain0081
  logUseOK (((1 : Rat) + (((3 : Rat) / (5 : Rat)) / ((18577253 : Rat) / (5000000 : Rat))))),
  -- log.domain0082
  logUseOK (((1 : Rat) + (((3 : Rat) / (5 : Rat)) / ((22408447 : Rat) / (5000000 : Rat)))))
]
theorem checked : records.all id = true := by decide +kernel
theorem record_count : records.length = 64 := by decide +kernel
end Erdos993Lean.ExactComparisons.F3All.Validity016
