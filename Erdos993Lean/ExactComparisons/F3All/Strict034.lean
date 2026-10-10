module

public import Erdos993Lean.ExactComparisons.F3All.Data

/-! Generated from the F3 text of version 2.10 of the manuscript.
No Python certificate evaluation is used; the checks are done by the Lean kernel. -/

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 400000
namespace Erdos993Lean.ExactComparisons.F3All.Strict034

def records : List Comparison := [
  -- P080.lower; P080: lambda=28/25, y=3/4: 4246467/10000000 < L_minus(1+(28/25)/(10585001/5000000)); L_plus(1+(28/25)/(21169999/10000000)) < 4246472/10000000.
  Comparison.ofRats ((4246467 : Rat)/10000000) ((logLower (((1 : Rat) + (((28 : Rat) / (25 : Rat)) / ((10585001 : Rat) / (5000000 : Rat))))))) .lt,
  -- P080.upper; P080: lambda=28/25, y=3/4: 4246467/10000000 < L_minus(1+(28/25)/(10585001/5000000)); L_plus(1+(28/25)/(21169999/10000000)) < 4246472/10000000.
  Comparison.ofRats ((logUpper (((1 : Rat) + (((28 : Rat) / (25 : Rat)) / ((21169999 : Rat) / (10000000 : Rat))))))) ((4246472 : Rat)/10000000) .lt,
  -- P081.lower; P081: lambda=28/25, y=99/128: 4165993/10000000 < L_minus(1+(28/25)/(10836017/5000000)); L_plus(1+(28/25)/(21672031/10000000)) < 4165999/10000000.
  Comparison.ofRats ((4165993 : Rat)/10000000) ((logLower (((1 : Rat) + (((28 : Rat) / (25 : Rat)) / ((10836017 : Rat) / (5000000 : Rat))))))) .lt,
  -- P081.upper; P081: lambda=28/25, y=99/128: 4165993/10000000 < L_minus(1+(28/25)/(10836017/5000000)); L_plus(1+(28/25)/(21672031/10000000)) < 4165999/10000000.
  Comparison.ofRats ((logUpper (((1 : Rat) + (((28 : Rat) / (25 : Rat)) / ((21672031 : Rat) / (10000000 : Rat))))))) ((4165999 : Rat)/10000000) .lt,
  -- P082.lower; P082: lambda=28/25, y=51/64: 4086754/10000000 < L_minus(1+(28/25)/(22185971/10000000)); L_plus(1+(28/25)/(1386623/625000)) < 4086759/10000000.
  Comparison.ofRats ((4086754 : Rat)/10000000) ((logLower (((1 : Rat) + (((28 : Rat) / (25 : Rat)) / ((22185971 : Rat) / (10000000 : Rat))))))) .lt,
  -- P082.upper; P082: lambda=28/25, y=51/64: 4086754/10000000 < L_minus(1+(28/25)/(22185971/10000000)); L_plus(1+(28/25)/(1386623/625000)) < 4086759/10000000.
  Comparison.ofRats ((logUpper (((1 : Rat) + (((28 : Rat) / (25 : Rat)) / ((1386623 : Rat) / (625000 : Rat))))))) ((4086759 : Rat)/10000000) .lt,
  -- P083.lower; P083: lambda=28/25, y=105/128: 4008738/10000000 < L_minus(1+(28/25)/(709753/312500)); L_plus(1+(28/25)/(22712093/10000000)) < 4008744/10000000.
  Comparison.ofRats ((4008738 : Rat)/10000000) ((logLower (((1 : Rat) + (((28 : Rat) / (25 : Rat)) / ((709753 : Rat) / (312500 : Rat))))))) .lt,
  -- P083.upper; P083: lambda=28/25, y=105/128: 4008738/10000000 < L_minus(1+(28/25)/(709753/312500)); L_plus(1+(28/25)/(22712093/10000000)) < 4008744/10000000.
  Comparison.ofRats ((logUpper (((1 : Rat) + (((28 : Rat) / (25 : Rat)) / ((22712093 : Rat) / (10000000 : Rat))))))) ((4008744 : Rat)/10000000) .lt,
  -- P084.lower; P084: lambda=28/25, y=27/32: 3931938/10000000 < L_minus(1+(28/25)/(11625349/5000000)); L_plus(1+(28/25)/(4650139/2000000)) < 3931943/10000000.
  Comparison.ofRats ((3931938 : Rat)/10000000) ((logLower (((1 : Rat) + (((28 : Rat) / (25 : Rat)) / ((11625349 : Rat) / (5000000 : Rat))))))) .lt,
  -- P084.upper; P084: lambda=28/25, y=27/32: 3931938/10000000 < L_minus(1+(28/25)/(11625349/5000000)); L_plus(1+(28/25)/(4650139/2000000)) < 3931943/10000000.
  Comparison.ofRats ((logUpper (((1 : Rat) + (((28 : Rat) / (25 : Rat)) / ((4650139 : Rat) / (2000000 : Rat))))))) ((3931943 : Rat)/10000000) .lt,
  -- P085.lower; P085: lambda=28/25, y=111/128: 3856343/10000000 < L_minus(1+(28/25)/(23802073/10000000)); L_plus(1+(28/25)/(23802069/10000000)) < 3856349/10000000.
  Comparison.ofRats ((3856343 : Rat)/10000000) ((logLower (((1 : Rat) + (((28 : Rat) / (25 : Rat)) / ((23802073 : Rat) / (10000000 : Rat))))))) .lt,
  -- P085.upper; P085: lambda=28/25, y=111/128: 3856343/10000000 < L_minus(1+(28/25)/(23802073/10000000)); L_plus(1+(28/25)/(23802069/10000000)) < 3856349/10000000.
  Comparison.ofRats ((logUpper (((1 : Rat) + (((28 : Rat) / (25 : Rat)) / ((23802069 : Rat) / (10000000 : Rat))))))) ((3856349 : Rat)/10000000) .lt,
  -- P086.lower; P086: lambda=28/25, y=57/64: 3781944/10000000 < L_minus(1+(28/25)/(12183261/5000000)); L_plus(1+(28/25)/(24366519/10000000)) < 3781949/10000000.
  Comparison.ofRats ((3781944 : Rat)/10000000) ((logLower (((1 : Rat) + (((28 : Rat) / (25 : Rat)) / ((12183261 : Rat) / (5000000 : Rat))))))) .lt,
  -- P086.upper; P086: lambda=28/25, y=57/64: 3781944/10000000 < L_minus(1+(28/25)/(12183261/5000000)); L_plus(1+(28/25)/(24366519/10000000)) < 3781949/10000000.
  Comparison.ofRats ((logUpper (((1 : Rat) + (((28 : Rat) / (25 : Rat)) / ((24366519 : Rat) / (10000000 : Rat))))))) ((3781949 : Rat)/10000000) .lt,
  -- P087.lower; P087: lambda=28/25, y=15/16: 3636689/10000000 < L_minus(1+(28/25)/(3191987/1250000)); L_plus(1+(28/25)/(25535893/10000000)) < 3636695/10000000.
  Comparison.ofRats ((3636689 : Rat)/10000000) ((logLower (((1 : Rat) + (((28 : Rat) / (25 : Rat)) / ((3191987 : Rat) / (1250000 : Rat))))))) .lt,
  -- P087.upper; P087: lambda=28/25, y=15/16: 3636689/10000000 < L_minus(1+(28/25)/(3191987/1250000)); L_plus(1+(28/25)/(25535893/10000000)) < 3636695/10000000.
  Comparison.ofRats ((logUpper (((1 : Rat) + (((28 : Rat) / (25 : Rat)) / ((25535893 : Rat) / (10000000 : Rat))))))) ((3636695 : Rat)/10000000) .lt
]

theorem checked : check records = true := by decide +kernel
theorem sound : ∀ c ∈ records, c.rationalHolds := check_sound records checked
theorem record_count : records.length = 16 := by decide +kernel

end Erdos993Lean.ExactComparisons.F3All.Strict034
