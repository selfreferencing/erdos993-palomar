module

public import Erdos993Lean.ExactComparisons.F3All.Data

/-! Generated from the F3 text of version 2.10 of the manuscript.
No Python certificate evaluation is used; the checks are done by the Lean kernel. -/

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 400000
namespace Erdos993Lean.ExactComparisons.F3All.Strict040

def records : List Comparison := [
  -- P128.lower; P128: lambda=263/200, y=3/4: 4831429/10000000 < L_minus(1+(263/200)/(10585001/5000000)); L_plus(1+(263/200)/(21169999/10000000)) < 4831434/10000000.
  Comparison.ofRats ((4831429 : Rat)/10000000) ((logLower (((1 : Rat) + (((263 : Rat) / (200 : Rat)) / ((10585001 : Rat) / (5000000 : Rat))))))) .lt,
  -- P128.upper; P128: lambda=263/200, y=3/4: 4831429/10000000 < L_minus(1+(263/200)/(10585001/5000000)); L_plus(1+(263/200)/(21169999/10000000)) < 4831434/10000000.
  Comparison.ofRats ((logUpper (((1 : Rat) + (((263 : Rat) / (200 : Rat)) / ((21169999 : Rat) / (10000000 : Rat))))))) ((4831434 : Rat)/10000000) .lt,
  -- P129.lower; P129: lambda=263/200, y=99/128: 4742274/10000000 < L_minus(1+(263/200)/(10836017/5000000)); L_plus(1+(263/200)/(21672031/10000000)) < 4742280/10000000.
  Comparison.ofRats ((4742274 : Rat)/10000000) ((logLower (((1 : Rat) + (((263 : Rat) / (200 : Rat)) / ((10836017 : Rat) / (5000000 : Rat))))))) .lt,
  -- P129.upper; P129: lambda=263/200, y=99/128: 4742274/10000000 < L_minus(1+(263/200)/(10836017/5000000)); L_plus(1+(263/200)/(21672031/10000000)) < 4742280/10000000.
  Comparison.ofRats ((logUpper (((1 : Rat) + (((263 : Rat) / (200 : Rat)) / ((21672031 : Rat) / (10000000 : Rat))))))) ((4742280 : Rat)/10000000) .lt,
  -- P130.lower; P130: lambda=263/200, y=63/80: 4689401/10000000 < L_minus(1+(263/200)/(439579/200000)); L_plus(1+(263/200)/(21978947/10000000)) < 4689407/10000000.
  Comparison.ofRats ((4689401 : Rat)/10000000) ((logLower (((1 : Rat) + (((263 : Rat) / (200 : Rat)) / ((439579 : Rat) / (200000 : Rat))))))) .lt,
  -- P130.upper; P130: lambda=263/200, y=63/80: 4689401/10000000 < L_minus(1+(263/200)/(439579/200000)); L_plus(1+(263/200)/(21978947/10000000)) < 4689407/10000000.
  Comparison.ofRats ((logUpper (((1 : Rat) + (((263 : Rat) / (200 : Rat)) / ((21978947 : Rat) / (10000000 : Rat))))))) ((4689407 : Rat)/10000000) .lt,
  -- P131.lower; P131: lambda=263/200, y=51/64: 4654410/10000000 < L_minus(1+(263/200)/(22185971/10000000)); L_plus(1+(263/200)/(1386623/625000)) < 4654416/10000000.
  Comparison.ofRats ((4654410 : Rat)/10000000) ((logLower (((1 : Rat) + (((263 : Rat) / (200 : Rat)) / ((22185971 : Rat) / (10000000 : Rat))))))) .lt,
  -- P131.upper; P131: lambda=263/200, y=51/64: 4654410/10000000 < L_minus(1+(263/200)/(22185971/10000000)); L_plus(1+(263/200)/(1386623/625000)) < 4654416/10000000.
  Comparison.ofRats ((logUpper (((1 : Rat) + (((263 : Rat) / (200 : Rat)) / ((1386623 : Rat) / (625000 : Rat))))))) ((4654416 : Rat)/10000000) .lt,
  -- P132.lower; P132: lambda=263/200, y=105/128: 4567830/10000000 < L_minus(1+(263/200)/(709753/312500)); L_plus(1+(263/200)/(22712093/10000000)) < 4567836/10000000.
  Comparison.ofRats ((4567830 : Rat)/10000000) ((logLower (((1 : Rat) + (((263 : Rat) / (200 : Rat)) / ((709753 : Rat) / (312500 : Rat))))))) .lt,
  -- P132.upper; P132: lambda=263/200, y=105/128: 4567830/10000000 < L_minus(1+(263/200)/(709753/312500)); L_plus(1+(263/200)/(22712093/10000000)) < 4567836/10000000.
  Comparison.ofRats ((logUpper (((1 : Rat) + (((263 : Rat) / (200 : Rat)) / ((22712093 : Rat) / (10000000 : Rat))))))) ((4567836 : Rat)/10000000) .lt,
  -- P133.lower; P133: lambda=263/200, y=21/25: 4496089/10000000 < L_minus(1+(263/200)/(23163671/10000000)); L_plus(1+(263/200)/(5790917/2500000)) < 4496094/10000000.
  Comparison.ofRats ((4496089 : Rat)/10000000) ((logLower (((1 : Rat) + (((263 : Rat) / (200 : Rat)) / ((23163671 : Rat) / (10000000 : Rat))))))) .lt,
  -- P133.upper; P133: lambda=263/200, y=21/25: 4496089/10000000 < L_minus(1+(263/200)/(23163671/10000000)); L_plus(1+(263/200)/(5790917/2500000)) < 4496094/10000000.
  Comparison.ofRats ((logUpper (((1 : Rat) + (((263 : Rat) / (200 : Rat)) / ((5790917 : Rat) / (2500000 : Rat))))))) ((4496094 : Rat)/10000000) .lt,
  -- P134.lower; P134: lambda=263/200, y=27/32: 4482525/10000000 < L_minus(1+(263/200)/(11625349/5000000)); L_plus(1+(263/200)/(4650139/2000000)) < 4482531/10000000.
  Comparison.ofRats ((4482525 : Rat)/10000000) ((logLower (((1 : Rat) + (((263 : Rat) / (200 : Rat)) / ((11625349 : Rat) / (5000000 : Rat))))))) .lt,
  -- P134.upper; P134: lambda=263/200, y=27/32: 4482525/10000000 < L_minus(1+(263/200)/(11625349/5000000)); L_plus(1+(263/200)/(4650139/2000000)) < 4482531/10000000.
  Comparison.ofRats ((logUpper (((1 : Rat) + (((263 : Rat) / (200 : Rat)) / ((4650139 : Rat) / (2000000 : Rat))))))) ((4482531 : Rat)/10000000) .lt,
  -- P135.lower; P135: lambda=263/200, y=111/128: 4398488/10000000 < L_minus(1+(263/200)/(23802073/10000000)); L_plus(1+(263/200)/(23802069/10000000)) < 4398494/10000000.
  Comparison.ofRats ((4398488 : Rat)/10000000) ((logLower (((1 : Rat) + (((263 : Rat) / (200 : Rat)) / ((23802073 : Rat) / (10000000 : Rat))))))) .lt,
  -- P135.upper; P135: lambda=263/200, y=111/128: 4398488/10000000 < L_minus(1+(263/200)/(23802073/10000000)); L_plus(1+(263/200)/(23802069/10000000)) < 4398494/10000000.
  Comparison.ofRats ((logUpper (((1 : Rat) + (((263 : Rat) / (200 : Rat)) / ((23802069 : Rat) / (10000000 : Rat))))))) ((4398494 : Rat)/10000000) .lt
]

theorem checked : check records = true := by decide +kernel
theorem sound : ∀ c ∈ records, c.rationalHolds := check_sound records checked
theorem record_count : records.length = 16 := by decide +kernel

end Erdos993Lean.ExactComparisons.F3All.Strict040
