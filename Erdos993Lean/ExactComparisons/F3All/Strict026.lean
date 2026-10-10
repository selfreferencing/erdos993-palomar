module

public import Erdos993Lean.ExactComparisons.F3All.Data

/-! Generated from the F3 text of version 2.10 of the manuscript.
No Python certificate evaluation is used; the checks are done by the Lean kernel. -/

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 400000
namespace Erdos993Lean.ExactComparisons.F3All.Strict026

def records : List Comparison := [
  -- P016.lower; P016: lambda=3/5, y=3/32: 4358687/10000000 < L_minus(1+(3/5)/(10982853/10000000)); L_plus(1+(3/5)/(219657/200000)) < 4358693/10000000.
  Comparison.ofRats ((4358687 : Rat)/10000000) ((logLower (((1 : Rat) + (((3 : Rat) / (5 : Rat)) / ((10982853 : Rat) / (10000000 : Rat))))))) .lt,
  -- P016.upper; P016: lambda=3/5, y=3/32: 4358687/10000000 < L_minus(1+(3/5)/(10982853/10000000)); L_plus(1+(3/5)/(219657/200000)) < 4358693/10000000.
  Comparison.ofRats ((logUpper (((1 : Rat) + (((3 : Rat) / (5 : Rat)) / ((219657 : Rat) / (200000 : Rat))))))) ((4358693 : Rat)/10000000) .lt,
  -- P017.lower; P017: lambda=3/5, y=3/16: 4037416/10000000 < L_minus(1+(3/5)/(376947/312500)); L_plus(1+(3/5)/(12062301/10000000)) < 4037422/10000000.
  Comparison.ofRats ((4037416 : Rat)/10000000) ((logLower (((1 : Rat) + (((3 : Rat) / (5 : Rat)) / ((376947 : Rat) / (312500 : Rat))))))) .lt,
  -- P017.upper; P017: lambda=3/5, y=3/16: 4037416/10000000 < L_minus(1+(3/5)/(376947/312500)); L_plus(1+(3/5)/(12062301/10000000)) < 4037422/10000000.
  Comparison.ofRats ((logUpper (((1 : Rat) + (((3 : Rat) / (5 : Rat)) / ((12062301 : Rat) / (10000000 : Rat))))))) ((4037422 : Rat)/10000000) .lt,
  -- P018.lower; P018: lambda=3/5, y=15/64: 3884129/10000000 < L_minus(1+(3/5)/(6320593/5000000)); L_plus(1+(3/5)/(12641183/10000000)) < 3884135/10000000.
  Comparison.ofRats ((3884129 : Rat)/10000000) ((logLower (((1 : Rat) + (((3 : Rat) / (5 : Rat)) / ((6320593 : Rat) / (5000000 : Rat))))))) .lt,
  -- P018.upper; P018: lambda=3/5, y=15/64: 3884129/10000000 < L_minus(1+(3/5)/(6320593/5000000)); L_plus(1+(3/5)/(12641183/10000000)) < 3884135/10000000.
  Comparison.ofRats ((logUpper (((1 : Rat) + (((3 : Rat) / (5 : Rat)) / ((12641183 : Rat) / (10000000 : Rat))))))) ((3884135 : Rat)/10000000) .lt,
  -- P019.lower; P019: lambda=3/5, y=9/32: 3735638/10000000 < L_minus(1+(3/5)/(13247849/10000000)); L_plus(1+(3/5)/(6623923/5000000)) < 3735644/10000000.
  Comparison.ofRats ((3735638 : Rat)/10000000) ((logLower (((1 : Rat) + (((3 : Rat) / (5 : Rat)) / ((13247849 : Rat) / (10000000 : Rat))))))) .lt,
  -- P019.upper; P019: lambda=3/5, y=9/32: 3735638/10000000 < L_minus(1+(3/5)/(13247849/10000000)); L_plus(1+(3/5)/(6623923/5000000)) < 3735644/10000000.
  Comparison.ofRats ((logUpper (((1 : Rat) + (((3 : Rat) / (5 : Rat)) / ((6623923 : Rat) / (5000000 : Rat))))))) ((3735644 : Rat)/10000000) .lt,
  -- P020.lower; P020: lambda=3/5, y=21/64: 3591861/10000000 < L_minus(1+(3/5)/(13883627/10000000)); L_plus(1+(3/5)/(1735453/1250000)) < 3591867/10000000.
  Comparison.ofRats ((3591861 : Rat)/10000000) ((logLower (((1 : Rat) + (((3 : Rat) / (5 : Rat)) / ((13883627 : Rat) / (10000000 : Rat))))))) .lt,
  -- P020.upper; P020: lambda=3/5, y=21/64: 3591861/10000000 < L_minus(1+(3/5)/(13883627/10000000)); L_plus(1+(3/5)/(1735453/1250000)) < 3591867/10000000.
  Comparison.ofRats ((logUpper (((1 : Rat) + (((3 : Rat) / (5 : Rat)) / ((1735453 : Rat) / (1250000 : Rat))))))) ((3591867 : Rat)/10000000) .lt,
  -- P021.lower; P021: lambda=3/5, y=3/8: 3452713/10000000 < L_minus(1+(3/5)/(3637479/2500000)); L_plus(1+(3/5)/(14549913/10000000)) < 3452719/10000000.
  Comparison.ofRats ((3452713 : Rat)/10000000) ((logLower (((1 : Rat) + (((3 : Rat) / (5 : Rat)) / ((3637479 : Rat) / (2500000 : Rat))))))) .lt,
  -- P021.upper; P021: lambda=3/5, y=3/8: 3452713/10000000 < L_minus(1+(3/5)/(3637479/2500000)); L_plus(1+(3/5)/(14549913/10000000)) < 3452719/10000000.
  Comparison.ofRats ((logUpper (((1 : Rat) + (((3 : Rat) / (5 : Rat)) / ((14549913 : Rat) / (10000000 : Rat))))))) ((3452719 : Rat)/10000000) .lt,
  -- P022.lower; P022: lambda=3/5, y=27/64: 3318108/10000000 < L_minus(1+(3/5)/(15248181/10000000)); L_plus(1+(3/5)/(7624089/5000000)) < 3318113/10000000.
  Comparison.ofRats ((3318108 : Rat)/10000000) ((logLower (((1 : Rat) + (((3 : Rat) / (5 : Rat)) / ((15248181 : Rat) / (10000000 : Rat))))))) .lt,
  -- P022.upper; P022: lambda=3/5, y=27/64: 3318108/10000000 < L_minus(1+(3/5)/(15248181/10000000)); L_plus(1+(3/5)/(7624089/5000000)) < 3318113/10000000.
  Comparison.ofRats ((logUpper (((1 : Rat) + (((3 : Rat) / (5 : Rat)) / ((7624089 : Rat) / (5000000 : Rat))))))) ((3318113 : Rat)/10000000) .lt,
  -- P023.lower; P023: lambda=3/5, y=15/32: 3187955/10000000 < L_minus(1+(3/5)/(3994989/2500000)); L_plus(1+(3/5)/(15979953/10000000)) < 3187960/10000000.
  Comparison.ofRats ((3187955 : Rat)/10000000) ((logLower (((1 : Rat) + (((3 : Rat) / (5 : Rat)) / ((3994989 : Rat) / (2500000 : Rat))))))) .lt,
  -- P023.upper; P023: lambda=3/5, y=15/32: 3187955/10000000 < L_minus(1+(3/5)/(3994989/2500000)); L_plus(1+(3/5)/(15979953/10000000)) < 3187960/10000000.
  Comparison.ofRats ((logUpper (((1 : Rat) + (((3 : Rat) / (5 : Rat)) / ((15979953 : Rat) / (10000000 : Rat))))))) ((3187960 : Rat)/10000000) .lt
]

theorem checked : check records = true := by decide +kernel
theorem sound : ∀ c ∈ records, c.rationalHolds := check_sound records checked
theorem record_count : records.length = 16 := by decide +kernel

end Erdos993Lean.ExactComparisons.F3All.Strict026
