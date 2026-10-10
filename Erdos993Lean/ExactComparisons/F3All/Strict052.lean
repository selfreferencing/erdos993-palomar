module

public import Erdos993Lean.ExactComparisons.F3All.Data

/-! Generated from the F3 text of version 2.10 of the manuscript.
No Python certificate evaluation is used; the checks are done by the Lean kernel. -/

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 400000
namespace Erdos993Lean.ExactComparisons.F3All.Strict052

def records : List Comparison := [
  -- P224.lower; P224: lambda=7/3, y=3/8: 9569230/10000000 < L_minus(1+(7/3)/(3637479/2500000)); L_plus(1+(7/3)/(14549913/10000000)) < 9569242/10000000.
  Comparison.ofRats ((9569230 : Rat)/10000000) ((logLower (((1 : Rat) + (((7 : Rat) / (3 : Rat)) / ((3637479 : Rat) / (2500000 : Rat))))))) .lt,
  -- P224.upper; P224: lambda=7/3, y=3/8: 9569230/10000000 < L_minus(1+(7/3)/(3637479/2500000)); L_plus(1+(7/3)/(14549913/10000000)) < 9569242/10000000.
  Comparison.ofRats ((logUpper (((1 : Rat) + (((7 : Rat) / (3 : Rat)) / ((14549913 : Rat) / (10000000 : Rat))))))) ((9569242 : Rat)/10000000) .lt,
  -- P225.lower; P225: lambda=7/3, y=121/200: 8216161/10000000 < L_minus(1+(7/3)/(4578131/2500000)); L_plus(1+(7/3)/(18312521/10000000)) < 8216170/10000000.
  Comparison.ofRats ((8216161 : Rat)/10000000) ((logLower (((1 : Rat) + (((7 : Rat) / (3 : Rat)) / ((4578131 : Rat) / (2500000 : Rat))))))) .lt,
  -- P225.upper; P225: lambda=7/3, y=121/200: 8216161/10000000 < L_minus(1+(7/3)/(4578131/2500000)); L_plus(1+(7/3)/(18312521/10000000)) < 8216170/10000000.
  Comparison.ofRats ((logUpper (((1 : Rat) + (((7 : Rat) / (3 : Rat)) / ((18312521 : Rat) / (10000000 : Rat))))))) ((8216170 : Rat)/10000000) .lt,
  -- P226.lower; P226: lambda=7/3, y=3/4: 7429783/10000000 < L_minus(1+(7/3)/(10585001/5000000)); L_plus(1+(7/3)/(21169999/10000000)) < 7429792/10000000.
  Comparison.ofRats ((7429783 : Rat)/10000000) ((logLower (((1 : Rat) + (((7 : Rat) / (3 : Rat)) / ((10585001 : Rat) / (5000000 : Rat))))))) .lt,
  -- P226.upper; P226: lambda=7/3, y=3/4: 7429783/10000000 < L_minus(1+(7/3)/(10585001/5000000)); L_plus(1+(7/3)/(21169999/10000000)) < 7429792/10000000.
  Comparison.ofRats ((logUpper (((1 : Rat) + (((7 : Rat) / (3 : Rat)) / ((21169999 : Rat) / (10000000 : Rat))))))) ((7429792 : Rat)/10000000) .lt,
  -- P227.lower; P227: lambda=7/3, y=121/160: 7397063/10000000 < L_minus(1+(7/3)/(21302729/10000000)); L_plus(1+(7/3)/(10651363/5000000)) < 7397072/10000000.
  Comparison.ofRats ((7397063 : Rat)/10000000) ((logLower (((1 : Rat) + (((7 : Rat) / (3 : Rat)) / ((21302729 : Rat) / (10000000 : Rat))))))) .lt,
  -- P227.upper; P227: lambda=7/3, y=121/160: 7397063/10000000 < L_minus(1+(7/3)/(21302729/10000000)); L_plus(1+(7/3)/(10651363/5000000)) < 7397072/10000000.
  Comparison.ofRats ((logUpper (((1 : Rat) + (((7 : Rat) / (3 : Rat)) / ((10651363 : Rat) / (5000000 : Rat))))))) ((7397072 : Rat)/10000000) .lt,
  -- P228.lower; P228: lambda=7/3, y=2541/3200: 7201184/10000000 < L_minus(1+(7/3)/(22123661/10000000)); L_plus(1+(7/3)/(11061829/5000000)) < 7201193/10000000.
  Comparison.ofRats ((7201184 : Rat)/10000000) ((logLower (((1 : Rat) + (((7 : Rat) / (3 : Rat)) / ((22123661 : Rat) / (10000000 : Rat))))))) .lt,
  -- P228.upper; P228: lambda=7/3, y=2541/3200: 7201184/10000000 < L_minus(1+(7/3)/(22123661/10000000)); L_plus(1+(7/3)/(11061829/5000000)) < 7201193/10000000.
  Comparison.ofRats ((logUpper (((1 : Rat) + (((7 : Rat) / (3 : Rat)) / ((11061829 : Rat) / (5000000 : Rat))))))) ((7201193 : Rat)/10000000) .lt,
  -- P229.lower; P229: lambda=7/3, y=5203/6400: 7104584/10000000 < L_minus(1+(7/3)/(4509183/2000000)); L_plus(1+(7/3)/(2818239/1250000)) < 7104592/10000000.
  Comparison.ofRats ((7104584 : Rat)/10000000) ((logLower (((1 : Rat) + (((7 : Rat) / (3 : Rat)) / ((4509183 : Rat) / (2000000 : Rat))))))) .lt,
  -- P229.upper; P229: lambda=7/3, y=5203/6400: 7104584/10000000 < L_minus(1+(7/3)/(4509183/2000000)); L_plus(1+(7/3)/(2818239/1250000)) < 7104592/10000000.
  Comparison.ofRats ((logUpper (((1 : Rat) + (((7 : Rat) / (3 : Rat)) / ((2818239 : Rat) / (1250000 : Rat))))))) ((7104592 : Rat)/10000000) .lt,
  -- P230.lower; P230: lambda=7/3, y=1331/1600: 7008877/10000000 < L_minus(1+(7/3)/(22976229/10000000)); L_plus(1+(7/3)/(11488113/5000000)) < 7008885/10000000.
  Comparison.ofRats ((7008877 : Rat)/10000000) ((logLower (((1 : Rat) + (((7 : Rat) / (3 : Rat)) / ((22976229 : Rat) / (10000000 : Rat))))))) .lt,
  -- P230.upper; P230: lambda=7/3, y=1331/1600: 7008877/10000000 < L_minus(1+(7/3)/(22976229/10000000)); L_plus(1+(7/3)/(11488113/5000000)) < 7008885/10000000.
  Comparison.ofRats ((logUpper (((1 : Rat) + (((7 : Rat) / (3 : Rat)) / ((11488113 : Rat) / (5000000 : Rat))))))) ((7008885 : Rat)/10000000) .lt,
  -- P231.lower; P231: lambda=7/3, y=1089/1280: 6914064/10000000 < L_minus(1+(7/3)/(5853689/2500000)); L_plus(1+(7/3)/(23414753/10000000)) < 6914073/10000000.
  Comparison.ofRats ((6914064 : Rat)/10000000) ((logLower (((1 : Rat) + (((7 : Rat) / (3 : Rat)) / ((5853689 : Rat) / (2500000 : Rat))))))) .lt,
  -- P231.upper; P231: lambda=7/3, y=1089/1280: 6914064/10000000 < L_minus(1+(7/3)/(5853689/2500000)); L_plus(1+(7/3)/(23414753/10000000)) < 6914073/10000000.
  Comparison.ofRats ((logUpper (((1 : Rat) + (((7 : Rat) / (3 : Rat)) / ((23414753 : Rat) / (10000000 : Rat))))))) ((6914073 : Rat)/10000000) .lt
]

theorem checked : check records = true := by decide +kernel
theorem sound : ∀ c ∈ records, c.rationalHolds := check_sound records checked
theorem record_count : records.length = 16 := by decide +kernel

end Erdos993Lean.ExactComparisons.F3All.Strict052
