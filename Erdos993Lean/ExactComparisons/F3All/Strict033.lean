module

public import Erdos993Lean.ExactComparisons.F3All.Data

/-! Generated from the F3 text of version 2.10 of the manuscript.
No Python certificate evaluation is used; the checks are done by the Lean kernel. -/

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 400000
namespace Erdos993Lean.ExactComparisons.F3All.Strict033

def records : List Comparison := [
  -- P072.lower; P072: lambda=28/25, y=9/16: 4935714/10000000 < L_minus(1+(28/25)/(4387637/2500000)); L_plus(1+(28/25)/(3510109/2000000)) < 4935720/10000000.
  Comparison.ofRats ((4935714 : Rat)/10000000) ((logLower (((1 : Rat) + (((28 : Rat) / (25 : Rat)) / ((4387637 : Rat) / (2500000 : Rat))))))) .lt,
  -- P072.upper; P072: lambda=28/25, y=9/16: 4935714/10000000 < L_minus(1+(28/25)/(4387637/2500000)); L_plus(1+(28/25)/(3510109/2000000)) < 4935720/10000000.
  Comparison.ofRats ((logUpper (((1 : Rat) + (((28 : Rat) / (25 : Rat)) / ((3510109 : Rat) / (2000000 : Rat))))))) ((4935720 : Rat)/10000000) .lt,
  -- P073.lower; P073: lambda=28/25, y=75/128: 4845063/10000000 < L_minus(1+(28/25)/(17966747/10000000)); L_plus(1+(28/25)/(2245843/1250000)) < 4845069/10000000.
  Comparison.ofRats ((4845063 : Rat)/10000000) ((logLower (((1 : Rat) + (((28 : Rat) / (25 : Rat)) / ((17966747 : Rat) / (10000000 : Rat))))))) .lt,
  -- P073.upper; P073: lambda=28/25, y=75/128: 4845063/10000000 < L_minus(1+(28/25)/(17966747/10000000)); L_plus(1+(28/25)/(2245843/1250000)) < 4845069/10000000.
  Comparison.ofRats ((logUpper (((1 : Rat) + (((28 : Rat) / (25 : Rat)) / ((2245843 : Rat) / (1250000 : Rat))))))) ((4845069 : Rat)/10000000) .lt,
  -- P074.lower; P074: lambda=28/25, y=39/64: 4755712/10000000 < L_minus(1+(28/25)/(1149551/625000)); L_plus(1+(28/25)/(18392813/10000000)) < 4755718/10000000.
  Comparison.ofRats ((4755712 : Rat)/10000000) ((logLower (((1 : Rat) + (((28 : Rat) / (25 : Rat)) / ((1149551 : Rat) / (625000 : Rat))))))) .lt,
  -- P074.upper; P074: lambda=28/25, y=39/64: 4755712/10000000 < L_minus(1+(28/25)/(1149551/625000)); L_plus(1+(28/25)/(18392813/10000000)) < 4755718/10000000.
  Comparison.ofRats ((logUpper (((1 : Rat) + (((28 : Rat) / (25 : Rat)) / ((18392813 : Rat) / (10000000 : Rat))))))) ((4755718 : Rat)/10000000) .lt,
  -- P075.lower; P075: lambda=28/25, y=81/128: 4667653/10000000 < L_minus(1+(28/25)/(18828989/10000000)); L_plus(1+(28/25)/(9414493/5000000)) < 4667659/10000000.
  Comparison.ofRats ((4667653 : Rat)/10000000) ((logLower (((1 : Rat) + (((28 : Rat) / (25 : Rat)) / ((18828989 : Rat) / (10000000 : Rat))))))) .lt,
  -- P075.upper; P075: lambda=28/25, y=81/128: 4667653/10000000 < L_minus(1+(28/25)/(18828989/10000000)); L_plus(1+(28/25)/(9414493/5000000)) < 4667659/10000000.
  Comparison.ofRats ((logUpper (((1 : Rat) + (((28 : Rat) / (25 : Rat)) / ((9414493 : Rat) / (5000000 : Rat))))))) ((4667659 : Rat)/10000000) .lt,
  -- P076.lower; P076: lambda=28/25, y=21/32: 4580879/10000000 < L_minus(1+(28/25)/(9637753/5000000)); L_plus(1+(28/25)/(19275503/10000000)) < 4580884/10000000.
  Comparison.ofRats ((4580879 : Rat)/10000000) ((logLower (((1 : Rat) + (((28 : Rat) / (25 : Rat)) / ((9637753 : Rat) / (5000000 : Rat))))))) .lt,
  -- P076.upper; P076: lambda=28/25, y=21/32: 4580879/10000000 < L_minus(1+(28/25)/(9637753/5000000)); L_plus(1+(28/25)/(19275503/10000000)) < 4580884/10000000.
  Comparison.ofRats ((logUpper (((1 : Rat) + (((28 : Rat) / (25 : Rat)) / ((19275503 : Rat) / (10000000 : Rat))))))) ((4580884 : Rat)/10000000) .lt,
  -- P077.lower; P077: lambda=28/25, y=87/128: 4495381/10000000 < L_minus(1+(28/25)/(19732611/10000000)); L_plus(1+(28/25)/(154161/78125)) < 4495386/10000000.
  Comparison.ofRats ((4495381 : Rat)/10000000) ((logLower (((1 : Rat) + (((28 : Rat) / (25 : Rat)) / ((19732611 : Rat) / (10000000 : Rat))))))) .lt,
  -- P077.upper; P077: lambda=28/25, y=87/128: 4495381/10000000 < L_minus(1+(28/25)/(19732611/10000000)); L_plus(1+(28/25)/(154161/78125)) < 4495386/10000000.
  Comparison.ofRats ((logUpper (((1 : Rat) + (((28 : Rat) / (25 : Rat)) / ((154161 : Rat) / (78125 : Rat))))))) ((4495386 : Rat)/10000000) .lt,
  -- P078.lower; P078: lambda=28/25, y=45/64: 4411152/10000000 < L_minus(1+(28/25)/(20200557/10000000)); L_plus(1+(28/25)/(10100277/5000000)) < 4411157/10000000.
  Comparison.ofRats ((4411152 : Rat)/10000000) ((logLower (((1 : Rat) + (((28 : Rat) / (25 : Rat)) / ((20200557 : Rat) / (10000000 : Rat))))))) .lt,
  -- P078.upper; P078: lambda=28/25, y=45/64: 4411152/10000000 < L_minus(1+(28/25)/(20200557/10000000)); L_plus(1+(28/25)/(10100277/5000000)) < 4411157/10000000.
  Comparison.ofRats ((logUpper (((1 : Rat) + (((28 : Rat) / (25 : Rat)) / ((10100277 : Rat) / (5000000 : Rat))))))) ((4411157 : Rat)/10000000) .lt,
  -- P079.lower; P079: lambda=28/25, y=93/128: 4328184/10000000 < L_minus(1+(28/25)/(20679599/10000000)); L_plus(1+(28/25)/(5169899/2500000)) < 4328189/10000000.
  Comparison.ofRats ((4328184 : Rat)/10000000) ((logLower (((1 : Rat) + (((28 : Rat) / (25 : Rat)) / ((20679599 : Rat) / (10000000 : Rat))))))) .lt,
  -- P079.upper; P079: lambda=28/25, y=93/128: 4328184/10000000 < L_minus(1+(28/25)/(20679599/10000000)); L_plus(1+(28/25)/(5169899/2500000)) < 4328189/10000000.
  Comparison.ofRats ((logUpper (((1 : Rat) + (((28 : Rat) / (25 : Rat)) / ((5169899 : Rat) / (2500000 : Rat))))))) ((4328189 : Rat)/10000000) .lt
]

theorem checked : check records = true := by decide +kernel
theorem sound : ∀ c ∈ records, c.rationalHolds := check_sound records checked
theorem record_count : records.length = 16 := by decide +kernel

end Erdos993Lean.ExactComparisons.F3All.Strict033
