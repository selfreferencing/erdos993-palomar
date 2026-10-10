module

public import Erdos993Lean.ExactComparisons.F3All.Data

/-! Generated from the F3 text of version 2.10 of the manuscript.
No Python certificate evaluation is used; the checks are done by the Lean kernel. -/

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 400000
namespace Erdos993Lean.ExactComparisons.F3All.Strict039

def records : List Comparison := [
  -- P120.lower; P120: lambda=263/200, y=63/100: 5308387/10000000 < L_minus(1+(263/200)/(18776107/10000000)); L_plus(1+(263/200)/(2347013/1250000)) < 5308392/10000000.
  Comparison.ofRats ((5308387 : Rat)/10000000) ((logLower (((1 : Rat) + (((263 : Rat) / (200 : Rat)) / ((18776107 : Rat) / (10000000 : Rat))))))) .lt,
  -- P120.upper; P120: lambda=263/200, y=63/100: 5308387/10000000 < L_minus(1+(263/200)/(18776107/10000000)); L_plus(1+(263/200)/(2347013/1250000)) < 5308392/10000000.
  Comparison.ofRats ((logUpper (((1 : Rat) + (((263 : Rat) / (200 : Rat)) / ((2347013 : Rat) / (1250000 : Rat))))))) ((5308392 : Rat)/10000000) .lt,
  -- P121.lower; P121: lambda=263/200, y=81/128: 5296812/10000000 < L_minus(1+(263/200)/(18828989/10000000)); L_plus(1+(263/200)/(9414493/5000000)) < 5296818/10000000.
  Comparison.ofRats ((5296812 : Rat)/10000000) ((logLower (((1 : Rat) + (((263 : Rat) / (200 : Rat)) / ((18828989 : Rat) / (10000000 : Rat))))))) .lt,
  -- P121.upper; P121: lambda=263/200, y=81/128: 5296812/10000000 < L_minus(1+(263/200)/(18828989/10000000)); L_plus(1+(263/200)/(9414493/5000000)) < 5296818/10000000.
  Comparison.ofRats ((logUpper (((1 : Rat) + (((263 : Rat) / (200 : Rat)) / ((9414493 : Rat) / (5000000 : Rat))))))) ((5296818 : Rat)/10000000) .lt,
  -- P122.lower; P122: lambda=263/200, y=21/32: 5201099/10000000 < L_minus(1+(263/200)/(9637753/5000000)); L_plus(1+(263/200)/(19275503/10000000)) < 5201105/10000000.
  Comparison.ofRats ((5201099 : Rat)/10000000) ((logLower (((1 : Rat) + (((263 : Rat) / (200 : Rat)) / ((9637753 : Rat) / (5000000 : Rat))))))) .lt,
  -- P122.upper; P122: lambda=263/200, y=21/32: 5201099/10000000 < L_minus(1+(263/200)/(9637753/5000000)); L_plus(1+(263/200)/(19275503/10000000)) < 5201105/10000000.
  Comparison.ofRats ((logUpper (((1 : Rat) + (((263 : Rat) / (200 : Rat)) / ((19275503 : Rat) / (10000000 : Rat))))))) ((5201105 : Rat)/10000000) .lt,
  -- P123.lower; P123: lambda=263/200, y=87/128: 5106711/10000000 < L_minus(1+(263/200)/(19732611/10000000)); L_plus(1+(263/200)/(154161/78125)) < 5106716/10000000.
  Comparison.ofRats ((5106711 : Rat)/10000000) ((logLower (((1 : Rat) + (((263 : Rat) / (200 : Rat)) / ((19732611 : Rat) / (10000000 : Rat))))))) .lt,
  -- P123.upper; P123: lambda=263/200, y=87/128: 5106711/10000000 < L_minus(1+(263/200)/(19732611/10000000)); L_plus(1+(263/200)/(154161/78125)) < 5106716/10000000.
  Comparison.ofRats ((logUpper (((1 : Rat) + (((263 : Rat) / (200 : Rat)) / ((154161 : Rat) / (78125 : Rat))))))) ((5106716 : Rat)/10000000) .lt,
  -- P124.lower; P124: lambda=263/200, y=273/400: 5095473/10000000 < L_minus(1+(263/200)/(4947047/2500000)); L_plus(1+(263/200)/(3957637/2000000)) < 5095478/10000000.
  Comparison.ofRats ((5095473 : Rat)/10000000) ((logLower (((1 : Rat) + (((263 : Rat) / (200 : Rat)) / ((4947047 : Rat) / (2500000 : Rat))))))) .lt,
  -- P124.upper; P124: lambda=263/200, y=273/400: 5095473/10000000 < L_minus(1+(263/200)/(4947047/2500000)); L_plus(1+(263/200)/(3957637/2000000)) < 5095478/10000000.
  Comparison.ofRats ((logUpper (((1 : Rat) + (((263 : Rat) / (200 : Rat)) / ((3957637 : Rat) / (2000000 : Rat))))))) ((5095478 : Rat)/10000000) .lt,
  -- P125.lower; P125: lambda=263/200, y=45/64: 5013640/10000000 < L_minus(1+(263/200)/(20200557/10000000)); L_plus(1+(263/200)/(10100277/5000000)) < 5013646/10000000.
  Comparison.ofRats ((5013640 : Rat)/10000000) ((logLower (((1 : Rat) + (((263 : Rat) / (200 : Rat)) / ((20200557 : Rat) / (10000000 : Rat))))))) .lt,
  -- P125.upper; P125: lambda=263/200, y=45/64: 5013640/10000000 < L_minus(1+(263/200)/(20200557/10000000)); L_plus(1+(263/200)/(10100277/5000000)) < 5013646/10000000.
  Comparison.ofRats ((logUpper (((1 : Rat) + (((263 : Rat) / (200 : Rat)) / ((10100277 : Rat) / (5000000 : Rat))))))) ((5013646 : Rat)/10000000) .lt,
  -- P126.lower; P126: lambda=263/200, y=93/128: 4921882/10000000 < L_minus(1+(263/200)/(20679599/10000000)); L_plus(1+(263/200)/(5169899/2500000)) < 4921888/10000000.
  Comparison.ofRats ((4921882 : Rat)/10000000) ((logLower (((1 : Rat) + (((263 : Rat) / (200 : Rat)) / ((20679599 : Rat) / (10000000 : Rat))))))) .lt,
  -- P126.upper; P126: lambda=263/200, y=93/128: 4921882/10000000 < L_minus(1+(263/200)/(20679599/10000000)); L_plus(1+(263/200)/(5169899/2500000)) < 4921888/10000000.
  Comparison.ofRats ((logUpper (((1 : Rat) + (((263 : Rat) / (200 : Rat)) / ((5169899 : Rat) / (2500000 : Rat))))))) ((4921888 : Rat)/10000000) .lt,
  -- P127.lower; P127: lambda=263/200, y=147/200: 4889169/10000000 < L_minus(1+(263/200)/(20854821/10000000)); L_plus(1+(263/200)/(10427409/5000000)) < 4889175/10000000.
  Comparison.ofRats ((4889169 : Rat)/10000000) ((logLower (((1 : Rat) + (((263 : Rat) / (200 : Rat)) / ((20854821 : Rat) / (10000000 : Rat))))))) .lt,
  -- P127.upper; P127: lambda=263/200, y=147/200: 4889169/10000000 < L_minus(1+(263/200)/(20854821/10000000)); L_plus(1+(263/200)/(10427409/5000000)) < 4889175/10000000.
  Comparison.ofRats ((logUpper (((1 : Rat) + (((263 : Rat) / (200 : Rat)) / ((10427409 : Rat) / (5000000 : Rat))))))) ((4889175 : Rat)/10000000) .lt
]

theorem checked : check records = true := by decide +kernel
theorem sound : ∀ c ∈ records, c.rationalHolds := check_sound records checked
theorem record_count : records.length = 16 := by decide +kernel

end Erdos993Lean.ExactComparisons.F3All.Strict039
