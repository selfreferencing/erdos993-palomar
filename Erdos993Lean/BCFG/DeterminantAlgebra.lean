module

public import Erdos993Lean.BCFG.RowParameters

/-! Eq.(3)--(5), (11), (14): generic exact scalar algebra.
No polynomial certificate, sign assumption or analytic transfer is used. -/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Erdos993Lean.BCFG.Analytic

open Finset

def scaledDet (a eps t0 e d R U K1 K2 rho : ℝ) : ℝ :=
  (a+K1*rho+K2*rho^2-(e+d*rho)-eps)*(R-(e+d*rho)*U)-
    U*(e+d*rho-t0)^2

/-- Coefficients c0,...,c3 in printed Eq.(4), zero beyond degree three. -/
def rawCoefficient (a eps t0 e d R U K1 K2 : ℝ) : ℕ → ℝ
  | 0 => R*(a-e-eps)-U*(e*(a-eps-2*t0)+t0^2)
  | 1 => R*(K1-d)-U*(e*K1+d*(a-eps-2*t0))
  | 2 => R*K2-U*(e*K2+d*K1)
  | 3 => -U*d*K2
  | _ => 0

def cubicValue (c : ℕ → ℝ) (t : ℝ) : ℝ := c 0+c 1*t+c 2*t^2+c 3*t^3

/-- Eq.(5); terms i<j are explicitly zero rather than using truncated powers. -/
def vacancyCoefficient (c : ℕ → ℝ) (rho0 : ℝ) (j : ℕ) : ℝ :=
  (1-rho0)^j * ∑ i ∈ range 4,
    if j ≤ i then (i.choose j : ℝ)*c i*rho0^(i-j) else 0

def bernsteinCoefficient (a : ℕ → ℝ) (j : ℕ) : ℝ :=
  ∑ i ∈ range (j+1), (j.choose i : ℝ)/(Nat.choose 3 i : ℝ)*a i

def lightJ (a : ℕ → ℝ) (u : ℝ) : ℝ := a 2+(2*u+1)*a 3
def lightC0 (a : ℕ → ℝ) (u : ℝ) : ℝ := a 0-u^2*(a 2+2*u*a 3)
def lightC1 (a : ℕ → ℝ) (u : ℝ) : ℝ :=
  a 0+a 1+a 2+a 3-(1-u)^2*lightJ a u

theorem scaledDet_eq_cubic (a eps t0 e d R U K1 K2 rho : ℝ) :
    scaledDet a eps t0 e d R U K1 K2 rho =
      cubicValue (rawCoefficient a eps t0 e d R U K1 K2) rho := by
  simp only [scaledDet, cubicValue, rawCoefficient]
  ring

theorem cubic_shift (c : ℕ → ℝ) (rho0 t : ℝ) :
    cubicValue c (rho0+(1-rho0)*t) = cubicValue (vacancyCoefficient c rho0) t := by
  norm_num [cubicValue, vacancyCoefficient, Finset.sum_range_succ] <;> ring

theorem scaledDet_normalized (a eps t0 e d R U K1 K2 rho0 t : ℝ) :
    scaledDet a eps t0 e d R U K1 K2 (rho0+(1-rho0)*t) =
      cubicValue (vacancyCoefficient (rawCoefficient a eps t0 e d R U K1 K2) rho0) t := by
  rw [scaledDet_eq_cubic, cubic_shift]

/-- The four heavy quantities give exactly Eq.(11), even outside the sign domain. -/
theorem heavy_cubic_identity (a : ℕ → ℝ) (t : ℝ) :
    cubicValue a t =
      bernsteinCoefficient a 0*(1-t)*(1-2*t)^2+
      3*(bernsteinCoefficient a 1+2/3*bernsteinCoefficient a 0)*t*(1-t)^2+
      3*(bernsteinCoefficient a 2-1/3*bernsteinCoefficient a 0)*t^2*(1-t)+
      bernsteinCoefficient a 3*t^3 := by
  norm_num [cubicValue, bernsteinCoefficient, Finset.sum_range_succ] <;> ring

/-- The three light quantities give exactly Eq.(14), without any response restriction. -/
theorem light_cubic_identity (a : ℕ → ℝ) (u t : ℝ) :
    cubicValue a t =
      (lightJ a u-a 3*(1-t))*(t-u)^2+lightC0 a u*(1-t)+lightC1 a u*t := by
  simp only [cubicValue, lightJ, lightC0, lightC1]
  ring

end Erdos993Lean.BCFG.Analytic

#check Erdos993Lean.BCFG.Analytic.scaledDet
#print axioms Erdos993Lean.BCFG.Analytic.scaledDet
#check Erdos993Lean.BCFG.Analytic.rawCoefficient
#print axioms Erdos993Lean.BCFG.Analytic.rawCoefficient
#check Erdos993Lean.BCFG.Analytic.cubicValue
#print axioms Erdos993Lean.BCFG.Analytic.cubicValue
#check Erdos993Lean.BCFG.Analytic.vacancyCoefficient
#print axioms Erdos993Lean.BCFG.Analytic.vacancyCoefficient
#check Erdos993Lean.BCFG.Analytic.bernsteinCoefficient
#print axioms Erdos993Lean.BCFG.Analytic.bernsteinCoefficient
#check Erdos993Lean.BCFG.Analytic.lightJ
#print axioms Erdos993Lean.BCFG.Analytic.lightJ
#check Erdos993Lean.BCFG.Analytic.lightC0
#print axioms Erdos993Lean.BCFG.Analytic.lightC0
#check Erdos993Lean.BCFG.Analytic.lightC1
#print axioms Erdos993Lean.BCFG.Analytic.lightC1
#check Erdos993Lean.BCFG.Analytic.scaledDet_eq_cubic
#print axioms Erdos993Lean.BCFG.Analytic.scaledDet_eq_cubic
#check Erdos993Lean.BCFG.Analytic.cubic_shift
#print axioms Erdos993Lean.BCFG.Analytic.cubic_shift
#check Erdos993Lean.BCFG.Analytic.scaledDet_normalized
#print axioms Erdos993Lean.BCFG.Analytic.scaledDet_normalized
#check Erdos993Lean.BCFG.Analytic.heavy_cubic_identity
#print axioms Erdos993Lean.BCFG.Analytic.heavy_cubic_identity
#check Erdos993Lean.BCFG.Analytic.light_cubic_identity
#print axioms Erdos993Lean.BCFG.Analytic.light_cubic_identity
