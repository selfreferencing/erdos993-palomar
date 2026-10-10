module

public import F4Heavy.Analysis.CapSlopeUpper
public import F4Heavy.Analysis.CapCoefficientBounds
public import F4Heavy.Analysis.CapAdverseAlgebra
public import F4Heavy.Analysis.CapDLogBounds
public import F4Heavy.Analysis.TailIdentityCoordinates

@[expose] public section
set_option autoImplicit false
namespace F4Heavy.Analysis
open F4Unified
noncomputable section

def capReflectMN (r : Row) (t : ℝ) : ℝ := (2+t)+2*gamma r t*(1+2*t)
def capReflectMD (t : ℝ) : ℝ := (1+2*t)*(2+t)
def capReflectLambdaN (r : Row) (t hn hd : ℝ) : ℝ :=
  let M := capReflectMN r t
  let Q := capReflectMD t
  let G := gamma r t-delta r t
  600*G^2*hn*Q^2+600*M*Q*G*hd-300*(alpha r t+beta r t)*Q^2*G*hd-
    3*Q^2*G*hd+650*hn*M*Q*G-240*hn*t*M^2
def capReflectLambdaD (r : Row) (t hd : ℝ) : ℝ :=
  300*(capReflectMD t)^2*(gamma r t-delta r t)*hd

theorem cap_lambda_reflect_quotient (r : Row) (t hn hd : ℝ) (ht : 0 < t)
    (hG : gamma r t-delta r t ≠ 0) (hhd : hd ≠ 0) :
    capLambda r t (hn/hd)-1/100 = capReflectLambdaN r t hn hd/capReflectLambdaD r t hd := by
  have h1 : 1+2*t ≠ 0 := by positivity
  have h2 : 2+t ≠ 0 := by positivity
  unfold capLambda capParentM capReflectLambdaN capReflectLambdaD capReflectMN capReflectMD
  field_simp [h1,h2,hG,hhd]
  <;> ring

def capReflectUN (r : Row) (t : ℝ) : ℝ :=
  2*(1+2*t)-2*t+gamma r t*(2*(1+2*t)-t)
def capReflectSixN (r : Row) (t : ℝ) : ℝ :=
  600*(gamma r t-delta r t)*(1+2*t)^2-300*(alpha r t+beta r t)*t*(1+2*t)+
    5*capReflectUN r t*t*(41-24*t)-3*t*(1+2*t)
def capReflectSevenN (r : Row) (t : ℝ) : ℝ :=
  capReflectUN r t*t-2*(gamma r t-delta r t)*(1+t)*(1+2*t)

theorem cap_six_reflect_quotient (r : Row) (t : ℝ) (ht : 0 < t) :
    2*(gamma r t-delta r t)*(1+2*t)/t-alpha r t-beta r t+
      2*capParentU r t*(1-(19/60+2*t/5))-1/100 = capReflectSixN r t/(300*t*(1+2*t)) := by
  have h1 : 1+2*t ≠ 0 := by positivity
  unfold capParentU capReflectSixN capReflectUN
  field_simp [ne_of_gt ht,h1]
  <;> ring

theorem cap_seven_reflect_quotient (r : Row) (t : ℝ) (ht : 0 < t) :
    capParentU r t-(gamma r t-delta r t)*(1+t)/t = capReflectSevenN r t/(2*t*(1+2*t)) := by
  have h1 : 1+2*t ≠ 0 := by positivity
  unfold capParentU capReflectSevenN capReflectUN
  field_simp [ne_of_gt ht,h1]
  <;> ring

def capReflectElevenN (r : Row) (t : ℝ) : ℝ :=
  if r = .H then 8*delta r t*(2+gamma r t)*(6+t)-2*t*(2+2*gamma r t-alpha r t-beta r t)^2
  else 2*delta r t*(1+2*t)^2*(6+t)-2*t^2*((2+2*gamma r t-alpha r t-beta r t)*(1+2*t)-(2+gamma r t)*t)
def capReflectElevenD (r : Row) (t : ℝ) : ℝ :=
  if r = .H then 4*(2+gamma r t)*(6+t) else (1+2*t)^2*(6+t)

theorem cap_eleven_reflect_quotient (r : Row) (t : ℝ) (ht : 0 < t) (hg : 0 < gamma r t) :
    2*delta r t-capCUpper r t*(2*t/(6+t)) = capReflectElevenN r t/capReflectElevenD r t := by
  have h1 : 1+2*t ≠ 0 := by positivity
  have h6 : 6+t ≠ 0 := by positivity
  have hG : 2+gamma r t ≠ 0 := by positivity
  by_cases he : r = .H
  · subst r
    simp only [capCUpper,capReflectElevenN,capReflectElevenD,ite_true]
    field_simp [h1,h6,hG]
    <;> ring
  · simp only [capCUpper,capReflectElevenN,capReflectElevenD,he,ite_false]
    field_simp [h1,h6,hG]
    <;> ring

def capReflectD13N (t : ℝ) : ℝ :=
  let T := capDLogChord t
  let Z := t^2+3*t+1
  500*beta .D t*t^3*(2+t)*T^2-
    500*delta .D t*(2*(2*(1+t))-t-2*(2+t)*T)*(2*(1+t))^2*Z-Z*t^2*(2+t)*T^2
def capReflectD13D (t : ℝ) : ℝ :=
  500*(t^2+3*t+1)*t^2*(2+t)*(capDLogChord t)^2

theorem cap_d13_reflect_quotient (t : ℝ) (ht : 0 < t) (hT : capDLogChord t ≠ 0) :
    beta .D t*t/(t^2+3*t+1)-delta .D t*capAdverseUpper (q t/2) (capDLogChord t)-1/500 =
      capReflectD13N t/capReflectD13D t := by
  have h1 : 1+t ≠ 0 := by positivity
  have h2 : 2+t ≠ 0 := by positivity
  have hZ : t^2+3*t+1 ≠ 0 := by positivity
  unfold capAdverseUpper q capReflectD13N capReflectD13D
  field_simp [ne_of_gt ht,h1,h2,hZ,hT]
  <;> ring_nf
  <;> field_simp [h2]
  <;> ring

def reflectCapChord : PolynomialExpr :=
  .add (.const ⟨36,35⟩) (.mul (.const ⟨113,350⟩) (.add .parent (.const ⟨-4,5⟩)))
theorem reflectCapChord_value (v t : ℝ) : reflectCapChord.value v t = capDLogChord t := by
  norm_num [reflectCapChord,PolynomialExpr.value,capDLogChord,fractionValue]
  <;> ring

end
end F4Heavy.Analysis
