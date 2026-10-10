module

public import Erdos993Lean.Analytic.V213.ZeroTiltLaplaceScalarBounds

/-!
Current T2a equations (38)--(43) and the literal polynomial
expressions in Section4.5. No coefficient table is evaluated here. The
conditional sign implications below expose precisely which printed polynomial
sign remains to be supplied by a separately reviewed kernel certificate.
-/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.ZeroTiltLaplace

open Real

noncomputable def pZero (q : ℝ) : ℝ := q/(1+q)
noncomputable def elimS (q u : ℝ) : ℝ := 1+q*u^2
noncomputable def elimT (q u : ℝ) : ℝ := 1-q+q*u^2
noncomputable def elimH0 (q u : ℝ) : ℝ := 1+q*u+q*u^2-q*u^3
noncomputable def interiorSlopeLower (q u d : ℝ) : ℝ :=
  1+aQ q*(1-q)-(1-aQ q)*q*u^2/elimT q u-
    (2+q)*(rateR q+d)*elimH0 q u/(2*q*(1+q)*(elimS q u)^2)
noncomputable def leafSlopeLower (q u d : ℝ) : ℝ :=
  1-aQ q*q-(1-aQ q)*q*u^2/elimT q u-
    (2-q)*(rateR q+d)*elimH0 q u/(2*q*(elimS q u)^2)
noncomputable def printedB0 (q u : ℝ) : ℝ :=
  (101+3*q)*(1-q)^2+q*(1+3*q)*(2-q)*u^2
noncomputable def printedC0 (q u : ℝ) : ℝ :=
  100-101*q-3*q^2+q*(1+3*q)*u^2
noncomputable def polyI (q u d : ℝ) : ℝ :=
  q*(1+q)^2*(2-q)*printedB0 q u*(elimS q u)^2-
    (100*q*(1-q)^2*(2+q)*(1+2*q)+50*d*(1-q)*(1+q)*(2-q)*(2+q))*
      elimT q u*elimH0 q u
noncomputable def polyJ (q u d : ℝ) : ℝ :=
  q*(1+q)*printedC0 q u*(elimS q u)^2-
    (100*q*(1+2*q)*(1-q)+50*d*(1+q)*(2-q))*elimT q u*elimH0 q u
noncomputable def denI (q u : ℝ) : ℝ :=
  100*q*(1-q)*(1+q)^2*(2-q)*elimT q u*(elimS q u)^2
noncomputable def denJ (q u : ℝ) : ℝ :=
  100*q*(1+q)*elimT q u*(elimS q u)^2

noncomputable def diagonalJMinus (q v d : ℝ) : ℝ :=
  1-aQ q*(1+v)-(1-aQ q)*q/(1+q-q^2)-aQ q/q-
    (rateR q+d)*(1+q)^2/(q*(1+2*q)^2)
noncomputable def diagonalJPlus (q v d : ℝ) : ℝ :=
  diagonalJMinus q v d+aQ q*v*(1+q)/q^2
noncomputable def deltaJ (q : ℝ) : ℝ :=
  100*q*(2-q)*(1-q)*(1+2*q)^2*(1+q-q^2)
noncomputable def polyMinus (q : ℝ) : ℝ :=
  -deltaJ q*diagonalJMinus q (wMinus q) (-1/125)
noncomputable def polyPlus (q : ℝ) : ℝ :=
  deltaJ q*diagonalJPlus q (wMinus q) (3/1250)
noncomputable def leafRationalLower (q d : ℝ) : ℝ :=
  (1-aQ q)*(2*q/(2+q)+2*q^3/(3*(2+q)^3))-
    aQ q*wPlus q*q*(2-q)/(2*(1-q))-(rateR q+d)/(1+q-q^2)
noncomputable def deltaE (q : ℝ) : ℝ :=
  600*(2-q)*(1-q)^2*(1+q)*(2+q)^3*(1+q-q^2)
noncomputable def polyE (q d : ℝ) : ℝ := deltaE q*leafRationalLower q d
noncomputable def polyT (q : ℝ) : ℝ := 3*q^4+113*q^3-81*q^2+11*q+2
noncomputable def centerC1 (q : ℝ) : ℝ :=
  q^3*(1+3*q)*(1+2*q)/(50*(2-q)*(1+q)*(2+q)*(1+q-q^2))
noncomputable def centerC2 (q : ℝ) : ℝ :=
  q^3*(1+2*q)*(1-q)^2*(99-103*q)/(150*(2-q)^3*(1+q)^3)
noncomputable def centerRationalLower (q d : ℝ) : ℝ :=
  (1-aQ q)*(2*(q*(1-q))/(2+q*(1-q))+
    2*(q*(1-q))^3/(3*(2+q*(1-q))^3))+
  aQ q*(1-wPlus q)*(2*q/(2+q))-(rateR q+d)/(1+2*q)

theorem q_factors_pos {q : ℝ} (hq : QDomain q) :
    0<q ∧ 0<1-q ∧ 0<1+q ∧ 0<2-q ∧ 0<2+q ∧ 0<1+q-q^2 := by
  have h0 : 0<q := by linarith [hq.1]
  have h1 : 0<1-q := by linarith [hq.2]
  refine ⟨h0,h1,by linarith,by linarith [hq.2],by linarith,?_⟩
  nlinarith [mul_pos h0 h1]

theorem elimination_factors_pos {q : ℝ} (hq : QDomain q) (u : ℝ) :
    0<elimS q u ∧ 0<elimT q u ∧ 0<denI q u ∧ 0<denJ q u := by
  rcases q_factors_pos hq with ⟨h0,h1,hp,h2,h2p,hf⟩
  have hu : 0≤q*u^2 := mul_nonneg h0.le (sq_nonneg u)
  have hs : 0<elimS q u := by unfold elimS; linarith
  have ht : 0<elimT q u := by unfold elimT; linarith
  refine ⟨hs,ht,?_,?_⟩ <;> simp only [denI, denJ] <;> positivity

/-- Exact printed equation38 clearing, with all denominator factors positive. -/
theorem interiorSlope_clearing {q : ℝ} (hq : QDomain q) (u d : ℝ) :
    interiorSlopeLower q u d=polyI q u d/denI q u := by
  rcases q_factors_pos hq with ⟨h0,h1,hp,h2,h2p,hf⟩
  have he := elimination_factors_pos hq u
  unfold interiorSlopeLower polyI denI printedB0 aQ rateR
  field_simp [h0.ne',h1.ne',hp.ne',h2.ne',he.1.ne',he.2.1.ne'] <;> simp only [elimT] <;> ring

theorem leafSlope_clearing {q : ℝ} (hq : QDomain q) (u d : ℝ) :
    leafSlopeLower q u d=polyJ q u d/denJ q u := by
  rcases q_factors_pos hq with ⟨h0,h1,hp,h2,h2p,hf⟩
  have he := elimination_factors_pos hq u
  unfold leafSlopeLower polyJ denJ printedC0 aQ rateR
  field_simp [h0.ne',h1.ne',hp.ne',h2.ne',he.1.ne',he.2.1.ne'] <;> simp only [elimT] <;> ring

theorem slopes_positive_of_polynomials {q u d : ℝ} (hq : QDomain q)
    (hi : 0<polyI q u d) (hj : 0<polyJ q u d) :
    0 < interiorSlopeLower q u d ∧ 0<leafSlopeLower q u d := by
  have he := elimination_factors_pos hq u
  rw [interiorSlope_clearing hq,leafSlope_clearing hq]
  exact ⟨div_pos hi he.2.2.1,div_pos hj he.2.2.2⟩

theorem diagonal_clearing_factors_pos {q : ℝ} (hq : QDomain q) :
    0<deltaJ q ∧ 0<deltaE q := by
  rcases q_factors_pos hq with ⟨h0,h1,hp,h2,h2p,hf⟩
  constructor <;> simp only [deltaJ, deltaE] <;> positivity

theorem diagonal_signs_of_polynomials {q d : ℝ} (hq : QDomain q)
    (hm : 0<polyMinus q) (hp : 0<polyPlus q) (he : 0≤polyE q d) :
    diagonalJMinus q (wMinus q) (-1/125)<0 ∧
    0<diagonalJPlus q (wMinus q) (3/1250) ∧ 0≤leafRationalLower q d := by
  have hden := diagonal_clearing_factors_pos hq
  unfold polyMinus at hm
  unfold polyPlus at hp
  unfold polyE at he
  exact ⟨by nlinarith [hden.1],by nlinarith [hden.1],by nlinarith [hden.2]⟩

/-- The small-p derivative sufficient condition has exactly the printed PT. -/
theorem polyT_clearing {q : ℝ} (hq : QDomain q) :
    aQ q*(1+q)-(pZero q)^2/(2-pZero q)=
      polyT q/(100*(1-q)*(1+q)*(2+q)) := by
  rcases q_factors_pos hq with ⟨h0,h1,hp,h2,h2p,hf⟩
  have hz : 2-pZero q=(2+q)/(1+q) := by
    unfold pZero
    field_simp [hp.ne'] <;> ring
  rw [hz]
  unfold aQ pZero polyT
  field_simp [h1.ne',hp.ne',h2p.ne'] <;> ring

theorem polyT_shift (v : ℝ) :
    polyT (v+1/3)=3*v^4+117*v^3+34*v^2-44*v/9+8/9 := by
  unfold polyT
  ring

theorem polyT_nonnegative_shift_square (v : ℝ) :
    polyT (v+1/3)=34*(v-11/153)^2+982/1377+3*v^4+117*v^3 := by
  unfold polyT
  ring

theorem polyT_pos {q : ℝ} (hq : QDomain q) : 0<polyT q := by
  let v:=q-1/3
  have hv : -(1/12:ℝ)≤v := by dsimp [v]; linarith [hq.1]
  have hqv : q=v+1/3 := by dsimp [v]; ring
  rw [hqv]
  by_cases hn : v≤0
  · rw [polyT_shift]
    have hc : (97/4:ℝ)≤34+117*v := by linarith
    have hprod := mul_nonneg (show 0≤34+117*v by linarith) (sq_nonneg v)
    have hp4 := pow_nonneg (sq_nonneg v) 2
    nlinarith
  · rw [polyT_nonnegative_shift_square]
    have hv0 : 0≤v := by linarith
    positivity

theorem small_parent_sufficient_condition {q : ℝ} (hq : QDomain q) :
    (pZero q)^2/(2-pZero q)<aQ q*(1+q) := by
  rcases q_factors_pos hq with ⟨h0,h1,hp1,h2,h2p,hf⟩
  have hp := polyT_pos hq
  have hden : 0<100*(1-q)*(1+q)*(2+q) := by positivity
  have hh := div_pos hp hden
  rw [← polyT_clearing hq] at hh
  linarith

/-- Only the cubic log-zeta term and linear log-q term are retained in this
identity. Dropping the remaining positive cubic log-q term is legitimate in
its later analytic use; no logarithm is identified with this lower model. -/
theorem center_rational_clearing {q : ℝ} (hq : QDomain q) (d : ℝ) :
    (1+2*q)*centerRationalLower q d=centerC1 q+centerC2 q-d := by
  rcases q_factors_pos hq with ⟨h0,h1,hp,h2,h2p,hf⟩
  have hz : 2+q*(1-q)=(2-q)*(1+q) := by ring
  unfold centerRationalLower centerC1 centerC2 aQ rateR wPlus
  rw [hz]
  field_simp [h1.ne',hp.ne',h2.ne',h2p.ne',hf.ne',show 1+2*q≠0 by positivity] <;> ring

theorem center_terms_pos {q : ℝ} (hq : QDomain q) :
    0<centerC1 q ∧ 0<centerC2 q := by
  rcases q_factors_pos hq with ⟨h0,h1,hp,h2,h2p,hf⟩
  have h99 : 0<99-103*q := by linarith [hq.2]
  unfold centerC1 centerC2
  constructor <;> positivity

end Erdos993Lean.Analytic.V213.ZeroTiltLaplace

-- Audit commands.
#check Erdos993Lean.Analytic.V213.ZeroTiltLaplace.q_factors_pos
#print axioms Erdos993Lean.Analytic.V213.ZeroTiltLaplace.q_factors_pos
#check Erdos993Lean.Analytic.V213.ZeroTiltLaplace.elimination_factors_pos
#print axioms Erdos993Lean.Analytic.V213.ZeroTiltLaplace.elimination_factors_pos
#check Erdos993Lean.Analytic.V213.ZeroTiltLaplace.interiorSlope_clearing
#print axioms Erdos993Lean.Analytic.V213.ZeroTiltLaplace.interiorSlope_clearing
#check Erdos993Lean.Analytic.V213.ZeroTiltLaplace.leafSlope_clearing
#print axioms Erdos993Lean.Analytic.V213.ZeroTiltLaplace.leafSlope_clearing
#check Erdos993Lean.Analytic.V213.ZeroTiltLaplace.slopes_positive_of_polynomials
#print axioms Erdos993Lean.Analytic.V213.ZeroTiltLaplace.slopes_positive_of_polynomials
#check Erdos993Lean.Analytic.V213.ZeroTiltLaplace.diagonal_clearing_factors_pos
#print axioms Erdos993Lean.Analytic.V213.ZeroTiltLaplace.diagonal_clearing_factors_pos
#check Erdos993Lean.Analytic.V213.ZeroTiltLaplace.diagonal_signs_of_polynomials
#print axioms Erdos993Lean.Analytic.V213.ZeroTiltLaplace.diagonal_signs_of_polynomials
#check Erdos993Lean.Analytic.V213.ZeroTiltLaplace.polyT_clearing
#print axioms Erdos993Lean.Analytic.V213.ZeroTiltLaplace.polyT_clearing
#check Erdos993Lean.Analytic.V213.ZeroTiltLaplace.polyT_shift
#print axioms Erdos993Lean.Analytic.V213.ZeroTiltLaplace.polyT_shift
#check Erdos993Lean.Analytic.V213.ZeroTiltLaplace.polyT_nonnegative_shift_square
#print axioms Erdos993Lean.Analytic.V213.ZeroTiltLaplace.polyT_nonnegative_shift_square
#check Erdos993Lean.Analytic.V213.ZeroTiltLaplace.polyT_pos
#print axioms Erdos993Lean.Analytic.V213.ZeroTiltLaplace.polyT_pos
#check Erdos993Lean.Analytic.V213.ZeroTiltLaplace.small_parent_sufficient_condition
#print axioms Erdos993Lean.Analytic.V213.ZeroTiltLaplace.small_parent_sufficient_condition
#check Erdos993Lean.Analytic.V213.ZeroTiltLaplace.center_rational_clearing
#print axioms Erdos993Lean.Analytic.V213.ZeroTiltLaplace.center_rational_clearing
#check Erdos993Lean.Analytic.V213.ZeroTiltLaplace.center_terms_pos
#print axioms Erdos993Lean.Analytic.V213.ZeroTiltLaplace.center_terms_pos
