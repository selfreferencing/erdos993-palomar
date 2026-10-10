module
public import Erdos993Lean.F4U.Light.Construction.KroneckerDigits
public import Erdos993Lean.F4U.Light.Construction.Polynomial2MassWidth
@[expose] public section

namespace F4Unified.LightConstruction.KroneckerIdentity
open F4U.Light.Linking F4U.Light.Linking.Polynomial2
open CoefficientAssembly

def evalIntRows : Rows → Int → Int → Int
  | [], _, _ => 0
  | a :: p, x, y => horner a x + y * evalIntRows p x y

theorem evalIntRows_padd (p q : Rows) (x y : Int) :
    evalIntRows (Polynomial2.padd p q) x y = evalIntRows p x y + evalIntRows q x y := by
  induction p generalizing q with
  | nil => simp [Polynomial2.padd, evalIntRows]
  | cons a p ih =>
    cases q with
    | nil => simp [Polynomial2.padd, evalIntRows]
    | cons b q => simp only [Polynomial2.padd, evalIntRows, horner_padd, ih]; ring

theorem evalIntRows_pscale (c : Int) (p : Rows) (x y : Int) :
    evalIntRows (Polynomial2.pscale c p) x y = c * evalIntRows p x y := by
  induction p with
  | nil => simp [Polynomial2.pscale, evalIntRows]
  | cons a p ih => simp only [Polynomial2.pscale, evalIntRows, horner_pscale, ih]; ring

theorem evalIntRows_psub (p q : Rows) (x y : Int) :
    evalIntRows (Polynomial2.psub p q) x y = evalIntRows p x y - evalIntRows q x y := by
  simp [Polynomial2.psub, Polynomial2.pneg, evalIntRows_padd, evalIntRows_pscale]
  ring

theorem evalIntRows_mulByRow (a : List Int) (q : Rows) (x y : Int) :
    evalIntRows (mulByRow a q) x y = horner a x * evalIntRows q x y := by
  induction q with
  | nil => simp [mulByRow, evalIntRows]
  | cons b q ih => simp only [mulByRow, evalIntRows, horner_mulRow, ih]; ring

theorem evalIntRows_pmul (p q : Rows) (x y : Int) :
    evalIntRows (pmul p q) x y = evalIntRows p x y * evalIntRows q x y := by
  induction p with
  | nil => simp [pmul, evalIntRows]
  | cons a p ih =>
    simp only [pmul, evalIntRows_padd, evalIntRows_mulByRow,
      evalIntRows, horner, zero_add, ih]
    ring

theorem evalIntRows_ppow (p : Rows) (n : Nat) (x y : Int) :
    evalIntRows (ppow p n) x y = evalIntRows p x y ^ n := by
  induction n with
  | zero => simp [ppow, Polynomial2.const, evalIntRows, horner]
  | succ n ih => simp only [ppow, evalIntRows_pmul, ih, pow_succ]

theorem getD_inner_padd (p q : List Int) (i : Nat) :
    (F4U.Light.padd p q).getD i 0 = p.getD i 0 + q.getD i 0 := by
  induction i generalizing p q with
  | zero =>
    cases p <;> cases q <;> simp [F4U.Light.padd]
  | succ i ih =>
    cases p with
    | nil => simp [F4U.Light.padd]
    | cons a p =>
      cases q with
      | nil => simp [F4U.Light.padd]
      | cons b q => simpa only [F4U.Light.padd, List.getD_cons_succ] using ih p q

theorem getD_inner_pscale (c : Int) (p : List Int) (i : Nat) :
    (F4U.Light.pscale c p).getD i 0 = c * p.getD i 0 := by
  induction i generalizing p with
  | zero => cases p <;> simp [F4U.Light.pscale]
  | succ i ih =>
    cases p with
    | nil => simp [F4U.Light.pscale]
    | cons a p => simpa only [F4U.Light.pscale, List.getD_cons_succ] using ih p

theorem coefficient_padd (p q : Rows) (j i : Nat) :
    coefficient (Polynomial2.padd p q) j i = coefficient p j i + coefficient q j i := by
  induction j generalizing p q with
  | zero =>
    cases p with
    | nil => simp [Polynomial2.padd, coefficient]
    | cons a p =>
      cases q with
      | nil => simp [Polynomial2.padd, coefficient]
      | cons b q =>
        simpa only [Polynomial2.padd, coefficient, List.getD_cons_zero] using getD_inner_padd a b i
  | succ j ih =>
    cases p with
    | nil => simp [Polynomial2.padd, coefficient]
    | cons a p =>
      cases q with
      | nil => simp [Polynomial2.padd, coefficient]
      | cons b q => simpa only [Polynomial2.padd, coefficient, List.getD_cons_succ] using ih p q

theorem coefficient_pscale (c : Int) (p : Rows) (j i : Nat) :
    coefficient (Polynomial2.pscale c p) j i = c * coefficient p j i := by
  induction j generalizing p with
  | zero =>
    cases p with
    | nil => simp [Polynomial2.pscale, coefficient]
    | cons a p =>
      simpa only [Polynomial2.pscale, coefficient, List.getD_cons_zero] using getD_inner_pscale c a i
  | succ j ih =>
    cases p with
    | nil => simp [Polynomial2.pscale, coefficient]
    | cons a p => simpa only [Polynomial2.pscale, coefficient, List.getD_cons_succ] using ih p

theorem coefficient_psub (p q : Rows) (j i : Nat) :
    coefficient (Polynomial2.psub p q) j i = coefficient p j i - coefficient q j i := by
  simp [Polynomial2.psub, Polynomial2.pneg, coefficient_padd, coefficient_pscale]
  ring

/-- The original complete coefficient rows are recovered, not merely their value. -/
theorem evalIntRows_zero_coefficients (p : Rows) {B : Int} (hB : 0 < B)
    (stride : Nat) (hstride : 0 < stride)
    (hwidth : CoefficientBoxAssembly.width p ≤ stride)
    (hmass : coefficientMass p < B)
    (hzero : evalIntRows p B (B ^ stride) = 0) : ∀ j i, coefficient p j i = 0 := by
  induction p with
  | nil => simp [coefficient]
  | cons a p ih =>
    have hp0 := Polynomial2MassWidth.norm_nonneg p
    change 0 ≤ coefficientMass p at hp0
    have ha0 := massList_nonneg a
    have halen : a.length ≤ stride := by
      simp only [CoefficientBoxAssembly.width] at hwidth
      exact le_trans (le_max_left _ _) hwidth
    have hawidth : CoefficientBoxAssembly.width p ≤ stride := by
      simp only [CoefficientBoxAssembly.width] at hwidth
      exact le_trans (le_max_right _ _) hwidth
    have hamass : F4U.Light.sumAbs a < B := by
      simp only [coefficientMass] at hmass
      omega
    have hpmass : coefficientMass p < B := by
      simp only [coefficientMass] at hmass
      omega
    have habs : |horner a B| < B ^ stride := abs_horner_lt a hB stride hstride halen hamass
    have hdvd : B ^ stride ∣ horner a B := by
      refine ⟨-evalIntRows p B (B ^ stride), ?_⟩
      simp only [evalIntRows] at hzero
      nlinarith
    have hazero : horner a B = 0 := small_dvd_zero hdvd habs
    have hpzero : evalIntRows p B (B ^ stride) = 0 := by
      simp only [evalIntRows, hazero, zero_add] at hzero
      exact (mul_eq_zero.mp hzero).resolve_left (ne_of_gt (pow_pos hB _))
    have hacoef := horner_zero_coefficients a hB hamass hazero
    intro j i
    cases j with
    | zero => simpa only [coefficient, List.getD_cons_zero] using hacoef i
    | succ j => simpa only [coefficient, List.getD_cons_succ] using ih hawidth hpmass hpzero j i

theorem normalizedEq_of_integer_code (p q : Rows) {B : Int} (hB : 0 < B)
    (stride : Nat) (hstride : 0 < stride)
    (hwidth : max (CoefficientBoxAssembly.width p) (CoefficientBoxAssembly.width q) ≤ stride)
    (hmass : coefficientMass p + coefficientMass q < B)
    (heq : evalIntRows p B (B ^ stride) = evalIntRows q B (B ^ stride)) :
    normalizedEq p q = true := by
  have hwm := le_trans (Polynomial2MassWidth.width_psub_le p q) hwidth
  have hnm := lt_of_le_of_lt (Polynomial2MassWidth.norm_psub_le p q) hmass
  have hzm : evalIntRows (Polynomial2.psub p q) B (B ^ stride) = 0 := by
    rw [evalIntRows_psub, heq, sub_self]
  have hc := evalIntRows_zero_coefficients (Polynomial2.psub p q) hB stride hstride hwm hnm hzm
  apply normalizedEq_of_coefficients_eq
  intro j i
  have hz := hc j i
  rw [coefficient_psub] at hz
  exact sub_eq_zero.mp hz

#print axioms evalIntRows
#print axioms evalIntRows_padd
#print axioms evalIntRows_pscale
#print axioms evalIntRows_psub
#print axioms evalIntRows_mulByRow
#print axioms evalIntRows_pmul
#print axioms evalIntRows_ppow
#print axioms getD_inner_padd
#print axioms getD_inner_pscale
#print axioms coefficient_padd
#print axioms coefficient_pscale
#print axioms coefficient_psub
#print axioms evalIntRows_zero_coefficients
#print axioms normalizedEq_of_integer_code
end F4Unified.LightConstruction.KroneckerIdentity
