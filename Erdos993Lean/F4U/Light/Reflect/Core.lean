module
public import Erdos993Lean.F4U.Light.Construction.KroneckerIdentity
public import Erdos993Lean.F4U.Light.Linking.Rational
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Linarith

/-! Reflective linking: the checker and its soundness proof.

A recipe is a straight-line program over `x`, `t`, rational constants and `+ - * / ^`.
The checker evaluates it once, keeping every value in the form

  (a / b) * N(x,t) / (product of atoms ^ e),

where `a b : Int`, `e` is a list of exponents over a fixed small table of "atom" polynomials and the
integer polynomial `N` is built by ring operations only.  `N` is never stored as coefficients: only its
specialization at `x = B` is computed (one integer per power of `t`, held as sign and magnitude so that the
kernel works in `Nat`), together with a bound on its coefficient mass.  Polynomial identities are recovered from the specialization by the existing
`horner_eq_coefficients`.  No gcd, no division, no rational arithmetic is executed. -/

@[expose] public section

namespace F4U.Light.Reflect
open F4U.Light.Linking
open F4Unified.LightConstruction

abbrev Rows := Polynomial2.Rows
abbrev ZPoly := List Int

/-! ## specialization at `x = B` -/

/-- Horner value with the growing number as the FIRST factor. -/
def hornerR : List Int → Int → Int
  | [], _ => 0
  | a :: p, B => hornerR p B * B + a

theorem hornerR_eq (p : List Int) (B : Int) : hornerR p B = KroneckerIdentity.horner p B := by
  induction p with
  | nil => rfl
  | cons a p ih => simp only [hornerR, KroneckerIdentity.horner, ih]; ring

def spec (B : Int) : Rows → ZPoly
  | [] => []
  | a :: p => hornerR a B :: spec B p

theorem spec_getD (B : Int) (p : Rows) (j : Nat) :
    (spec B p).getD j 0 = KroneckerIdentity.horner (p.getD j []) B := by
  induction p generalizing j with
  | nil => simp [spec, KroneckerIdentity.horner]
  | cons a p ih =>
    cases j with
    | zero => simp [spec, hornerR_eq]
    | succ j => simpa [spec] using ih j

theorem spec_padd (B : Int) (p q : Rows) :
    spec B (Polynomial2.padd p q) = F4U.Light.padd (spec B p) (spec B q) := by
  induction p generalizing q with
  | nil => simp [Polynomial2.padd, spec, F4U.Light.padd]
  | cons a p ih =>
    cases q with
    | nil => simp [Polynomial2.padd, spec, F4U.Light.padd]
    | cons b q =>
      simp only [Polynomial2.padd, spec, F4U.Light.padd, hornerR_eq, KroneckerIdentity.horner_padd, ih]

theorem spec_pscale (B c : Int) (p : Rows) :
    spec B (Polynomial2.pscale c p) = F4U.Light.pscale c (spec B p) := by
  induction p with
  | nil => simp [Polynomial2.pscale, spec, F4U.Light.pscale]
  | cons a p ih =>
    simp only [Polynomial2.pscale, spec, F4U.Light.pscale, hornerR_eq, KroneckerIdentity.horner_pscale, ih]

theorem spec_mulByRow (B : Int) (a : List Int) (q : Rows) :
    spec B (Polynomial2.mulByRow a q) = F4U.Light.pscale (hornerR a B) (spec B q) := by
  induction q with
  | nil => simp [Polynomial2.mulByRow, spec, F4U.Light.pscale]
  | cons b q ih =>
    simp only [Polynomial2.mulByRow, spec, F4U.Light.pscale, hornerR_eq, KroneckerIdentity.horner_mulRow, ih]

theorem spec_pmul (B : Int) (p q : Rows) :
    spec B (Polynomial2.pmul p q) = Polynomial2.mulRow (spec B p) (spec B q) := by
  induction p with
  | nil => simp [Polynomial2.pmul, spec, Polynomial2.mulRow]
  | cons a p ih =>
    simp only [Polynomial2.pmul, spec_padd, spec_mulByRow, spec, Polynomial2.mulRow, ih, hornerR]

def powZ (r : ZPoly) : Nat → ZPoly
  | 0 => [1]
  | n + 1 => Polynomial2.mulRow (powZ r n) r

theorem spec_const_one (B : Int) : spec B (Polynomial2.const 1) = [1] := by
  simp [Polynomial2.const, spec, hornerR]

theorem spec_ppow (B : Int) (p : Rows) (n : Nat) :
    spec B (Polynomial2.ppow p n) = powZ (spec B p) n := by
  induction n with
  | zero => simp [Polynomial2.ppow, spec_const_one, powZ]
  | succ n ih => simp only [Polynomial2.ppow, spec_pmul, ih, powZ]

/-! ## coefficient mass, restated for `coefficientMass` -/

abbrev mass := Polynomial2.coefficientMass

theorem mass_nonneg (p : Rows) : 0 ≤ mass p := Polynomial2MassWidth.norm_nonneg p
theorem mass_padd_le (p q : Rows) : mass (Polynomial2.padd p q) ≤ mass p + mass q :=
  Polynomial2MassWidth.norm_padd_le p q
theorem mass_pscale (c : Int) (p : Rows) : mass (Polynomial2.pscale c p) = |c| * mass p :=
  Polynomial2MassWidth.norm_pscale c p
theorem mass_pmul_le (p q : Rows) : mass (Polynomial2.pmul p q) ≤ mass p * mass q :=
  Polynomial2MassWidth.norm_pmul_le p q
theorem mass_ppow_le (p : Rows) (n : Nat) : mass (Polynomial2.ppow p n) ≤ mass p ^ n :=
  Polynomial2MassWidth.norm_ppow_le p n

theorem sumAbs_getD_le (P : Rows) (j : Nat) : F4U.Light.sumAbs (P.getD j []) ≤ mass P := by
  induction P generalizing j with
  | nil => simp [F4U.Light.sumAbs, mass, Polynomial2.coefficientMass]
  | cons a P ih =>
    cases j with
    | zero =>
      have h := mass_nonneg P
      simp only [List.getD_cons_zero, mass, Polynomial2.coefficientMass] at *
      omega
    | succ j =>
      have h := KroneckerIdentity.massList_nonneg a
      have h2 := ih j
      simp only [List.getD_cons_succ, mass, Polynomial2.coefficientMass] at *
      omega

/-! ## equality of specializations up to trailing zeros -/

def allZ : ZPoly → Bool
  | [] => true
  | a :: p => decide (a = 0) && allZ p

def eqZ : ZPoly → ZPoly → Bool
  | [], q => allZ q
  | a :: p, [] => decide (a = 0) && allZ p
  | a :: p, b :: q => decide (a = b) && eqZ p q

theorem allZ_getD {p : ZPoly} (h : allZ p = true) (i : Nat) : p.getD i 0 = 0 := by
  induction p generalizing i with
  | nil => simp
  | cons a p ih =>
    simp only [allZ, Bool.and_eq_true, decide_eq_true_eq] at h
    cases i with
    | zero => simpa using h.1
    | succ i => simpa using ih h.2 i

theorem eqZ_getD {p q : ZPoly} (h : eqZ p q = true) (i : Nat) : p.getD i 0 = q.getD i 0 := by
  induction p generalizing q i with
  | nil =>
    simp only [eqZ] at h
    simpa using (allZ_getD h i).symm
  | cons a p ih =>
    cases q with
    | nil =>
      simp only [eqZ, Bool.and_eq_true, decide_eq_true_eq] at h
      cases i with
      | zero => simpa using h.1
      | succ i => simpa using allZ_getD h.2 i
    | cons b q =>
      simp only [eqZ, Bool.and_eq_true, decide_eq_true_eq] at h
      cases i with
      | zero => simpa using h.1
      | succ i => simpa using ih h.2 i

/-- Equal specializations at `x = B` with total mass below `B` give the polynomial identity. -/
theorem normalizedEq_of_spec {B : Int} (hB : 0 < B) (P Q : Rows) (hm : mass P + mass Q < B)
    (h : eqZ (spec B P) (spec B Q) = true) : Polynomial2.normalizedEq P Q = true := by
  apply CoefficientAssembly.normalizedEq_of_coefficients_eq
  intro j i
  have hj := eqZ_getD h j
  rw [spec_getD, spec_getD] at hj
  exact KroneckerIdentity.horner_eq_coefficients (P.getD j []) (Q.getD j []) hB
    (lt_of_le_of_lt (add_le_add (sumAbs_getD_le P j) (sumAbs_getD_le Q j)) hm) hj i

/-! ## products of atom powers -/

def mulPowRows (N A : Rows) : Nat → Rows
  | 0 => N
  | k + 1 => mulPowRows (Polynomial2.pmul A N) A k

def mulAtomsRows : Rows → List Rows → List Nat → Rows
  | N, [], _ => N
  | N, _ :: _, [] => N
  | N, A :: As, k :: us => mulAtomsRows (mulPowRows N A k) As us

def mulPowZ (N A : ZPoly) : Nat → ZPoly
  | 0 => N
  | k + 1 => mulPowZ (Polynomial2.mulRow A N) A k

def mulAtomsZ : ZPoly → List ZPoly → List Nat → ZPoly
  | N, [], _ => N
  | N, _ :: _, [] => N
  | N, A :: As, k :: us => mulAtomsZ (mulPowZ N A k) As us

noncomputable def atomEval : List Rows → List Nat → ℝ → ℝ → ℝ
  | [], _, _, _ => 1
  | _ :: _, [], _, _ => 1
  | A :: As, k :: us, x, t => Polynomial2.eval A x t ^ k * atomEval As us x t

def atomMass : List Int → List Nat → Int
  | [], _ => 1
  | _ :: _, [] => 1
  | m :: ms, k :: us => m ^ k * atomMass ms us

theorem eval_mulPowRows (N A : Rows) (k : Nat) (x t : ℝ) :
    Polynomial2.eval (mulPowRows N A k) x t = Polynomial2.eval N x t * Polynomial2.eval A x t ^ k := by
  induction k generalizing N with
  | zero => simp [mulPowRows]
  | succ k ih => simp only [mulPowRows, ih, Polynomial2.eval_pmul, pow_succ]; ring

theorem eval_mulAtomsRows (N : Rows) (As : List Rows) (us : List Nat) (x t : ℝ) :
    Polynomial2.eval (mulAtomsRows N As us) x t = Polynomial2.eval N x t * atomEval As us x t := by
  induction As generalizing N us with
  | nil => simp [mulAtomsRows, atomEval]
  | cons A As ih =>
    cases us with
    | nil => simp [mulAtomsRows, atomEval]
    | cons k us => simp only [mulAtomsRows, atomEval, ih, eval_mulPowRows]; ring

theorem spec_mulPowRows (B : Int) (N A : Rows) (k : Nat) :
    spec B (mulPowRows N A k) = mulPowZ (spec B N) (spec B A) k := by
  induction k generalizing N with
  | zero => rfl
  | succ k ih => simp only [mulPowRows, mulPowZ, ih, spec_pmul]

theorem spec_mulAtomsRows (B : Int) (N : Rows) (As : List Rows) (us : List Nat) :
    spec B (mulAtomsRows N As us) = mulAtomsZ (spec B N) (As.map (spec B)) us := by
  induction As generalizing N us with
  | nil => simp [mulAtomsRows, mulAtomsZ]
  | cons A As ih =>
    cases us with
    | nil => simp [mulAtomsRows, mulAtomsZ]
    | cons k us => simp only [mulAtomsRows, mulAtomsZ, List.map_cons, ih, spec_mulPowRows]

theorem mass_mulPowRows_le (N A : Rows) (k : Nat) :
    mass (mulPowRows N A k) ≤ mass N * mass A ^ k := by
  induction k generalizing N with
  | zero => simp [mulPowRows]
  | succ k ih =>
    calc mass (mulPowRows N A (k + 1)) = mass (mulPowRows (Polynomial2.pmul A N) A k) := rfl
      _ ≤ mass (Polynomial2.pmul A N) * mass A ^ k := ih _
      _ ≤ (mass A * mass N) * mass A ^ k :=
        mul_le_mul_of_nonneg_right (mass_pmul_le A N) (pow_nonneg (mass_nonneg A) k)
      _ = mass N * mass A ^ (k + 1) := by ring

theorem atomMass_nonneg (As : List Rows) (us : List Nat) : 0 ≤ atomMass (As.map mass) us := by
  induction As generalizing us with
  | nil => simp [atomMass]
  | cons A As ih =>
    cases us with
    | nil => simp [atomMass]
    | cons k us =>
      simp only [List.map_cons, atomMass]
      exact mul_nonneg (pow_nonneg (mass_nonneg A) k) (ih us)

theorem mass_mulAtomsRows_le (N : Rows) (As : List Rows) (us : List Nat) :
    mass (mulAtomsRows N As us) ≤ mass N * atomMass (As.map mass) us := by
  induction As generalizing N us with
  | nil => simp [mulAtomsRows, atomMass]
  | cons A As ih =>
    cases us with
    | nil => simp [mulAtomsRows, atomMass]
    | cons k us =>
      calc mass (mulAtomsRows N (A :: As) (k :: us)) = mass (mulAtomsRows (mulPowRows N A k) As us) := rfl
        _ ≤ mass (mulPowRows N A k) * atomMass (As.map mass) us := ih _ _
        _ ≤ (mass N * mass A ^ k) * atomMass (As.map mass) us :=
          mul_le_mul_of_nonneg_right (mass_mulPowRows_le N A k) (atomMass_nonneg As us)
        _ = mass N * atomMass ((A :: As).map mass) (k :: us) := by
          simp only [List.map_cons, atomMass]; ring

/-! ## sign and magnitude: the same arithmetic over `Nat`

Lean's kernel executes `Nat` operations on large literals several times faster than `Int` operations,
so the numerator's specialization is carried as a list of (sign, magnitude) pairs. -/

abbrev SM := Bool × Nat
abbrev NPoly := List SM

def smZ (c : SM) : Int := if c.1 then -(c.2 : Int) else (c.2 : Int)

def toZ : NPoly → ZPoly
  | [] => []
  | c :: p => smZ c :: toZ p

def ofInt : Int → SM
  | Int.ofNat n => (false, n)
  | Int.negSucc n => (true, n + 1)

theorem smZ_ofInt (z : Int) : smZ (ofInt z) = z := by
  cases z with
  | ofNat n => simp [ofInt, smZ]
  | negSucc n => simp [ofInt, smZ, Int.negSucc_eq]

def ofZ : ZPoly → NPoly
  | [] => []
  | z :: p => ofInt z :: ofZ p

theorem toZ_ofZ (p : ZPoly) : toZ (ofZ p) = p := by
  induction p with
  | nil => rfl
  | cons z p ih => simp only [ofZ, toZ, smZ_ofInt, ih]

theorem toZ_one : toZ [(false, 1)] = [1] := by simp [toZ, smZ]

def addSM (a b : SM) : SM :=
  if a.1 = b.1 then (a.1, a.2 + b.2)
  else if b.2 ≤ a.2 then (a.1, a.2 - b.2) else (b.1, b.2 - a.2)

theorem smZ_addSM (a b : SM) : smZ (addSM a b) = smZ a + smZ b := by
  obtain ⟨s1, m1⟩ := a
  obtain ⟨s2, m2⟩ := b
  cases s1 <;> cases s2
  · simp [addSM, smZ]
  · by_cases h : m2 ≤ m1
    · simp [addSM, smZ, h] <;> omega
    · simp [addSM, smZ, h] <;> omega
  · by_cases h : m2 ≤ m1
    · simp [addSM, smZ, h] <;> omega
    · simp [addSM, smZ, h] <;> omega
  · simp [addSM, smZ] <;> omega

def addN : NPoly → NPoly → NPoly
  | [], q => q
  | a :: p, [] => a :: p
  | a :: p, b :: q => addSM a b :: addN p q

theorem toZ_addN (p q : NPoly) : toZ (addN p q) = F4U.Light.padd (toZ p) (toZ q) := by
  induction p generalizing q with
  | nil => simp [addN, toZ, F4U.Light.padd]
  | cons a p ih =>
    cases q with
    | nil => simp [addN, toZ, F4U.Light.padd]
    | cons b q => simp only [addN, toZ, F4U.Light.padd, smZ_addSM, ih]

def scaleKeep (m : Nat) : NPoly → NPoly
  | [] => []
  | c :: p => (c.1, c.2 * m) :: scaleKeep m p

def scaleFlip (m : Nat) : NPoly → NPoly
  | [] => []
  | c :: p => (!c.1, c.2 * m) :: scaleFlip m p

def scaleSM (a : SM) (p : NPoly) : NPoly := if a.1 then scaleFlip a.2 p else scaleKeep a.2 p

theorem toZ_scaleKeep (m : Nat) (p : NPoly) :
    toZ (scaleKeep m p) = F4U.Light.pscale (m : Int) (toZ p) := by
  induction p with
  | nil => simp [scaleKeep, toZ, F4U.Light.pscale]
  | cons c p ih =>
    obtain ⟨s, k⟩ := c
    cases s <;> simp [scaleKeep, toZ, F4U.Light.pscale, smZ, ih, mul_comm]

theorem toZ_scaleFlip (m : Nat) (p : NPoly) :
    toZ (scaleFlip m p) = F4U.Light.pscale (-(m : Int)) (toZ p) := by
  induction p with
  | nil => simp [scaleFlip, toZ, F4U.Light.pscale]
  | cons c p ih =>
    obtain ⟨s, k⟩ := c
    cases s <;> simp [scaleFlip, toZ, F4U.Light.pscale, smZ, ih, mul_comm]

theorem toZ_scaleSM (a : SM) (p : NPoly) :
    toZ (scaleSM a p) = F4U.Light.pscale (smZ a) (toZ p) := by
  obtain ⟨s, m⟩ := a
  cases s <;> simp [scaleSM, smZ, toZ_scaleKeep, toZ_scaleFlip]

/-- Schoolbook product; the FIRST list supplies the scalars (put the shorter numbers there). -/
def mulN : NPoly → NPoly → NPoly
  | [], _ => []
  | a :: p, q => addN (scaleSM a q) ((false, 0) :: mulN p q)

theorem toZ_mulN (p q : NPoly) : toZ (mulN p q) = Polynomial2.mulRow (toZ p) (toZ q) := by
  induction p with
  | nil => simp [mulN, toZ, Polynomial2.mulRow]
  | cons a p ih =>
    simp only [mulN, toZ_addN, toZ_scaleSM, toZ, Polynomial2.mulRow, ih]
    simp [smZ]

def powN (r : NPoly) : Nat → NPoly
  | 0 => [(false, 1)]
  | n + 1 => mulN (powN r n) r

theorem toZ_powN (r : NPoly) (n : Nat) : toZ (powN r n) = powZ (toZ r) n := by
  induction n with
  | zero => simp [powN, toZ, smZ, powZ]
  | succ n ih => simp only [powN, powZ, toZ_mulN, ih]

def mulPowN (N a : NPoly) : Nat → NPoly
  | 0 => N
  | k + 1 => mulPowN (mulN a N) a k

def mulAtomsN : NPoly → List NPoly → List Nat → NPoly
  | N, [], _ => N
  | N, _ :: _, [] => N
  | N, a :: as, k :: us => mulAtomsN (mulPowN N a k) as us

theorem toZ_mulPowN (N a : NPoly) (k : Nat) :
    toZ (mulPowN N a k) = mulPowZ (toZ N) (toZ a) k := by
  induction k generalizing N with
  | zero => rfl
  | succ k ih => simp only [mulPowN, mulPowZ, ih, toZ_mulN]

theorem toZ_mulAtomsN (N : NPoly) (l : List ZPoly) (us : List Nat) :
    toZ (mulAtomsN N (l.map ofZ) us) = mulAtomsZ (toZ N) l us := by
  induction l generalizing N us with
  | nil => simp [mulAtomsN, mulAtomsZ]
  | cons a l ih =>
    cases us with
    | nil => simp [mulAtomsN, mulAtomsZ]
    | cons k us => simp only [List.map_cons, mulAtomsN, mulAtomsZ, ih, toZ_mulPowN, toZ_ofZ]

def allZN : NPoly → Bool
  | [] => true
  | a :: p => decide (a.2 = 0) && allZN p

def eqSM (a b : SM) : Bool := decide (a.2 = b.2) && (decide (a.1 = b.1) || decide (a.2 = 0))

def eqN : NPoly → NPoly → Bool
  | [], q => allZN q
  | a :: p, [] => decide (a.2 = 0) && allZN p
  | a :: p, b :: q => eqSM a b && eqN p q

/-- Always `true`; evaluating it makes the kernel compute every magnitude. -/
def forceN : NPoly → Bool
  | [] => true
  | a :: p => decide (a.2 = a.2) && forceN p

theorem smZ_zero {a : SM} (h : a.2 = 0) : smZ a = 0 := by
  obtain ⟨s, m⟩ := a
  cases s <;> simp_all [smZ]

theorem smZ_eqSM {a b : SM} (h : eqSM a b = true) : smZ a = smZ b := by
  obtain ⟨s1, m1⟩ := a
  obtain ⟨s2, m2⟩ := b
  simp only [eqSM, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at h
  obtain ⟨hm, hs | hz⟩ := h
  · subst hm; subst hs; rfl
  · subst hm; subst hz; cases s1 <;> cases s2 <;> simp [smZ]

theorem allZN_allZ {p : NPoly} (h : allZN p = true) : allZ (toZ p) = true := by
  induction p with
  | nil => rfl
  | cons a p ih =>
    simp only [allZN, Bool.and_eq_true, decide_eq_true_eq] at h
    simp only [toZ, allZ, Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨smZ_zero h.1, ih h.2⟩

theorem eqN_eqZ {p q : NPoly} (h : eqN p q = true) : eqZ (toZ p) (toZ q) = true := by
  induction p generalizing q with
  | nil =>
    simp only [eqN] at h
    simpa only [toZ, eqZ] using allZN_allZ h
  | cons a p ih =>
    cases q with
    | nil =>
      simp only [eqN, Bool.and_eq_true, decide_eq_true_eq] at h
      simp only [toZ, eqZ, Bool.and_eq_true, decide_eq_true_eq]
      exact ⟨smZ_zero h.1, allZN_allZ h.2⟩
    | cons b q =>
      simp only [eqN, Bool.and_eq_true] at h
      simp only [toZ, eqZ, Bool.and_eq_true, decide_eq_true_eq]
      exact ⟨smZ_eqSM h.1, ih h.2⟩

/-- Coefficient mass over `Nat`. -/
def sumNatAbs : List Int → Nat
  | [] => 0
  | a :: p => a.natAbs + sumNatAbs p

def massN : Rows → Nat
  | [] => 0
  | a :: p => sumNatAbs a + massN p

theorem sumNatAbs_eq (p : List Int) : ((sumNatAbs p : Nat) : Int) = F4U.Light.sumAbs p := by
  induction p with
  | nil => simp [sumNatAbs, F4U.Light.sumAbs]
  | cons a p ih =>
    simp only [sumNatAbs, F4U.Light.sumAbs, Nat.cast_add, ih, KroneckerIdentity.absI_eq_abs,
      Int.natCast_natAbs]

theorem massN_eq (P : Rows) : ((massN P : Nat) : Int) = mass P := by
  induction P with
  | nil => simp [massN, mass, Polynomial2.coefficientMass]
  | cons a P ih =>
    show ((sumNatAbs a + massN P : Nat) : Int) = F4U.Light.sumAbs a + mass P
    rw [Nat.cast_add, sumNatAbs_eq, ih]

/-! ## exponent lists -/

def addE : List Nat → List Nat → List Nat
  | [], q => q
  | a :: p, [] => a :: p
  | a :: p, b :: q => (a + b) :: addE p q

def scaleE (n : Nat) : List Nat → List Nat
  | [] => []
  | k :: us => (k * n) :: scaleE n us

theorem atomEval_nil (A : List Rows) (x t : ℝ) : atomEval A [] x t = 1 := by
  cases A <;> rfl

theorem atomEval_addE (A : List Rows) (u v : List Nat) (x t : ℝ) :
    atomEval A (addE u v) x t = atomEval A u x t * atomEval A v x t := by
  induction A generalizing u v with
  | nil => simp [atomEval]
  | cons A As ih =>
    cases u with
    | nil => simp [addE, atomEval]
    | cons a u =>
      cases v with
      | nil => simp [addE, atomEval]
      | cons b v => simp only [addE, atomEval, ih, pow_add]; ring

theorem atomEval_scaleE (A : List Rows) (n : Nat) (u : List Nat) (x t : ℝ) :
    atomEval A (scaleE n u) x t = atomEval A u x t ^ n := by
  induction A generalizing u with
  | nil => simp [atomEval]
  | cons A As ih =>
    cases u with
    | nil => simp [scaleE, atomEval]
    | cons a u => simp only [scaleE, atomEval, ih, pow_mul, mul_pow]

/-! ## pure algebra over the reals -/

theorem add_alg (a1 b1 a2 b2 a b k1 k2 p1 p2 M U1 U2 : ℝ)
    (hb1 : b1 ≠ 0) (hb2 : b2 ≠ 0) (hb : b ≠ 0) (hM : M ≠ 0) (hU1 : U1 ≠ 0) (hU2 : U2 ≠ 0)
    (h1 : a1 * b = a * k1 * b1) (h2 : a2 * b = a * k2 * b2) :
    a1 / b1 * (p1 / (M * U1)) + a2 / b2 * (p2 / (M * U2)) =
      a / b * ((k1 * (p1 * U2) + k2 * (p2 * U1)) / (M * U1 * U2)) := by
  have e1 : a1 = a * k1 * b1 / b := by rw [eq_div_iff hb]; exact h1
  have e2 : a2 = a * k2 * b2 / b := by rw [eq_div_iff hb]; exact h2
  rw [e1, e2]
  field_simp <;> ring

theorem sub_alg (a1 b1 a2 b2 a b k1 k2 p1 p2 M U1 U2 : ℝ)
    (hb1 : b1 ≠ 0) (hb2 : b2 ≠ 0) (hb : b ≠ 0) (hM : M ≠ 0) (hU1 : U1 ≠ 0) (hU2 : U2 ≠ 0)
    (h1 : a1 * b = a * k1 * b1) (h2 : -a2 * b = a * k2 * b2) :
    a1 / b1 * (p1 / (M * U1)) - a2 / b2 * (p2 / (M * U2)) =
      a / b * ((k1 * (p1 * U2) + k2 * (p2 * U1)) / (M * U1 * U2)) := by
  have e1 : a1 = a * k1 * b1 / b := by rw [eq_div_iff hb]; exact h1
  have e2 : a2 = -(a * k2 * b2) / b := by rw [eq_div_iff hb]; linarith
  rw [e1, e2]
  field_simp <;> ring

theorem mul_alg (a1 b1 a2 b2 a b p1 p2 E1 E2 : ℝ)
    (hb1 : b1 ≠ 0) (hb2 : b2 ≠ 0) (hb : b ≠ 0) (hE1 : E1 ≠ 0) (hE2 : E2 ≠ 0)
    (h : a1 * a2 * b = a * (b1 * b2)) :
    a1 / b1 * (p1 / E1) * (a2 / b2 * (p2 / E2)) = a / b * (p1 * p2 / (E1 * E2)) := by
  have e : a = a1 * a2 * b / (b1 * b2) := by rw [eq_div_iff (mul_ne_zero hb1 hb2)]; exact h.symm
  rw [e]
  field_simp <;> ring

theorem div_alg (a1 b1 a2 b2 a b c0 p1 E1 F M U2 W : ℝ)
    (hb1 : b1 ≠ 0) (hb2 : b2 ≠ 0) (hb : b ≠ 0) (ha2 : a2 ≠ 0) (hc0 : c0 ≠ 0)
    (hE1 : E1 ≠ 0) (hF : F ≠ 0) (hM : M ≠ 0) (hU2 : U2 ≠ 0)
    (hE : E1 * F = M * W) (h : a1 * b2 * b = a * (b1 * a2 * c0)) :
    a1 / b1 * (p1 / E1) / (a2 / b2 * (c0 * F / (M * U2))) = a / b * (p1 * U2 / W) := by
  have e : a = a1 * b2 * b / (b1 * a2 * c0) := by
    rw [eq_div_iff (mul_ne_zero (mul_ne_zero hb1 ha2) hc0)]; exact h.symm
  have eW : W = E1 * F / M := by rw [eq_div_iff hM]; linarith
  rw [e, eW]
  field_simp <;> ring

theorem pow_alg (a1 b1 a b p1 E1 : ℝ) (n : ℕ) (hb1 : b1 ≠ 0) (hb : b ≠ 0)
    (h : a1 ^ n * b = a * b1 ^ n) :
    (a1 / b1 * (p1 / E1)) ^ n = a / b * (p1 ^ n / E1 ^ n) := by
  have e : a / b = a1 ^ n / b1 ^ n := by
    rw [div_eq_div_iff hb (pow_ne_zero n hb1)]; exact h.symm
  rw [e, mul_pow, div_pow, div_pow]

theorem root_alg (a b lam mu P E G Ns Ds : ℝ) (hb : b ≠ 0) (hlam : lam ≠ 0) (hmu : mu ≠ 0)
    (hE : E ≠ 0) (hab : mu * b = a * lam) (hN : mu * P = G * Ns) (hD : lam * E = G * Ds) :
    Ds ≠ 0 ∧ Ns / Ds = a / b * (P / E) := by
  have hGD : G * Ds ≠ 0 := by rw [← hD]; exact mul_ne_zero hlam hE
  have hG : G ≠ 0 := (mul_ne_zero_iff.mp hGD).1
  have hDs : Ds ≠ 0 := (mul_ne_zero_iff.mp hGD).2
  refine ⟨hDs, ?_⟩
  have eP : P = G * Ns / mu := by rw [eq_div_iff hmu]; linarith
  have eE : E = G * Ds / lam := by rw [eq_div_iff hlam]; linarith
  have ea : a = mu * b / lam := by rw [eq_div_iff hlam]; linarith
  rw [eP, eE, ea]
  field_simp <;> ring

/-! ## values and the invariant -/

structure FVal where
  a : Int
  b : Int
  r : NPoly
  e : List Nat
  nb : Int

def dflt : FVal := ⟨0, 1, [], [], 0⟩

/-- `y` is the real number represented by `v` at `(x,t)`. -/
def Inv (B : Int) (A : List Rows) (x t : ℝ) (v : FVal) (y : ℝ) : Prop :=
  ∃ P : Rows, toZ v.r = spec B P ∧ mass P ≤ v.nb ∧ atomEval A v.e x t ≠ 0 ∧ (v.b : ℝ) ≠ 0 ∧
    y = (v.a : ℝ) / (v.b : ℝ) * (Polynomial2.eval P x t / atomEval A v.e x t)

theorem inv_dflt (B : Int) (A : List Rows) (x t : ℝ) : Inv B A x t dflt 0 := by
  refine ⟨[], rfl, ?_, ?_, ?_, ?_⟩
  · simp [dflt, mass, Polynomial2.coefficientMass]
  · simp [dflt, atomEval_nil]
  · simp [dflt]
  · simp [dflt]

theorem forall₂_getD {α β : Type} {R : α → β → Prop} {l1 : List α} {l2 : List β}
    (h : List.Forall₂ R l1 l2) {d1 : α} {d2 : β} (hd : R d1 d2) (i : Nat) :
    R (l1.getD i d1) (l2.getD i d2) := by
  induction h generalizing i with
  | nil => simpa using hd
  | cons hab _ ih =>
    cases i with
    | zero => simpa using hab
    | succ i => simpa using ih i

/-! ## the operations -/

def sgnA (neg : Bool) (a : Int) : Int := if neg then -a else a

def addF (aN : List NPoly) (aM : List Int) (neg : Bool) (p q : FVal) (k1 k2 a b : Int)
    (m u1 u2 : List Nat) : Option FVal :=
  if decide (b ≠ 0) && decide (p.a * b = a * k1 * p.b) &&
      decide (sgnA neg q.a * b = a * k2 * q.b) &&
      decide (p.e = addE m u1) && decide (q.e = addE m u2) then
    some ⟨a, b,
      addN (scaleSM (ofInt k1) (mulAtomsN p.r aN u2)) (scaleSM (ofInt k2) (mulAtomsN q.r aN u1)),
      addE p.e u2,
      F4U.Light.absI k1 * (p.nb * atomMass aM u2) + F4U.Light.absI k2 * (q.nb * atomMass aM u1)⟩
  else none

theorem addF_sound {B : Int} {A : List Rows} {x t : ℝ} {neg : Bool} {p q : FVal}
    {k1 k2 a b : Int} {m u1 u2 : List Nat} {v : FVal} {y1 y2 : ℝ}
    (hp : Inv B A x t p y1) (hq : Inv B A x t q y2)
    (h : addF ((A.map (spec B)).map ofZ) (A.map mass) neg p q k1 k2 a b m u1 u2 = some v) :
    Inv B A x t v (if neg then y1 - y2 else y1 + y2) := by
  unfold addF at h
  split at h
  next hc =>
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
    obtain ⟨⟨⟨⟨hb, h1⟩, h2⟩, he1⟩, he2⟩ := hc
    obtain ⟨P1, hr1, hm1, hE1, hb1, rfl⟩ := hp
    obtain ⟨P2, hr2, hm2, hE2, hb2, rfl⟩ := hq
    cases h
    rw [he1, atomEval_addE] at hE1
    rw [he2, atomEval_addE] at hE2
    have hM := (mul_ne_zero_iff.mp hE1).1
    have hU1 := (mul_ne_zero_iff.mp hE1).2
    have hU2 := (mul_ne_zero_iff.mp hE2).2
    have hbR : (b : ℝ) ≠ 0 := by exact_mod_cast hb
    refine ⟨Polynomial2.padd (Polynomial2.pscale k1 (mulAtomsRows P1 A u2))
      (Polynomial2.pscale k2 (mulAtomsRows P2 A u1)), ?_, ?_, ?_, hbR, ?_⟩
    · simp only [toZ_addN, toZ_scaleSM, smZ_ofInt, toZ_mulAtomsN, hr1, hr2, spec_padd, spec_pscale,
        spec_mulAtomsRows]
    · have hA2 := atomMass_nonneg A u2
      have hA1 := atomMass_nonneg A u1
      calc mass (Polynomial2.padd (Polynomial2.pscale k1 (mulAtomsRows P1 A u2))
              (Polynomial2.pscale k2 (mulAtomsRows P2 A u1)))
          ≤ mass (Polynomial2.pscale k1 (mulAtomsRows P1 A u2)) +
              mass (Polynomial2.pscale k2 (mulAtomsRows P2 A u1)) := mass_padd_le _ _
        _ = |k1| * mass (mulAtomsRows P1 A u2) + |k2| * mass (mulAtomsRows P2 A u1) := by
          rw [mass_pscale, mass_pscale]
        _ ≤ |k1| * (p.nb * atomMass (A.map mass) u2) + |k2| * (q.nb * atomMass (A.map mass) u1) :=
          add_le_add
            (mul_le_mul_of_nonneg_left (le_trans (mass_mulAtomsRows_le P1 A u2)
              (mul_le_mul_of_nonneg_right hm1 hA2)) (abs_nonneg k1))
            (mul_le_mul_of_nonneg_left (le_trans (mass_mulAtomsRows_le P2 A u1)
              (mul_le_mul_of_nonneg_right hm2 hA1)) (abs_nonneg k2))
        _ = F4U.Light.absI k1 * (p.nb * atomMass (A.map mass) u2) +
              F4U.Light.absI k2 * (q.nb * atomMass (A.map mass) u1) := by
          rw [KroneckerIdentity.absI_eq_abs, KroneckerIdentity.absI_eq_abs]
    · show atomEval A (addE p.e u2) x t ≠ 0
      rw [he1, atomEval_addE, atomEval_addE]
      exact mul_ne_zero (mul_ne_zero hM hU1) hU2
    · show _ = (a : ℝ) / (b : ℝ) * (Polynomial2.eval _ x t / atomEval A (addE p.e u2) x t)
      have h1' : (p.a : ℝ) * b = a * k1 * p.b := by exact_mod_cast h1
      simp only [he1, he2, atomEval_addE, Polynomial2.eval_padd, Polynomial2.eval_pscale,
        eval_mulAtomsRows]
      cases neg with
      | false =>
        have h2' : (q.a : ℝ) * b = a * k2 * q.b := by
          simp only [sgnA, Bool.false_eq_true, ite_false] at h2; exact_mod_cast h2
        simp only [Bool.false_eq_true, ite_false]
        exact add_alg _ _ _ _ _ _ _ _ _ _ _ _ _ hb1 hb2 hbR hM hU1 hU2 h1' h2'
      | true =>
        have h2' : -(q.a : ℝ) * b = a * k2 * q.b := by
          simp only [sgnA, ite_true] at h2; exact_mod_cast h2
        simp only [ite_true]
        exact sub_alg _ _ _ _ _ _ _ _ _ _ _ _ _ hb1 hb2 hbR hM hU1 hU2 h1' h2'
  next => cases h

def mulF (sw : Bool) (p q : FVal) (a b : Int) : Option FVal :=
  if decide (b ≠ 0) && decide (p.a * q.a * b = a * (p.b * q.b)) then
    some ⟨a, b, if sw then mulN p.r q.r else mulN q.r p.r,
      addE p.e q.e, p.nb * q.nb⟩
  else none

theorem mulF_sound {B : Int} {A : List Rows} {x t : ℝ} {sw : Bool} {p q : FVal}
    {a b : Int} {v : FVal} {y1 y2 : ℝ}
    (hp : Inv B A x t p y1) (hq : Inv B A x t q y2)
    (h : mulF sw p q a b = some v) : Inv B A x t v (y1 * y2) := by
  unfold mulF at h
  split at h
  next hc =>
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
    obtain ⟨hb, h1⟩ := hc
    obtain ⟨P1, hr1, hm1, hE1, hb1, rfl⟩ := hp
    obtain ⟨P2, hr2, hm2, hE2, hb2, rfl⟩ := hq
    cases h
    have hbR : (b : ℝ) ≠ 0 := by exact_mod_cast hb
    have h1' : (p.a : ℝ) * q.a * b = a * (p.b * q.b) := by exact_mod_cast h1
    have hn1 := mass_nonneg P1
    have hn2 := mass_nonneg P2
    cases sw with
    | true =>
      refine ⟨Polynomial2.pmul P1 P2, ?_, ?_, ?_, hbR, ?_⟩
      · simp only [toZ_mulN, spec_pmul, hr1, hr2, ite_true]
      · exact le_trans (mass_pmul_le P1 P2) (mul_le_mul hm1 hm2 hn2 (le_trans hn1 hm1))
      · show atomEval A (addE p.e q.e) x t ≠ 0
        rw [atomEval_addE]; exact mul_ne_zero hE1 hE2
      · show _ = (a : ℝ) / (b : ℝ) * (Polynomial2.eval _ x t / atomEval A (addE p.e q.e) x t)
        rw [atomEval_addE, Polynomial2.eval_pmul]
        exact mul_alg _ _ _ _ _ _ _ _ _ _ hb1 hb2 hbR hE1 hE2 h1'
    | false =>
      refine ⟨Polynomial2.pmul P2 P1, ?_, ?_, ?_, hbR, ?_⟩
      · simp only [toZ_mulN, spec_pmul, hr1, hr2, Bool.false_eq_true, ite_false]
      · exact le_trans (mass_pmul_le P2 P1)
          (by rw [mul_comm]; exact mul_le_mul hm1 hm2 hn2 (le_trans hn1 hm1))
      · show atomEval A (addE p.e q.e) x t ≠ 0
        rw [atomEval_addE]; exact mul_ne_zero hE1 hE2
      · show _ = (a : ℝ) / (b : ℝ) * (Polynomial2.eval _ x t / atomEval A (addE p.e q.e) x t)
        rw [atomEval_addE, Polynomial2.eval_pmul, mul_comm (Polynomial2.eval P2 x t)]
        exact mul_alg _ _ _ _ _ _ _ _ _ _ hb1 hb2 hbR hE1 hE2 h1'
  next => cases h

def divF (B : Int) (aN : List NPoly) (aM : List Int) (p q : FVal) (a b c0 : Int)
    (f m u2 w : List Nat) : Option FVal :=
  if decide (0 < B) && decide (b ≠ 0) && decide (q.a ≠ 0) && decide (c0 ≠ 0) &&
      decide (p.a * q.b * b = a * (p.b * q.a * c0)) &&
      decide (q.e = addE m u2) && decide (addE p.e f = addE m w) &&
      eqN q.r (scaleSM (ofInt c0) (mulAtomsN [(false, 1)] aN f)) &&
      decide (q.nb + F4U.Light.absI c0 * atomMass aM f < B) then
    some ⟨a, b, mulAtomsN p.r aN u2, w, p.nb * atomMass aM u2⟩
  else none

theorem divF_sound {B : Int} {A : List Rows} {x t : ℝ} {p q : FVal}
    {a b c0 : Int} {f m u2 w : List Nat} {v : FVal} {y1 y2 : ℝ}
    (hp : Inv B A x t p y1) (hq : Inv B A x t q y2) (hy2 : y2 ≠ 0)
    (h : divF B ((A.map (spec B)).map ofZ) (A.map mass) p q a b c0 f m u2 w = some v) :
    Inv B A x t v (y1 / y2) := by
  unfold divF at h
  split at h
  next hc =>
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
    obtain ⟨⟨⟨⟨⟨⟨⟨⟨hB, hb⟩, ha2⟩, hc0⟩, h1⟩, he2⟩, hef⟩, hz⟩, hbound⟩ := hc
    obtain ⟨P1, hr1, hm1, hE1, hb1, rfl⟩ := hp
    obtain ⟨P2, hr2, hm2, hE2, hb2, rfl⟩ := hq
    cases h
    have hbR : (b : ℝ) ≠ 0 := by exact_mod_cast hb
    have ha2R : (q.a : ℝ) ≠ 0 := by exact_mod_cast ha2
    have hc0R : (c0 : ℝ) ≠ 0 := by exact_mod_cast hc0
    have h1' : (p.a : ℝ) * q.b * b = a * (p.b * q.a * c0) := by exact_mod_cast h1
    -- the divisor's numerator is `c0 * atoms ^ f`
    have hQ : Polynomial2.normalizedEq P2
        (Polynomial2.pscale c0 (mulAtomsRows (Polynomial2.const 1) A f)) = true := by
      apply normalizedEq_of_spec hB
      · have hA := atomMass_nonneg A f
        have hm : mass (Polynomial2.pscale c0 (mulAtomsRows (Polynomial2.const 1) A f)) ≤
            F4U.Light.absI c0 * atomMass (A.map mass) f := by
          rw [mass_pscale, KroneckerIdentity.absI_eq_abs]
          refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg c0)
          have h0 := mass_mulAtomsRows_le (Polynomial2.const 1) A f
          have h1 : mass (Polynomial2.const 1) = 1 := by decide
          rw [h1, one_mul] at h0
          exact h0
        linarith
      · have hz' := eqN_eqZ hz
        simp only [toZ_scaleSM, smZ_ofInt, toZ_mulAtomsN, toZ_one, hr2] at hz'
        rw [spec_pscale, spec_mulAtomsRows, spec_const_one]
        exact hz'
    have hQe := Polynomial2.normalizedEq_sound hQ x t
    rw [Polynomial2.eval_pscale, eval_mulAtomsRows, Polynomial2.eval_const] at hQe
    simp only [Int.cast_one, one_mul] at hQe
    rw [he2, atomEval_addE] at hE2
    have hM := (mul_ne_zero_iff.mp hE2).1
    have hU2 := (mul_ne_zero_iff.mp hE2).2
    -- the divisor value is nonzero, hence its numerator
    have hP2 : Polynomial2.eval P2 x t ≠ 0 := by
      intro hzero
      apply hy2
      rw [hzero]; simp
    have hF : atomEval A f x t ≠ 0 := by
      intro hzero
      apply hP2
      rw [hQe, hzero, mul_zero]
    have hEW : atomEval A p.e x t * atomEval A f x t = atomEval A m x t * atomEval A w x t := by
      rw [← atomEval_addE, ← atomEval_addE, hef]
    have hW : atomEval A w x t ≠ 0 := by
      intro hzero
      have := mul_ne_zero hE1 hF
      rw [hEW, hzero, mul_zero] at this
      exact this rfl
    refine ⟨mulAtomsRows P1 A u2, ?_, ?_, hW, hbR, ?_⟩
    · simp only [toZ_mulAtomsN, spec_mulAtomsRows, hr1]
    · exact le_trans (mass_mulAtomsRows_le P1 A u2)
        (mul_le_mul_of_nonneg_right hm1 (atomMass_nonneg A u2))
    · show _ = (a : ℝ) / (b : ℝ) * (Polynomial2.eval (mulAtomsRows P1 A u2) x t / atomEval A w x t)
      rw [eval_mulAtomsRows, he2, atomEval_addE, hQe]
      exact div_alg _ _ _ _ _ _ _ _ _ _ _ _ _ hb1 hb2 hbR ha2R hc0R hE1 hF hM hU2 hEW h1'
  next => cases h

def powF (p : FVal) (n : Nat) (a b : Int) : Option FVal :=
  if decide (b ≠ 0) && decide (p.a ^ n * b = a * p.b ^ n) then
    some ⟨a, b, powN p.r n, scaleE n p.e, p.nb ^ n⟩
  else none

theorem powF_sound {B : Int} {A : List Rows} {x t : ℝ} {p : FVal} {n : Nat}
    {a b : Int} {v : FVal} {y1 : ℝ}
    (hp : Inv B A x t p y1) (h : powF p n a b = some v) : Inv B A x t v (y1 ^ n) := by
  unfold powF at h
  split at h
  next hc =>
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
    obtain ⟨hb, h1⟩ := hc
    obtain ⟨P1, hr1, hm1, hE1, hb1, rfl⟩ := hp
    cases h
    have hbR : (b : ℝ) ≠ 0 := by exact_mod_cast hb
    have h1' : (p.a : ℝ) ^ n * b = a * (p.b : ℝ) ^ n := by exact_mod_cast h1
    refine ⟨Polynomial2.ppow P1 n, ?_, ?_, ?_, hbR, ?_⟩
    · simp only [toZ_powN, spec_ppow, hr1]
    · exact le_trans (mass_ppow_le P1 n) (pow_le_pow_left₀ (mass_nonneg P1) hm1 n)
    · show atomEval A (scaleE n p.e) x t ≠ 0
      rw [atomEval_scaleE]; exact pow_ne_zero n hE1
    · show _ = (a : ℝ) / (b : ℝ) * (Polynomial2.eval _ x t / atomEval A (scaleE n p.e) x t)
      rw [atomEval_scaleE, Polynomial2.eval_ppow]
      exact pow_alg _ _ _ _ _ _ n hb1 hbR h1'
  next => cases h

/-! ## programs -/

inductive Instr where
  | x
  | t
  | const (k : Nat)
  | add (i j : Nat) (k1 k2 a b : Int) (m u1 u2 : List Nat)
  | sub (i j : Nat) (k1 k2 a b : Int) (m u1 u2 : List Nat)
  | mul (i j : Nat) (sw : Bool) (a b : Int)
  | div (i j : Nat) (a b c0 : Int) (f m u2 w : List Nat)
  | pow (i : Nat) (n : Nat) (a b : Int)

noncomputable def stepR (CR : List ℝ) (x t : ℝ) (st : List ℝ) : Instr → ℝ
  | .x => x
  | .t => t
  | .const k => CR.getD k 0
  | .add i j _ _ _ _ _ _ _ => st.getD i 0 + st.getD j 0
  | .sub i j _ _ _ _ _ _ _ => st.getD i 0 - st.getD j 0
  | .mul i j _ _ _ => st.getD i 0 * st.getD j 0
  | .div i j _ _ _ _ _ _ _ => st.getD i 0 / st.getD j 0
  | .pow i n _ _ => st.getD i 0 ^ n

noncomputable def runR (CR : List ℝ) (x t : ℝ) : List Instr → List ℝ → List ℝ
  | [], st => st
  | ins :: is, st => runR CR x t is (stepR CR x t st ins :: st)

/-- The values of the program at the listed positions (counted back from the last instruction). One
`kernel_rfl` on a list of these links every root of a program to its expression in a single check. -/
noncomputable def rootVals (CR : List ℝ) (x t : ℝ) (prog : List Instr) : List Nat → List ℝ
  | [] => []
  | p :: ps => (runR CR x t prog []).getD p 0 :: rootVals CR x t prog ps

theorem hd_eq {α : Type} {a b : α} {as bs : List α} (h : a :: as = b :: bs) : a = b := (List.cons.inj h).1
theorem tl_eq {α : Type} {a b : α} {as bs : List α} (h : a :: as = b :: bs) : as = bs := (List.cons.inj h).2

def divisorOK (st : List ℝ) : Instr → Prop
  | .div _ j _ _ _ _ _ _ _ => st.getD j 0 ≠ 0
  | _ => True

def DivOK (CR : List ℝ) (x t : ℝ) : List Instr → List ℝ → Prop
  | [], _ => True
  | ins :: is, st => divisorOK st ins ∧ DivOK CR x t is (stepR CR x t st ins :: st)

/-- The divisor values, in program order. -/
noncomputable def divisorVals (CR : List ℝ) (x t : ℝ) : List Instr → List ℝ → List ℝ
  | [], _ => []
  | ins :: is, st =>
    match ins with
    | .div _ j _ _ _ _ _ _ _ => st.getD j 0 :: divisorVals CR x t is (stepR CR x t st ins :: st)
    | _ => divisorVals CR x t is (stepR CR x t st ins :: st)

theorem divOK_of_vals (CR : List ℝ) (x t : ℝ) (prog : List Instr) (st : List ℝ)
    (h : ∀ v ∈ divisorVals CR x t prog st, v ≠ 0) : DivOK CR x t prog st := by
  induction prog generalizing st with
  | nil => trivial
  | cons ins is ih =>
    cases ins <;> simp only [divisorVals, List.mem_cons, forall_eq_or_imp] at h <;>
      first
        | exact ⟨trivial, ih _ h⟩
        | exact ⟨h.1, ih _ h.2⟩

theorem allNe_nil : ∀ v ∈ ([] : List ℝ), v ≠ 0 := by simp
theorem allNe_cons {a : ℝ} {l : List ℝ} (h : a ≠ 0) (hl : ∀ v ∈ l, v ≠ 0) :
    ∀ v ∈ a :: l, v ≠ 0 := by
  intro v hv
  rcases List.mem_cons.mp hv with rfl | hv
  · exact h
  · exact hl v hv

def stepF (B : Int) (aN : List NPoly) (aM : List Int) (C : List (Int × Int)) (st : List FVal) :
    Instr → Option FVal
  | .x => some ⟨1, 1, ofZ (spec B Polynomial2.X), [], 1⟩
  | .t => some ⟨1, 1, ofZ (spec B Polynomial2.Y), [], 1⟩
  | .const k =>
    if decide ((C.getD k (0, 1)).2 ≠ 0) then
      some ⟨(C.getD k (0, 1)).1, (C.getD k (0, 1)).2, ofZ (spec B (Polynomial2.const 1)), [], 1⟩
    else none
  | .add i j k1 k2 a b m u1 u2 => addF aN aM false (st.getD i dflt) (st.getD j dflt) k1 k2 a b m u1 u2
  | .sub i j k1 k2 a b m u1 u2 => addF aN aM true (st.getD i dflt) (st.getD j dflt) k1 k2 a b m u1 u2
  | .mul i j sw a b => mulF sw (st.getD i dflt) (st.getD j dflt) a b
  | .div i j a b c0 f m u2 w => divF B aN aM (st.getD i dflt) (st.getD j dflt) a b c0 f m u2 w
  | .pow i n a b => powF (st.getD i dflt) n a b

def runF (B : Int) (aN : List NPoly) (aM : List Int) (C : List (Int × Int)) :
    List Instr → List FVal → Option (List FVal)
  | [], st => some st
  | ins :: is, st =>
    match stepF B aN aM C st ins with
    | none => none
    | some v => if forceN v.r then runF B aN aM C is (v :: st) else none

/-- The real constants agree with the integer table. -/
def ConstsOK (C : List (Int × Int)) (CR : List ℝ) : Prop :=
  ∀ k, CR.getD k 0 = ((C.getD k (0, 1)).1 : ℝ) / ((C.getD k (0, 1)).2 : ℝ)

theorem constsOK_of_map {C : List (Int × Int)} {CR : List ℝ}
    (h : CR = C.map (fun p => (p.1 : ℝ) / (p.2 : ℝ))) : ConstsOK C CR := by
  intro k
  subst h
  have h0 : (0 : ℝ) = (fun p : Int × Int => (p.1 : ℝ) / (p.2 : ℝ)) (0, 1) := by simp
  rw [h0, List.getD_map]

theorem stepF_sound {B : Int} {A : List Rows} {C : List (Int × Int)} {CR : List ℝ}
    (hC : ConstsOK C CR) {x t : ℝ} {stF : List FVal} {stR : List ℝ}
    (hst : List.Forall₂ (Inv B A x t) stF stR) {ins : Instr} (hdiv : divisorOK stR ins) {v : FVal}
    (h : stepF B ((A.map (spec B)).map ofZ) (A.map mass) C stF ins = some v) :
    Inv B A x t v (stepR CR x t stR ins) := by
  have hd := inv_dflt B A x t
  cases ins with
  | x =>
    simp only [stepF, Option.some.injEq] at h
    subst h
    refine ⟨Polynomial2.X, toZ_ofZ _, (by decide : mass Polynomial2.X ≤ (1 : Int)), ?_, by simp, ?_⟩
    · simp [atomEval_nil]
    · simp [stepR, atomEval_nil]
  | t =>
    simp only [stepF, Option.some.injEq] at h
    subst h
    refine ⟨Polynomial2.Y, toZ_ofZ _, (by decide : mass Polynomial2.Y ≤ (1 : Int)), ?_, by simp, ?_⟩
    · simp [atomEval_nil]
    · simp [stepR, atomEval_nil]
  | const k =>
    simp only [stepF] at h
    split at h
    next hc =>
      simp only [decide_eq_true_eq] at hc
      cases h
      refine ⟨Polynomial2.const 1, toZ_ofZ _, (by decide : mass (Polynomial2.const 1) ≤ (1 : Int)), ?_,
        by exact_mod_cast hc, ?_⟩
      · simp [atomEval_nil]
      · show CR.getD k 0 = ((C.getD k (0, 1)).1 : ℝ) / ((C.getD k (0, 1)).2 : ℝ) *
          (Polynomial2.eval (Polynomial2.const 1) x t / atomEval A [] x t)
        rw [atomEval_nil, Polynomial2.eval_const, hC k]
        simp
    next => cases h
  | add i j k1 k2 a b m u1 u2 =>
    have := addF_sound (forall₂_getD hst hd i) (forall₂_getD hst hd j) h
    simpa [stepR] using this
  | sub i j k1 k2 a b m u1 u2 =>
    have := addF_sound (forall₂_getD hst hd i) (forall₂_getD hst hd j) h
    simpa [stepR] using this
  | mul i j sw a b =>
    exact mulF_sound (forall₂_getD hst hd i) (forall₂_getD hst hd j) h
  | div i j a b c0 f m u2 w =>
    exact divF_sound (forall₂_getD hst hd i) (forall₂_getD hst hd j) hdiv h
  | pow i n a b =>
    exact powF_sound (forall₂_getD hst hd i) h

theorem runF_sound {B : Int} {A : List Rows} {C : List (Int × Int)} {CR : List ℝ}
    (hC : ConstsOK C CR) (x t : ℝ) (prog : List Instr) :
    ∀ (stF : List FVal) (stR : List ℝ) (stF' : List FVal),
      List.Forall₂ (Inv B A x t) stF stR → DivOK CR x t prog stR →
      runF B ((A.map (spec B)).map ofZ) (A.map mass) C prog stF = some stF' →
      List.Forall₂ (Inv B A x t) stF' (runR CR x t prog stR) := by
  induction prog with
  | nil =>
    intro stF stR stF' hst _ h
    simp only [runF, Option.some.injEq] at h
    subst h
    exact hst
  | cons ins is ih =>
    intro stF stR stF' hst hdiv h
    simp only [runF] at h
    split at h
    next => cases h
    next v hv =>
      split at h
      next =>
        exact ih _ _ _ (List.Forall₂.cons (stepF_sound hC hst hdiv.1 hv) hst) hdiv.2 h
      next => cases h

/-! ## comparison of a computed value with a stored reduced pair -/

def rootCheck (B : Int) (aN : List NPoly) (aM : List Int) (v : FVal) (p : RationalPair)
    (G : Rows) (lam mu : Int) : Bool :=
  decide (0 < B) && decide (lam ≠ 0) && decide (mu ≠ 0) && decide (mu * v.b = v.a * lam) &&
  eqN (scaleSM (ofInt mu) v.r) (mulN (ofZ (spec B G)) (ofZ (spec B p.numerator))) &&
  decide (F4U.Light.absI mu * v.nb + (massN G : Int) * (massN p.numerator : Int) < B) &&
  eqN (scaleSM (ofInt lam) (mulAtomsN [(false, 1)] aN v.e))
    (mulN (ofZ (spec B G)) (ofZ (spec B p.denominator))) &&
  decide (F4U.Light.absI lam * atomMass aM v.e + (massN G : Int) * (massN p.denominator : Int) < B)

theorem rootCheck_sound {B : Int} {A : List Rows} {x t : ℝ} {v : FVal} {y : ℝ}
    {p : RationalPair} {G : Rows} {lam mu : Int} (hv : Inv B A x t v y)
    (h : rootCheck B ((A.map (spec B)).map ofZ) (A.map mass) v p G lam mu = true) :
    p.NonzeroDenominator x t ∧ p.value x t = y := by
  simp only [rootCheck, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨hB, hlam⟩, hmu⟩, hab⟩, hzN⟩, hbN⟩, hzD⟩, hbD⟩ := h
  obtain ⟨P, hr, hm, hE, hb, rfl⟩ := hv
  have hzN' := eqN_eqZ hzN
  have hzD' := eqN_eqZ hzD
  simp only [toZ_scaleSM, smZ_ofInt, toZ_mulN, toZ_ofZ, hr] at hzN'
  simp only [toZ_scaleSM, smZ_ofInt, toZ_mulN, toZ_ofZ, toZ_mulAtomsN, toZ_one] at hzD'
  simp only [massN_eq] at hbN hbD
  have hN : Polynomial2.normalizedEq (Polynomial2.pscale mu P) (Polynomial2.pmul G p.numerator) = true := by
    apply normalizedEq_of_spec hB
    · have h1 : mass (Polynomial2.pscale mu P) ≤ F4U.Light.absI mu * v.nb := by
        rw [mass_pscale, KroneckerIdentity.absI_eq_abs]
        exact mul_le_mul_of_nonneg_left hm (abs_nonneg mu)
      have h2 := mass_pmul_le G p.numerator
      linarith
    · rw [spec_pscale, spec_pmul]; exact hzN'
  have hD : Polynomial2.normalizedEq
      (Polynomial2.pscale lam (mulAtomsRows (Polynomial2.const 1) A v.e))
      (Polynomial2.pmul G p.denominator) = true := by
    apply normalizedEq_of_spec hB
    · have h1 : mass (Polynomial2.pscale lam (mulAtomsRows (Polynomial2.const 1) A v.e)) ≤
          F4U.Light.absI lam * atomMass (A.map mass) v.e := by
        rw [mass_pscale, KroneckerIdentity.absI_eq_abs]
        refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg lam)
        have h0 := mass_mulAtomsRows_le (Polynomial2.const 1) A v.e
        have h1 : mass (Polynomial2.const 1) = 1 := by decide
        rw [h1, one_mul] at h0
        exact h0
      have h2 := mass_pmul_le G p.denominator
      linarith
    · rw [spec_pscale, spec_pmul, spec_mulAtomsRows, spec_const_one]; exact hzD'
  have hNe := Polynomial2.normalizedEq_sound hN x t
  have hDe := Polynomial2.normalizedEq_sound hD x t
  rw [Polynomial2.eval_pscale, Polynomial2.eval_pmul] at hNe
  rw [Polynomial2.eval_pscale, Polynomial2.eval_pmul, eval_mulAtomsRows, Polynomial2.eval_const] at hDe
  simp only [Int.cast_one, one_mul] at hDe
  have hlamR : (lam : ℝ) ≠ 0 := by exact_mod_cast hlam
  have hmuR : (mu : ℝ) ≠ 0 := by exact_mod_cast hmu
  have habR : (mu : ℝ) * v.b = v.a * lam := by exact_mod_cast hab
  exact root_alg _ _ _ _ _ _ _ _ _ hb hlamR hmuR hE habR hNe hDe

/-- One root: the program's last instruction is the root. -/
def checkRoot1 (B : Int) (A : List Rows) (C : List (Int × Int)) (prog : List Instr)
    (p : RationalPair) (G : Rows) (lam mu : Int) : Bool :=
  match runF B ((A.map (spec B)).map ofZ) (A.map mass) C prog [] with
  | some (v :: _) => rootCheck B ((A.map (spec B)).map ofZ) (A.map mass) v p G lam mu
  | _ => false

theorem checkRoot1_sound {B : Int} {A : List Rows} {C : List (Int × Int)} {prog : List Instr}
    {p : RationalPair} {G : Rows} {lam mu : Int}
    (h : checkRoot1 B A C prog p G lam mu = true) {CR : List ℝ} (hC : ConstsOK C CR) (x t : ℝ)
    (hdiv : DivOK CR x t prog []) :
    p.NonzeroDenominator x t ∧ p.value x t = (runR CR x t prog []).headD 0 := by
  unfold checkRoot1 at h
  split at h
  next v rest hrun =>
    have hs := runF_sound hC x t prog [] [] _ List.Forall₂.nil hdiv hrun
    cases hR : runR CR x t prog [] with
    | nil => rw [hR] at hs; cases hs
    | cons y ys =>
      rw [hR] at hs
      cases hs with
      | cons hvy _ => exact rootCheck_sound hvy h
  next => cases h

/-- A whole family: one evaluation, many roots.  `pos` counts back from the last instruction. -/
structure RootSpec where
  pos : Nat
  pair : RationalPair
  G : Rows
  lam : Int
  mu : Int

def checkRoots (B : Int) (aN : List NPoly) (aM : List Int) (st : List FVal) : List RootSpec → Bool
  | [] => true
  | r :: rs => rootCheck B aN aM (st.getD r.pos dflt) r.pair r.G r.lam r.mu && checkRoots B aN aM st rs

def checkFamily (B : Int) (A : List Rows) (C : List (Int × Int)) (prog : List Instr)
    (roots : List RootSpec) : Bool :=
  match runF B ((A.map (spec B)).map ofZ) (A.map mass) C prog [] with
  | some st => checkRoots B ((A.map (spec B)).map ofZ) (A.map mass) st roots
  | none => false

theorem checkRoots_sound {B : Int} {A : List Rows} {x t : ℝ} {st : List FVal} {stR : List ℝ}
    (hst : List.Forall₂ (Inv B A x t) st stR) (roots : List RootSpec)
    (h : checkRoots B ((A.map (spec B)).map ofZ) (A.map mass) st roots = true) :
    ∀ r ∈ roots, r.pair.NonzeroDenominator x t ∧ r.pair.value x t = stR.getD r.pos 0 := by
  induction roots with
  | nil => intro r hr; cases hr
  | cons r0 rs ih =>
    simp only [checkRoots, Bool.and_eq_true] at h
    intro r hr
    rcases List.mem_cons.mp hr with rfl | hr
    · exact rootCheck_sound (forall₂_getD hst (inv_dflt B A x t) _) h.1
    · exact ih h.2 r hr

theorem checkFamily_sound {B : Int} {A : List Rows} {C : List (Int × Int)} {prog : List Instr}
    {roots : List RootSpec} (h : checkFamily B A C prog roots = true)
    {CR : List ℝ} (hC : ConstsOK C CR) (x t : ℝ) (hdiv : DivOK CR x t prog []) :
    ∀ r ∈ roots, r.pair.NonzeroDenominator x t ∧
      r.pair.value x t = (runR CR x t prog []).getD r.pos 0 := by
  unfold checkFamily at h
  split at h
  next st hrun =>
    exact checkRoots_sound (runF_sound hC x t prog [] [] _ List.Forall₂.nil hdiv hrun) roots h
  next => cases h

end F4U.Light.Reflect
