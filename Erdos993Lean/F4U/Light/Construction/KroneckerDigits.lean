module
public import Erdos993Lean.F4U.Light.Construction.CoefficientAssembly
public import Mathlib.Data.Int.Basic
@[expose] public section

namespace F4Unified.LightConstruction.KroneckerIdentity

def horner : List Int → Int → Int
  | [], _ => 0
  | a :: p, B => a + B * horner p B

theorem absI_eq_abs (a : Int) : F4U.Light.absI a = |a| := by
  unfold F4U.Light.absI
  split_ifs with h
  · exact (abs_of_neg h).symm
  · exact (abs_of_nonneg (le_of_not_gt h)).symm

theorem massList_nonneg (p : List Int) : 0 ≤ F4U.Light.sumAbs p := by
  induction p with
  | nil => simp [F4U.Light.sumAbs]
  | cons a p ih =>
    simp only [F4U.Light.sumAbs, absI_eq_abs]
    exact add_nonneg (abs_nonneg _) ih

theorem small_dvd_zero {a B : Int} (hd : B ∣ a) (ha : |a| < B) : a = 0 := by
  have hnat : a.natAbs < B.natAbs := by
    rw [← Nat.cast_lt (α := Int)]
    simpa only [Int.natCast_natAbs] using (ha.trans_le (le_abs_self B))
  exact Int.eq_zero_of_dvd_of_natAbs_lt_natAbs hd hnat

theorem horner_zero_coefficients (p : List Int) {B : Int} (hB : 0 < B)
    (hmass : F4U.Light.sumAbs p < B) (hzero : horner p B = 0) :
    ∀ i, p.getD i 0 = 0 := by
  induction p with
  | nil => simp
  | cons a p ih =>
    have hp0 := massList_nonneg p
    have habs : |a| < B := by
      simp only [F4U.Light.sumAbs, absI_eq_abs] at hmass
      omega
    have hdvd : B ∣ a := by
      refine ⟨-horner p B, ?_⟩
      simp only [horner] at hzero
      nlinarith
    have ha : a = 0 := small_dvd_zero hdvd habs
    have hpzero : horner p B = 0 := by
      simp only [horner, ha, zero_add] at hzero
      exact (mul_eq_zero.mp hzero).resolve_left (ne_of_gt hB)
    have hpmass : F4U.Light.sumAbs p < B := by
      simpa only [F4U.Light.sumAbs, ha, absI_eq_abs, abs_zero, zero_add] using hmass
    intro i
    cases i with
    | zero => simpa using ha
    | succ i => simpa only [List.getD_cons_succ] using ih hpmass hpzero i

theorem horner_eq_coefficients (p q : List Int) {B : Int} (hB : 0 < B)
    (hmass : F4U.Light.sumAbs p + F4U.Light.sumAbs q < B)
    (heq : horner p B = horner q B) :
    ∀ i, p.getD i 0 = q.getD i 0 := by
  induction p generalizing q with
  | nil =>
    have hqmass : F4U.Light.sumAbs q < B := by simpa only [F4U.Light.sumAbs, zero_add] using hmass
    have hqzero : horner q B = 0 := by simpa only [horner] using heq.symm
    intro i
    simpa only [List.getD_nil] using (horner_zero_coefficients q hB hqmass hqzero i).symm
  | cons a p ih =>
    cases q with
    | nil =>
      have hpmass : F4U.Light.sumAbs (a :: p) < B := by simpa only [F4U.Light.sumAbs, add_zero] using hmass
      have hpzero : horner (a :: p) B = 0 := by simpa only [horner] using heq
      intro i
      simpa only [List.getD_nil] using horner_zero_coefficients (a :: p) hB hpmass hpzero i
    | cons b q =>
      have hp0 := massList_nonneg p
      have hq0 := massList_nonneg q
      have habs : |a - b| < B := by
        calc
          |a - b| ≤ |a| + |b| := abs_sub _ _
          _ ≤ F4U.Light.sumAbs (a :: p) + F4U.Light.sumAbs (b :: q) := by
            simp only [F4U.Light.sumAbs, absI_eq_abs]
            omega
          _ < B := hmass
      have hdvd : B ∣ a - b := by
        refine ⟨horner q B - horner p B, ?_⟩
        simp only [horner] at heq
        nlinarith
      have hab : a = b := by have hz := small_dvd_zero hdvd habs; omega
      have htail : horner p B = horner q B := by
        simp only [horner, hab] at heq
        apply mul_left_cancel₀ (ne_of_gt hB)
        linarith
      have htailmass : F4U.Light.sumAbs p + F4U.Light.sumAbs q < B := by
        simp only [F4U.Light.sumAbs, absI_eq_abs] at hmass
        have ha0 := abs_nonneg a
        have hb0 := abs_nonneg b
        omega
      intro i
      cases i with
      | zero => simpa using hab
      | succ i => simpa only [List.getD_cons_succ] using ih q htailmass htail i

theorem abs_horner_le (p : List Int) {B : Int} (hB : 1 ≤ B) (n : Nat)
    (hlen : p.length ≤ n + 1) :
    |horner p B| ≤ F4U.Light.sumAbs p * B ^ n := by
  induction n generalizing p with
  | zero =>
    cases p with
    | nil => simp [horner, F4U.Light.sumAbs]
    | cons a p =>
      have hp : p = [] := by
        cases p with
        | nil => rfl
        | cons b p => simp only [List.length_cons] at hlen; omega
      subst p
      simp [horner, F4U.Light.sumAbs, absI_eq_abs]
  | succ n ih =>
    cases p with
    | nil => simp [horner, F4U.Light.sumAbs]
    | cons a p =>
      have hp : p.length ≤ n + 1 := by simp only [List.length_cons] at hlen; omega
      have hb0 : 0 ≤ B := le_trans (by norm_num) hB
      have hpow : 1 ≤ B ^ (n + 1) := one_le_pow₀ hB
      calc
        |horner (a :: p) B| = |a + B * horner p B| := rfl
        _ ≤ |a| + |B| * |horner p B| := by simpa only [abs_mul] using abs_add_le a (B * horner p B)
        _ = |a| + B * |horner p B| := by rw [abs_of_nonneg hb0]
        _ ≤ |a| + B * (F4U.Light.sumAbs p * B ^ n) :=
          add_le_add (le_refl _) (mul_le_mul_of_nonneg_left (ih p hp) hb0)
        _ ≤ |a| * B ^ (n + 1) + B * (F4U.Light.sumAbs p * B ^ n) :=
          add_le_add (le_mul_of_one_le_right (abs_nonneg a) hpow) (le_refl _)
        _ = F4U.Light.sumAbs (a :: p) * B ^ (n + 1) := by
          simp only [F4U.Light.sumAbs, absI_eq_abs, pow_succ]
          ring

theorem abs_horner_lt (p : List Int) {B : Int} (hB : 0 < B) (stride : Nat)
    (hstride : 0 < stride) (hlen : p.length ≤ stride)
    (hmass : F4U.Light.sumAbs p < B) : |horner p B| < B ^ stride := by
  have hb1 : 1 ≤ B := by omega
  have hs : stride - 1 + 1 = stride := by omega
  have hlen' : p.length ≤ (stride - 1) + 1 := by omega
  have hn := abs_horner_le p hb1 (stride - 1) hlen'
  calc
    |horner p B| ≤ F4U.Light.sumAbs p * B ^ (stride - 1) := hn
    _ < B * B ^ (stride - 1) := mul_lt_mul_of_pos_right hmass (pow_pos hB _)
    _ = B ^ stride := by rw [mul_comm, ← pow_succ, hs]

theorem horner_padd (p q : List Int) (B : Int) :
    horner (F4U.Light.padd p q) B = horner p B + horner q B := by
  induction p generalizing q with
  | nil => simp [F4U.Light.padd, horner]
  | cons a p ih =>
    cases q with
    | nil => simp [F4U.Light.padd, horner]
    | cons b q => simp only [F4U.Light.padd, horner, ih]; ring

theorem horner_pscale (c : Int) (p : List Int) (B : Int) :
    horner (F4U.Light.pscale c p) B = c * horner p B := by
  induction p with
  | nil => simp [F4U.Light.pscale, horner]
  | cons a p ih => simp only [F4U.Light.pscale, horner, ih]; ring

theorem massList_padd_le (p q : List Int) :
    F4U.Light.sumAbs (F4U.Light.padd p q) ≤ F4U.Light.sumAbs p + F4U.Light.sumAbs q := by
  induction p generalizing q with
  | nil => simp [F4U.Light.padd, F4U.Light.sumAbs]
  | cons a p ih =>
    cases q with
    | nil => simp [F4U.Light.padd, F4U.Light.sumAbs]
    | cons b q =>
      simp only [F4U.Light.padd, F4U.Light.sumAbs, absI_eq_abs]
      have h := add_le_add (abs_add_le a b) (ih q)
      linarith

theorem massList_pscale (c : Int) (p : List Int) :
    F4U.Light.sumAbs (F4U.Light.pscale c p) = |c| * F4U.Light.sumAbs p := by
  induction p with
  | nil => simp [F4U.Light.pscale, F4U.Light.sumAbs]
  | cons a p ih =>
    simp only [F4U.Light.pscale, F4U.Light.sumAbs, absI_eq_abs, abs_mul, ih]
    ring

theorem horner_mulRow (p q : List Int) (B : Int) :
    horner (F4U.Light.Linking.Polynomial2.mulRow p q) B = horner p B * horner q B := by
  induction p with
  | nil => simp [F4U.Light.Linking.Polynomial2.mulRow, horner]
  | cons a p ih =>
    simp only [F4U.Light.Linking.Polynomial2.mulRow, horner_padd, horner_pscale,
      horner, ih, zero_add]
    ring

#print axioms horner
#print axioms absI_eq_abs
#print axioms massList_nonneg
#print axioms small_dvd_zero
#print axioms horner_zero_coefficients
#print axioms horner_eq_coefficients
#print axioms abs_horner_le
#print axioms abs_horner_lt
#print axioms horner_padd
#print axioms horner_pscale
#print axioms massList_padd_le
#print axioms massList_pscale
#print axioms horner_mulRow
end F4Unified.LightConstruction.KroneckerIdentity
