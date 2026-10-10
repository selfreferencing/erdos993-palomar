module

public import Erdos993Lean.F4U.Light.Construction.CoefficientBoxAssembly
public import Erdos993Lean.F4U.Light.Construction.KroneckerDigits
public import Erdos993Lean.F4U.Light.Linking.Polynomial2

/-! Bounds for the complete existing integer row objects, including padding.
The aliases below preserve the original coefficient mass and maximum row
length. They introduce no replacement polynomial or omitted-coefficient rule.
Multiplication uses a safe sum of widths even when a factor is an empty row.
-/

@[expose] public section

namespace F4Unified.LightConstruction.Polynomial2MassWidth

open F4U.Light.Linking.Polynomial2
open KroneckerIdentity

abbrev norm := coefficientMass
abbrev width := CoefficientBoxAssembly.width

theorem norm_nonneg (p : Rows) : 0 ≤ norm p := by
  induction p with
  | nil => rfl
  | cons a p ih =>
    exact add_nonneg (massList_nonneg a) ih

theorem norm_padd_le (p q : Rows) : norm (padd p q) ≤ norm p + norm q := by
  induction p generalizing q with
  | nil => simp [padd, norm, coefficientMass]
  | cons a p ih =>
    cases q with
    | nil => simp [padd, norm, coefficientMass]
    | cons b q =>
      have hr := massList_padd_le a b
      have ht := ih q
      simp only [padd, norm, coefficientMass]
      change F4U.Light.sumAbs (F4U.Light.padd a b) + norm (padd p q) ≤
        F4U.Light.sumAbs a + norm p + (F4U.Light.sumAbs b + norm q)
      omega

theorem norm_pscale (c : Int) (p : Rows) : norm (pscale c p) = |c| * norm p := by
  induction p with
  | nil => simp [pscale, norm, coefficientMass]
  | cons a p ih =>
    change F4U.Light.sumAbs (F4U.Light.pscale c a) + norm (pscale c p) =
      |c| * (F4U.Light.sumAbs a + norm p)
    rw [massList_pscale, ih]
    ring

theorem norm_psub_le (p q : Rows) : norm (psub p q) ≤ norm p + norm q := by
  unfold psub pneg
  calc
    norm (padd p (pscale (-1) q)) ≤ norm p + norm (pscale (-1) q) := norm_padd_le _ _
    _ = norm p + norm q := by simp [norm_pscale]

theorem norm_mulRow_le (p q : List Int) :
    F4U.Light.sumAbs (mulRow p q) ≤ F4U.Light.sumAbs p * F4U.Light.sumAbs q := by
  induction p with
  | nil => simp [mulRow, F4U.Light.sumAbs]
  | cons a p ih =>
    calc
      F4U.Light.sumAbs (mulRow (a :: p) q) ≤
          F4U.Light.sumAbs (F4U.Light.pscale a q) +
            F4U.Light.sumAbs (0 :: mulRow p q) := massList_padd_le _ _
      _ = |a| * F4U.Light.sumAbs q + F4U.Light.sumAbs (mulRow p q) := by
        rw [massList_pscale]
        simp only [F4U.Light.sumAbs, absI_eq_abs, abs_zero, zero_add]
      _ ≤ |a| * F4U.Light.sumAbs q + F4U.Light.sumAbs p * F4U.Light.sumAbs q :=
        add_le_add (le_refl _) ih
      _ = F4U.Light.sumAbs (a :: p) * F4U.Light.sumAbs q := by
        simp only [F4U.Light.sumAbs, absI_eq_abs]
        ring

theorem norm_mulByRow_le (a : List Int) (q : Rows) :
    norm (mulByRow a q) ≤ F4U.Light.sumAbs a * norm q := by
  induction q with
  | nil => simp [mulByRow, norm, coefficientMass]
  | cons b q ih =>
    change F4U.Light.sumAbs (mulRow a b) + norm (mulByRow a q) ≤
      F4U.Light.sumAbs a * (F4U.Light.sumAbs b + norm q)
    calc
      F4U.Light.sumAbs (mulRow a b) + norm (mulByRow a q) ≤
          F4U.Light.sumAbs a * F4U.Light.sumAbs b + F4U.Light.sumAbs a * norm q :=
        add_le_add (norm_mulRow_le a b) ih
      _ = F4U.Light.sumAbs a * (F4U.Light.sumAbs b + norm q) := by ring

theorem norm_pmul_le (p q : Rows) : norm (pmul p q) ≤ norm p * norm q := by
  induction p with
  | nil => simp [pmul, norm, coefficientMass]
  | cons a p ih =>
    calc
      norm (pmul (a :: p) q) ≤ norm (mulByRow a q) + norm ([] :: pmul p q) :=
        norm_padd_le _ _
      _ = norm (mulByRow a q) + norm (pmul p q) := by
        simp only [norm, coefficientMass, F4U.Light.sumAbs, zero_add]
      _ ≤ F4U.Light.sumAbs a * norm q + norm p * norm q :=
        add_le_add (norm_mulByRow_le a q) ih
      _ = norm (a :: p) * norm q := by
        simp only [norm, coefficientMass]
        ring

theorem norm_ppow_le (p : Rows) (n : Nat) : norm (ppow p n) ≤ norm p ^ n := by
  induction n with
  | zero =>
    norm_num [ppow, const, norm, coefficientMass, F4U.Light.sumAbs, absI_eq_abs]
  | succ n ih =>
    calc
      norm (ppow p (n + 1)) ≤ norm (ppow p n) * norm p := norm_pmul_le _ _
      _ ≤ norm p ^ n * norm p := mul_le_mul_of_nonneg_right ih (norm_nonneg p)
      _ = norm p ^ (n + 1) := (pow_succ _ _).symm

theorem row_length_padd (p q : List Int) :
    (F4U.Light.padd p q).length = max p.length q.length := by
  induction p generalizing q with
  | nil => simp [F4U.Light.padd]
  | cons a p ih =>
    cases q with
    | nil => simp [F4U.Light.padd]
    | cons b q =>
      simp only [F4U.Light.padd, List.length_cons, ih]
      omega

theorem row_length_pscale (c : Int) (p : List Int) :
    (F4U.Light.pscale c p).length = p.length := by
  induction p with
  | nil => rfl
  | cons a p ih => simp only [F4U.Light.pscale, List.length_cons, ih]

theorem width_padd_le (p q : Rows) : width (padd p q) ≤ max (width p) (width q) := by
  induction p generalizing q with
  | nil => simp [padd, width, CoefficientBoxAssembly.width]
  | cons a p ih =>
    cases q with
    | nil => simp [padd, width, CoefficientBoxAssembly.width]
    | cons b q =>
      change max (F4U.Light.padd a b).length (width (padd p q)) ≤
        max (width (a :: p)) (width (b :: q))
      rw [row_length_padd]
      have ha : a.length ≤ width (a :: p) := Nat.le_max_left _ _
      have hb : b.length ≤ width (b :: q) := Nat.le_max_left _ _
      have hp : width p ≤ width (a :: p) := Nat.le_max_right _ _
      have hq : width q ≤ width (b :: q) := Nat.le_max_right _ _
      apply max_le
      · exact max_le (le_trans ha (Nat.le_max_left _ _))
          (le_trans hb (Nat.le_max_right _ _))
      · exact le_trans (ih q)
          (max_le (le_trans hp (Nat.le_max_left _ _))
            (le_trans hq (Nat.le_max_right _ _)))

theorem width_pscale (c : Int) (p : Rows) : width (pscale c p) = width p := by
  induction p with
  | nil => rfl
  | cons a p ih =>
    change max (F4U.Light.pscale c a).length (width (pscale c p)) = max a.length (width p)
    rw [row_length_pscale, ih]

theorem width_psub_le (p q : Rows) : width (psub p q) ≤ max (width p) (width q) := by
  unfold psub pneg
  calc
    width (padd p (pscale (-1) q)) ≤ max (width p) (width (pscale (-1) q)) := width_padd_le _ _
    _ = max (width p) (width q) := by rw [width_pscale]

theorem row_length_mulRow_le (p q : List Int) : (mulRow p q).length ≤ p.length + q.length := by
  induction p with
  | nil => simp [mulRow]
  | cons a p ih =>
    rw [mulRow, row_length_padd, row_length_pscale]
    simp only [List.length_cons]
    apply max_le <;> omega

theorem width_mulByRow_le (a : List Int) (q : Rows) :
    width (mulByRow a q) ≤ a.length + width q := by
  induction q with
  | nil => simp [mulByRow, width, CoefficientBoxAssembly.width]
  | cons b q ih =>
    change max (mulRow a b).length (width (mulByRow a q)) ≤ a.length + max b.length (width q)
    apply max_le
    · exact le_trans (row_length_mulRow_le a b)
        (Nat.add_le_add (le_refl _) (Nat.le_max_left _ _))
    · exact le_trans ih (Nat.add_le_add (le_refl _) (Nat.le_max_right _ _))

theorem width_pmul_le (p q : Rows) : width (pmul p q) ≤ width p + width q := by
  induction p with
  | nil => simp [pmul, width, CoefficientBoxAssembly.width]
  | cons a p ih =>
    calc
      width (pmul (a :: p) q) ≤ max (width (mulByRow a q)) (width ([] :: pmul p q)) :=
        width_padd_le _ _
      _ = max (width (mulByRow a q)) (width (pmul p q)) := by
        simp only [width, CoefficientBoxAssembly.width, List.length_nil, Nat.zero_max]
      _ ≤ max (a.length + width q) (width p + width q) :=
        max_le_max (width_mulByRow_le a q) ih
      _ = max a.length (width p) + width q := by omega
      _ = width (a :: p) + width q := rfl

theorem width_ppow_le (p : Rows) (n : Nat) : width (ppow p n) ≤ n * width p + 1 := by
  induction n with
  | zero => simp [ppow, const, width, CoefficientBoxAssembly.width]
  | succ n ih =>
    calc
      width (ppow p (n + 1)) ≤ width (ppow p n) + width p := width_pmul_le _ _
      _ ≤ (n * width p + 1) + width p := Nat.add_le_add ih (le_refl _)
      _ = (n + 1) * width p + 1 := by ring

#print axioms norm
#print axioms width
#print axioms norm_nonneg
#print axioms norm_padd_le
#print axioms norm_pscale
#print axioms norm_psub_le
#print axioms norm_mulRow_le
#print axioms norm_mulByRow_le
#print axioms norm_pmul_le
#print axioms norm_ppow_le
#print axioms row_length_padd
#print axioms row_length_pscale
#print axioms width_padd_le
#print axioms width_pscale
#print axioms width_psub_le
#print axioms row_length_mulRow_le
#print axioms width_mulByRow_le
#print axioms width_pmul_le
#print axioms width_ppow_le

end F4Unified.LightConstruction.Polynomial2MassWidth
