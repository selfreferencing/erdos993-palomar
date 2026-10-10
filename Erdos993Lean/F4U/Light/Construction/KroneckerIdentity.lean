module
public import Erdos993Lean.F4U.Light.Construction.KroneckerRows
@[expose] public section

namespace F4Unified.LightConstruction.KroneckerIdentity
open F4U.Light.Linking.Polynomial2

/-- Full literal leaves and every algebraic operation survive in this syntax. -/
inductive Expr where
  | leaf (rows : Rows)
  | add (a b : Expr)
  | sub (a b : Expr)
  | mul (a b : Expr)
  | pow (a : Expr) (n : Nat)
  | scale (c : Int) (a : Expr)
  deriving DecidableEq, Repr

def Expr.toRows : Expr → Rows
  | .leaf p => p
  | .add a b => padd a.toRows b.toRows
  | .sub a b => psub a.toRows b.toRows
  | .mul a b => pmul a.toRows b.toRows
  | .pow a n => ppow a.toRows n
  | .scale c a => pscale c a.toRows

def Expr.norm : Expr → Int
  | .leaf p => coefficientMass p
  | .add a b => a.norm + b.norm
  | .sub a b => a.norm + b.norm
  | .mul a b => a.norm * b.norm
  | .pow a n => a.norm ^ n
  | .scale c a => |c| * a.norm

def Expr.width : Expr → Nat
  | .leaf p => CoefficientBoxAssembly.width p
  | .add a b => max a.width b.width
  | .sub a b => max a.width b.width
  | .mul a b => a.width + b.width
  | .pow a n => n * a.width + 1
  | .scale _ a => a.width

/-- Integer evaluation of the syntax; it never expands `toRows` products. -/
def Expr.evalInt : Expr → Int → Int → Int
  | .leaf p, x, y => evalIntRows p x y
  | .add a b, x, y => a.evalInt x y + b.evalInt x y
  | .sub a b, x, y => a.evalInt x y - b.evalInt x y
  | .mul a b, x, y => a.evalInt x y * b.evalInt x y
  | .pow a n, x, y => a.evalInt x y ^ n
  | .scale c a, x, y => c * a.evalInt x y

theorem Expr.norm_nonneg (a : Expr) : 0 ≤ a.norm := by
  induction a with
  | leaf p => exact Polynomial2MassWidth.norm_nonneg p
  | add a b ha hb => exact add_nonneg ha hb
  | sub a b ha hb => exact add_nonneg ha hb
  | mul a b ha hb => exact mul_nonneg ha hb
  | pow a n ha => exact pow_nonneg ha n
  | scale c a ha => exact mul_nonneg (abs_nonneg _) ha

theorem Expr.norm_toRows_le (a : Expr) : coefficientMass a.toRows ≤ a.norm := by
  induction a with
  | leaf p => exact le_refl _
  | add a b ha hb =>
    exact le_trans (Polynomial2MassWidth.norm_padd_le _ _) (add_le_add ha hb)
  | sub a b ha hb =>
    exact le_trans (Polynomial2MassWidth.norm_psub_le _ _) (add_le_add ha hb)
  | mul a b ha hb =>
    exact le_trans (Polynomial2MassWidth.norm_pmul_le _ _)
      (mul_le_mul ha hb (Polynomial2MassWidth.norm_nonneg _) (Expr.norm_nonneg _))
  | pow a n ha =>
    exact le_trans (Polynomial2MassWidth.norm_ppow_le _ _)
      (pow_le_pow_left₀ (Polynomial2MassWidth.norm_nonneg _) ha n)
  | scale c a ha =>
    change Polynomial2MassWidth.norm (pscale c a.toRows) ≤ |c| * a.norm
    rw [Polynomial2MassWidth.norm_pscale]
    exact mul_le_mul_of_nonneg_left ha (abs_nonneg _)

theorem Expr.width_toRows_le (a : Expr) : CoefficientBoxAssembly.width a.toRows ≤ a.width := by
  induction a with
  | leaf p => exact le_refl _
  | add a b ha hb =>
    exact le_trans (Polynomial2MassWidth.width_padd_le _ _) (max_le_max ha hb)
  | sub a b ha hb =>
    exact le_trans (Polynomial2MassWidth.width_psub_le _ _) (max_le_max ha hb)
  | mul a b ha hb =>
    exact le_trans (Polynomial2MassWidth.width_pmul_le _ _) (add_le_add ha hb)
  | pow a n ha =>
    exact le_trans (Polynomial2MassWidth.width_ppow_le _ _)
      (Nat.add_le_add_right (Nat.mul_le_mul_left n ha) 1)
  | scale c a ha =>
    simpa only [Expr.toRows, Expr.width, Polynomial2MassWidth.width_pscale] using ha

theorem Expr.evalInt_toRows (a : Expr) (x y : Int) :
    evalIntRows a.toRows x y = a.evalInt x y := by
  induction a with
  | leaf p => rfl
  | add a b ha hb => simp only [Expr.toRows, Expr.evalInt, evalIntRows_padd, ha, hb]
  | sub a b ha hb => simp only [Expr.toRows, Expr.evalInt, evalIntRows_psub, ha, hb]
  | mul a b ha hb => simp only [Expr.toRows, Expr.evalInt, evalIntRows_pmul, ha, hb]
  | pow a n ha => simp only [Expr.toRows, Expr.evalInt, evalIntRows_ppow, ha]
  | scale c a ha => simp only [Expr.toRows, Expr.evalInt, evalIntRows_pscale, ha]

/-- Bounds concern the complete expression before any convolution is expanded. -/
def checkIdentity (lhs rhs : Expr) (B : Int) (stride : Nat) : Bool :=
  decide (0 < B) && decide (0 < stride) &&
  decide (max lhs.width rhs.width ≤ stride) &&
  decide (2 * (lhs.norm + rhs.norm) < B) &&
  decide (lhs.evalInt B (B ^ stride) = rhs.evalInt B (B ^ stride))

/-- The checked encoding has a proved coefficient decoding, restoring the old API. -/
theorem checkIdentity_sound {lhs rhs : Expr} {B : Int} {stride : Nat}
    (h : checkIdentity lhs rhs B stride = true) :
    normalizedEq lhs.toRows rhs.toRows = true := by
  simp only [checkIdentity, Bool.and_eq_true, decide_eq_true_eq] at h
  rcases h with ⟨⟨⟨⟨hB, hs⟩, hw⟩, hn⟩, he⟩
  have hn0 := add_nonneg (Expr.norm_nonneg lhs) (Expr.norm_nonneg rhs)
  have hn' : lhs.norm + rhs.norm < B := by omega
  apply normalizedEq_of_integer_code lhs.toRows rhs.toRows hB stride hs
  · exact le_trans (max_le_max (Expr.width_toRows_le lhs) (Expr.width_toRows_le rhs)) hw
  · exact lt_of_le_of_lt (add_le_add (Expr.norm_toRows_le lhs) (Expr.norm_toRows_le rhs)) hn'
  · simpa only [Expr.evalInt_toRows] using he

#print axioms Expr
#print axioms Expr.toRows
#print axioms Expr.norm
#print axioms Expr.width
#print axioms Expr.evalInt
#print axioms Expr.norm_nonneg
#print axioms Expr.norm_toRows_le
#print axioms Expr.width_toRows_le
#print axioms Expr.evalInt_toRows
#print axioms checkIdentity
#print axioms checkIdentity_sound
end F4Unified.LightConstruction.KroneckerIdentity
