module

public import Erdos993Lean.BCFG.ClearingLightForms

/-! Small cancellations applied to expanded monomials, before the final comparison. -/
@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Erdos993Lean.BCFG.Analytic

theorem clearing_pow_inv_sq {a c : ℝ} {n : ℕ} (ha : a ≠ 0) (hn : 2 ≤ n) :
    a^n*(a⁻¹^2*c) = a^(n-2)*c := by
  calc
    a^n*(a⁻¹^2*c) = a^(n-2)*a^2*((a^2)⁻¹*c) := by
      rw [← pow_add, Nat.sub_add_cancel hn, inv_pow]
    _ = a^(n-2)*c := by field_simp [ha] <;> ring

theorem clearing_pow_mul_inv_sq {a b c : ℝ} {n : ℕ} (ha : a ≠ 0) (hn : 2 ≤ n) :
    a^n*(b*(a⁻¹^2*c)) = a^(n-2)*(b*c) := by
  calc
    a^n*(b*(a⁻¹^2*c)) = b*(a^n*(a⁻¹^2*c)) := by ring
    _ = a^(n-2)*(b*c) := by rw [clearing_pow_inv_sq ha hn]; ring

end Erdos993Lean.BCFG.Analytic
