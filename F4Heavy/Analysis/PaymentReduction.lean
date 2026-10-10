module

public import F4Heavy.Contract
public import F4Heavy.Analysis.Quadratic

@[expose] public section
set_option autoImplicit false

namespace F4Heavy.Analysis
open F4Unified

noncomputable def paymentA (r : Row) (lam Y rho u : ℝ) : ℝ :=
  gamma r lam - delta r lam - p lam Y * Y * parentP r lam Y rho +
    delta r lam / childJ lam u

noncomputable def paymentB (r : Row) (lam Y rho u : ℝ) : ℝ :=
  p lam Y * (2 * parentP r lam Y rho - alpha r lam - beta r lam) -
    2 * delta r lam * childH u / childJ lam u

noncomputable def paymentC (r : Row) (lam Y rho u : ℝ) : ℝ :=
  p lam Y * parentN r lam Y rho / Y + p lam Y * beta r lam * rho * childH u +
    delta r lam * (childH u) ^ 2 / childJ lam u

theorem payment_quadratic (r : Row) (lam Y rho u y : ℝ) (hJ : 0 < childJ lam u) :
    payment r lam Y rho u y =
      paymentA r lam Y rho u * y ^ 2 + paymentB r lam Y rho u * y +
        paymentC r lam Y rho u := by
  unfold payment reserve paymentA paymentB paymentC
  rw [if_pos hJ]
  simp only [div_eq_mul_inv]
  ring

theorem payment_minAt (r : Row) (lam Y rho u : ℝ)
    (hJ : 0 < childJ lam u) (hA : 0 < paymentA r lam Y rho u) :
    MinAt r lam Y rho u
      ((4 * paymentA r lam Y rho u * paymentC r lam Y rho u -
        (paymentB r lam Y rho u) ^ 2) / (4 * paymentA r lam Y rho u)) := by
  constructor
  · intro y _
    rw [payment_quadratic r lam Y rho u y hJ]
    exact quadratic_lower_bound _ _ _ _ hA
  · refine ⟨-paymentB r lam Y rho u / (2 * paymentA r lam Y rho u), Or.inl hJ, ?_⟩
    rw [payment_quadratic r lam Y rho u _ hJ]
    exact quadratic_attains _ _ _ (ne_of_gt hA)

theorem payment_positive_of_discriminant (r : Row) (lam Y rho u y : ℝ)
    (hJ : 0 < childJ lam u) (hA : 0 < paymentA r lam Y rho u)
    (hD : 0 < 4 * paymentA r lam Y rho u * paymentC r lam Y rho u -
      (paymentB r lam Y rho u) ^ 2) :
    0 < payment r lam Y rho u y := by
  rw [payment_quadratic r lam Y rho u y hJ]
  exact quadratic_positive _ _ _ _ hA hD

theorem admissible_zero_forces_response (lam u y : ℝ) (hJ : childJ lam u = 0)
    (hadm : Admissible lam u y) : y = childH u := by
  rcases hadm with hpos | ⟨_, hy⟩
  · rw [hJ] at hpos
    exact (lt_irrefl _ hpos).elim
  · exact hy

theorem payment_zero_reserve (r : Row) (lam Y rho u : ℝ) (hJ : childJ lam u = 0) :
    payment r lam Y rho u (childH u) =
      p lam Y * parentN r lam Y rho / Y +
      p lam Y * (2 * parentP r lam Y rho - alpha r lam - beta r lam +
        beta r lam * rho) * childH u +
      (gamma r lam - delta r lam - p lam Y * Y * parentP r lam Y rho) *
        (childH u) ^ 2 := by
  unfold payment reserve
  simp only [hJ, lt_self_iff_false, if_false]
  ring

theorem payment_minAt_zero (r : Row) (lam Y rho u : ℝ) (hJ : childJ lam u = 0) :
    MinAt r lam Y rho u (payment r lam Y rho u (childH u)) := by
  constructor
  · intro y hadm
    rw [admissible_zero_forces_response lam u y hJ hadm]
  · exact ⟨childH u, Or.inr ⟨hJ, rfl⟩, rfl⟩

-- P must be replaced in every occurrence, including the source-free part of N.
noncomputable def paymentWithParent (r : Row) (lam Y rho u y P : ℝ) : ℝ :=
  p lam Y * ((rowData r).price / (1 + lam) * rho * source lam Y rho +
    alpha r lam * (1 - rho) - P) / Y +
  p lam Y * beta r lam * rho * childH u +
  p lam Y * (2 * P - alpha r lam - beta r lam) * y +
  (gamma r lam - delta r lam - p lam Y * Y * P) * y ^ 2 + reserve r lam u y

theorem paymentWithParent_original (r : Row) (lam Y rho u y : ℝ) :
    paymentWithParent r lam Y rho u y (parentP r lam Y rho) =
      payment r lam Y rho u y := by
  rfl

theorem correlated_parent_replacement (r : Row) (lam Y rho u y P : ℝ) (hY : Y ≠ 0) :
    paymentWithParent r lam Y rho u y P - payment r lam Y rho u y =
      -(p lam Y / Y) * (P - parentP r lam Y rho) * (1 - Y * y) ^ 2 := by
  unfold paymentWithParent payment parentN
  field_simp
  <;> ring

theorem parent_replacement_lower_bound (r : Row) (lam Y rho u y P : ℝ)
    (hp : 0 ≤ p lam Y) (hY : 0 < Y) (hP : parentP r lam Y rho ≤ P) :
    paymentWithParent r lam Y rho u y P ≤ payment r lam Y rho u y := by
  have hid := correlated_parent_replacement r lam Y rho u y P (ne_of_gt hY)
  have hnonneg := mul_nonneg
    (mul_nonneg (div_nonneg hp hY.le) (sub_nonneg.mpr hP)) (sq_nonneg (1 - Y * y))
  nlinarith only [hid, hnonneg]

theorem reserve_envelope_lower_bound (r : Row) (lam u y L : ℝ)
    (hdelta : 0 ≤ delta r lam) (hJ : 0 < childJ lam u) (hJL : childJ lam u ≤ L) :
    delta r lam * (childH u - y) ^ 2 / L ≤ reserve r lam u y := by
  unfold reserve
  rw [if_pos hJ]
  exact div_le_div_of_nonneg_left (mul_nonneg hdelta (sq_nonneg _)) hJ hJL

theorem source_tangent_identity (K rho theta : ℝ) :
    K * rho ^ 2 - K * (2 * theta * rho - theta ^ 2) = K * (rho - theta) ^ 2 := by
  ring

theorem source_tangent_lower_bound (K rho theta : ℝ) (hK : 0 ≤ K) :
    K * (2 * theta * rho - theta ^ 2) ≤ K * rho ^ 2 := by
  have heq := source_tangent_identity K rho theta
  have hs := mul_nonneg hK (sq_nonneg (rho - theta))
  linarith

-- Exact sufficient obligations on the original domain, not an assumed positivity theorem.
theorem compactHeavy_of_response_obligations (r : Row)
    (hpositive : ∀ lam Y rho u, PairDomain r lam Y rho u (childH u) →
      (rowData r).xMin ≤ parentX lam Y → parentX lam Y ≤ 1 →
      0 < childJ lam u → 0 < paymentA r lam Y rho u ∧
        0 < 4 * paymentA r lam Y rho u * paymentC r lam Y rho u -
          (paymentB r lam Y rho u) ^ 2)
    (hzero : ∀ lam Y rho u, PairDomain r lam Y rho u (childH u) →
      (rowData r).xMin ≤ parentX lam Y → parentX lam Y ≤ 1 →
      childJ lam u = 0 → 0 < payment r lam Y rho u (childH u)) : CompactHeavy r := by
  intro lam Y rho u y hdom hxmin hxmax
  rcases hdom with ⟨hr, hY, hrho, hu, hcap, hadm⟩
  rcases hadm with hJ | ⟨hJ, hy⟩
  · have hdomain : PairDomain r lam Y rho u (childH u) :=
      ⟨hr, hY, hrho, hu, hcap, Or.inl hJ⟩
    obtain ⟨hA, hD⟩ := hpositive lam Y rho u hdomain hxmin hxmax hJ
    exact payment_positive_of_discriminant r lam Y rho u y hJ hA hD
  · subst y
    exact hzero lam Y rho u ⟨hr, hY, hrho, hu, hcap, Or.inr ⟨hJ, rfl⟩⟩ hxmin hxmax hJ

end F4Heavy.Analysis
