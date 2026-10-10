module

public import F4Heavy.Analysis.BernsteinSemantics

@[expose] public section
set_option autoImplicit false

namespace F4Heavy.Analysis
open F4Heavy.Finite
open scoped BigOperators

theorem fractionGet_zero (p : List Fraction) (i : Nat) (hi : p.length ≤ i) :
    fractionValue (p[i]?.getD Fraction.zero) = 0 := by
  rw [List.getElem?_eq_none hi]
  exact fractionValue_zero

theorem polynomialAdd_den_pos (p q : List Fraction)
    (hp : ∀ c ∈ p, 0 < c.den) (hq : ∀ c ∈ q, 0 < c.den) :
    ∀ c ∈ polynomialAdd p q, 0 < c.den := by
  intro c hc
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hc
  exact fraction_add_den_pos _ _ (fractionGet_den_pos p i hp) (fractionGet_den_pos q i hq)

theorem polynomialAdd_value (p q : List Fraction) (x : ℝ)
    (hp : ∀ c ∈ p, 0 < c.den) (hq : ∀ c ∈ q, 0 < c.den) :
    realHorner ((polynomialAdd p q).map fractionValue) x =
      realHorner (p.map fractionValue) x + realHorner (q.map fractionValue) x := by
  unfold polynomialAdd
  simp only [List.map_map, Function.comp_def]
  rw [realHorner_map_range]
  calc
    _ = ∑ i ∈ Finset.range (max p.length q.length),
        (fractionValue (p[i]?.getD Fraction.zero) + fractionValue (q[i]?.getD Fraction.zero)) * x^i := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [fractionValue_add _ _ (fractionGet_den_pos p i hp) (fractionGet_den_pos q i hq)]
    _ = _ := by
      simp only [add_mul, Finset.sum_add_distrib]
      rw [← realHorner_padded_sum p _ x (Nat.le_max_left _ _),
        ← realHorner_padded_sum q _ x (Nat.le_max_right _ _)]

theorem polynomialMul_den_pos (p q : List Fraction)
    (hp : ∀ c ∈ p, 0 < c.den) (hq : ∀ c ∈ q, 0 < c.den) :
    ∀ c ∈ polynomialMul p q, 0 < c.den := by
  unfold polynomialMul
  split
  · simp
  · intro c hc
    obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hc
    apply fraction_sum_den_pos
    intro c hc
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hc
    exact fraction_mul_den_pos _ _ (fractionGet_den_pos p i hp) (fractionGet_den_pos q (k-i) hq)

theorem convolution_sum_value (f g : Nat → ℝ) (m n : Nat) (x : ℝ)
    (hm : 0 < m) (hn : 0 < n) (hf : ∀ i, m ≤ i → f i = 0) (hg : ∀ i, n ≤ i → g i = 0) :
    (∑ k ∈ Finset.range (m+n-1), (∑ i ∈ Finset.range (k+1), f i * g (k-i)) * x^k) =
      (∑ i ∈ Finset.range m, f i * x^i) * (∑ j ∈ Finset.range n, g j * x^j) := by
  simp only [Finset.sum_mul]
  rw [← triangle_sum_reindex (m+n-1) (fun k i => f i * g (k-i) * x^k)]
  simp only [Nat.add_sub_cancel]
  calc
    _ = ∑ i ∈ Finset.range m, ∑ j ∈ Finset.range (m+n-1-i), f i * g j * x^(j+i) := by
      symm
      apply Finset.sum_subset (Finset.range_mono (by omega))
      intro i hi hnot
      have him := mt Finset.mem_range.mpr hnot
      simp only [hf i (by omega), zero_mul, Finset.sum_const_zero]
    _ = ∑ i ∈ Finset.range m, f i * x^i * (∑ j ∈ Finset.range n, g j * x^j) := by
      apply Finset.sum_congr rfl
      intro i hi
      have him := Finset.mem_range.mp hi
      have heq : (∑ j ∈ Finset.range n, g j*x^j) =
          ∑ j ∈ Finset.range (m+n-1-i), g j*x^j := by
        apply Finset.sum_subset (Finset.range_mono (by omega))
        intro j hj hnot
        have hjn := mt Finset.mem_range.mpr hnot
        simp [hg j (by omega)]
      rw [heq, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      rw [pow_add]
      ring
    _ = _ := rfl

theorem polynomialMul_value (p q : List Fraction) (x : ℝ)
    (hp : ∀ c ∈ p, 0 < c.den) (hq : ∀ c ∈ q, 0 < c.den) :
    realHorner ((polynomialMul p q).map fractionValue) x =
      realHorner (p.map fractionValue) x * realHorner (q.map fractionValue) x := by
  by_cases hp0 : p = []
  · subst p; simp [polynomialMul, realHorner]
  by_cases hq0 : q = []
  · subst q; simp [polynomialMul, realHorner]
  have hm : 0 < p.length := by cases p <;> simp_all
  have hn : 0 < q.length := by cases q <;> simp_all
  unfold polynomialMul
  simp only [Bool.or_eq_true, List.isEmpty_iff, hp0, hq0, or_self, ite_false]
  simp only [List.map_map, Function.comp_def]
  rw [realHorner_map_range, realHorner_sum_get p, realHorner_sum_get q]
  apply Eq.trans _ (convolution_sum_value
    (fun i => fractionValue (p[i]?.getD Fraction.zero))
    (fun i => fractionValue (q[i]?.getD Fraction.zero)) p.length q.length x hm hn
    (fractionGet_zero p) (fractionGet_zero q))
  apply Finset.sum_congr rfl
  intro k hk
  have hterms : ∀ c ∈ (List.range (k+1)).map (fun i =>
      Fraction.mul (p[i]?.getD Fraction.zero) (q[k-i]?.getD Fraction.zero)), 0 < c.den := by
    intro c hc
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hc
    exact fraction_mul_den_pos _ _ (fractionGet_den_pos p i hp) (fractionGet_den_pos q (k-i) hq)
  rw [fractionValue_sum _ hterms]
  simp only [List.map_map, Function.comp_def]
  rw [list_range_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  exact fractionValue_mul _ _ (fractionGet_den_pos p i hp) (fractionGet_den_pos q (k-i) hq)

end F4Heavy.Analysis
