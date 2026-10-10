module

public import F4Heavy.Analysis.ShiftSemantics

@[expose] public section
set_option autoImplicit false

namespace F4Heavy.Analysis
open F4Heavy.Finite
open scoped BigOperators

noncomputable def bernsteinWeight (n k : Nat) (x : ℝ) : ℝ :=
  (n.choose k : ℝ) * x^k * (1-x)^(n-k)

theorem bernsteinWeight_nonneg (n k : Nat) (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    0 ≤ bernsteinWeight n k x := by
  unfold bernsteinWeight
  positivity

theorem bernsteinWeight_sum (n : Nat) (x : ℝ) :
    (∑ k ∈ Finset.range (n+1), bernsteinWeight n k x) = 1 := by
  have h := add_pow x (1-x) n
  have hs : x + (1-x) = 1 := by ring
  rw [hs, one_pow] at h
  rw [h]
  apply Finset.sum_congr rfl
  intro k hk
  unfold bernsteinWeight
  ring

theorem choose_ratio_product (n i k : Nat) (hkn : k ≤ n) (hki : k ≤ i) :
    (i.choose k : ℝ) / (n.choose k : ℝ) * (n.choose i : ℝ) =
      ((n-k).choose (i-k) : ℝ) := by
  have hd : (n.choose k : ℝ) ≠ 0 := ne_of_gt (by exact_mod_cast Nat.choose_pos hkn)
  have h : (n.choose i : ℝ) * (i.choose k : ℝ) =
      (n.choose k : ℝ) * ((n-k).choose (i-k) : ℝ) := by
    exact_mod_cast (Nat.choose_mul hki : n.choose i * i.choose k = n.choose k * (n-k).choose (i-k))
  rw [div_mul_eq_mul_div]
  apply (div_eq_iff hd).2
  convert h using 1 <;> ring

theorem bernstein_monomial_sum (n k : Nat) (x : ℝ) (hkn : k ≤ n) :
    (∑ j ∈ Finset.range (n+1-k),
      ((j+k).choose k : ℝ) / (n.choose k : ℝ) * bernsteinWeight n (j+k) x) = x^k := by
  have hrange : n+1-k = (n-k)+1 := by omega
  rw [hrange]
  calc
    _ = x^k * ∑ j ∈ Finset.range (n-k+1), x^j * (1-x)^(n-k-j) * ((n-k).choose j : ℝ) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      unfold bernsteinWeight
      rw [← mul_assoc, ← mul_assoc, choose_ratio_product n (j+k) k hkn (by omega),
        Nat.add_sub_cancel, pow_add]
      have he : n-(j+k) = n-k-j := by omega
      rw [he]
      ring
    _ = x^k * (x+(1-x))^(n-k) := by rw [add_pow]
    _ = x^k := by simp

theorem bernstein_reconstruction_sum (n : Nat) (f : Nat → ℝ) (x : ℝ) :
    (∑ i ∈ Finset.range (n+1),
      (∑ k ∈ Finset.range (i+1), f k * ((i.choose k : ℝ)/(n.choose k : ℝ))) *
        bernsteinWeight n i x) =
      ∑ k ∈ Finset.range (n+1), f k * x^k := by
  simp only [Finset.sum_mul]
  rw [← triangle_sum_reindex (n+1)
    (fun i k => f k * ((i.choose k : ℝ)/(n.choose k : ℝ)) * bernsteinWeight n i x)]
  apply Finset.sum_congr rfl
  intro k hk
  rw [← bernstein_monomial_sum n k x (by have := Finset.mem_range.mp hk; omega), Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  ring

theorem bernstein_positive_combination (n : Nat) (f : Nat → ℝ) (x : ℝ)
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hf : ∀ k ≤ n, 0 < f k) :
    0 < ∑ k ∈ Finset.range (n+1), f k * bernsteinWeight n k x := by
  apply Finset.sum_pos'
  · intro k hk
    exact mul_nonneg (hf k (by have := Finset.mem_range.mp hk; omega)).le
      (bernsteinWeight_nonneg n k x hx0 hx1)
  · by_cases hx : x = 1
    · refine ⟨n, by simp, ?_⟩
      simpa [bernsteinWeight, hx] using hf n le_rfl
    · refine ⟨0, by simp, ?_⟩
      have hd : 0 < 1-x := sub_pos.mpr (lt_of_le_of_ne hx1 hx)
      simpa [bernsteinWeight] using mul_pos (hf 0 (Nat.zero_le _)) (pow_pos hd n)

theorem bernsteinCoefficient_den_pos (q : List Fraction) (n i : Nat)
    (hq : ∀ c ∈ q, 0 < c.den) (hi : i ≤ n) :
    0 < (Fraction.sum ((List.range (min (i+1) q.length)).map fun k =>
      Fraction.mul (q[k]?.getD Fraction.zero)
        ⟨F4Heavy.Finite.choose i k, F4Heavy.Finite.choose n k⟩)).den := by
  apply fraction_sum_den_pos
  intro c hc
  obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hc
  have hk' := List.mem_range.mp hk
  apply fraction_mul_den_pos _ _ (fractionGet_den_pos q k hq)
  exact choose_den_positive n k (by omega)

theorem bernsteinCoefficient_value (q : List Fraction) (n i : Nat)
    (hq : ∀ c ∈ q, 0 < c.den) (hi : i ≤ n) :
    fractionValue (Fraction.sum ((List.range (min (i+1) q.length)).map fun k =>
      Fraction.mul (q[k]?.getD Fraction.zero)
        ⟨F4Heavy.Finite.choose i k, F4Heavy.Finite.choose n k⟩)) =
    ∑ k ∈ Finset.range (i+1), fractionValue (q[k]?.getD Fraction.zero) *
      ((i.choose k : ℝ)/(n.choose k : ℝ)) := by
  have hterms : ∀ c ∈ (List.range (min (i+1) q.length)).map (fun k =>
      Fraction.mul (q[k]?.getD Fraction.zero)
        ⟨F4Heavy.Finite.choose i k, F4Heavy.Finite.choose n k⟩), 0 < c.den := by
    intro c hc
    obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hc
    have hk' := List.mem_range.mp hk
    exact fraction_mul_den_pos _ _ (fractionGet_den_pos q k hq)
      (choose_den_positive n k (by omega))
  rw [fractionValue_sum _ hterms]
  simp only [List.map_map, Function.comp_def]
  rw [list_range_sum]
  calc
    _ = ∑ k ∈ Finset.range (min (i+1) q.length), fractionValue (q[k]?.getD Fraction.zero) *
        ((i.choose k : ℝ)/(n.choose k : ℝ)) := by
      apply Finset.sum_congr rfl
      intro k hk
      have hk' := Finset.mem_range.mp hk
      rw [fractionValue_mul _ _ (fractionGet_den_pos q k hq) (choose_den_positive n k (by omega))]
      simp [fractionValue, choose_value]
    _ = _ := by
      apply Finset.sum_subset (Finset.range_mono (Nat.min_le_left _ _))
      intro k hk hnot
      have hk' := Finset.mem_range.mp hk
      have hn := mt Finset.mem_range.mpr hnot
      rw [List.getElem?_eq_none (by omega)]
      simp [fractionValue_zero]

theorem bernstein_den_pos (p : List Fraction) (a b : Fraction) (n : Nat)
    (hp : ∀ c ∈ p, 0 < c.den) (ha : 0 < a.den) (hb : 0 < b.den) :
    ∀ c ∈ bernstein p a b n, 0 < c.den := by
  intro c hc
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hc
  have hi' := List.mem_range.mp hi
  exact bernsteinCoefficient_den_pos _ n i
    (shifted_den_pos p a (Fraction.sub b a) hp ha (fraction_sub_den_pos b a hb ha)) (by omega)

theorem bernstein_values (p : List Fraction) (a b : Fraction) (n : Nat)
    (hp : ∀ c ∈ p, 0 < c.den) (ha : 0 < a.den) (hb : 0 < b.den) :
    (bernstein p a b n).map fractionValue =
      (List.range (n+1)).map (fun i => ∑ k ∈ Finset.range (i+1),
        fractionValue ((shifted p a (Fraction.sub b a))[k]?.getD Fraction.zero) *
          ((i.choose k : ℝ)/(n.choose k : ℝ))) := by
  unfold bernstein
  simp only [List.map_map, Function.comp_def]
  apply List.map_congr_left
  intro i hi
  have hi' := List.mem_range.mp hi
  exact bernsteinCoefficient_value _ n i
    (shifted_den_pos p a (Fraction.sub b a) hp ha (fraction_sub_den_pos b a hb ha)) (by omega)

theorem realHorner_padded_sum (p : List Fraction) (n : Nat) (x : ℝ) (hn : p.length ≤ n) :
    realHorner (p.map fractionValue) x =
      ∑ k ∈ Finset.range n, fractionValue (p[k]?.getD Fraction.zero) * x^k := by
  rw [realHorner_sum_get]
  apply Finset.sum_subset (Finset.range_mono hn)
  intro k hk hnot
  have hn' := mt Finset.mem_range.mpr hnot
  rw [List.getElem?_eq_none (by omega)]
  simp [fractionValue_zero]

theorem bernstein_value (p : List Fraction) (a b : Fraction) (n : Nat) (x : ℝ)
    (hp : ∀ c ∈ p, 0 < c.den) (ha : 0 < a.den) (hb : 0 < b.den)
    (hn : p.length ≤ n+1) :
    (∑ i ∈ Finset.range (n+1), fractionValue ((bernstein p a b n)[i]?.getD Fraction.zero) *
      bernsteinWeight n i x) =
    realHorner (p.map fractionValue) (fractionValue a + (fractionValue b-fractionValue a)*x) := by
  have hvals := bernstein_values p a b n hp ha hb
  have hcoeff : ∀ i ≤ n, fractionValue ((bernstein p a b n)[i]?.getD Fraction.zero) =
      ∑ k ∈ Finset.range (i+1),
        fractionValue ((shifted p a (Fraction.sub b a))[k]?.getD Fraction.zero) *
          ((i.choose k : ℝ)/(n.choose k : ℝ)) := by
    intro i hi
    have hil : i < (bernstein p a b n).length := by simp [bernstein]; omega
    have hie := congrArg (fun l : List ℝ => l[i]?.getD 0) hvals
    simpa [List.getElem?_eq_getElem, hil, show i < n+1 by omega] using hie
  rw [Finset.sum_congr (s₁ := Finset.range (n+1)) rfl (fun i hi => congrArg (fun z => z * bernsteinWeight n i x)
    (hcoeff i (by have := Finset.mem_range.mp hi; omega)))]
  rw [bernstein_reconstruction_sum]
  rw [← realHorner_padded_sum _ (n+1) x (by simpa [shifted] using hn)]
  rw [shifted_value p a (Fraction.sub b a) x hp ha (fraction_sub_den_pos b a hb ha),
    fractionValue_sub b a hb ha]

theorem bernstein_positive_values (p : List Fraction) (a b : Fraction) (n : Nat) (x : ℝ)
    (hp : ∀ c ∈ p, 0 < c.den) (ha : 0 < a.den) (hb : 0 < b.den)
    (hn : p.length ≤ n+1) (hab : fractionValue a < fractionValue b)
    (hx0 : fractionValue a ≤ x) (hx1 : x ≤ fractionValue b)
    (hcheck : ∀ c ∈ bernstein p a b n, 0 < fractionValue c) :
    0 < realHorner (p.map fractionValue) x := by
  let t := (x-fractionValue a)/(fractionValue b-fractionValue a)
  have hd : 0 < fractionValue b-fractionValue a := sub_pos.mpr hab
  have ht0 : 0 ≤ t := div_nonneg (sub_nonneg.mpr hx0) hd.le
  have ht1 : t ≤ 1 := (div_le_one hd).2 (by linarith only [hx1])
  have hid : fractionValue a + (fractionValue b-fractionValue a)*t = x := by
    dsimp only [t]
    field_simp
    ring
  have hval := bernstein_value p a b n t hp ha hb hn
  rw [hid] at hval
  rw [← hval]
  apply bernstein_positive_combination n _ t ht0 ht1
  intro i hi
  have hil : i < (bernstein p a b n).length := by simp [bernstein]; omega
  rw [List.getElem?_eq_getElem hil]
  exact hcheck _ (List.getElem_mem hil)

theorem bernstein_positive (p : List Fraction) (a b : Fraction) (n : Nat) (x : ℝ)
    (hp : ∀ c ∈ p, 0 < c.den) (ha : 0 < a.den) (hb : 0 < b.den)
    (hn : p.length ≤ n+1) (hab : fractionValue a < fractionValue b)
    (hx0 : fractionValue a ≤ x) (hx1 : x ≤ fractionValue b)
    (hcheck : ∀ c ∈ bernstein p a b n, Fraction.positive c = true) :
    0 < realHorner (p.map fractionValue) x := by
  exact bernstein_positive_values p a b n x hp ha hb hn hab hx0 hx1
    (fun c hc => fraction_positive_sound c (hcheck c hc))

theorem bernstein_positive_of_allEq (p controls : List Fraction) (a b : Fraction) (n : Nat) (x : ℝ)
    (hp : ∀ c ∈ p, 0 < c.den) (ha : 0 < a.den) (hb : 0 < b.den)
    (hn : p.length ≤ n+1) (hab : fractionValue a < fractionValue b)
    (hx0 : fractionValue a ≤ x) (hx1 : x ≤ fractionValue b)
    (heq : Fraction.allEq (bernstein p a b n) controls = true)
    (hcheck : ∀ c ∈ controls, Fraction.positive c = true) :
    0 < realHorner (p.map fractionValue) x := by
  apply bernstein_positive_values p a b n x hp ha hb hn hab hx0 hx1
  intro c hc
  have hm : fractionValue c ∈ controls.map fractionValue := by
    rw [← fraction_allEq_sound _ _ heq]
    exact List.mem_map.mpr ⟨c, hc, rfl⟩
  obtain ⟨d, hd, he⟩ := List.mem_map.mp hm
  rw [← he]
  exact fraction_positive_sound d (hcheck d hd)

end F4Heavy.Analysis
