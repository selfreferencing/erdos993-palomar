module

public import F4Heavy.Analysis.CommonTransformSemantics

@[expose] public section
set_option autoImplicit false

namespace F4Heavy.Analysis
open F4Heavy.Finite

theorem parentColumns_endpoint_value (p : List (List Fraction)) (xl : Fraction)
    (m : Nat) (v : ℝ)
    (hp : ∀ row ∈ p, ∀ c ∈ row, 0 < c.den) (hl : 0 < xl.den)
    (hm : ∀ row ∈ p, row.length ≤ m+1) :
    matrixValue p v 1 = realHorner ((column (parentColumns p xl m) m).map fractionValue) v := by
  have h := parentColumns_value p xl m v 1 hp hl hm
  rw [show fractionValue xl + (1-fractionValue xl)*1 = 1 by ring] at h
  rw [h, Finset.sum_eq_single m]
  · simp [bernsteinWeight]
  · intro j hj hne
    have hjm : j < m := by have := Finset.mem_range.mp hj; omega
    simp [bernsteinWeight, zero_pow (show m-j ≠ 0 by omega)]
  · simp

theorem matrixEq_row_value (p q : List (List Fraction)) (j : Nat) (v : ℝ)
    (h : matrixEq p q = true) :
    realHorner ((p[j]?.getD []).map fractionValue) v =
      realHorner ((q[j]?.getD []).map fractionValue) v := by
  have he := congrArg (fun mat : List (List ℝ) => realHorner (mat[j]?.getD []) v)
    (matrixEq_sound p q h)
  cases hpg : p[j]? <;> cases hqg : q[j]? <;>
    simp_all only [List.getElem?_map, Option.map_none, Option.map_some,
      Option.getD_none, Option.getD_some, List.map_nil, realHorner_nil]

theorem commonColumns_last_value (p : List (List Fraction)) (xl a b : Fraction)
    (q : ℝ) (hp : ∀ row ∈ p, ∀ c ∈ row, 0 < c.den) (hl : 0 < xl.den)
    (hc : 0 < (commonActivityCenter a b).den)
    (hm : ∀ row ∈ p, row.length ≤ (p[0]?.getD []).length)
    (hfirst : 0 < (p[0]?.getD []).length) (hq : 1-q ≠ 0) :
    realHorner (((commonColumns p xl a b true)[(p[0]?.getD []).length-1]?.getD []).map fractionValue)
        (q-fractionValue (commonActivityCenter a b)) =
      (1-q)^(p.length-1) * matrixValue p (q/(1-q)) 1 := by
  let m := (p[0]?.getD []).length-1
  have hlen : ∀ row ∈ p, row.length ≤ m+1 := by
    intro row hr
    have := hm row hr
    dsimp only [m]
    omega
  have hd := column_den_pos _ m (parentColumns_den_pos p xl m hp hl)
  have hs := scaledColumn_den_pos _ (F4Heavy.Finite.choose m m) hd
  have hj : m < (List.range (m+1)).length := by simp
  unfold commonColumns
  simp only [ite_true]
  change realHorner ((((List.range (m+1)).map (fun j => shifted
    (projective ((column (parentColumns p xl m) j).map
      (fun c => Fraction.mul c (Fraction.ofInt (F4Heavy.Finite.choose m j)))))
    (commonActivityCenter a b) Fraction.one))[m]?.getD []).map fractionValue) _ = _
  simp only [List.getElem?_map, List.getElem?_eq_getElem hj, List.getElem_range, Option.map_some, Option.getD_some]
  rw [shifted_value _ _ _ _ (projective_den_pos _ hs) hc (by decide), fractionValue_one, one_mul]
  rw [show fractionValue (commonActivityCenter a b) + (q-fractionValue (commonActivityCenter a b)) = q by ring]
  rw [projective_homogenization _ q hs hq, scaledColumn_value _ _ _ hd,
    choose_value, Nat.choose_self]
  simp only [Nat.cast_one, one_mul]
  simp only [List.length_map, column, parentColumns]
  rw [parentColumns_endpoint_value p xl m (q/(1-q)) hp hl hlen]
  rfl

theorem commonColumns_endpoint_positive (p cols : List (List Fraction)) (xl a b : Fraction)
    (q : ℝ) (hp : ∀ row ∈ p, ∀ c ∈ row, 0 < c.den) (hl : 0 < xl.den)
    (hc : 0 < (commonActivityCenter a b).den)
    (hm : ∀ row ∈ p, row.length ≤ (p[0]?.getD []).length)
    (hfirst : 0 < (p[0]?.getD []).length) (hq : q < 1)
    (heq : matrixEq (commonColumns p xl a b true) cols = true)
    (hpos : 0 < realHorner ((cols[(p[0]?.getD []).length-1]?.getD []).map fractionValue)
      (q-fractionValue (commonActivityCenter a b))) :
    0 < matrixValue p (q/(1-q)) 1 := by
  have hq' : 0 < 1-q := sub_pos.mpr hq
  rw [← matrixEq_row_value _ _ _ _ heq,
    commonColumns_last_value p xl a b q hp hl hc hm hfirst (ne_of_gt hq')] at hpos
  exact (mul_pos_iff_of_pos_left (pow_pos hq' _)).mp hpos

theorem primitiveLowerCheck_column_positive (cols : List (List Fraction)) (r scale : Fraction)
    (p : List Fraction) (j : Nat) (v : ℝ) (hp : ∀ a ∈ p, 0 < a.den)
    (hcols : ∀ c ∈ cols, ∀ a ∈ c, 0 < a.den) (hr : 0 < r.den)
    (hv : |v| ≤ fractionValue r) (hj : j < p.length)
    (hcheck : primitiveLowerCheck cols r scale p = true)
    (hpos : 0 < fractionValue (p[j]?.getD Fraction.zero)) :
    0 < realHorner ((cols[j]?.getD []).map fractionValue) v := by
  have hh : Fraction.positive scale = true ∧
      Fraction.allEq (p.map (Fraction.mul scale)) (cols.map (fun c => lowerColumn c r)) = true := by
    simpa only [primitiveLowerCheck, Bool.and_eq_true] using hcheck
  have hs : 0 < scale.den := by
    have h : 0 < scale.den ∧ 0 < scale.num := by simpa [Fraction.positive] using hh.1
    exact h.1
  have hlen : p.length = cols.length := by
    have h := (Bool.and_eq_true_iff.mp hh.2).1
    simpa only [List.length_map, beq_iff_eq] using h
  have hjc : j < cols.length := by omega
  have he := congrArg (fun l : List ℝ => l[j]?.getD 0) (fraction_allEq_sound _ _ hh.2)
  simp only [List.getElem?_map, List.getElem?_eq_getElem hj, List.getElem?_eq_getElem hjc,
    Option.map_some, Option.getD_some] at he
  rw [fractionValue_mul scale _ hs (hp _ (List.getElem_mem hj))] at he
  rw [List.getElem?_eq_getElem hj, Option.getD_some] at hpos
  rw [List.getElem?_eq_getElem hjc, Option.getD_some]
  apply lt_of_lt_of_le _ (lowerColumn_sound _ r v (hcols _ (List.getElem_mem hjc)) hr hv)
  rw [← he]
  exact mul_pos (fraction_positive_sound scale hh.1) hpos

end F4Heavy.Analysis
