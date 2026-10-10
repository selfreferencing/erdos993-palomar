module

public import F4Heavy.Analysis.CommonEndpointSemantics
public import F4Heavy.Analysis.SquareSemantics

@[expose] public section
set_option autoImplicit false

namespace F4Heavy.Analysis
open F4Heavy.Finite

theorem matrixValue_transpose (p : List (List Fraction)) (n : Nat) (v x : ℝ)
    (hn : ∀ row ∈ p, row.length ≤ n) :
    matrixValue p v x = realHorner ((List.range n).map (fun j =>
      realHorner ((column p j).map fractionValue) v)) x := by
  unfold matrixValue
  have he : p.map (fun row => realHorner (row.map fractionValue) x) =
      p.map (fun row => ∑ j ∈ Finset.range n, fractionValue (row[j]?.getD Fraction.zero)*x^j) := by
    apply List.map_congr_left
    intro row hr
    exact realHorner_padded_sum row n x (hn row hr)
  rw [he, realHorner_map_sum, realHorner_map_range]
  apply Finset.sum_congr rfl
  intro j hj
  have hs := realHorner_map_scale (p.map (fun row => fractionValue (row[j]?.getD Fraction.zero))) (x^j) v
  simpa only [column, List.map_map, Function.comp_def, mul_comm] using hs

theorem realHorner_padded_range (p : List Fraction) (n : Nat) (x : ℝ) (hn : p.length ≤ n) :
    realHorner ((List.range n).map (fun j => fractionValue (p[j]?.getD Fraction.zero))) x =
      realHorner (p.map fractionValue) x := by
  rw [realHorner_map_range, ← realHorner_padded_sum p n x hn]

/-- Assemble coefficientwise square identities without replacing them with a
single combined finite computation. -/
theorem parametricSquare_value (p quot : List (List Fraction)) (a0 a1 : List Fraction)
    (center : Fraction) (n : Nat) (q z : ℝ)
    (hq : ∀ row ∈ quot, ∀ c ∈ row, 0 < c.den)
    (h0 : ∀ c ∈ a0, 0 < c.den) (h1 : ∀ c ∈ a1, 0 < c.den) (hc : 0 < center.den)
    (hpn : ∀ row ∈ p, row.length ≤ n) (hqn : ∀ row ∈ quot, row.length ≤ n)
    (h0n : a0.length ≤ n) (h1n : a1.length ≤ n)
    (hcheck : ∀ i < n, squareReconstruction (column p i) (column quot i) center
      (a0[i]?.getD Fraction.zero) (a1[i]?.getD Fraction.zero) = true) :
    matrixValue p z q = realHorner (a0.map fractionValue) q +
      (z-fractionValue center)*realHorner (a1.map fractionValue) q +
      (z-fractionValue center)^2*matrixValue quot z q := by
  rw [matrixValue_transpose p n z q hpn, matrixValue_transpose quot n z q hqn]
  have he : (List.range n).map (fun i => realHorner ((column p i).map fractionValue) z) =
      (List.range n).map (fun i => fractionValue (a0[i]?.getD Fraction.zero) +
        (z-fractionValue center)*fractionValue (a1[i]?.getD Fraction.zero) +
        (z-fractionValue center)^2*realHorner ((column quot i).map fractionValue) z) := by
    apply List.map_congr_left
    intro i hi
    simpa only [mul_comm] using squareReconstruction_sound (column p i) (column quot i)
      center (a0[i]?.getD Fraction.zero) (a1[i]?.getD Fraction.zero) z
      (column_den_pos quot i hq) hc (fractionGet_den_pos a0 i h0) (fractionGet_den_pos a1 i h1)
      (hcheck i (List.mem_range.mp hi))
  rw [he, realHorner_map_add, realHorner_map_add]
  have hs1 := realHorner_map_scale ((List.range n).map
    (fun i => fractionValue (a1[i]?.getD Fraction.zero))) (z-fractionValue center) q
  have hsq := realHorner_map_scale ((List.range n).map
    (fun i => realHorner ((column quot i).map fractionValue) z)) ((z-fractionValue center)^2) q
  simp only [List.map_map, Function.comp_def] at hs1 hsq
  rw [hs1, hsq, realHorner_padded_range a0 n q h0n, realHorner_padded_range a1 n q h1n]

theorem polynomialNeg_value (p : List Fraction) (x : ℝ) :
    realHorner ((p.map Fraction.neg).map fractionValue) x = -realHorner (p.map fractionValue) x := by
  have hs := realHorner_map_scale (p.map fractionValue) (-1) x
  simpa only [List.map_map, Function.comp_def, fractionValue_neg, neg_one_mul] using hs

theorem densePolynomialScale_value (p : List Fraction) (c : Fraction) (x : ℝ)
    (hp : ∀ a ∈ p, 0 < a.den) (hc : 0 < c.den) :
    realHorner ((p.map (Fraction.mul c)).map fractionValue) x =
      fractionValue c * realHorner (p.map fractionValue) x := by
  have he : (p.map (Fraction.mul c)).map fractionValue =
      (p.map fractionValue).map (fun a => fractionValue c * a) := by
    simp only [List.map_map, Function.comp_def]
    apply List.map_congr_left
    intro a ha
    exact fractionValue_mul c a hc (hp a ha)
  rw [he, realHorner_map_scale]

theorem parametricDiscriminant_value (a0 a1 q0 disc : List Fraction) (q : ℝ)
    (h0 : ∀ c ∈ a0, 0 < c.den) (h1 : ∀ c ∈ a1, 0 < c.den) (hq : ∀ c ∈ q0, 0 < c.den)
    (hcheck : Fraction.allEq (polynomialAdd ((polynomialMul a0 q0).map (Fraction.mul (Fraction.ofInt 4)))
      ((polynomialMul a1 a1).map Fraction.neg)) disc = true) :
    realHorner (disc.map fractionValue) q =
      4*realHorner (q0.map fractionValue) q*realHorner (a0.map fractionValue) q -
        (realHorner (a1.map fractionValue) q)^2 := by
  have hprod := polynomialMul_den_pos a0 q0 h0 hq
  have hs : ∀ c ∈ (polynomialMul a0 q0).map (Fraction.mul (Fraction.ofInt 4)), 0 < c.den := by
    intro c hc
    obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hc
    exact fraction_mul_den_pos _ _ Nat.zero_lt_one (hprod d hd)
  have hn : ∀ c ∈ (polynomialMul a1 a1).map Fraction.neg, 0 < c.den := by
    intro c hc
    obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hc
    exact polynomialMul_den_pos a1 a1 h1 h1 d hd
  rw [← fraction_allEq_sound _ _ hcheck, polynomialAdd_value _ _ q hs hn,
    densePolynomialScale_value _ _ q hprod Nat.zero_lt_one, polynomialNeg_value,
    polynomialMul_value a0 q0 q h0 hq, polynomialMul_value a1 a1 q h1 h1,
    fractionValue_ofInt]
  push_cast
  ring

theorem projectiveParentColumns_original_positive (p cols : List (List Fraction)) (xl : Fraction)
    (q t : ℝ) (hp : ∀ row ∈ p, ∀ c ∈ row, 0 < c.den) (hl : 0 < xl.den)
    (hm : ∀ row ∈ p, row.length ≤ (p[0]?.getD []).length)
    (hfirst : 0 < (p[0]?.getD []).length) (hq : q < 1) (ht : t < 1)
    (heq : matrixEq (projectiveParentColumns p xl) cols = true)
    (hpos : 0 < matrixValue cols (t/(1-t)) q) :
    0 < matrixValue p (q/(1-q)) (fractionValue xl + (1-fractionValue xl)*t) := by
  have hq' : 0 < 1-q := sub_pos.mpr hq
  have ht' : 0 < 1-t := sub_pos.mpr ht
  rw [← matrixEq_value _ _ _ _ heq] at hpos
  have hprod := mul_pos (pow_pos ht' ((p[0]?.getD []).length-1)) hpos
  rw [projectiveParentColumns_value p xl q t hp hl hm hfirst (ne_of_gt hq') (ne_of_gt ht')] at hprod
  exact (mul_pos_iff_of_pos_left (pow_pos hq' _)).mp hprod

theorem projectiveParentColumns_last_value (p : List (List Fraction)) (xl : Fraction)
    (q : ℝ) (hp : ∀ row ∈ p, ∀ c ∈ row, 0 < c.den) (hl : 0 < xl.den)
    (hm : ∀ row ∈ p, row.length ≤ (p[0]?.getD []).length)
    (hfirst : 0 < (p[0]?.getD []).length) (hq : 1-q ≠ 0) :
    realHorner (((projectiveParentColumns p xl)[(p[0]?.getD []).length-1]?.getD []).map fractionValue) q =
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
  unfold projectiveParentColumns
  change realHorner ((((List.range (m+1)).map (fun j =>
    projective ((column (parentColumns p xl m) j).map
      (fun c => Fraction.mul c (Fraction.ofInt (F4Heavy.Finite.choose m j))))))[m]?.getD []).map fractionValue) q = _
  simp only [List.getElem?_map, List.getElem?_eq_getElem hj, List.getElem_range, Option.map_some, Option.getD_some]
  rw [projective_homogenization _ q hs hq, scaledColumn_value _ _ _ hd, choose_value, Nat.choose_self]
  simp only [Nat.cast_one, one_mul, List.length_map, column, parentColumns]
  rw [parentColumns_endpoint_value p xl m (q/(1-q)) hp hl hlen]
  rfl

theorem projectiveParentColumns_endpoint_positive (p cols : List (List Fraction)) (xl : Fraction)
    (q : ℝ) (hp : ∀ row ∈ p, ∀ c ∈ row, 0 < c.den) (hl : 0 < xl.den)
    (hm : ∀ row ∈ p, row.length ≤ (p[0]?.getD []).length)
    (hfirst : 0 < (p[0]?.getD []).length) (hq : q < 1)
    (heq : matrixEq (projectiveParentColumns p xl) cols = true)
    (hpos : 0 < realHorner ((cols[(p[0]?.getD []).length-1]?.getD []).map fractionValue) q) :
    0 < matrixValue p (q/(1-q)) 1 := by
  have hq' : 0 < 1-q := sub_pos.mpr hq
  rw [← matrixEq_row_value _ _ _ _ heq,
    projectiveParentColumns_last_value p xl q hp hl hm hfirst (ne_of_gt hq')] at hpos
  exact (mul_pos_iff_of_pos_left (pow_pos hq' _)).mp hpos

end F4Heavy.Analysis
