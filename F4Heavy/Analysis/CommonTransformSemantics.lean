module

public import F4Heavy.Analysis.MatrixSemantics

@[expose] public section
set_option autoImplicit false

namespace F4Heavy.Analysis
open F4Heavy.Finite

def commonActivityCenter (a b : Fraction) : Fraction :=
  Fraction.div (Fraction.add (Fraction.div a (Fraction.add Fraction.one a))
    (Fraction.div b (Fraction.add Fraction.one b))) (Fraction.ofInt 2)

theorem scaledColumn_den_pos (p : List Fraction) (k : Nat)
    (hp : ∀ c ∈ p, 0 < c.den) :
    ∀ c ∈ p.map (fun c => Fraction.mul c (Fraction.ofInt k)), 0 < c.den := by
  intro c hc
  obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hc
  exact fraction_mul_den_pos d (Fraction.ofInt k) (hp d hd) Nat.zero_lt_one

theorem scaledColumn_value (p : List Fraction) (k : Nat) (v : ℝ)
    (hp : ∀ c ∈ p, 0 < c.den) :
    realHorner ((p.map (fun c => Fraction.mul c (Fraction.ofInt k))).map fractionValue) v =
      (k : ℝ) * realHorner (p.map fractionValue) v := by
  have he : (p.map (fun c => Fraction.mul c (Fraction.ofInt k))).map fractionValue =
      (p.map fractionValue).map (fun x => (k : ℝ)*x) := by
    simp only [List.map_map, Function.comp_def]
    apply List.map_congr_left
    intro c hc
    rw [fractionValue_mul c _ (hp c hc) Nat.zero_lt_one, fractionValue_ofInt]
    simp [mul_comm]
  rw [he, realHorner_map_scale]

theorem projectiveParentColumns_den_pos (p : List (List Fraction)) (xl : Fraction)
    (hp : ∀ row ∈ p, ∀ c ∈ row, 0 < c.den) (hl : 0 < xl.den) :
    ∀ row ∈ projectiveParentColumns p xl, ∀ c ∈ row, 0 < c.den := by
  intro row hr
  obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hr
  exact projective_den_pos _ (scaledColumn_den_pos _ _
    (column_den_pos _ _ (parentColumns_den_pos p xl _ hp hl)))

/-- Both projective coordinates, with the positive homogenizing factors explicit. -/
theorem projectiveParentColumns_value (p : List (List Fraction)) (xl : Fraction)
    (q t : ℝ) (hp : ∀ row ∈ p, ∀ c ∈ row, 0 < c.den) (hl : 0 < xl.den)
    (hm : ∀ row ∈ p, row.length ≤ (p[0]?.getD []).length)
    (hfirst : 0 < (p[0]?.getD []).length) (hq : 1-q ≠ 0) (ht : 1-t ≠ 0) :
    (1-t)^((p[0]?.getD []).length-1) *
        matrixValue (projectiveParentColumns p xl) (t/(1-t)) q =
      (1-q)^(p.length-1) *
        matrixValue p (q/(1-q)) (fractionValue xl + (1-fractionValue xl)*t) := by
  let m := (p[0]?.getD []).length-1
  have hlen : ∀ row ∈ p, row.length ≤ m+1 := by
    intro row hr
    have := hm row hr
    dsimp only [m]
    omega
  have hc : ∀ j, ∀ c ∈ column (parentColumns p xl m) j, 0 < c.den :=
    fun j => column_den_pos _ j (parentColumns_den_pos p xl m hp hl)
  have hv : matrixValue (projectiveParentColumns p xl) (t/(1-t)) q =
      (1-q)^(p.length-1) * realHorner ((List.range (m+1)).map (fun j =>
        (m.choose j : ℝ) * realHorner
          ((column (parentColumns p xl m) j).map fractionValue) (q/(1-q)))) (t/(1-t)) := by
    unfold matrixValue projectiveParentColumns
    simp only [List.map_map, Function.comp_def]
    have he : ∀ j, realHorner ((projective ((column (parentColumns p xl m) j).map
        (fun c => Fraction.mul c (Fraction.ofInt (F4Heavy.Finite.choose m j))))).map fractionValue) q =
        (1-q)^(p.length-1) * ((m.choose j : ℝ) * realHorner
          ((column (parentColumns p xl m) j).map fractionValue) (q/(1-q))) := by
      intro j
      rw [projective_homogenization _ q (scaledColumn_den_pos _ _ (hc j)) hq,
        scaledColumn_value _ _ _ (hc j), choose_value]
      simp only [List.length_map, column, parentColumns]
    change realHorner ((List.range (m+1)).map (fun j =>
      realHorner ((projective ((column (parentColumns p xl m) j).map
        (fun c => Fraction.mul c (Fraction.ofInt (F4Heavy.Finite.choose m j))))).map fractionValue) q)) _ = _
    simp_rw [he]
    simpa only [List.map_map, Function.comp_def] using realHorner_map_scale
      ((List.range (m+1)).map (fun j => (m.choose j : ℝ) *
        realHorner ((column (parentColumns p xl m) j).map fractionValue) (q/(1-q))))
      ((1-q)^(p.length-1)) (t/(1-t))
  rw [hv, parentColumns_projective_value p xl m (q/(1-q)) t hp hl hlen ht]
  ring

theorem commonColumns_shifted_value (p : List (List Fraction)) (xl a b : Fraction)
    (z v : ℝ) (hp : ∀ row ∈ p, ∀ c ∈ row, 0 < c.den) (hl : 0 < xl.den)
    (hc : 0 < (commonActivityCenter a b).den) :
    matrixValue (commonColumns p xl a b true) z v =
      matrixValue (projectiveParentColumns p xl) z (fractionValue (commonActivityCenter a b)+v) := by
  unfold matrixValue commonColumns projectiveParentColumns
  simp only [List.map_map, Function.comp_def, ite_true]
  congr 1
  apply List.map_congr_left
  intro j hj
  let m := (p[0]?.getD []).length-1
  have hd := projective_den_pos _ (scaledColumn_den_pos _ (F4Heavy.Finite.choose m j)
    (column_den_pos _ j (parentColumns_den_pos p xl m hp hl)))
  simpa only [fractionValue_one, one_mul, m, commonActivityCenter] using shifted_value _ (commonActivityCenter a b)
    Fraction.one v hd hc (by decide)

/-- A checked common-column matrix yields positivity of the original numerator
at every interior parent coordinate; no finite checks are assumed to be real facts. -/
theorem commonColumns_original_positive (p cols : List (List Fraction)) (xl a b : Fraction)
    (q t : ℝ) (hp : ∀ row ∈ p, ∀ c ∈ row, 0 < c.den) (hl : 0 < xl.den)
    (hc : 0 < (commonActivityCenter a b).den)
    (hm : ∀ row ∈ p, row.length ≤ (p[0]?.getD []).length)
    (hfirst : 0 < (p[0]?.getD []).length) (hq : q < 1) (ht : t < 1)
    (heq : matrixEq (commonColumns p xl a b true) cols = true)
    (hpos : 0 < matrixValue cols (t/(1-t)) (q-fractionValue (commonActivityCenter a b))) :
    0 < matrixValue p (q/(1-q)) (fractionValue xl + (1-fractionValue xl)*t) := by
  have hq' : 0 < 1-q := sub_pos.mpr hq
  have ht' : 0 < 1-t := sub_pos.mpr ht
  rw [← matrixEq_value _ _ _ _ heq, commonColumns_shifted_value p xl a b _ _ hp hl hc] at hpos
  rw [show fractionValue (commonActivityCenter a b) + (q-fractionValue (commonActivityCenter a b)) = q by ring] at hpos
  have hprod := mul_pos (pow_pos ht' ((p[0]?.getD []).length-1)) hpos
  rw [projectiveParentColumns_value p xl q t hp hl hm hfirst (ne_of_gt hq') (ne_of_gt ht')] at hprod
  exact (mul_pos_iff_of_pos_left (pow_pos hq' _)).mp hprod

end F4Heavy.Analysis
