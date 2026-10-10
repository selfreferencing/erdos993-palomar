module

public import F4Heavy.Analysis.FractionSemantics

@[expose] public section
set_option autoImplicit false

namespace F4Heavy.Analysis
open F4Heavy.Finite

def validPolynomial (p : Polynomial) : Prop := ∀ t ∈ p, 0 < t.c.den

noncomputable def termValue (t : Term) (v x : ℝ) : ℝ :=
  fractionValue t.c * v ^ t.v * x ^ t.x

noncomputable def polynomialValue (p : Polynomial) (v x : ℝ) : ℝ :=
  (p.map (fun t => termValue t v x)).sum

theorem polynomialValue_nil (v x : ℝ) : polynomialValue [] v x = 0 := rfl

theorem polynomialValue_cons (t : Term) (p : Polynomial) (v x : ℝ) :
    polynomialValue (t :: p) v x = termValue t v x + polynomialValue p v x := by
  simp [polynomialValue]

theorem termValue_zero (t : Term) (v x : ℝ) (h : t.c.num = 0) :
    termValue t v x = 0 := by
  simp [termValue, fractionValue, h]

theorem mergeTerms_valid (fuel : Nat) (a b : Polynomial)
    (ha : validPolynomial a) (hb : validPolynomial b) :
    validPolynomial (mergeTerms fuel a b) := by
  induction fuel generalizing a b with
  | zero =>
    cases a with
    | nil => exact hb
    | cons s aa =>
      cases b with
      | nil => exact ha
      | cons t bb => simp [mergeTerms, validPolynomial]
  | succ fuel ih =>
    cases a with
    | nil => exact hb
    | cons s aa =>
      cases b with
      | nil => exact ha
      | cons t bb =>
        have hs := ha s (by simp)
        have ht := hb t (by simp)
        have haa : validPolynomial aa := fun u hu => ha u (by simp [hu])
        have hbb : validPolynomial bb := fun u hu => hb u (by simp [hu])
        simp only [mergeTerms]
        split
        · split
          · exact ih aa bb haa hbb
          · intro u hu
            simp only [List.mem_cons] at hu
            rcases hu with rfl | hu
            · exact fraction_add_den_pos s.c t.c hs ht
            · exact ih aa bb haa hbb u hu
        · split
          · intro u hu
            simp only [List.mem_cons] at hu
            rcases hu with rfl | hu
            · exact hs
            · exact ih aa (t :: bb) haa hb u hu
          · intro u hu
            simp only [List.mem_cons] at hu
            rcases hu with rfl | hu
            · exact ht
            · exact ih (s :: aa) bb ha hbb u hu

theorem mergeTerms_value (fuel : Nat) (a b : Polynomial) (v x : ℝ)
    (ha : validPolynomial a) (hb : validPolynomial b)
    (hf : a.length + b.length ≤ fuel) :
    polynomialValue (mergeTerms fuel a b) v x =
      polynomialValue a v x + polynomialValue b v x := by
  induction fuel generalizing a b with
  | zero =>
    have hal : a = [] := List.length_eq_zero_iff.mp (by omega)
    have hbl : b = [] := List.length_eq_zero_iff.mp (by omega)
    subst a; subst b
    simp [mergeTerms, polynomialValue]
  | succ fuel ih =>
    cases a with
    | nil => simp [mergeTerms, polynomialValue]
    | cons s aa =>
      cases b with
      | nil => simp [mergeTerms, polynomialValue]
      | cons t bb =>
        have hs := ha s (by simp)
        have ht := hb t (by simp)
        have haa : validPolynomial aa := fun u hu => ha u (by simp [hu])
        have hbb : validPolynomial bb := fun u hu => hb u (by simp [hu])
        simp only [List.length_cons] at hf
        simp only [mergeTerms]
        split
        · rename_i he
          have heq : s.v = t.v ∧ s.x = t.x := by simpa using he
          have hc : termValue { s with c := Fraction.add s.c t.c } v x =
              termValue s v x + termValue t v x := by
            simp only [termValue, fractionValue_add s.c t.c hs ht, heq.1, heq.2]
            ring
          split
          · rename_i hz
            have hz' : (Fraction.add s.c t.c).num = 0 := by simpa using hz
            have hzero := termValue_zero { s with c := Fraction.add s.c t.c } v x hz'
            rw [ih aa bb haa hbb (by omega)]
            simp only [polynomialValue_cons]
            linarith
          · rw [polynomialValue_cons, hc, ih aa bb haa hbb (by omega)]
            simp only [polynomialValue_cons]
            ring
        · split
          · rw [polynomialValue_cons, ih aa (t :: bb) haa hb (by simp; omega)]
            simp only [polynomialValue_cons]
            ring
          · rw [polynomialValue_cons, ih (s :: aa) bb ha hbb (by simp; omega)]
            simp only [polynomialValue_cons]
            ring

theorem polyAdd_valid (a b : Polynomial) (ha : validPolynomial a) (hb : validPolynomial b) :
    validPolynomial (polyAdd a b) := mergeTerms_valid _ a b ha hb

theorem polyAdd_value (a b : Polynomial) (v x : ℝ)
    (ha : validPolynomial a) (hb : validPolynomial b) :
    polynomialValue (polyAdd a b) v x = polynomialValue a v x + polynomialValue b v x :=
  mergeTerms_value _ a b v x ha hb (le_refl _)

def multiplicationRow (s : Term) (b : Polynomial) : Polynomial :=
  b.filterMap fun t =>
    let c := Fraction.mul s.c t.c
    if c.num == 0 then none else some ⟨s.v + t.v, s.x + t.x, c⟩

theorem multiplicationRow_cons (s t : Term) (b : Polynomial) :
    multiplicationRow s (t :: b) =
      if (Fraction.mul s.c t.c).num == 0 then multiplicationRow s b
      else ⟨s.v + t.v, s.x + t.x, Fraction.mul s.c t.c⟩ :: multiplicationRow s b := by
  by_cases h : (Fraction.mul s.c t.c).num = 0
  · simp [multiplicationRow, h]
  · simp [multiplicationRow, h]

theorem multiplicationRow_valid (s : Term) (b : Polynomial)
    (hs : 0 < s.c.den) (hb : validPolynomial b) : validPolynomial (multiplicationRow s b) := by
  induction b with
  | nil => simp [multiplicationRow, validPolynomial]
  | cons t bb ih =>
    have ht := hb t (by simp)
    have hbb : validPolynomial bb := fun u hu => hb u (by simp [hu])
    rw [multiplicationRow_cons]
    split
    · exact ih hbb
    · intro u hu
      simp only [List.mem_cons] at hu
      rcases hu with rfl | hu
      · exact fraction_mul_den_pos s.c t.c hs ht
      · exact ih hbb u hu

theorem multiplicationRow_value (s : Term) (b : Polynomial) (v x : ℝ)
    (hs : 0 < s.c.den) (hb : validPolynomial b) :
    polynomialValue (multiplicationRow s b) v x = termValue s v x * polynomialValue b v x := by
  induction b with
  | nil => simp [multiplicationRow, polynomialValue]
  | cons t bb ih =>
    have ht := hb t (by simp)
    have hbb : validPolynomial bb := fun u hu => hb u (by simp [hu])
    have hm : termValue ⟨s.v + t.v, s.x + t.x, Fraction.mul s.c t.c⟩ v x =
        termValue s v x * termValue t v x := by
      simp only [termValue, fractionValue_mul s.c t.c hs ht, pow_add]
      ring
    rw [multiplicationRow_cons]
    split
    · rename_i hz
      have hz' : (Fraction.mul s.c t.c).num = 0 := by simpa using hz
      have hzero := termValue_zero ⟨s.v + t.v, s.x + t.x, Fraction.mul s.c t.c⟩ v x hz'
      simp only [ih hbb, polynomialValue_cons]
      rw [hm] at hzero
      nlinarith only [hzero]
    · simp only [polynomialValue_cons, hm, ih hbb]
      ring

theorem multiplicationFold_valid (a b acc : Polynomial)
    (ha : validPolynomial a) (hb : validPolynomial b) (hc : validPolynomial acc) :
    validPolynomial (a.foldl (fun z s => polyAdd z (multiplicationRow s b)) acc) := by
  induction a generalizing acc with
  | nil => exact hc
  | cons s aa ih =>
    exact ih (polyAdd acc (multiplicationRow s b))
      (fun t ht => ha t (by simp [ht]))
      (polyAdd_valid _ _ hc (multiplicationRow_valid s b (ha s (by simp)) hb))

theorem multiplicationFold_value (a b acc : Polynomial) (v x : ℝ)
    (ha : validPolynomial a) (hb : validPolynomial b) (hc : validPolynomial acc) :
    polynomialValue (a.foldl (fun z s => polyAdd z (multiplicationRow s b)) acc) v x =
      polynomialValue acc v x + polynomialValue a v x * polynomialValue b v x := by
  induction a generalizing acc with
  | nil => simp [polynomialValue]
  | cons s aa ih =>
    have hs := ha s (by simp)
    have haa : validPolynomial aa := fun t ht => ha t (by simp [ht])
    have hr := multiplicationRow_valid s b hs hb
    simp only [List.foldl_cons]
    rw [ih _ haa (polyAdd_valid _ _ hc hr), polyAdd_value _ _ v x hc hr,
      multiplicationRow_value s b v x hs hb, polynomialValue_cons]
    ring

theorem polyMul_valid (a b : Polynomial) (ha : validPolynomial a) (hb : validPolynomial b) :
    validPolynomial (polyMul a b) := by
  by_cases h : a.length ≤ b.length
  · simp only [polyMul, ite_eq_left h]
    exact multiplicationFold_valid a b [] ha hb (by simp [validPolynomial])
  · simp only [polyMul, ite_eq_right h]
    exact multiplicationFold_valid b a [] hb ha (by simp [validPolynomial])

theorem polyMul_value (a b : Polynomial) (v x : ℝ)
    (ha : validPolynomial a) (hb : validPolynomial b) :
    polynomialValue (polyMul a b) v x = polynomialValue a v x * polynomialValue b v x := by
  by_cases h : a.length ≤ b.length
  · simp only [polyMul, ite_eq_left h]
    simpa only [multiplicationRow, polynomialValue_nil, zero_add] using
      multiplicationFold_value a b [] v x ha hb (by simp [validPolynomial])
  · simp only [polyMul, ite_eq_right h]
    simpa only [multiplicationRow, polynomialValue_nil, zero_add, mul_comm] using
      multiplicationFold_value b a [] v x hb ha (by simp [validPolynomial])

theorem polynomialValue_one (v x : ℝ) : polynomialValue [⟨0, 0, Fraction.one⟩] v x = 1 := by
  simp [polynomialValue, termValue, fractionValue_one]

theorem polyPow_valid (p : Polynomial) (n : Nat) (hp : validPolynomial p) :
    validPolynomial (polyPow p n) := by
  induction n with
  | zero => simp [polyPow, validPolynomial, Fraction.one, Fraction.ofInt]
  | succ n ih => exact polyMul_valid p (polyPow p n) hp ih

theorem polyPow_value (p : Polynomial) (n : Nat) (v x : ℝ) (hp : validPolynomial p) :
    polynomialValue (polyPow p n) v x = polynomialValue p v x ^ n := by
  induction n with
  | zero => simp [polyPow, polynomialValue_one]
  | succ n ih =>
    rw [polyPow, polyMul_value p _ v x hp (polyPow_valid p n hp), ih, pow_succ]
    ring

theorem polyEq_sound (a b : Polynomial) (v x : ℝ) (h : polyEq a b = true) :
    polynomialValue a v x = polynomialValue b v x := by
  induction a generalizing b with
  | nil =>
    have hl : 0 = b.length := by simpa [polyEq] using h
    have hb : b = [] := List.length_eq_zero_iff.mp hl.symm
    subst b
    rfl
  | cons s aa ih =>
    cases b with
    | nil => simp [polyEq] at h
    | cons t bb =>
      have hh : aa.length = bb.length ∧
          ((s.v = t.v ∧ s.x = t.x) ∧ Fraction.eq s.c t.c = true) ∧
          (aa.zip bb).all (fun (u,w) => u.v == w.v && u.x == w.x && Fraction.eq u.c w.c) = true := by
        simpa [polyEq] using h
      have ht : termValue s v x = termValue t v x := by
        simp only [termValue, hh.2.1.1.1, hh.2.1.1.2, fraction_eq_sound s.c t.c hh.2.1.2]
      have htail : polyEq aa bb = true := by simp [polyEq, hh.1, hh.2.2]
      simp only [polynomialValue_cons, ht, ih bb htail]

theorem polynomialScale_valid (p : Polynomial) (c : Fraction)
    (hp : validPolynomial p) (hc : 0 < c.den) :
    validPolynomial (p.map fun t => { t with c := Fraction.mul c t.c }) := by
  intro t ht
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ht
  exact fraction_mul_den_pos c s.c hc (hp s hs)

theorem polynomialScale_value (p : Polynomial) (c : Fraction) (v x : ℝ)
    (hp : validPolynomial p) (hc : 0 < c.den) :
    polynomialValue (p.map fun t => { t with c := Fraction.mul c t.c }) v x =
      fractionValue c * polynomialValue p v x := by
  induction p with
  | nil => simp [polynomialValue]
  | cons t pp ih =>
    have ht := hp t (by simp)
    have hpp : validPolynomial pp := fun s hs => hp s (by simp [hs])
    simp only [List.map_cons, polynomialValue_cons, ih hpp, termValue,
      fractionValue_mul c t.c hc ht]
    ring

theorem polyTimes_valid (p f : Polynomial) (n : Nat)
    (hp : validPolynomial p) (hf : validPolynomial f) : validPolynomial (polyTimes p f n) := by
  induction n generalizing p with
  | zero => exact hp
  | succ n ih => exact ih (polyMul p f) (polyMul_valid p f hp hf)

theorem polyTimes_value (p f : Polynomial) (n : Nat) (v x : ℝ)
    (hp : validPolynomial p) (hf : validPolynomial f) :
    polynomialValue (polyTimes p f n) v x =
      polynomialValue p v x * polynomialValue f v x ^ n := by
  induction n generalizing p with
  | zero => simp [polyTimes]
  | succ n ih =>
    rw [polyTimes, ih (polyMul p f) (polyMul_valid p f hp hf),
      polyMul_value p f v x hp hf, pow_succ]
    ring

theorem factorFold_valid (fs : List (Polynomial × Nat)) (acc : Polynomial)
    (hf : ∀ f ∈ fs, validPolynomial f.1) (ha : validPolynomial acc) :
    validPolynomial (fs.foldl (fun z f => polyTimes z f.1 f.2) acc) := by
  induction fs generalizing acc with
  | nil => exact ha
  | cons f fs ih =>
    exact ih _ (fun g hg => hf g (by simp [hg]))
      (polyTimes_valid acc f.1 f.2 ha (hf f (by simp)))

theorem factorFold_value (fs : List (Polynomial × Nat)) (acc : Polynomial) (v x : ℝ)
    (hf : ∀ f ∈ fs, validPolynomial f.1) (ha : validPolynomial acc) :
    polynomialValue (fs.foldl (fun z f => polyTimes z f.1 f.2) acc) v x =
      polynomialValue acc v x * (fs.map fun f => polynomialValue f.1 v x ^ f.2).prod := by
  induction fs generalizing acc with
  | nil => simp
  | cons f fs ih =>
    have hff := hf f (by simp)
    simp only [List.foldl_cons, List.map_cons, List.prod_cons]
    rw [ih _ (fun g hg => hf g (by simp [hg])) (polyTimes_valid acc f.1 f.2 ha hff),
      polyTimes_value acc f.1 f.2 v x ha hff]
    ring

theorem factorCheck_sound (p : Polynomial) (c : Fraction) (fs : List (Polynomial × Nat))
    (v x : ℝ) (hc : 0 < c.den) (hf : ∀ f ∈ fs, validPolynomial f.1)
    (hcheck : factorCheck p c fs = true) :
    polynomialValue p v x =
      fractionValue c * (fs.map fun f => polynomialValue f.1 v x ^ f.2).prod := by
  have hone : validPolynomial [⟨0, 0, Fraction.one⟩] := by
    simp [validPolynomial, Fraction.one, Fraction.ofInt]
  have hvalue := polyEq_sound _ _ v x hcheck
  rw [polynomialScale_value _ c v x (factorFold_valid fs _ hf hone) hc,
    factorFold_value fs _ v x hf hone, polynomialValue_one, one_mul] at hvalue
  exact hvalue

theorem factorProduct_positive (fs : List (Polynomial × Nat)) (v x : ℝ)
    (hf : ∀ f ∈ fs, 0 < polynomialValue f.1 v x) :
    0 < (fs.map fun f => polynomialValue f.1 v x ^ f.2).prod := by
  induction fs with
  | nil => simp
  | cons f fs ih =>
    simp only [List.map_cons, List.prod_cons]
    exact mul_pos (pow_pos (hf f (by simp)) f.2) (ih (fun g hg => hf g (by simp [hg])))

theorem factorCheck_positive (p : Polynomial) (c : Fraction) (fs : List (Polynomial × Nat))
    (v x : ℝ) (hc : Fraction.positive c = true) (hf : ∀ f ∈ fs, validPolynomial f.1)
    (hpos : ∀ f ∈ fs, 0 < polynomialValue f.1 v x)
    (hcheck : factorCheck p c fs = true) : 0 < polynomialValue p v x := by
  have hden : 0 < c.den := by
    have h : 0 < c.den ∧ 0 < c.num := by simpa [Fraction.positive] using hc
    exact h.1
  rw [factorCheck_sound p c fs v x hden hf hcheck]
  exact mul_pos (fraction_positive_sound c hc) (factorProduct_positive fs v x hpos)

end F4Heavy.Analysis
