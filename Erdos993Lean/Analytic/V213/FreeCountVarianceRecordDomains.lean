module

public import Erdos993Lean.Analytic.V213.FreeCountVarianceCover

/-!
These are semantic decoders of the actual F3All
record guards, not new checks of any finite record.  The separate A-row
m-range guard is deliberately not inferred from aRowOK.  No conclusion
about CA, AC, a logarithm enclosure, or the full variance curve occurs here.
-/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.FreeCountVariance.Certificates

open Erdos993Lean.ExactComparisons.F3All

/-- Extract a particular Boolean from an explicitly supplied checked list. -/
theorem bool_record_true {records : List Bool} (hall : records.all id = true)
    {b : Bool} (hb : b ∈ records) : b = true := by
  exact (List.all_eq_true.mp hall) b hb

theorem pointOK_coordinates {p : Point} (h : pointOK p = true) :
    p.f.lam = p.b.lam ∧ p.f.y = p.e.y := by
  exact of_decide_eq_true h

theorem pointOK_coordinates_real {p : Point} (h : pointOK p = true) :
    (p.f.lam : ℝ) = (p.b.lam : ℝ) ∧ (p.f.y : ℝ) = (p.e.y : ℝ) := by
  exact_mod_cast pointOK_coordinates h

theorem expUseOK_domain {y : Rat} (h : expUseOK y = true) :
    (0 : ℝ) ≤ y ∧ (y : ℝ) ≤ 3 := by
  have hr : 0 ≤ y ∧ y ≤ 3 := of_decide_eq_true h
  exact_mod_cast hr

theorem logUseOK_domain {z : Rat} (h : logUseOK z = true) :
    (1 : ℝ) ≤ z ∧ (z : ℝ) < 8 := by
  have hr : 1 ≤ z ∧ z < 8 := of_decide_eq_true h
  exact_mod_cast hr

theorem capRightOK_pairs {D u : Rat} (h : capRightOK D u = true) :
    (D = 6/5 ∧ u = 263/200) ∨ (D = 7/5 ∧ u = 3/2) ∨
    (D = 8/5 ∧ u = 7/4) ∨ (D = 9/5 ∧ u = 2) ∨
    (D = 21/10 ∧ u = 7/3) := by
  exact of_decide_eq_true h

theorem capRightOK_pairs_real {D u : Rat} (h : capRightOK D u = true) :
    ((D : ℝ) = 6/5 ∧ (u : ℝ) = 263/200) ∨
    ((D : ℝ) = 7/5 ∧ (u : ℝ) = 3/2) ∨
    ((D : ℝ) = 8/5 ∧ (u : ℝ) = 7/4) ∨
    ((D : ℝ) = 9/5 ∧ (u : ℝ) = 2) ∨
    ((D : ℝ) = 21/10 ∧ (u : ℝ) = 7/3) := by
  rcases capRightOK_pairs h with h | h | h | h | h <;>
    rcases h with ⟨rfl, rfl⟩ <;> norm_num

theorem capRightOK_positive {D u : Rat} (h : capRightOK D u = true) :
    (0 : ℝ) < D ∧ (5/4 : ℝ) < u ∧ (u : ℝ) ≤ 7/3 := by
  rcases capRightOK_pairs_real h with h | h | h | h | h <;>
    rcases h with ⟨hD, hu⟩ <;> rw [hD, hu] <;> norm_num

theorem cRowOK_parts {r : CRow} (h : cRowOK r = true) :
    pointOK r.left = true ∧ pointOK r.right = true ∧
    capRightOK r.D r.left.b.lam = true ∧
    (r.left.b.lam = r.right.b.lam ∧ 0 ≤ r.left.e.y ∧
      r.left.e.y < r.right.e.y ∧ r.right.e.y ≤ 5/4) := by
  simpa only [cRowOK, Bool.and_eq_true, decide_eq_true_eq, and_assoc] using h

theorem cRowOK_domain_real {r : CRow} (h : cRowOK r = true) :
    (r.left.b.lam : ℝ) = (r.right.b.lam : ℝ) ∧
    (0 : ℝ) ≤ r.left.e.y ∧ (r.left.e.y : ℝ) < r.right.e.y ∧
    (r.right.e.y : ℝ) ≤ 5/4 := by
  have hr : (r.left.b.lam : ℝ) = (r.right.b.lam : ℝ) ∧
      (0 : ℝ) ≤ r.left.e.y ∧ (r.left.e.y : ℝ) < r.right.e.y ∧
      (r.right.e.y : ℝ) ≤ ((5/4 : Rat) : ℝ) := by
    exact_mod_cast (cRowOK_parts h).2.2.2
  simpa only [Rat.cast_div, Rat.cast_ofNat] using hr

theorem aRowOK_parts {r : ARow} (h : aRowOK r = true) :
    pointOK r.ac = true ∧ pointOK r.ad = true ∧ pointOK r.bd = true ∧
    (0 < r.D ∧ 1/3 ≤ r.ac.b.lam ∧ r.ac.b.lam < r.bd.b.lam ∧ r.bd.b.lam ≤ 7/3 ∧
      r.ad.b.lam = r.ac.b.lam ∧ r.ad.e.y = r.bd.e.y ∧
      0 ≤ r.ac.e.y ∧ r.ac.e.y < r.bd.e.y ∧ r.bd.e.y ≤ 3 ∧
      r.mid.y = (r.ac.e.y + r.bd.e.y)/2) := by
  simpa only [aRowOK, Bool.and_eq_true, decide_eq_true_eq, and_assoc] using h

theorem aRowOK_domain_real {r : ARow} (h : aRowOK r = true) :
    (0 : ℝ) < r.D ∧ (1/3 : ℝ) ≤ r.ac.b.lam ∧
    (r.ac.b.lam : ℝ) < r.bd.b.lam ∧ (r.bd.b.lam : ℝ) ≤ 7/3 ∧
    (r.ad.b.lam : ℝ) = r.ac.b.lam ∧ (r.ad.e.y : ℝ) = r.bd.e.y ∧
    (0 : ℝ) ≤ r.ac.e.y ∧ (r.ac.e.y : ℝ) < r.bd.e.y ∧ (r.bd.e.y : ℝ) ≤ 3 ∧
    (r.mid.y : ℝ) = ((r.ac.e.y : ℝ) + r.bd.e.y)/2 := by
  have hr : (0 : ℝ) < r.D ∧ ((1/3 : Rat) : ℝ) ≤ r.ac.b.lam ∧
      (r.ac.b.lam : ℝ) < r.bd.b.lam ∧ (r.bd.b.lam : ℝ) ≤ ((7/3 : Rat) : ℝ) ∧
      (r.ad.b.lam : ℝ) = r.ac.b.lam ∧ (r.ad.e.y : ℝ) = r.bd.e.y ∧
      (0 : ℝ) ≤ r.ac.e.y ∧ (r.ac.e.y : ℝ) < r.bd.e.y ∧ (r.bd.e.y : ℝ) ≤ 3 ∧
      (r.mid.y : ℝ) = ((r.ac.e.y : ℝ) + r.bd.e.y)/2 := by
    exact_mod_cast (aRowOK_parts h).2.2.2
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_one] using hr

/-- The printed m-range is a separate guard, absent from aRowOK. -/
theorem m_range_real {m : Rat} (h : decide (0 ≤ m ∧ m ≤ 49/100) = true) :
    (0 : ℝ) ≤ m ∧ (m : ℝ) ≤ 49/100 := by
  have hr : 0 ≤ m ∧ m ≤ 49/100 := of_decide_eq_true h
  have hc : (0 : ℝ) ≤ m ∧ (m : ℝ) ≤ ((49/100 : Rat) : ℝ) := by
    exact_mod_cast hr
  simpa only [Rat.cast_div, Rat.cast_ofNat] using hc

theorem epsilon_pos_of_range {m : ℝ} (hm0 : 0 ≤ m) (hm1 : m ≤ 49/100) :
    0 < 7/12 - (12/5)*m^2 := by
  have hs := mul_nonneg (sub_nonneg.mpr hm1)
    (add_nonneg (show (0 : ℝ) ≤ 49/100 by norm_num) hm0)
  nlinarith

theorem cellEpsilon_pos {r : ARow}
    (hm : decide (0 ≤ r.m ∧ r.m ≤ 49/100) = true) :
    (0 : ℝ) < cellEpsilon r := by
  have h := m_range_real hm
  have hp := epsilon_pos_of_range h.1 h.2
  simpa only [cellEpsilon, Rat.cast_sub, Rat.cast_div, Rat.cast_mul,
    Rat.cast_pow, Rat.cast_ofNat] using hp

end Erdos993Lean.Analytic.V213.FreeCountVariance.Certificates

-- Type and axiom audit commands.
#check Erdos993Lean.Analytic.V213.FreeCountVariance.Certificates.bool_record_true
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.Certificates.bool_record_true
#check Erdos993Lean.Analytic.V213.FreeCountVariance.Certificates.pointOK_coordinates
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.Certificates.pointOK_coordinates
#check Erdos993Lean.Analytic.V213.FreeCountVariance.Certificates.pointOK_coordinates_real
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.Certificates.pointOK_coordinates_real
#check Erdos993Lean.Analytic.V213.FreeCountVariance.Certificates.expUseOK_domain
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.Certificates.expUseOK_domain
#check Erdos993Lean.Analytic.V213.FreeCountVariance.Certificates.logUseOK_domain
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.Certificates.logUseOK_domain
#check Erdos993Lean.Analytic.V213.FreeCountVariance.Certificates.capRightOK_pairs
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.Certificates.capRightOK_pairs
#check Erdos993Lean.Analytic.V213.FreeCountVariance.Certificates.capRightOK_pairs_real
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.Certificates.capRightOK_pairs_real
#check Erdos993Lean.Analytic.V213.FreeCountVariance.Certificates.capRightOK_positive
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.Certificates.capRightOK_positive
#check Erdos993Lean.Analytic.V213.FreeCountVariance.Certificates.cRowOK_parts
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.Certificates.cRowOK_parts
#check Erdos993Lean.Analytic.V213.FreeCountVariance.Certificates.cRowOK_domain_real
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.Certificates.cRowOK_domain_real
#check Erdos993Lean.Analytic.V213.FreeCountVariance.Certificates.aRowOK_parts
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.Certificates.aRowOK_parts
#check Erdos993Lean.Analytic.V213.FreeCountVariance.Certificates.aRowOK_domain_real
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.Certificates.aRowOK_domain_real
#check Erdos993Lean.Analytic.V213.FreeCountVariance.Certificates.m_range_real
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.Certificates.m_range_real
#check Erdos993Lean.Analytic.V213.FreeCountVariance.Certificates.epsilon_pos_of_range
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.Certificates.epsilon_pos_of_range
#check Erdos993Lean.Analytic.V213.FreeCountVariance.Certificates.cellEpsilon_pos
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.Certificates.cellEpsilon_pos
