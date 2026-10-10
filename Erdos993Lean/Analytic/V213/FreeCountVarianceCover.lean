module

public import Erdos993Lean.ExactComparisons.F3All.Formulas
public import Mathlib

/-!
The continuous interpretation of the *existing*
ordered-cover Boolean.  No finite cover, point record, or comparison is
evaluated here.  Both ends of every interval are included.  In particular,
the empty suffix of coverFrom is not mistaken for a nonempty cover.
-/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.FreeCountVariance.Certificates

open Erdos993Lean.ExactComparisons.F3All

theorem coverFrom_endpoints {lo hi : Rat} {rows : List (Rat × Rat)}
    (hc : coverFrom hi lo rows = true) : lo ≤ hi := by
  induction rows generalizing lo with
  | nil =>
      have h : lo = hi := by simpa only [coverFrom, decide_eq_true_eq] using hc
      exact h.le
  | cons ab rest ih =>
      rcases ab with ⟨a, b⟩
      have h : (a = lo ∧ a < b) ∧ coverFrom hi b rest = true := by
        simpa only [coverFrom, Bool.and_eq_true, decide_eq_true_eq] using hc
      have hab : lo ≤ b := by simpa only [h.1.1] using h.1.2.le
      exact hab.trans (ih h.2)

theorem coverFrom_strict_endpoints {lo hi : Rat} {rows : List (Rat × Rat)}
    (hne : rows ≠ []) (hc : coverFrom hi lo rows = true) : lo < hi := by
  cases rows with
  | nil => exact (hne rfl).elim
  | cons ab rest =>
      rcases ab with ⟨a, b⟩
      have h : (a = lo ∧ a < b) ∧ coverFrom hi b rest = true := by
        simpa only [coverFrom, Bool.and_eq_true, decide_eq_true_eq] using hc
      have hab : lo < b := by simpa only [h.1.1] using h.1.2
      exact hab.trans_le (coverFrom_endpoints h.2)

/-- A nonempty successful ordered chain covers its entire closed Real span. -/
theorem coverFrom_covers_real {lo hi : Rat} {rows : List (Rat × Rat)}
    (hne : rows ≠ []) (hc : coverFrom hi lo rows = true)
    {x : ℝ} (hxlo : (lo : ℝ) ≤ x) (hxhi : x ≤ (hi : ℝ)) :
    ∃ ab ∈ rows, (ab.1 : ℝ) ≤ x ∧ x ≤ (ab.2 : ℝ) := by
  induction rows generalizing lo with
  | nil => exact (hne rfl).elim
  | cons ab rest ih =>
      rcases ab with ⟨a, b⟩
      have h : (a = lo ∧ a < b) ∧ coverFrom hi b rest = true := by
        simpa only [coverFrom, Bool.and_eq_true, decide_eq_true_eq] using hc
      by_cases hxb : x ≤ (b : ℝ)
      · refine ⟨(a, b), by simp, ?_, hxb⟩
        simpa only [h.1.1] using hxlo
      · have hbx : (b : ℝ) < x := lt_of_not_ge hxb
        have hrest : rest ≠ [] := by
          intro he
          have hlast : b = hi := by
            simpa only [he, coverFrom, decide_eq_true_eq] using h.2
          exact (not_lt_of_ge hxhi) (by simpa only [hlast] using hbx)
        obtain ⟨cd, hcd, hbounds⟩ := ih hrest h.2 hbx.le
        exact ⟨cd, List.mem_cons_of_mem _ hcd, hbounds⟩

theorem coverOK_parts {lo hi : Rat} {rows : List (Rat × Rat)}
    (hc : coverOK lo hi rows = true) :
    rows ≠ [] ∧ coverFrom hi lo rows = true := by
  have h : Bool.not rows.isEmpty = true ∧ coverFrom hi lo rows = true := by
    simpa only [coverOK, Bool.and_eq_true] using hc
  refine ⟨?_, h.2⟩
  intro he
  simpa [he] using h.1

theorem coverOK_covers_real {lo hi : Rat} {rows : List (Rat × Rat)}
    (hc : coverOK lo hi rows = true)
    {x : ℝ} (hxlo : (lo : ℝ) ≤ x) (hxhi : x ≤ (hi : ℝ)) :
    ∃ ab ∈ rows, (ab.1 : ℝ) ≤ x ∧ x ≤ (ab.2 : ℝ) := by
  obtain ⟨hne, hfrom⟩ := coverOK_parts hc
  exact coverFrom_covers_real hne hfrom hxlo hxhi

/-- This is only a local-to-global rule: each local analytic proof is explicit. -/
theorem coverOK_property {lo hi : Rat} {rows : List (Rat × Rat)}
    (hc : coverOK lo hi rows = true) {P : ℝ → Prop}
    (hlocal : ∀ ab ∈ rows, ∀ x : ℝ, (ab.1 : ℝ) ≤ x → x ≤ (ab.2 : ℝ) → P x)
    {x : ℝ} (hxlo : (lo : ℝ) ≤ x) (hxhi : x ≤ (hi : ℝ)) : P x := by
  obtain ⟨ab, hab, hx⟩ := coverOK_covers_real hc hxlo hxhi
  exact hlocal ab hab x hx.1 hx.2

/-- Record endpoints can be projected without discarding the original record. -/
theorem coverOK_record {R : Type*} (left right : R → Rat) (records : List R)
    {lo hi : Rat}
    (hc : coverOK lo hi (records.map (fun r => (left r, right r))) = true)
    {x : ℝ} (hxlo : (lo : ℝ) ≤ x) (hxhi : x ≤ (hi : ℝ)) :
    ∃ r ∈ records, (left r : ℝ) ≤ x ∧ x ≤ (right r : ℝ) := by
  obtain ⟨ab, hab, hx⟩ := coverOK_covers_real hc hxlo hxhi
  obtain ⟨r, hr, he⟩ := List.mem_map.mp hab
  refine ⟨r, hr, ?_⟩
  simpa only [← he] using hx

/-- Two independently checked ordered covers give a closed rectangular cover. -/
theorem coverOK_rectangle {alo ahi blo bhi : Rat}
    {xs ys : List (Rat × Rat)}
    (hxs : coverOK alo ahi xs = true) (hys : coverOK blo bhi ys = true)
    {x y : ℝ} (hxlo : (alo : ℝ) ≤ x) (hxhi : x ≤ (ahi : ℝ))
    (hylo : (blo : ℝ) ≤ y) (hyhi : y ≤ (bhi : ℝ)) :
    ∃ ab ∈ xs, ∃ cd ∈ ys,
      ((ab.1 : ℝ) ≤ x ∧ x ≤ (ab.2 : ℝ)) ∧
      ((cd.1 : ℝ) ≤ y ∧ y ≤ (cd.2 : ℝ)) := by
  obtain ⟨ab, hab, hx⟩ := coverOK_covers_real hxs hxlo hxhi
  obtain ⟨cd, hcd, hy⟩ := coverOK_covers_real hys hylo hyhi
  exact ⟨ab, hab, cd, hcd, hx, hy⟩

end Erdos993Lean.Analytic.V213.FreeCountVariance.Certificates

-- Type and axiom audit commands.
#check Erdos993Lean.Analytic.V213.FreeCountVariance.Certificates.coverFrom_endpoints
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.Certificates.coverFrom_endpoints
#check Erdos993Lean.Analytic.V213.FreeCountVariance.Certificates.coverFrom_strict_endpoints
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.Certificates.coverFrom_strict_endpoints
#check Erdos993Lean.Analytic.V213.FreeCountVariance.Certificates.coverFrom_covers_real
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.Certificates.coverFrom_covers_real
#check Erdos993Lean.Analytic.V213.FreeCountVariance.Certificates.coverOK_parts
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.Certificates.coverOK_parts
#check Erdos993Lean.Analytic.V213.FreeCountVariance.Certificates.coverOK_covers_real
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.Certificates.coverOK_covers_real
#check Erdos993Lean.Analytic.V213.FreeCountVariance.Certificates.coverOK_property
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.Certificates.coverOK_property
#check Erdos993Lean.Analytic.V213.FreeCountVariance.Certificates.coverOK_record
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.Certificates.coverOK_record
#check Erdos993Lean.Analytic.V213.FreeCountVariance.Certificates.coverOK_rectangle
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.Certificates.coverOK_rectangle
