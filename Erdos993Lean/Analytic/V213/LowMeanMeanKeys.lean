module

public import Erdos993Lean.Analytic.V213.LowMeanCertificateFacts

/-!
Table 4 is keyed by certificate and lower/upper side. The kernel
checks each selected record's certificate fields and key, then its exact
formula, so the two-column printed table is not interpreted by row position.
-/

@[expose] public section

namespace Erdos993Lean.Analytic.V213

def lowMeanMeanKeyRecord (number : ℕ) (lower : Bool) :
    LowMeanCertificateInput × LowMeanIntegerExpr × lowMeanFraction × Bool × ℕ :=
  (lowMeanMeanRecords.find? (fun r => decide (r.2.2.2.2 = number) && decide (r.2.2.2.1 = lower))).getD (lowMeanMeanAt 0)

noncomputable def lowMeanCertificateLowerValue (c : LowMeanCertificateInput) (number : ℕ) : ℝ :=
  if number = 1 then lowMeanCertificateCurvedEndpoint c c.h (51356, 53625)
  else if number = 2 then lowMeanCertificateCurvedEndpoint c c.h (3823, 4125)
  else if number = 24 then lowMeanCertificateCurvedEndpoint c c.l (3998483, 5557500)
  else lowMeanCertificateRationalMargin c (lowMeanFractionReal c.muA)

def lowMeanMeanKeyCheck (i : ℕ) : Bool :=
  let lo := lowMeanMeanKeyRecord (i + 1) true
  let up := lowMeanMeanKeyRecord (i + 1) false
  decide (lo.1 = lowMeanCertificateAt i ∧ lo.2.2.2.1 = true ∧ lo.2.2.2.2 = i + 1 ∧
    up.1 = lowMeanCertificateAt i ∧ up.2.2.2.1 = false ∧ up.2.2.2.2 = i + 1) &&
    lowMeanIntegerPositiveCheck lo.2.1 (lowMeanMeanRecordShape lo) (1, 5000) &&
    lowMeanIntegerPositiveCheck up.2.1 (lowMeanMeanRecordShape up) (1, 5000)

theorem lowMean_meanKeys_kernel : (List.range 28).all lowMeanMeanKeyCheck = true := by
  decide +kernel

/-- Both Table 4 endpoints for each certificate, with the three eq63
curved lower formulas retained exactly. -/
theorem lowMean_meanKey_bounds (i : ℕ) (hi : i < 28) :
    (1 / 5000 : ℝ) < lowMeanCertificateLowerValue (lowMeanCertificateAt i) (i + 1) ∧
      (1 / 5000 : ℝ) < lowMeanCertificateRationalMargin (lowMeanCertificateAt i)
        (lowMeanFractionReal (lowMeanCertificateAt i).muB) := by
  have h := Erdos993Lean.F4Fast.forall_lt_of_range_all lowMean_meanKeys_kernel i hi
  simp only [lowMeanMeanKeyCheck, Bool.and_eq_true, decide_eq_true_eq] at h
  have hlo := lowMean_integerPositive_sound h.1.2
  have hup := lowMean_integerPositive_sound h.2
  have hk := h.1.1
  rw [lowMean_meanRecord_shape_real] at hlo hup
  constructor
  · simpa [lowMeanFractionReal, lowMeanMeanRecordValue, lowMeanCertificateLowerValue, hk.1, hk.2.1, hk.2.2.1] using hlo
  · simpa [lowMeanFractionReal, lowMeanMeanRecordValue, hk.2.2.2.1, hk.2.2.2.2.1, hk.2.2.2.2.2] using hup

end Erdos993Lean.Analytic.V213

#print axioms Erdos993Lean.Analytic.V213.lowMean_meanKey_bounds
