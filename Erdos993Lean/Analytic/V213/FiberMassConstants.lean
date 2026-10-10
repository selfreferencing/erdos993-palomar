module

public import Erdos993Lean.Analytic.V213.FiberMassData

/-!
Reviewed F01: all six strict scalar comparisons in the three printed
Eq74 rows. Positive denominators and Int products are kernel-checked with
`List.range.all`, then consumed through the accepted F4Fast range lemma.
These are scalar bounds, separate from all-real mass-window completeness.
-/

@[expose] public section

namespace Erdos993Lean.Analytic.V213

theorem fiber_mass_bound_checks :
    (List.range 3).all (fun k => fiberMassBoundCheck (fiberMassBoundById (fiberMassIdentityAt k))) = true := by
  decide +kernel

theorem fiber_mass_bound_checked {k : ℕ} (hk : k < 3) :
    fiberMassBoundCheck (fiberMassBoundById (fiberMassIdentityAt k)) = true :=
  Erdos993Lean.F4Fast.forall_lt_of_range_all fiber_mass_bound_checks k hk

theorem fiber_mass_named_identity_checked (id : FiberMassIdentity) :
    fiberMassBoundCheck (fiberMassBoundById id) = true := by
  cases id with
  | w1_n14 => exact fiber_mass_bound_checked (k := 0) (by decide +kernel)
  | w15_n22 => exact fiber_mass_bound_checked (k := 1) (by decide +kernel)
  | w15_n32 => exact fiber_mass_bound_checked (k := 2) (by decide +kernel)

theorem fiber_mass_identity_bindings :
    (fiberMassBoundById .w1_n14).minimumN = 14 ∧
    (fiberMassBoundById .w1_n14).window = (1, 1) ∧
    (fiberMassBoundById .w15_n22).minimumN = 22 ∧
    (fiberMassBoundById .w15_n22).window = (3, 2) ∧
    (fiberMassBoundById .w15_n32).minimumN = 32 ∧
    (fiberMassBoundById .w15_n32).window = (3, 2) := by
  decide +kernel

theorem fiber_mass_bound_sound {x : FiberMassBoundRow}
    (h : fiberMassBoundCheck x = true) :
    max (lowMeanFractionReal x.left) (lowMeanFractionReal x.right) <
      lowMeanFractionReal x.bound := by
  unfold fiberMassBoundCheck at h
  have hdata := of_decide_eq_true h
  have hc : lowMeanFractionValid x.left ∧ lowMeanFractionValid x.right ∧
      lowMeanFractionValid x.bound ∧ lowMeanFractionLT x.left x.bound ∧
      lowMeanFractionLT x.right x.bound := hdata
  exact max_lt_iff.mpr ⟨(lowMean_fraction_lt_iff hc.1 hc.2.2.1).mp hc.2.2.2.1,
    (lowMean_fraction_lt_iff hc.2.1 hc.2.2.1).mp hc.2.2.2.2⟩

theorem fiber_mass_constants_w1 :
    max (4802 / 14641 : ℝ) (25 / 81) < 1 / 3 := by
  have h := fiber_mass_bound_sound (fiber_mass_named_identity_checked .w1_n14)
  simpa [fiberMassBoundById, lowMeanFractionReal] using h

theorem fiber_mass_constants_w15_n22_reduced :
    max (1476225 / 70860608 : ℝ) (23 / 1008) < 1 / 40 := by
  have h := fiber_mass_bound_sound (fiber_mass_named_identity_checked .w15_n22)
  simpa [fiberMassBoundById, lowMeanFractionReal] using h

theorem fiber_mass_constants_w15_n32 :
    max (4096 / (297 * 1025) : ℝ) (9604 / (297 * 2147)) < 1 / 60 := by
  have h := fiber_mass_bound_sound (fiber_mass_named_identity_checked .w15_n32)
  have hl : (297 * 1025 : ℝ) = 304425 := by
    exact_mod_cast (by decide +kernel : (297 : ℕ) * 1025 = 304425)
  have hr : (297 * 2147 : ℝ) = 637659 := by
    exact_mod_cast (by decide +kernel : (297 : ℕ) * 2147 = 637659)
  rw [hl, hr]
  simpa [fiberMassBoundById, lowMeanFractionReal] using h

end Erdos993Lean.Analytic.V213
