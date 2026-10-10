module

public import Erdos993Lean.Analytic.V213.FreeCountVarianceCaps
public import Erdos993Lean.Analytic.Reserve.Assembly

/-!
Current Section 3 forest assembly, conditional on the explicit actual local
comparisons. The reserve coefficients are exactly
the current alpha, zero signed coefficient, and current gamma. This file
constructs its own StepCert; it does not use an old Band, completed variance
curve, Profile30, or a named unproved current-paper theorem.

The reused generic graph induction includes Cauchy--Schwarz on the actual
grandchild list, the selected-child t=0 case, isolated components and edges,
root nonnegativity, and component additivity.

-/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.FreeCountVariance

open Finset

section FixedActivity

variable {D lam : ℝ} (hD : 0<D) (hlam : 0<lam)
variable (hZ : ∀ t y : ℝ, 0≤t → logMass lam t≤y → 0<Z D lam t y)
variable (hCC : ∀ t y : ℝ, 0≤t → logMass lam t≤y → 0≤CC D lam t y)
variable (hCA : ∀ t y : ℝ, 0≤t → logMass lam t≤y → 0≤CA D lam t y)
variable (hAC : ∀ t y : ℝ, 0≤t → logMass lam t≤y → 0≤AC D lam t y)

include hD hlam hZ hCC hCA hAC

/-- The current leaf equality and the actual four local inequalities give the
generic per-activity certificate. Every local hypothesis includes t=0. -/
theorem stepCert_of_feasible_comparisons :
    Reserve.StepCert (gamma D lam) lam (alpha D lam) 0 (capA D lam) := by
  refine ⟨hlam, (alpha_pos hD hlam).le, gamma_pos hD hlam, ?_, ?_, ?_⟩
  · have hp := mul_pos (alpha_pos hD hlam) (gamma_pos hD hlam)
    nlinarith
  · change alpha D lam*logMass lam 0 + 0*message lam 0 +
        gamma D lam*message lam 0^2/logMass lam 0 ≤
      capA D lam*message lam 0-message lam 0*(1-message lam 0)
    simpa only [message_zero, logMass_zero, zero_mul, add_zero, reserve] using
      (selected_leaf_reserve (D := D) hlam).le
  · intro t y ht hy
    change logMass lam t≤y at hy
    refine ⟨?_, ?_, ?_, ?_⟩
    · exact (Z_eq_cZ D lam t y) ▸ hZ t y ht hy
    · exact (CC_eq_compCC D lam t y) ▸ hCC t y ht hy
    · exact (CA_eq_compCB D lam t y) ▸ hCA t y ht hy
    · exact (AC_eq_compBC D lam t y) ▸ hAC t y ht hy

section Graph

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- The literal current reserve inequality on every good rooted subtree. -/
theorem reserve_le_root_surplus (hG : G.IsAcyclic) {B : Finset V}
    (hB : Erdos993Lean.IsIndepFinset G B) (s : Finset V) (r : V)
    (hs : Erdos993Lean.ConnectedIn G s) (hr : r∈s) (hgood : Reserve.Good G B s r) :
    reserve D lam (Reserve.yLog G lam s r) (Reserve.port G B lam s r) ≤
      capA D lam*Reserve.meanB G B lam s-Reserve.varB G B lam s := by
  have hc := stepCert_of_feasible_comparisons hD hlam hZ hCC hCA hAC
  have hh := Reserve.reserveAt_of_good hG hB hc s r hs hr hgood
  simpa only [Reserve.ReserveAt, Reserve.resF, zero_mul, add_zero, reserve] using hh

/-- Component roots, including the no-selected-vertex and singleton cases. -/
theorem selected_variance_le_component (hG : G.IsAcyclic) {B K : Finset V}
    (hB : Erdos993Lean.IsIndepFinset G B) (hleaf : Reserve.LeafProp G B)
    (hK : Erdos993Lean.ConnectedIn G K) (hclosed : ∀ v∈K, ∀ w, G.Adj v w → w∈K) :
    Reserve.varB G B lam K ≤ capA D lam*Reserve.meanB G B lam K :=
  Reserve.varB_le_of_component hG hB hleaf
    (stepCert_of_feasible_comparisons hD hlam hZ hCC hCA hAC) hK hclosed

/-- Component additivity on an arbitrary closed finite vertex set. -/
theorem selected_variance_le_closed (hG : G.IsAcyclic) {B : Finset V}
    (hB : Erdos993Lean.IsIndepFinset G B) (hleaf : Reserve.LeafProp G B)
    (s : Finset V) (hclosed : ∀ v∈s, ∀ w, G.Adj v w → w∈s) :
    Reserve.varB G B lam s ≤ capA D lam*Reserve.meanB G B lam s :=
  Reserve.varB_le_of_closed hG hB hleaf
    (stepCert_of_feasible_comparisons hD hlam hZ hCC hCA hAC) s hclosed

end Graph

/-- The selected-count half of the current forest statement. -/
theorem selected_variance_le_of_feasible_comparisons (F : FiniteForest)
    {B : Finset (Fin F.n)} (hB : F.graph.IsIndepSet (B : Set (Fin F.n)))
    (hleaf : Reserve.LeafProp F.graph B) :
    HardCore.varKB F lam B ≤ capA D lam*weightW F lam B :=
  Reserve.varKB_le_of_stepCert F hB hleaf
    (stepCert_of_feasible_comparisons hD hlam hZ hCC hCA hAC)

/-- The actual free-count variance, from the mixture identities. -/
theorem free_variance_le_of_feasible_comparisons (F : FiniteForest)
    {B : Finset (Fin F.n)} (hB : F.graph.IsIndepSet (B : Set (Fin F.n)))
    (hleaf : Reserve.LeafProp F.graph B) :
    (forestMixture F B lam).varM ≤ D*(forestMixture F B lam).meanM := by
  have hc := stepCert_of_feasible_comparisons hD hlam hZ hCC hCA hAC
  have hc' : Reserve.StepCert (gamma D lam) lam (alpha D lam) 0
      (1+(D-1)*actQ lam) := by
    simpa only [capA, q, actQ] using hc
  exact Reserve.varM_le_of_stepCert F hB hleaf hc'

end FixedActivity

section ClosedCap

variable {c : Cap} {lam : ℝ} (hc : c.Contains lam)
variable (hJ : ∀ t y : ℝ, 0≤t → logMass lam t≤y → J lam t<c.jBound)
variable (hell : ∀ t y : ℝ, 0≤t → logMass lam t≤y → -c.eta<ell c.value lam y)
variable (hCC : ∀ t y : ℝ, 0≤t → logMass lam t≤y → 0≤CC c.value lam t y)
variable (hCA : ∀ t y : ℝ, 0≤t → logMass lam t≤y → 0≤CA c.value lam t y)
variable (hAC : ∀ t y : ℝ, 0≤t → logMass lam t≤y → 0≤AC c.value lam t y)

include hc hJ hell

/-- Z positivity is derived here from the literal J and ell bounds; it is not
silently included as an extra completed analytic claim. -/
theorem Z_pos_of_cap_feasible_bounds {t y : ℝ} (ht : 0≤t) (hy : logMass lam t≤y) :
    0<Z c.value lam t y := by
  have hz := Cap.denominator_of_two_bounds hc ht (hJ t y ht hy) (hell t y ht hy)
  have hp := message_pos (Cap.activity_pos hc) y
  have hg := gamma_pos c.value_pos (Cap.activity_pos hc)
  have hbase : 0<(3/4:ℝ)*message lam y*gamma c.value lam := by positivity
  exact hbase.trans hz

include hCC hCA hAC

theorem cap_stepCert_of_feasible_comparisons :
    Reserve.StepCert (gamma c.value lam) lam (alpha c.value lam) 0 (capA c.value lam) :=
  stepCert_of_feasible_comparisons c.value_pos (Cap.activity_pos hc)
    (fun _ _ ht hy => Z_pos_of_cap_feasible_bounds hc hJ hell ht hy) hCC hCA hAC

/-- A closed cap proves both current graph conclusions once its actual local
inequalities have been supplied on the full feasible domain. -/
theorem forest_variances_le_closed_cap (F : FiniteForest) {B : Finset (Fin F.n)}
    (hB : F.graph.IsIndepSet (B : Set (Fin F.n))) (hleaf : Reserve.LeafProp F.graph B) :
    HardCore.varKB F lam B ≤ capA c.value lam*weightW F lam B ∧
      (forestMixture F B lam).varM ≤ c.value*(forestMixture F B lam).meanM := by
  have hz : ∀ t y : ℝ, 0≤t → logMass lam t≤y → 0<Z c.value lam t y :=
    fun _ _ ht hy => Z_pos_of_cap_feasible_bounds hc hJ hell ht hy
  exact ⟨selected_variance_le_of_feasible_comparisons c.value_pos (Cap.activity_pos hc)
      hz hCC hCA hAC F hB hleaf,
    free_variance_le_of_feasible_comparisons c.value_pos (Cap.activity_pos hc)
      hz hCC hCA hAC F hB hleaf⟩

/-- Leaf selection is proved by the actual maximum-marginal-weight property. -/
theorem maxWeight_variances_le_closed_cap (F : FiniteForest) {B : Finset (Fin F.n)}
    (hB : IsMaxWeight F lam B) :
    HardCore.varKB F lam B ≤ capA c.value lam*weightW F lam B ∧
      (forestMixture F B lam).varM ≤ c.value*(forestMixture F B lam).meanM :=
  forest_variances_le_closed_cap hc hJ hell hCC hCA hAC F hB.1
    (Reserve.leafProp_of_isMaxWeight F (Cap.activity_pos hc) hB)

end ClosedCap

section FiveCaps

variable (hJ : ∀ (c : Cap) (lam : ℝ), c.Contains lam →
  ∀ t y : ℝ, 0≤t → logMass lam t≤y → J lam t<c.jBound)
variable (hell : ∀ (c : Cap) (lam : ℝ), c.Contains lam →
  ∀ t y : ℝ, 0≤t → logMass lam t≤y → -c.eta<ell c.value lam y)
variable (hCC : ∀ (c : Cap) (lam : ℝ), c.Contains lam →
  ∀ t y : ℝ, 0≤t → logMass lam t≤y → 0≤CC c.value lam t y)
variable (hCA : ∀ (c : Cap) (lam : ℝ), c.Contains lam →
  ∀ t y : ℝ, 0≤t → logMass lam t≤y → 0≤CA c.value lam t y)
variable (hAC : ∀ (c : Cap) (lam : ℝ), c.Contains lam →
  ∀ t y : ℝ, 0≤t → logMass lam t≤y → 0≤AC c.value lam t y)

include hJ hell hCC hCA hAC

/-- The exact left-selected piecewise cap, including all activity endpoints.
The five quantified scalar hypotheses are explicit. -/
theorem forest_variances_le_Dhat (F : FiniteForest) {lam : ℝ}
    (hlam : (1/3:ℝ)≤lam) (hlam7 : lam≤7/3) {B : Finset (Fin F.n)}
    (hB : F.graph.IsIndepSet (B : Set (Fin F.n))) (hleaf : Reserve.LeafProp F.graph B) :
    HardCore.varKB F lam B ≤ (1+(Dhat lam-1)*q lam)*weightW F lam B ∧
      (forestMixture F B lam).varM ≤ Dhat lam*(forestMixture F B lam).meanM := by
  have hc := selectedCap_contains hlam hlam7
  have hh := forest_variances_le_closed_cap hc
    (hJ _ lam hc) (hell _ lam hc) (hCC _ lam hc) (hCA _ lam hc) (hAC _ lam hc) F hB hleaf
  simpa only [Dhat, capA] using hh

theorem maxWeight_variances_le_Dhat (F : FiniteForest) {lam : ℝ}
    (hlam : (1/3:ℝ)≤lam) (hlam7 : lam≤7/3) {B : Finset (Fin F.n)}
    (hB : IsMaxWeight F lam B) :
    HardCore.varKB F lam B ≤ (1+(Dhat lam-1)*q lam)*weightW F lam B ∧
      (forestMixture F B lam).varM ≤ Dhat lam*(forestMixture F B lam).meanM :=
  forest_variances_le_Dhat hJ hell hCC hCA hAC F hlam hlam7 hB.1
    (Reserve.leafProp_of_isMaxWeight F (by linarith) hB)

/-- A downstream profile can consume the stronger all-forest result after
proving its own Db agrees with this current Dhat. No other profile field,
old profile, rank condition, or graph-size restriction is used to prove it. -/
theorem varianceBound_of_profile_Db (P : Profile)
    (hDb : ∀ lam : ℝ, InRange lam → P.Db lam=Dhat lam) : VarianceBound P := by
  intro F _ lam hlam _ B hB
  rw [hDb lam hlam]
  exact (maxWeight_variances_le_Dhat hJ hell hCC hCA hAC F hlam.1 hlam.2 hB).2

end FiveCaps

end Erdos993Lean.Analytic.V213.FreeCountVariance

#check Erdos993Lean.Analytic.V213.FreeCountVariance.stepCert_of_feasible_comparisons
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.stepCert_of_feasible_comparisons
#check Erdos993Lean.Analytic.V213.FreeCountVariance.reserve_le_root_surplus
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.reserve_le_root_surplus
#check Erdos993Lean.Analytic.V213.FreeCountVariance.selected_variance_le_component
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.selected_variance_le_component
#check Erdos993Lean.Analytic.V213.FreeCountVariance.selected_variance_le_closed
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.selected_variance_le_closed
#check Erdos993Lean.Analytic.V213.FreeCountVariance.selected_variance_le_of_feasible_comparisons
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.selected_variance_le_of_feasible_comparisons
#check Erdos993Lean.Analytic.V213.FreeCountVariance.free_variance_le_of_feasible_comparisons
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.free_variance_le_of_feasible_comparisons
#check Erdos993Lean.Analytic.V213.FreeCountVariance.Z_pos_of_cap_feasible_bounds
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.Z_pos_of_cap_feasible_bounds
#check Erdos993Lean.Analytic.V213.FreeCountVariance.cap_stepCert_of_feasible_comparisons
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.cap_stepCert_of_feasible_comparisons
#check Erdos993Lean.Analytic.V213.FreeCountVariance.forest_variances_le_closed_cap
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.forest_variances_le_closed_cap
#check Erdos993Lean.Analytic.V213.FreeCountVariance.maxWeight_variances_le_closed_cap
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.maxWeight_variances_le_closed_cap
#check Erdos993Lean.Analytic.V213.FreeCountVariance.forest_variances_le_Dhat
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.forest_variances_le_Dhat
#check Erdos993Lean.Analytic.V213.FreeCountVariance.maxWeight_variances_le_Dhat
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.maxWeight_variances_le_Dhat
#check Erdos993Lean.Analytic.V213.FreeCountVariance.varianceBound_of_profile_Db
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.varianceBound_of_profile_Db
