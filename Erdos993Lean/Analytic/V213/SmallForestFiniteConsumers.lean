module

public import Erdos993Lean.Analytic.V213.SmallForestRisingChecks
public import Erdos993Lean.Analytic.V213.SmallForestCatalanChecks
public import Erdos993Lean.Analytic.V213.SmallForestFamilyChecks
public import Erdos993Lean.Analytic.V213.SmallForestCatalanLines

/-!
Finite arithmetic is connected to the actual new graph
lemmas. The affine-family consumer deliberately retains its printed supporting
line hypotheses; those must be discharged by the nine universal patterns and
horizontal proof, not by any old finite tangent catalogue.
-/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.SmallForest

open Finset SmallForestPrinted SmallForestFinite SmallForestCatalan

/-- The only sign-sensitive edge-budget step, valid for either sign of B. -/
theorem affine_edge_budget (a b e C : ℝ) (he0 : 0 ≤ e) (heC : e ≤ C) :
    a + C * min b 0 ≤ a + b * e := by
  by_cases hb : 0 ≤ b
  · rw [min_eq_right hb]
    nlinarith only [mul_nonneg hb he0]
  · have hb0 : b ≤ 0 := le_of_lt (lt_of_not_ge hb)
    have h := mul_le_mul_of_nonpos_right heC hb0
    rw [min_eq_left hb0]
    nlinarith only [h]

variable (F : FiniteForest) [DecidableRel F.graph.Adj]

/-- Each current rising corner extends in precisely the proved monotone directions. -/
theorem printed_rising_margin (A : Finset (Fin F.n))
    (hA : F.graph.IsIndepSet (A : Set (Fin F.n)))
    (r : RisingInput) (hr : r ∈ risingInputs)
    (ha : 2*r.k+r.aOffset ≤ A.card) (hc : (Aᶜ).card ≤ r.c) :
    (r.margin : ℝ) ≤
      (indepCount F.graph univ r.k : ℝ) - indepCount F.graph univ (r.k-1) := by
  rcases all_rising_facts r hr with ⟨hv, _hpos, hk, hbase⟩
  have hv' : realRising (2*r.k+r.aOffset) r.c r.k = (r.margin : ℝ) := by
    rw [risingQ_eq] at hv
    unfold realRising
    exact_mod_cast hv
  have h1 := realRising_monotone_a (2*r.k+r.aOffset) A.card r.c r.k hk hbase ha
  have h2 := realRising_antitone_c A.card (Aᶜ).card r.c r.k hc
  have h3 := catalan_rising_bound F A hA hk
  rw [hv'] at h1
  exact h1.trans (h2.trans h3)

theorem printed_rising_strict (A : Finset (Fin F.n))
    (hA : F.graph.IsIndepSet (A : Set (Fin F.n)))
    (r : RisingInput) (hr : r ∈ risingInputs)
    (ha : 2*r.k+r.aOffset ≤ A.card) (hc : (Aᶜ).card ≤ r.c) :
    (indepCount F.graph univ (r.k-1) : ℝ) < indepCount F.graph univ r.k := by
  have hb := printed_rising_margin F A hA r hr ha hc
  have hp : (0 : ℝ) < (r.margin : ℝ) := by
    exact_mod_cast (all_rising_facts r hr).2.1
  linarith only [hb, hp]

/-- The four individually printed Catalan rows give the full graph margin. -/
theorem printed_named_catalan_margin (A : Finset (Fin F.n))
    (hA : F.graph.IsIndepSet (A : Set (Fin F.n)))
    (hmax : ∀ S : Finset (Fin F.n), F.graph.IsIndepSet (S : Set (Fin F.n)) → S.card ≤ A.card)
    (r : CatalanInput) (hr : r ∈ namedCatalanInputs)
    (ha : A.card = r.a) (hc : (Aᶜ).card = r.c) :
    (36 : ℝ) ≤ variation F r.k 1 := by
  rcases all_named_catalan_facts r hr with ⟨hconst, hslope, h36, hpos, hc2, hk⟩
  have hcc : 2 ≤ (Aᶜ).card := by simpa only [hc] using hc2
  have hb := catalan_cut_forest_bound F A hA hmax hcc r.k r.s r.t hk
  rw [ha, hc, hconst, hslope] at hb
  have h36' : (36 : ℝ) ≤ (r.constant : ℝ) := by exact_mod_cast h36
  have hslope' : (0 : ℝ) ≤ (r.slope : ℝ) := by exact_mod_cast le_of_lt hpos
  have he : (0 : ℝ) ≤ (internalEdges F A : ℝ) := by positivity
  linarith only [hb, h36', mul_nonneg hslope' he]

/-- The four printed Newton points preserve their stronger stated margin 232. -/
theorem printed_newton_catalan_margin (A : Finset (Fin F.n))
    (hA : F.graph.IsIndepSet (A : Set (Fin F.n)))
    (hmax : ∀ S : Finset (Fin F.n), F.graph.IsIndepSet (S : Set (Fin F.n)) → S.card ≤ A.card)
    (x : ℕ) (hx : x ∈ a14Indices) (ha : A.card = 14) (hc : (Aᶜ).card = 7+x) :
    (232 : ℝ) ≤ variation F 7 1 := by
  rcases all_a14_facts x hx with ⟨hconst, hslope, h232, h18⟩
  have hcc : 2 ≤ (Aᶜ).card := by omega
  have hb := catalan_cut_forest_bound F A hA hmax hcc 7 1 4 (by decide)
  rw [ha, hc, hconst, hslope] at hb
  have h232' : (232 : ℝ) ≤ (a14Constant x : ℝ) := by exact_mod_cast h232
  have hslope' : (0 : ℝ) ≤ (a14Slope x : ℝ) := by
    have : (0 : ℚ) ≤ a14Slope x := by linarith only [h18]
    exact_mod_cast this
  have he : (0 : ℝ) ≤ (internalEdges F A : ℝ) := by positivity
  linarith only [hb, h232', mul_nonneg hslope' he]

/-- Table families yield 26 once their actual printed affine lines are known valid.
The analytic hypotheses are explicit, with every h through k+1 and every
available m; finite endpoint arithmetic cannot satisfy them by itself. -/
theorem printed_family_margin_of_lines (A : Finset (Fin F.n))
    (hA : F.graph.IsIndepSet (A : Set (Fin F.n)))
    (hmax : ∀ S : Finset (Fin F.n), F.graph.IsIndepSet (S : Set (Fin F.n)) → S.card ≤ A.card)
    (r : FamilyInput) (hr : r ∈ familyInputs) (ha : A.card = r.a)
    (hc : (Aᶜ).card ∈ Icc r.lo r.hi)
    (hq : ∀ h ∈ Icc 1 (r.k+1), (0 : ℝ) ≤ ((familyLineQ r h).2 : ℝ))
    (hline : ∀ h ∈ Icc 1 (r.k+1), ∀ m : ℕ, m+h ≤ A.card →
      ((familyLineQ r h).1 : ℝ) + ((familyLineQ r h).2 : ℝ)*m ≤
        G (r.w : ℝ) ((r.k : ℤ)-h) m) :
    (26 : ℝ) ≤ variation F r.k (r.w : ℝ) := by
  rcases all_family_endpoints r hr with ⟨_, _, _, _, hlo, _hlohi, hk, hw0, hw1⟩
  have hc2 : 2 ≤ (Aᶜ).card := hlo.trans (mem_Icc.mp hc).1
  have hw : (0 : ℝ) ≤ (r.w : ℝ) ∧ (r.w : ℝ) ≤ 1 := by exact_mod_cast And.intro hw0 hw1
  have hv := affine_summation F A hA hmax hc2 hk (r.w : ℝ) hw
    (fun h => ((familyLineQ r h).1 : ℝ))
    (fun h => ((familyLineQ r h).2 : ℝ)) hq hline
  have hv' : (familyAQ r (Aᶜ).card : ℝ) +
      (familyBQ r (Aᶜ).card : ℝ)*(internalEdges F A : ℝ) ≤ variation F r.k (r.w : ℝ) := by
    unfold familyAQ familyBQ
    rw [affineAQ_cast, affineBQ_cast]
    simpa only [ha] using hv
  have hm := all_family_margins r hr (Aᶜ).card hc
  have hm' : (26 : ℝ) ≤ (familyAQ r (Aᶜ).card : ℝ) +
      ((Aᶜ).card-1 : ℝ)*min (familyBQ r (Aᶜ).card : ℝ) 0 := by exact_mod_cast hm
  have he0 : (0 : ℝ) ≤ (internalEdges F A : ℝ) := by positivity
  have heC : (internalEdges F A : ℝ) ≤ ((Aᶜ).card : ℝ)-1 := by
    have he : (internalEdges F A : ℝ) ≤ (((Aᶜ).card-1 : ℕ) : ℝ) := by
      exact_mod_cast internalEdges_le F A
    rw [Nat.cast_sub (by omega : 1 ≤ (Aᶜ).card), Nat.cast_one] at he
    exact he
  have he := affine_edge_budget (familyAQ r (Aᶜ).card : ℝ)
    (familyBQ r (Aᶜ).card : ℝ) (internalEdges F A : ℝ) ((Aᶜ).card-1 : ℝ) he0 heC
  exact hm'.trans (he.trans hv')

end Erdos993Lean.Analytic.V213.SmallForest

#check Erdos993Lean.Analytic.V213.SmallForest.affine_edge_budget
#print axioms Erdos993Lean.Analytic.V213.SmallForest.affine_edge_budget
#check Erdos993Lean.Analytic.V213.SmallForest.printed_rising_margin
#print axioms Erdos993Lean.Analytic.V213.SmallForest.printed_rising_margin
#check Erdos993Lean.Analytic.V213.SmallForest.printed_rising_strict
#print axioms Erdos993Lean.Analytic.V213.SmallForest.printed_rising_strict
#check Erdos993Lean.Analytic.V213.SmallForest.printed_named_catalan_margin
#print axioms Erdos993Lean.Analytic.V213.SmallForest.printed_named_catalan_margin
#check Erdos993Lean.Analytic.V213.SmallForest.printed_newton_catalan_margin
#print axioms Erdos993Lean.Analytic.V213.SmallForest.printed_newton_catalan_margin
#check Erdos993Lean.Analytic.V213.SmallForest.printed_family_margin_of_lines
#print axioms Erdos993Lean.Analytic.V213.SmallForest.printed_family_margin_of_lines
