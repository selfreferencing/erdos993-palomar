module

public import Erdos993Lean.Analytic.V213.ZeroTiltLaplaceUnitBinding

/-!
The actual single telescoping identity, separate from
the historical paired-potential forest reduction. `vertexPotential` uses the
current Psi and assigned aH leaf convention. The concluding inequality keeps
the local sigma inequalities explicit; their instantiation on actual rooted
forests and subsequent mean/product assembly remain separate obligations.
-/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.ZeroTiltLaplace

open Finset

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem rooted_sum_add (hG : G.IsAcyclic) (f g : Finset V → V → ℝ)
    {s : Finset V} (hs : ConnectedIn G s) {r : V} (hr : r ∈ s) :
    Tail.treeSum G (fun s r => f s r+g s r) s r =
      Tail.treeSum G f s r+Tail.treeSum G g s r := by
  refine Tail.rooted_induction hG (P := fun s r =>
    Tail.treeSum G (fun s r => f s r+g s r) s r =
      Tail.treeSum G f s r+Tail.treeSum G g s r) ?_ hs hr
  intro s r hs hr ih
  rw [Tail.treeSum_eq _ hr, Tail.treeSum_eq f hr, Tail.treeSum_eq g hr,
    Finset.sum_congr rfl ih, Finset.sum_add_distrib]
  ring

theorem rooted_sum_congr (hG : G.IsAcyclic) {f g : Finset V → V → ℝ}
    (hfg : ∀ s r, ConnectedIn G s → r ∈ s → f s r = g s r)
    {s : Finset V} (hs : ConnectedIn G s) {r : V} (hr : r ∈ s) :
    Tail.treeSum G f s r = Tail.treeSum G g s r := by
  apply le_antisymm
  · exact Tail.treeSum_le_treeSum hG (fun s r hs hr => (hfg s r hs hr).le) hs hr
  · exact Tail.treeSum_le_treeSum hG (fun s r hs hr => (hfg s r hs hr).ge) hs hr

/-- Every nonroot potential occurs once with each sign. -/
theorem rooted_sum_telescope (hG : G.IsAcyclic) (P : Finset V → V → ℝ)
    {s : Finset V} (hs : ConnectedIn G s) {r : V} (hr : r ∈ s) :
    Tail.treeSum G
      (fun s r => P s r-∑ w ∈ nbrsIn G s r, P (compIn G (s.erase r) w) w) s r = P s r := by
  refine Tail.rooted_induction hG (P := fun s r =>
    Tail.treeSum G
      (fun s r => P s r-∑ w ∈ nbrsIn G s r, P (compIn G (s.erase r) w) w) s r = P s r)
    ?_ hs hr
  intro s r hs hr ih
  rw [Tail.treeSum_eq _ hr, Finset.sum_congr rfl ih]
  ring

noncomputable def vertexPotential (G : SimpleGraph V) [DecidableRel G.Adj]
    (A : Finset V) (lam : ℝ) (s : Finset V) (r : V) : ℝ :=
  if r ∈ A then a lam*H lam (Tail.rootProb G lam s r)
  else Psi lam (Tail.rootProb G lam s r)

noncomputable def selectedSurplus (G : SimpleGraph V) [DecidableRel G.Adj]
    (A : Finset V) (lam : ℝ) (s : Finset V) (r : V) : ℝ :=
  if r ∈ A then
    (∑ w ∈ nbrsIn G s r, vertexPotential G A lam (compIn G (s.erase r) w) w)-
      vertexPotential G A lam s r
  else 0

noncomputable def outsideDefect (G : SimpleGraph V) [DecidableRel G.Adj]
    (A : Finset V) (lam : ℝ) (s : Finset V) (r : V) : ℝ :=
  if r ∈ A then 0 else
    vertexPotential G A lam s r-
      ∑ w ∈ nbrsIn G s r, vertexPotential G A lam (compIn G (s.erase r) w) w

/-- Exact displayed cancellation before any inequality is substituted. -/
theorem outside_defect_telescope (hG : G.IsAcyclic) (A : Finset V) (lam : ℝ)
    {s : Finset V} (hs : ConnectedIn G s) {r : V} (hr : r ∈ s) (hrA : r ∉ A) :
    Tail.treeSum G (outsideDefect G A lam) s r =
      Psi lam (Tail.rootProb G lam s r)+Tail.treeSum G (selectedSurplus G A lam) s r := by
  let P := vertexPotential G A lam
  have hsplit : ∀ s r, ConnectedIn G s → r ∈ s → outsideDefect G A lam s r =
      (P s r-∑ w ∈ nbrsIn G s r, P (compIn G (s.erase r) w) w)+
        selectedSurplus G A lam s r := by
    intro s r _ _
    by_cases h : r ∈ A <;> simp [outsideDefect, selectedSurplus, P, h] <;> ring
  rw [rooted_sum_congr hG hsplit hs hr, rooted_sum_add hG _ _ hs hr,
    rooted_sum_telescope hG P hs hr]
  simp only [P, vertexPotential, if_neg hrA]

/-- Local hypotheses need only hold on a branch-closed domain of rooted sets.
This matters for the retained no-outside-leaf condition: it is not asserted
for every arbitrary connected subset of the ambient forest. -/
theorem rooted_sum_le_on_closed (hG : G.IsAcyclic)
    (Good : Finset V → V → Prop) (f g : Finset V → V → ℝ)
    (hchildren : ∀ s r, ConnectedIn G s → r ∈ s → Good s r →
      ∀ w ∈ nbrsIn G s r, Good (compIn G (s.erase r) w) w)
    (hfg : ∀ s r, ConnectedIn G s → r ∈ s → Good s r → f s r ≤ g s r)
    {s : Finset V} (hs : ConnectedIn G s) {r : V} (hr : r ∈ s) (hgood : Good s r) :
    Tail.treeSum G f s r ≤ Tail.treeSum G g s r := by
  refine Tail.rooted_induction hG (P := fun s r => Good s r →
    Tail.treeSum G f s r ≤ Tail.treeSum G g s r) ?_ hs hr hgood
  intro s r hs hr ih hg
  rw [Tail.treeSum_eq _ hr, Tail.treeSum_eq _ hr]
  exact add_le_add (hfg s r hs hr hg)
    (Finset.sum_le_sum (fun w hw => ih w hw (hchildren s r hs hr hg w hw)))

/-- Conditional local-to-global step by one sum, with no second subtree invariant. -/
theorem outside_sigma_ge_root_plus_selected (hG : G.IsAcyclic) (A : Finset V) (lam : ℝ)
    (sigma : Finset V → V → ℝ) (Good : Finset V → V → Prop)
    (hchildren : ∀ s r, ConnectedIn G s → r ∈ s → Good s r →
      ∀ w ∈ nbrsIn G s r, Good (compIn G (s.erase r) w) w)
    (hlocal : ∀ s r, ConnectedIn G s → r ∈ s → Good s r →
      outsideDefect G A lam s r ≤ if r ∈ A then 0 else sigma s r)
    {s : Finset V} (hs : ConnectedIn G s) {r : V} (hr : r ∈ s) (hrA : r ∉ A)
    (hgood : Good s r) :
    Psi lam (Tail.rootProb G lam s r)+Tail.treeSum G (selectedSurplus G A lam) s r ≤
      Tail.treeSum G (fun s r => if r ∈ A then 0 else sigma s r) s r := by
  rw [← outside_defect_telescope hG A lam hs hr hrA]
  exact rooted_sum_le_on_closed hG Good _ _ hchildren hlocal hs hr hgood

theorem outside_sigma_nonnegative (hG : G.IsAcyclic) (A : Finset V) (lam : ℝ)
    (sigma : Finset V → V → ℝ) (Good : Finset V → V → Prop)
    (hchildren : ∀ s r, ConnectedIn G s → r ∈ s → Good s r →
      ∀ w ∈ nbrsIn G s r, Good (compIn G (s.erase r) w) w)
    (hlocal : ∀ s r, ConnectedIn G s → r ∈ s → Good s r →
      outsideDefect G A lam s r ≤ if r ∈ A then 0 else sigma s r)
    (hselected : ∀ s r, ConnectedIn G s → r ∈ s → 0 ≤ selectedSurplus G A lam s r)
    {s : Finset V} (hs : ConnectedIn G s) {r : V} (hr : r ∈ s) (hrA : r ∉ A)
    (hgood : Good s r)
    (hroot : 0 ≤ Psi lam (Tail.rootProb G lam s r)) :
    0 ≤ Tail.treeSum G (fun s r => if r ∈ A then 0 else sigma s r) s r := by
  exact (add_nonneg hroot (Tail.treeSum_nonneg hG hselected hs hr)).trans
    (outside_sigma_ge_root_plus_selected hG A lam sigma Good hchildren hlocal hs hr hrA hgood)

end Erdos993Lean.Analytic.V213.ZeroTiltLaplace

-- Audit commands.
#check Erdos993Lean.Analytic.V213.ZeroTiltLaplace.rooted_sum_add
#print axioms Erdos993Lean.Analytic.V213.ZeroTiltLaplace.rooted_sum_add
#check Erdos993Lean.Analytic.V213.ZeroTiltLaplace.rooted_sum_congr
#print axioms Erdos993Lean.Analytic.V213.ZeroTiltLaplace.rooted_sum_congr
#check Erdos993Lean.Analytic.V213.ZeroTiltLaplace.rooted_sum_telescope
#print axioms Erdos993Lean.Analytic.V213.ZeroTiltLaplace.rooted_sum_telescope
#check Erdos993Lean.Analytic.V213.ZeroTiltLaplace.outside_defect_telescope
#print axioms Erdos993Lean.Analytic.V213.ZeroTiltLaplace.outside_defect_telescope
#check Erdos993Lean.Analytic.V213.ZeroTiltLaplace.rooted_sum_le_on_closed
#print axioms Erdos993Lean.Analytic.V213.ZeroTiltLaplace.rooted_sum_le_on_closed
#check Erdos993Lean.Analytic.V213.ZeroTiltLaplace.outside_sigma_ge_root_plus_selected
#print axioms Erdos993Lean.Analytic.V213.ZeroTiltLaplace.outside_sigma_ge_root_plus_selected
#check Erdos993Lean.Analytic.V213.ZeroTiltLaplace.outside_sigma_nonnegative
#print axioms Erdos993Lean.Analytic.V213.ZeroTiltLaplace.outside_sigma_nonnegative
