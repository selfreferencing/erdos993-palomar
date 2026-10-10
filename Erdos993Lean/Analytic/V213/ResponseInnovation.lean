module

public import Erdos993Lean.Analytic.O2.Records
public import Erdos993Lean.Analytic.Tail.Marginal

/-!
Current paper Lemma 5.5 (f4:lem2.4): the mean and innovation identities.
The rooted fold carries exactly the printed parent-vacancy recursion.  The last
identity substitutes the actual component marginal for rho*p; no sign is imposed
on the response zR.
-/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.VarianceResponse

open Finset Erdos993Lean.Analytic.Tail Erdos993Lean.Analytic.Reserve
open Erdos993Lean.Analytic.O2

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- The first mean sum in printed Lemma 5.5(a). -/
theorem response_mean_fold (hG : G.IsAcyclic) {lam : ℝ} (hl : 0 < lam)
    {s : Finset V} (hs : ConnectedIn G s) {r : V} (hr : r ∈ s) (rho t : ℝ) :
    dfold G lam (fun u v _ _ => rootProb G lam u v * zR G lam u v) s r rho t =
      meanB G univ lam s := by
  refine rooted_induction hG (P := fun s r => ∀ rho t : ℝ,
    dfold G lam (fun u v _ _ => rootProb G lam u v * zR G lam u v) s r rho t =
      meanB G univ lam s) ?_ hs hr rho t
  intro s r hs hr ih rho t
  rw [dfold_eq _ _ hr, Finset.sum_congr rfl (fun w hw => ih w hw _ _),
    ← meanB_erase_root hG hl.le hs hr]
  have hp := port_univ_eq (G := G) hl.le hr
  unfold port at hp
  linarith

/-- The marginal mean identity with the same arbitrary boundary as the variance induction. -/
theorem boundary_marginal_mean_fold (hG : G.IsAcyclic) {lam : ℝ} (hl : 0 < lam)
    {s : Finset V} (hs : ConnectedIn G s) {r : V} (hr : r ∈ s) (rho t : ℝ) :
    dfold G lam (fun u v rho _ => rho * rootProb G lam u v) s r rho t =
      rho * meanB G univ lam s + (1-rho) * meanB G univ lam (s.erase r) := by
  refine rooted_induction hG (P := fun s r => ∀ rho t : ℝ,
    dfold G lam (fun u v rho _ => rho * rootProb G lam u v) s r rho t =
      rho * meanB G univ lam s + (1-rho) * meanB G univ lam (s.erase r))
    ?_ hs hr rho t
  intro s r hs hr ih rho t
  rw [dfold_eq _ _ hr, Finset.sum_congr rfl (fun w hw => ih w hw _ _),
    Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
    ← meanB_erase_root hG hl.le hs hr, ← meanB_outside_root hG hl.le hs hr,
    meanB_root hl.le hr, aB_univ]
  ring

/-- Every actual descendant carries the component marginal rho*p. -/
theorem dfold_marginal_rewrite (hG : G.IsAcyclic) {lam : ℝ} (hl : 0 < lam)
    (f : Finset V → V → ℝ → ℝ → ℝ) {s : Finset V} (hs : ConnectedIn G s)
    {r : V} (hr : r ∈ s) :
    dfold G lam (fun u v rho t => f u v (rho * rootProb G lam u v) t) s r 1 0 =
      dfold G lam (fun u v _ t => f u v (marg G lam s v) t) s r 1 0 := by
  let Inv : Finset V → V → ℝ → ℝ → Prop :=
    fun u v rho _ => ∀ x ∈ u, marg G lam s x = mu G lam u v rho x
  refine dfold_congr_of_inv hG lam Inv ?_ ?_ hs hr ?_
  · intro u v rho t hu hv hi w hw x hx
    exact (hi x (Finset.mem_of_mem_erase (compIn_subset _ _ hx))).trans
      (mu_branch hG hl.le hv hw hx rho)
  · intro u v rho t hu hv hi
    have hpi : rho * rootProb G lam u v = marg G lam s v :=
      ((hi v hv).trans (mu_root hv rho)).symm
    exact congrArg (fun pi => f u v pi t) hpi
  · intro x hx
    exact (mu_one s r x).symm

/-- The second sum in printed Lemma 5.5(a) uses actual marginals in this component. -/
theorem marginal_fold_eq_sum (hG : G.IsAcyclic) {lam : ℝ} (hl : 0 < lam)
    {s : Finset V} (hs : ConnectedIn G s) {r : V} (hr : r ∈ s) :
    dfold G lam (fun u v rho _ => rho * rootProb G lam u v) s r 1 0 =
      ∑ v ∈ s, marg G lam s v := by
  rw [dfold_marginal_rewrite hG hl (fun _ _ pi _ => pi) hs hr,
    dfold_const hG lam (fun v => marg G lam s v) hs hr]

theorem mean_eq_marginal_sum (hG : G.IsAcyclic) {lam : ℝ} (hl : 0 < lam)
    {s : Finset V} (hs : ConnectedIn G s) {r : V} (hr : r ∈ s) :
    meanB G univ lam s = ∑ v ∈ s, marg G lam s v := by
  have hm := boundary_marginal_mean_fold hG hl hs hr 1 0
  simp only [one_mul, sub_self, zero_mul, add_zero] at hm
  exact hm.symm.trans (marginal_fold_eq_sum hG hl hs hr)

/-- Both equalities in printed Lemma 5.5(a). -/
theorem mean_identity (hG : G.IsAcyclic) {lam : ℝ} (hl : 0 < lam)
    {s : Finset V} (hs : ConnectedIn G s) {r : V} (hr : r ∈ s) :
    dfold G lam (fun u v _ _ => rootProb G lam u v * zR G lam u v) s r 1 0 =
      meanB G univ lam s ∧
    meanB G univ lam s = ∑ v ∈ s, marg G lam s v :=
  ⟨response_mean_fold hG hl hs hr 1 0, mean_eq_marginal_sum hG hl hs hr⟩

/-- The arbitrary-boundary induction printed in the proof of Lemma 5.5(b). -/
theorem innovation_boundary_identity (hG : G.IsAcyclic) {lam : ℝ} (hl : 0 < lam)
    {s : Finset V} (hs : ConnectedIn G s) {r : V} (hr : r ∈ s) (rho t : ℝ) :
    dfold G lam (fun u v rho _ => rho * rootProb G lam u v *
      (1-rootProb G lam u v) * zR G lam u v ^ 2) s r rho t =
    rho * varB G univ lam s + (1-rho) * varB G univ lam (s.erase r) :=
  dfold_innov hG hl.le hs hr rho t

/-- Printed Lemma 5.5(b), first expression. -/
theorem innovation_identity (hG : G.IsAcyclic) {lam : ℝ} (hl : 0 < lam)
    {s : Finset V} (hs : ConnectedIn G s) {r : V} (hr : r ∈ s) :
    varB G univ lam s = dfold G lam (fun u v rho _ => rho * rootProb G lam u v *
      (1-rootProb G lam u v) * zR G lam u v ^ 2) s r 1 0 := by
  simpa only [one_mul, sub_self, zero_mul, add_zero] using
    (innovation_boundary_identity hG hl hs hr 1 0).symm

/-- Printed Lemma 5.5(b), second expression with the actual component marginal. -/
theorem innovation_marginal_identity (hG : G.IsAcyclic) {lam : ℝ} (hl : 0 < lam)
    {s : Finset V} (hs : ConnectedIn G s) {r : V} (hr : r ∈ s) :
    varB G univ lam s = dfold G lam (fun u v _ _ => marg G lam s v *
      (1-rootProb G lam u v) * zR G lam u v ^ 2) s r 1 0 := by
  rw [innovation_identity hG hl hs hr,
    dfold_marginal_rewrite hG hl
      (fun u v pi _ => pi * (1-rootProb G lam u v) * zR G lam u v ^ 2) hs hr]

end Erdos993Lean.Analytic.V213.VarianceResponse

#check Erdos993Lean.Analytic.V213.VarianceResponse.response_mean_fold
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.response_mean_fold
#check Erdos993Lean.Analytic.V213.VarianceResponse.boundary_marginal_mean_fold
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.boundary_marginal_mean_fold
#check Erdos993Lean.Analytic.V213.VarianceResponse.dfold_marginal_rewrite
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.dfold_marginal_rewrite
#check Erdos993Lean.Analytic.V213.VarianceResponse.marginal_fold_eq_sum
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.marginal_fold_eq_sum
#check Erdos993Lean.Analytic.V213.VarianceResponse.mean_eq_marginal_sum
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.mean_eq_marginal_sum
#check Erdos993Lean.Analytic.V213.VarianceResponse.mean_identity
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.mean_identity
#check Erdos993Lean.Analytic.V213.VarianceResponse.innovation_boundary_identity
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.innovation_boundary_identity
#check Erdos993Lean.Analytic.V213.VarianceResponse.innovation_identity
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.innovation_identity
#check Erdos993Lean.Analytic.V213.VarianceResponse.innovation_marginal_identity
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.innovation_marginal_identity
