module

public import Erdos993Lean.Analytic.V213.LowMeanCoverageData

/-! Int/Nat checks for all eleven groups, 28 certificates and 55 accepted inputs. -/

@[expose] public section

namespace Erdos993Lean.Analytic.V213

def lowMeanGroupFacts (k : ℕ) : Prop :=
  let g := lowMeanGroupAt k
  g.iotaLo ≤ g.iotaHi ∧ g.iotaHi < 55 ∧ g.certLo ≤ g.certHi ∧ g.certHi < 28 ∧
  lowMeanFractionValid g.l ∧ lowMeanFractionValid g.h ∧
  lowMeanFractionValid g.D ∧ lowMeanFractionValid g.theta ∧
  lowMeanFractionValid g.muLo ∧ lowMeanFractionValid g.muHi ∧
  lowMeanFractionLT (0, 1) g.l ∧ lowMeanFractionLT g.h (1, 1) ∧
  lowMeanFractionLT (0, 1) g.D ∧ lowMeanFractionLT (0, 1) g.theta ∧
  lowMeanFractionEq (lowMeanFractionMul g.muLo g.h) (4, 1) ∧
  g.iotaLo ≤ g.dWitness ∧ g.dWitness ≤ g.iotaHi ∧
  g.iotaLo ≤ g.thetaWitness ∧ g.thetaWitness ≤ g.iotaHi ∧
  g.iotaLo ≤ g.meanWitness ∧ g.meanWitness ≤ g.iotaHi ∧
  (lowMeanInputRowAt g.dWitness).D = g.D ∧
  (lowMeanInputRowAt g.thetaWitness).theta = g.theta ∧
  (lowMeanInputRowAt g.meanWitness).mu0 = g.muHi ∧
  lowMeanActivityQFraction (lowMeanN44LoFraction g.iotaLo) = g.l ∧
  lowMeanActivityQFraction (lowMeanN44HiFraction g.iotaHi) = g.h
instance lowMeanGroupFactsDecidable (k : ℕ) : Decidable (lowMeanGroupFacts k) := by unfold lowMeanGroupFacts; infer_instance

def lowMeanCertificateGroupFacts (i : ℕ) : Prop :=
  let k := lowMeanCertificateGroupAt i
  let g := lowMeanGroupAt k
  let c := lowMeanCertificateAt i
  k < 11 ∧ g.certLo ≤ i ∧ i ≤ g.certHi ∧
  c.l = g.l ∧ c.h = g.h ∧ c.D = g.D ∧ c.theta = g.theta ∧
  (i = g.certLo → c.muA = g.muLo) ∧
  (i = g.certHi → c.muB = g.muHi) ∧
  (i < g.certHi → c.muB = (lowMeanCertificateAt (i + 1)).muA)
instance lowMeanCertificateGroupFactsDecidable (i : ℕ) : Decidable (lowMeanCertificateGroupFacts i) := by
  unfold lowMeanCertificateGroupFacts; infer_instance

def lowMeanInputGroupFacts (i : ℕ) : Prop :=
  let r := lowMeanInputRowAt i
  let g := lowMeanGroupAt r.group
  r.group < 11 ∧ g.iotaLo ≤ i ∧ i ≤ g.iotaHi ∧
  lowMeanFractionValid r.D ∧ lowMeanFractionValid r.theta ∧ lowMeanFractionValid r.mu0 ∧
  lowMeanFractionLE r.D g.D ∧ lowMeanFractionLE r.theta g.theta ∧
  lowMeanFractionLE r.mu0 g.muHi
instance lowMeanInputGroupFactsDecidable (i : ℕ) : Decidable (lowMeanInputGroupFacts i) := by unfold lowMeanInputGroupFacts; infer_instance

def lowMeanN44EndpointFacts (i : ℕ) : Prop :=
  let lo := lowMeanN44LoFraction i
  let hi := lowMeanN44HiFraction i
  let g := lowMeanGroupAt (lowMeanInputRowAt i).group
  lowMeanFractionValid lo ∧ lowMeanFractionValid hi ∧ 0 ≤ lo.1 ∧ 0 ≤ hi.1 ∧
  lowMeanFractionLE (1, 3) lo ∧ lowMeanFractionLE hi (7, 3) ∧
  lowMeanFractionLT lo hi ∧
  lowMeanFractionLE g.l (lowMeanActivityQFraction lo) ∧
  lowMeanFractionLE (lowMeanActivityQFraction hi) g.h ∧
  lowMeanActivityCapFraction hi = (lowMeanInputRowAt i).D ∧
  (i < 54 → hi = lowMeanN44LoFraction (i + 1))
instance lowMeanN44EndpointFactsDecidable (i : ℕ) : Decidable (lowMeanN44EndpointFacts i) := by unfold lowMeanN44EndpointFacts; infer_instance

def lowMeanGroupMembersCheck (k : ℕ) : Bool :=
  let g := lowMeanGroupAt k
  ((List.range (g.certHi - g.certLo + 1)).all fun j =>
    decide (lowMeanCertificateGroupAt (g.certLo + j) = k)) &&
  ((List.range (g.iotaHi - g.iotaLo + 1)).all fun j =>
    decide ((lowMeanInputRowAt (g.iotaLo + j)).group = k))

theorem lowMean_cover_dimensions_kernel :
    lowMeanGroups.length = 11 ∧ lowMeanInputRows.length = 55 ∧ lowMeanCertificateGroups.length = 28 ∧
    Erdos993Lean.Analytic.N44.Data.pieceLo.length = 55 ∧
    Erdos993Lean.Analytic.N44.Data.pieceHi.length = 55 ∧
    lowMeanN44LoFraction 0 = (1, 3) ∧ lowMeanN44HiFraction 54 = (7, 3) ∧
    (lowMeanGroupAt 0).l = (1, 4) ∧ (lowMeanGroupAt 10).h = (7, 10) ∧
    (lowMeanGroupAt 0).iotaLo = 0 ∧ (lowMeanGroupAt 10).iotaHi = 54 ∧
    (lowMeanGroupAt 0).certLo = 0 ∧ (lowMeanGroupAt 10).certHi = 27 := by
  decide +kernel

theorem lowMean_groups_order_kernel :
    (List.range 10).all (fun k => decide (
      (lowMeanGroupAt k).iotaHi + 1 = (lowMeanGroupAt (k + 1)).iotaLo ∧
      (lowMeanGroupAt k).certHi + 1 = (lowMeanGroupAt (k + 1)).certLo ∧
      (lowMeanGroupAt k).h = (lowMeanGroupAt (k + 1)).l)) = true := by
  decide +kernel

theorem lowMean_inputs_separated_kernel :
    (List.range 55).all (fun i => (List.range 55).all (fun j => decide
      (i < j → lowMeanFractionLE (lowMeanN44HiFraction i) (lowMeanN44LoFraction j)))) = true := by
  decide +kernel

theorem lowMean_groups_kernel :
    (List.range 11).all (fun k => decide (lowMeanGroupFacts k) && lowMeanGroupMembersCheck k) = true := by
  decide +kernel

theorem lowMean_certificate_groups_kernel :
    (List.range 28).all (fun i => decide (lowMeanCertificateGroupFacts i)) = true := by
  decide +kernel

theorem lowMean_input_groups_kernel :
    (List.range 55).all (fun i => decide (lowMeanInputGroupFacts i) && decide (lowMeanN44EndpointFacts i)) = true := by
  decide +kernel

theorem lowMean_group_checked (k : ℕ) (hk : k < 11) : lowMeanGroupFacts k ∧ lowMeanGroupMembersCheck k = true := by
  have h := Erdos993Lean.F4Fast.forall_lt_of_range_all lowMean_groups_kernel k hk
  simp only [Bool.and_eq_true] at h
  exact ⟨of_decide_eq_true h.1, h.2⟩

theorem lowMean_certificate_group_checked (i : ℕ) (hi : i < 28) : lowMeanCertificateGroupFacts i := by
  exact of_decide_eq_true (Erdos993Lean.F4Fast.forall_lt_of_range_all lowMean_certificate_groups_kernel i hi)

theorem lowMean_input_group_checked (i : ℕ) (hi : i < 55) : lowMeanInputGroupFacts i ∧ lowMeanN44EndpointFacts i := by
  have h := Erdos993Lean.F4Fast.forall_lt_of_range_all lowMean_input_groups_kernel i hi
  simp only [Bool.and_eq_true] at h
  exact ⟨of_decide_eq_true h.1, of_decide_eq_true h.2⟩

theorem lowMean_group_certificate_member (k i : ℕ) (hk : k < 11)
    (hi : (lowMeanGroupAt k).certLo ≤ i ∧ i ≤ (lowMeanGroupAt k).certHi) :
    lowMeanCertificateGroupAt i = k := by
  have h := (lowMean_group_checked k hk).2
  simp only [lowMeanGroupMembersCheck, Bool.and_eq_true] at h
  obtain ⟨h, _⟩ := h
  have hn : i - (lowMeanGroupAt k).certLo <
      (lowMeanGroupAt k).certHi - (lowMeanGroupAt k).certLo + 1 := by omega
  have h' := Erdos993Lean.F4Fast.forall_lt_of_range_all h _ hn
  have he : (lowMeanGroupAt k).certLo + (i - (lowMeanGroupAt k).certLo) = i := by omega
  simpa only [he] using of_decide_eq_true h'

theorem lowMean_group_input_member (k i : ℕ) (hk : k < 11)
    (hi : (lowMeanGroupAt k).iotaLo ≤ i ∧ i ≤ (lowMeanGroupAt k).iotaHi) :
    (lowMeanInputRowAt i).group = k := by
  have h := (lowMean_group_checked k hk).2
  simp only [lowMeanGroupMembersCheck, Bool.and_eq_true] at h
  obtain ⟨_, h⟩ := h
  have hn : i - (lowMeanGroupAt k).iotaLo <
      (lowMeanGroupAt k).iotaHi - (lowMeanGroupAt k).iotaLo + 1 := by omega
  have h' := Erdos993Lean.F4Fast.forall_lt_of_range_all h _ hn
  have he : (lowMeanGroupAt k).iotaLo + (i - (lowMeanGroupAt k).iotaLo) = i := by omega
  simpa only [he] using of_decide_eq_true h'

end Erdos993Lean.Analytic.V213
