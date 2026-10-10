module

public import Erdos993Lean.BCFG.Generated.All

/-!
Aggregate for the 28 specified BCFG packet polynomials. This module reuses
all per-polynomial positivity/shape theorems; it performs no certificate replay.

The forest/analytic clearing contract is deliberately outside this theorem.
-/

@[expose] public section
set_option autoImplicit false

namespace Erdos993Lean.BCFG.Packet

open CertData

/-- One constructor for each original certificate-index ID, in packet order. -/
inductive PolynomialId where
  | bHeavyB0
  | bHeavyB3
  | bHeavyH1
  | bHeavyH2
  | bLightCurvature
  | bLightLeft
  | bLightRight
  | cHeavyB0
  | cHeavyB3
  | cHeavyH1
  | cHeavyH2
  | cLightCurvature
  | cLightLeft
  | cLightRight
  | fHeavyB0
  | fHeavyB3
  | fHeavyH1
  | fHeavyH2
  | fLightCurvature
  | fLightLeft
  | fLightRight
  | gHeavyB0
  | gHeavyB3
  | gHeavyH1
  | gHeavyH2
  | gLightCurvature
  | gLightLeft
  | gLightRight
  deriving DecidableEq, Repr

/-- The source polynomial, normalization data and exact closed-domain chart. -/
structure PolynomialData where
  id : String
  N : Nat
  M : Nat
  p : Bi
  A : Bi
  lower : List Rat
  intervals : List IntervalCertificate
  l : Rat
  h : Rat
  a : Rat
  b : Rat

def data : PolynomialId → PolynomialData
  | .bHeavyB0 =>
      ⟨BHeavyB0.polynomialId, BHeavyB0.N, BHeavyB0.M, BHeavyB0.p, BHeavyB0.A,
        BHeavyB0.lower, BHeavyB0.intervals, BHeavyB0.l, BHeavyB0.h, BHeavyB0.a, BHeavyB0.b⟩
  | .bHeavyB3 =>
      ⟨BHeavyB3.polynomialId, BHeavyB3.N, BHeavyB3.M, BHeavyB3.p, BHeavyB3.A,
        BHeavyB3.lower, BHeavyB3.intervals, BHeavyB3.l, BHeavyB3.h, BHeavyB3.a, BHeavyB3.b⟩
  | .bHeavyH1 =>
      ⟨BHeavyH1.polynomialId, BHeavyH1.N, BHeavyH1.M, BHeavyH1.p, BHeavyH1.A,
        BHeavyH1.lower, BHeavyH1.intervals, BHeavyH1.l, BHeavyH1.h, BHeavyH1.a, BHeavyH1.b⟩
  | .bHeavyH2 =>
      ⟨BHeavyH2.polynomialId, BHeavyH2.N, BHeavyH2.M, BHeavyH2.p, BHeavyH2.A,
        BHeavyH2.lower, BHeavyH2.intervals, BHeavyH2.l, BHeavyH2.h, BHeavyH2.a, BHeavyH2.b⟩
  | .bLightCurvature =>
      ⟨BLightCurvature.polynomialId, BLightCurvature.N, BLightCurvature.M, BLightCurvature.p, BLightCurvature.A,
        BLightCurvature.lower, BLightCurvature.intervals, BLightCurvature.l, BLightCurvature.h, BLightCurvature.a, BLightCurvature.b⟩
  | .bLightLeft =>
      ⟨BLightLeft.polynomialId, BLightLeft.N, BLightLeft.M, BLightLeft.p, BLightLeft.A,
        BLightLeft.lower, BLightLeft.intervals, BLightLeft.l, BLightLeft.h, BLightLeft.a, BLightLeft.b⟩
  | .bLightRight =>
      ⟨BLightRight.polynomialId, BLightRight.N, BLightRight.M, BLightRight.p, BLightRight.A,
        BLightRight.lower, BLightRight.intervals, BLightRight.l, BLightRight.h, BLightRight.a, BLightRight.b⟩
  | .cHeavyB0 =>
      ⟨CHeavyB0.polynomialId, CHeavyB0.N, CHeavyB0.M, CHeavyB0.p, CHeavyB0.A,
        CHeavyB0.lower, CHeavyB0.intervals, CHeavyB0.l, CHeavyB0.h, CHeavyB0.a, CHeavyB0.b⟩
  | .cHeavyB3 =>
      ⟨CHeavyB3.polynomialId, CHeavyB3.N, CHeavyB3.M, CHeavyB3.p, CHeavyB3.A,
        CHeavyB3.lower, CHeavyB3.intervals, CHeavyB3.l, CHeavyB3.h, CHeavyB3.a, CHeavyB3.b⟩
  | .cHeavyH1 =>
      ⟨CHeavyH1.polynomialId, CHeavyH1.N, CHeavyH1.M, CHeavyH1.p, CHeavyH1.A,
        CHeavyH1.lower, CHeavyH1.intervals, CHeavyH1.l, CHeavyH1.h, CHeavyH1.a, CHeavyH1.b⟩
  | .cHeavyH2 =>
      ⟨CHeavyH2.polynomialId, CHeavyH2.N, CHeavyH2.M, CHeavyH2.p, CHeavyH2.A,
        CHeavyH2.lower, CHeavyH2.intervals, CHeavyH2.l, CHeavyH2.h, CHeavyH2.a, CHeavyH2.b⟩
  | .cLightCurvature =>
      ⟨CLightCurvature.polynomialId, CLightCurvature.N, CLightCurvature.M, CLightCurvature.p, CLightCurvature.A,
        CLightCurvature.lower, CLightCurvature.intervals, CLightCurvature.l, CLightCurvature.h, CLightCurvature.a, CLightCurvature.b⟩
  | .cLightLeft =>
      ⟨CLightLeft.polynomialId, CLightLeft.N, CLightLeft.M, CLightLeft.p, CLightLeft.A,
        CLightLeft.lower, CLightLeft.intervals, CLightLeft.l, CLightLeft.h, CLightLeft.a, CLightLeft.b⟩
  | .cLightRight =>
      ⟨CLightRight.polynomialId, CLightRight.N, CLightRight.M, CLightRight.p, CLightRight.A,
        CLightRight.lower, CLightRight.intervals, CLightRight.l, CLightRight.h, CLightRight.a, CLightRight.b⟩
  | .fHeavyB0 =>
      ⟨FHeavyB0.polynomialId, FHeavyB0.N, FHeavyB0.M, FHeavyB0.p, FHeavyB0.A,
        FHeavyB0.lower, FHeavyB0.intervals, FHeavyB0.l, FHeavyB0.h, FHeavyB0.a, FHeavyB0.b⟩
  | .fHeavyB3 =>
      ⟨FHeavyB3.polynomialId, FHeavyB3.N, FHeavyB3.M, FHeavyB3.p, FHeavyB3.A,
        FHeavyB3.lower, FHeavyB3.intervals, FHeavyB3.l, FHeavyB3.h, FHeavyB3.a, FHeavyB3.b⟩
  | .fHeavyH1 =>
      ⟨FHeavyH1.polynomialId, FHeavyH1.N, FHeavyH1.M, FHeavyH1.p, FHeavyH1.A,
        FHeavyH1.lower, FHeavyH1.intervals, FHeavyH1.l, FHeavyH1.h, FHeavyH1.a, FHeavyH1.b⟩
  | .fHeavyH2 =>
      ⟨FHeavyH2.polynomialId, FHeavyH2.N, FHeavyH2.M, FHeavyH2.p, FHeavyH2.A,
        FHeavyH2.lower, FHeavyH2.intervals, FHeavyH2.l, FHeavyH2.h, FHeavyH2.a, FHeavyH2.b⟩
  | .fLightCurvature =>
      ⟨FLightCurvature.polynomialId, FLightCurvature.N, FLightCurvature.M, FLightCurvature.p, FLightCurvature.A,
        FLightCurvature.lower, FLightCurvature.intervals, FLightCurvature.l, FLightCurvature.h, FLightCurvature.a, FLightCurvature.b⟩
  | .fLightLeft =>
      ⟨FLightLeft.polynomialId, FLightLeft.N, FLightLeft.M, FLightLeft.p, FLightLeft.A,
        FLightLeft.lower, FLightLeft.intervals, FLightLeft.l, FLightLeft.h, FLightLeft.a, FLightLeft.b⟩
  | .fLightRight =>
      ⟨FLightRight.polynomialId, FLightRight.N, FLightRight.M, FLightRight.p, FLightRight.A,
        FLightRight.lower, FLightRight.intervals, FLightRight.l, FLightRight.h, FLightRight.a, FLightRight.b⟩
  | .gHeavyB0 =>
      ⟨GHeavyB0.polynomialId, GHeavyB0.N, GHeavyB0.M, GHeavyB0.p, GHeavyB0.A,
        GHeavyB0.lower, GHeavyB0.intervals, GHeavyB0.l, GHeavyB0.h, GHeavyB0.a, GHeavyB0.b⟩
  | .gHeavyB3 =>
      ⟨GHeavyB3.polynomialId, GHeavyB3.N, GHeavyB3.M, GHeavyB3.p, GHeavyB3.A,
        GHeavyB3.lower, GHeavyB3.intervals, GHeavyB3.l, GHeavyB3.h, GHeavyB3.a, GHeavyB3.b⟩
  | .gHeavyH1 =>
      ⟨GHeavyH1.polynomialId, GHeavyH1.N, GHeavyH1.M, GHeavyH1.p, GHeavyH1.A,
        GHeavyH1.lower, GHeavyH1.intervals, GHeavyH1.l, GHeavyH1.h, GHeavyH1.a, GHeavyH1.b⟩
  | .gHeavyH2 =>
      ⟨GHeavyH2.polynomialId, GHeavyH2.N, GHeavyH2.M, GHeavyH2.p, GHeavyH2.A,
        GHeavyH2.lower, GHeavyH2.intervals, GHeavyH2.l, GHeavyH2.h, GHeavyH2.a, GHeavyH2.b⟩
  | .gLightCurvature =>
      ⟨GLightCurvature.polynomialId, GLightCurvature.N, GLightCurvature.M, GLightCurvature.p, GLightCurvature.A,
        GLightCurvature.lower, GLightCurvature.intervals, GLightCurvature.l, GLightCurvature.h, GLightCurvature.a, GLightCurvature.b⟩
  | .gLightLeft =>
      ⟨GLightLeft.polynomialId, GLightLeft.N, GLightLeft.M, GLightLeft.p, GLightLeft.A,
        GLightLeft.lower, GLightLeft.intervals, GLightLeft.l, GLightLeft.h, GLightLeft.a, GLightLeft.b⟩
  | .gLightRight =>
      ⟨GLightRight.polynomialId, GLightRight.N, GLightRight.M, GLightRight.p, GLightRight.A,
        GLightRight.lower, GLightRight.intervals, GLightRight.l, GLightRight.h, GLightRight.a, GLightRight.b⟩

def allIds : List PolynomialId := [
  .bHeavyB0,
  .bHeavyB3,
  .bHeavyH1,
  .bHeavyH2,
  .bLightCurvature,
  .bLightLeft,
  .bLightRight,
  .cHeavyB0,
  .cHeavyB3,
  .cHeavyH1,
  .cHeavyH2,
  .cLightCurvature,
  .cLightLeft,
  .cLightRight,
  .fHeavyB0,
  .fHeavyB3,
  .fHeavyH1,
  .fHeavyH2,
  .fLightCurvature,
  .fLightLeft,
  .fLightRight,
  .gHeavyB0,
  .gHeavyB3,
  .gHeavyH1,
  .gHeavyH2,
  .gLightCurvature,
  .gLightLeft,
  .gLightRight
]

theorem allIds_complete (k : PolynomialId) : k ∈ allIds := by
  cases k <;> decide +kernel

theorem allIds_nodup : allIds.Nodup := by decide +kernel

theorem polynomial_count : allIds.length = 28 := by decide +kernel

/-- Exact names, in the original certificate-index order. -/
def packetIds : List String := allIds.map (fun k => (data k).id)

theorem packetIds_exact : packetIds = [
  "B.heavy.b0",
  "B.heavy.b3",
  "B.heavy.h1",
  "B.heavy.h2",
  "B.light.curvature",
  "B.light.left",
  "B.light.right",
  "C.heavy.b0",
  "C.heavy.b3",
  "C.heavy.h1",
  "C.heavy.h2",
  "C.light.curvature",
  "C.light.left",
  "C.light.right",
  "F.heavy.b0",
  "F.heavy.b3",
  "F.heavy.h1",
  "F.heavy.h2",
  "F.light.curvature",
  "F.light.left",
  "F.light.right",
  "G.heavy.b0",
  "G.heavy.b3",
  "G.heavy.h1",
  "G.heavy.h2",
  "G.light.curvature",
  "G.light.left",
  "G.light.right"
] := rfl

/-- Single axiom-report target for all 28 specified polynomials.
The domain is closed; each proof is the already established per-ID theorem. -/
theorem all_polynomials_positive (k : PolynomialId) {lambda y : Real}
    (hlambda : ((data k).l : Real) ≤ lambda ∧ lambda ≤ ((data k).h : Real))
    (hy : ((data k).a : Real) ≤ y ∧ y ≤ ((data k).a : Real)+((data k).b : Real)) :
    0 < Bi.sourceEval (data k).N (data k).p lambda y := by
  cases k with
  | bHeavyB0 => exact BHeavyB0.positive hlambda hy
  | bHeavyB3 => exact BHeavyB3.positive hlambda hy
  | bHeavyH1 => exact BHeavyH1.positive hlambda hy
  | bHeavyH2 => exact BHeavyH2.positive hlambda hy
  | bLightCurvature => exact BLightCurvature.positive hlambda hy
  | bLightLeft => exact BLightLeft.positive hlambda hy
  | bLightRight => exact BLightRight.positive hlambda hy
  | cHeavyB0 => exact CHeavyB0.positive hlambda hy
  | cHeavyB3 => exact CHeavyB3.positive hlambda hy
  | cHeavyH1 => exact CHeavyH1.positive hlambda hy
  | cHeavyH2 => exact CHeavyH2.positive hlambda hy
  | cLightCurvature => exact CLightCurvature.positive hlambda hy
  | cLightLeft => exact CLightLeft.positive hlambda hy
  | cLightRight => exact CLightRight.positive hlambda hy
  | fHeavyB0 => exact FHeavyB0.positive hlambda hy
  | fHeavyB3 => exact FHeavyB3.positive hlambda hy
  | fHeavyH1 => exact FHeavyH1.positive hlambda hy
  | fHeavyH2 => exact FHeavyH2.positive hlambda hy
  | fLightCurvature => exact FLightCurvature.positive hlambda hy
  | fLightLeft => exact FLightLeft.positive hlambda hy
  | fLightRight => exact FLightRight.positive hlambda hy
  | gHeavyB0 => exact GHeavyB0.positive hlambda hy
  | gHeavyB3 => exact GHeavyB3.positive hlambda hy
  | gHeavyH1 => exact GHeavyH1.positive hlambda hy
  | gHeavyH2 => exact GHeavyH2.positive hlambda hy
  | gLightCurvature => exact GLightCurvature.positive hlambda hy
  | gLightLeft => exact GLightLeft.positive hlambda hy
  | gLightRight => exact GLightRight.positive hlambda hy

/-- Counts are functions of the actual imported coefficient lists. -/
def sourceCount (k : PolynomialId) : Nat :=
  ((data k).p.flatten.filter (fun c => c != 0)).length

def normCount (k : PolynomialId) : Nat := (data k).A.flatten.length

def lowerCount (k : PolynomialId) : Nat := (data k).lower.length

def intervalCount (k : PolynomialId) : Nat := (data k).intervals.length

def positiveCount (k : PolynomialId) : Nat :=
  ((data k).intervals.map (fun I => I.coeffs.length)).sum

def tally (f : PolynomialId → Nat) : Nat := (allIds.map f).sum

/- The following proofs rewrite the 28 existing shape theorems, then ask the
kernel to check only a sum of small natural numbers. They do not re-evaluate
rational coefficients, normalization identities, or positivity comparisons. -/

theorem source_coefficient_count : tally sourceCount = 8868 := by
  simp only [tally, allIds, sourceCount, data, List.map_cons, List.map_nil,
    BHeavyB0.source_nonzero_count,
    BHeavyB3.source_nonzero_count,
    BHeavyH1.source_nonzero_count,
    BHeavyH2.source_nonzero_count,
    BLightCurvature.source_nonzero_count,
    BLightLeft.source_nonzero_count,
    BLightRight.source_nonzero_count,
    CHeavyB0.source_nonzero_count,
    CHeavyB3.source_nonzero_count,
    CHeavyH1.source_nonzero_count,
    CHeavyH2.source_nonzero_count,
    CLightCurvature.source_nonzero_count,
    CLightLeft.source_nonzero_count,
    CLightRight.source_nonzero_count,
    FHeavyB0.source_nonzero_count,
    FHeavyB3.source_nonzero_count,
    FHeavyH1.source_nonzero_count,
    FHeavyH2.source_nonzero_count,
    FLightCurvature.source_nonzero_count,
    FLightLeft.source_nonzero_count,
    FLightRight.source_nonzero_count,
    GHeavyB0.source_nonzero_count,
    GHeavyB3.source_nonzero_count,
    GHeavyH1.source_nonzero_count,
    GHeavyH2.source_nonzero_count,
    GLightCurvature.source_nonzero_count,
    GLightLeft.source_nonzero_count,
    GLightRight.source_nonzero_count,
    List.sum_cons, List.sum_nil] <;> decide +kernel

theorem norm_coefficient_count : tally normCount = 12544 := by
  simp only [tally, allIds, normCount, data, List.map_cons, List.map_nil,
    BHeavyB0.norm_entry_count,
    BHeavyB3.norm_entry_count,
    BHeavyH1.norm_entry_count,
    BHeavyH2.norm_entry_count,
    BLightCurvature.norm_entry_count,
    BLightLeft.norm_entry_count,
    BLightRight.norm_entry_count,
    CHeavyB0.norm_entry_count,
    CHeavyB3.norm_entry_count,
    CHeavyH1.norm_entry_count,
    CHeavyH2.norm_entry_count,
    CLightCurvature.norm_entry_count,
    CLightLeft.norm_entry_count,
    CLightRight.norm_entry_count,
    FHeavyB0.norm_entry_count,
    FHeavyB3.norm_entry_count,
    FHeavyH1.norm_entry_count,
    FHeavyH2.norm_entry_count,
    FLightCurvature.norm_entry_count,
    FLightLeft.norm_entry_count,
    FLightRight.norm_entry_count,
    GHeavyB0.norm_entry_count,
    GHeavyB3.norm_entry_count,
    GHeavyH1.norm_entry_count,
    GHeavyH2.norm_entry_count,
    GLightCurvature.norm_entry_count,
    GLightLeft.norm_entry_count,
    GLightRight.norm_entry_count,
    List.sum_cons, List.sum_nil] <;> decide +kernel

theorem lower_coefficient_count : tally lowerCount = 764 := by
  simp only [tally, allIds, lowerCount, data, List.map_cons, List.map_nil,
    BHeavyB0.lower_length,
    BHeavyB3.lower_length,
    BHeavyH1.lower_length,
    BHeavyH2.lower_length,
    BLightCurvature.lower_length,
    BLightLeft.lower_length,
    BLightRight.lower_length,
    CHeavyB0.lower_length,
    CHeavyB3.lower_length,
    CHeavyH1.lower_length,
    CHeavyH2.lower_length,
    CLightCurvature.lower_length,
    CLightLeft.lower_length,
    CLightRight.lower_length,
    FHeavyB0.lower_length,
    FHeavyB3.lower_length,
    FHeavyH1.lower_length,
    FHeavyH2.lower_length,
    FLightCurvature.lower_length,
    FLightLeft.lower_length,
    FLightRight.lower_length,
    GHeavyB0.lower_length,
    GHeavyB3.lower_length,
    GHeavyH1.lower_length,
    GHeavyH2.lower_length,
    GLightCurvature.lower_length,
    GLightLeft.lower_length,
    GLightRight.lower_length,
    BHeavyB0.M, BHeavyB3.M, BHeavyH1.M, BHeavyH2.M, BLightCurvature.M, BLightLeft.M, BLightRight.M, CHeavyB0.M, CHeavyB3.M, CHeavyH1.M, CHeavyH2.M, CLightCurvature.M, CLightLeft.M, CLightRight.M, FHeavyB0.M, FHeavyB3.M, FHeavyH1.M, FHeavyH2.M, FLightCurvature.M, FLightLeft.M, FLightRight.M, GHeavyB0.M, GHeavyB3.M, GHeavyH1.M, GHeavyH2.M, GLightCurvature.M, GLightLeft.M, GLightRight.M,
    List.sum_cons, List.sum_nil] <;> decide +kernel

theorem interval_identity_count : tally intervalCount = 33 := by
  simp only [tally, allIds, intervalCount, data, List.map_cons, List.map_nil,
    BHeavyB0.interval_count,
    BHeavyB3.interval_count,
    BHeavyH1.interval_count,
    BHeavyH2.interval_count,
    BLightCurvature.interval_count,
    BLightLeft.interval_count,
    BLightRight.interval_count,
    CHeavyB0.interval_count,
    CHeavyB3.interval_count,
    CHeavyH1.interval_count,
    CHeavyH2.interval_count,
    CLightCurvature.interval_count,
    CLightLeft.interval_count,
    CLightRight.interval_count,
    FHeavyB0.interval_count,
    FHeavyB3.interval_count,
    FHeavyH1.interval_count,
    FHeavyH2.interval_count,
    FLightCurvature.interval_count,
    FLightLeft.interval_count,
    FLightRight.interval_count,
    GHeavyB0.interval_count,
    GHeavyB3.interval_count,
    GHeavyH1.interval_count,
    GHeavyH2.interval_count,
    GLightCurvature.interval_count,
    GLightLeft.interval_count,
    GLightRight.interval_count,
    List.sum_cons, List.sum_nil] <;> decide +kernel

theorem positive_coefficient_count : tally positiveCount = 914 := by
  simp only [tally, allIds, positiveCount, data, List.map_cons, List.map_nil,
    BHeavyB0.interval_coefficient_count,
    BHeavyB3.interval_coefficient_count,
    BHeavyH1.interval_coefficient_count,
    BHeavyH2.interval_coefficient_count,
    BLightCurvature.interval_coefficient_count,
    BLightLeft.interval_coefficient_count,
    BLightRight.interval_coefficient_count,
    CHeavyB0.interval_coefficient_count,
    CHeavyB3.interval_coefficient_count,
    CHeavyH1.interval_coefficient_count,
    CHeavyH2.interval_coefficient_count,
    CLightCurvature.interval_coefficient_count,
    CLightLeft.interval_coefficient_count,
    CLightRight.interval_coefficient_count,
    FHeavyB0.interval_coefficient_count,
    FHeavyB3.interval_coefficient_count,
    FHeavyH1.interval_coefficient_count,
    FHeavyH2.interval_coefficient_count,
    FLightCurvature.interval_coefficient_count,
    FLightLeft.interval_coefficient_count,
    FLightRight.interval_coefficient_count,
    GHeavyB0.interval_coefficient_count,
    GHeavyB3.interval_coefficient_count,
    GHeavyH1.interval_coefficient_count,
    GHeavyH2.interval_coefficient_count,
    GLightCurvature.interval_coefficient_count,
    GLightLeft.interval_coefficient_count,
    GLightRight.interval_coefficient_count,
    List.sum_cons, List.sum_nil] <;> decide +kernel

/-- Packet inventory, with each coefficient total derived from imported lists. -/
theorem packet_inventory :
    allIds.length = 28 ∧
    tally sourceCount = 8868 ∧
    tally normCount = 12544 ∧
    tally lowerCount = 764 ∧
    tally intervalCount = 33 ∧
    tally positiveCount = 914 :=
  ⟨polynomial_count, source_coefficient_count, norm_coefficient_count,
    lower_coefficient_count, interval_identity_count, positive_coefficient_count⟩

end Erdos993Lean.BCFG.Packet
