module

public import Erdos993Lean.BCFG.WholePacket

/-!
Minimal named assumption boundary for the optional BCFG analytic transfer.
The finite positivity input is fixed to the actual 28 generated arrays.
Vertex, eligibility, occupation and Phi below are explicitly abstract inputs.
No forest interpretation, clearing identity, or inhabitant of the transfer
contract is supplied here.


-/

@[expose] public section

set_option autoImplicit false

universe u

namespace Erdos993Lean.BCFG

inductive AnalyticRow where
  | B | C | F | G
  deriving DecidableEq, Repr

/-- Names of the seven determinant functions, not definitions of those functions. -/
inductive DeterminantFunction where
  | H0 | H3 | H1 | H2 | J | C0 | C1
  deriving DecidableEq, Repr

/-- Fixed lookup into the actual packet arrays; there is no arbitrary polynomial input. -/
def analyticPolynomialId : AnalyticRow → DeterminantFunction → Packet.PolynomialId
  | .B, .H0 => .bHeavyB0
  | .B, .H3 => .bHeavyB3
  | .B, .H1 => .bHeavyH1
  | .B, .H2 => .bHeavyH2
  | .B, .J => .bLightCurvature
  | .B, .C0 => .bLightLeft
  | .B, .C1 => .bLightRight
  | .C, .H0 => .cHeavyB0
  | .C, .H3 => .cHeavyB3
  | .C, .H1 => .cHeavyH1
  | .C, .H2 => .cHeavyH2
  | .C, .J => .cLightCurvature
  | .C, .C0 => .cLightLeft
  | .C, .C1 => .cLightRight
  | .F, .H0 => .fHeavyB0
  | .F, .H3 => .fHeavyB3
  | .F, .H1 => .fHeavyH1
  | .F, .H2 => .fHeavyH2
  | .F, .J => .fLightCurvature
  | .F, .C0 => .fLightLeft
  | .F, .C1 => .fLightRight
  | .G, .H0 => .gHeavyB0
  | .G, .H3 => .gHeavyB3
  | .G, .H1 => .gHeavyH1
  | .G, .H2 => .gHeavyH2
  | .G, .J => .gLightCurvature
  | .G, .C0 => .gLightLeft
  | .G, .C1 => .gLightRight

/-- The activity interval is read from the fixed packet data, including both ends. -/
def InAnalyticRow (r : AnalyticRow) (lambda : Real) : Prop :=
  ((Packet.data (analyticPolynomialId r .H0)).l : Real) ≤ lambda ∧
    lambda ≤ ((Packet.data (analyticPolynomialId r .H0)).h : Real)

/-- Positivity of the seven actual full polynomials on their own exact domains. -/
def RowPolynomialPositive (r : AnalyticRow) : Prop :=
  ∀ (f : DeterminantFunction) (lambda y : Real),
    ((Packet.data (analyticPolynomialId r f)).l : Real) ≤ lambda ∧
      lambda ≤ ((Packet.data (analyticPolynomialId r f)).h : Real) →
    ((Packet.data (analyticPolynomialId r f)).a : Real) ≤ y ∧
      y ≤ ((Packet.data (analyticPolynomialId r f)).a : Real) +
        ((Packet.data (analyticPolynomialId r f)).b : Real) →
    0 < Bi.evalReal (Packet.data (analyticPolynomialId r f)).p lambda y

/-- Reuses the unconditional finite core; this has no analytic transfer hypothesis. -/
theorem row_polynomials_positive (r : AnalyticRow) : RowPolynomialPositive r := by
  intro f lambda y hlambda hy
  exact Packet.all_whole_polynomials_positive (analyticPolynomialId r f) hlambda hy

/-- An abstract interface only. Phi is supplied by the caller, not defined here
as an actual forest payment or identified with the older O2 BandData.Phi.
A future forest instantiation must give those definitions and identification. -/
structure AbstractVertexPayment (Vertex : Type u) where
  row : Vertex → AnalyticRow
  activity : Vertex → Real
  p : Vertex → Real
  Phi : Vertex → Real
  eligible : Vertex → Prop

/-- Named remaining assumption, in the repository's Prop-record style.
Proving this field for an actual forest interface requires the entire analytic
transfer: correct payment normalization/identification, local reduction,
source fix 1, log/mass/gate facts, determinant decompositions and positive
clearing identities, matrix sign and all responses, tails, leaves and coverage.
None of those obligations is asserted as proved by this structure declaration. -/
structure BCFGAnalyticTransfer {Vertex : Type u}
    (I : AbstractVertexPayment Vertex) : Prop where
  transfer_of_row_polynomials : ∀ v : Vertex,
    I.eligible v → InAnalyticRow (I.row v) (I.activity v) → 0 < I.p v →
    RowPolynomialPositive (I.row v) → I.p v / 10000 < I.Phi v

/-- Conditional assembly only. The named transfer is a real hypothesis;
no inhabitant of it, concrete graph claim, or forest payment definition is supplied. -/
theorem vertex_payment_pos_of_transfer {Vertex : Type u}
    (I : AbstractVertexPayment Vertex) (transfer : BCFGAnalyticTransfer I)
    (v : Vertex) (hv : I.eligible v)
    (hlambda : InAnalyticRow (I.row v) (I.activity v)) (hp : 0 < I.p v) :
    I.p v / 10000 < I.Phi v := by
  exact transfer.transfer_of_row_polynomials v hv hlambda hp
    (row_polynomials_positive (I.row v))

end Erdos993Lean.BCFG
