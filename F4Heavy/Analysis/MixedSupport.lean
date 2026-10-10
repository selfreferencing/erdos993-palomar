module

public import F4Heavy.Analysis.MixedLogPayment

@[expose] public section
set_option autoImplicit false

namespace F4Heavy.Analysis
open F4Unified

theorem mixedPayment_response_difference (r : Row) (lam Y rho u y theta P lo hi L : ℝ) :
    mixedPayment r lam Y rho u y theta P lo hi -
      responsePolynomial (p lam Y*tangentN r lam Y rho theta P/lo)
        (p lam Y*beta r lam*rho) (p lam Y*(2*P-alpha r lam-beta r lam))
        (gamma r lam-delta r lam-p lam Y*hi*P) (delta r lam) L (childH u) y =
    reserve r lam u y-delta r lam*(childH u-y)^2/L := by
  unfold mixedPayment responsePolynomial
  ring

theorem mixedPayment_response_lower_bound (r : Row) (lam Y rho u y theta P lo hi L : ℝ)
    (hdelta : 0 ≤ delta r lam) (hadm : Admissible lam u y)
    (hJL : childJ lam u ≤ L) :
    responsePolynomial (p lam Y*tangentN r lam Y rho theta P/lo)
      (p lam Y*beta r lam*rho) (p lam Y*(2*P-alpha r lam-beta r lam))
      (gamma r lam-delta r lam-p lam Y*hi*P) (delta r lam) L (childH u) y ≤
    mixedPayment r lam Y rho u y theta P lo hi := by
  have hreserve : delta r lam*(childH u-y)^2/L ≤ reserve r lam u y := by
    rcases hadm with hJ | ⟨hJ, hy⟩
    · exact reserve_envelope_lower_bound r lam u y L hdelta hJ hJL
    · rw [hy]
      simp [reserve]
  have heq := mixedPayment_response_difference r lam Y rho u y theta P lo hi L
  linarith only [heq, hreserve]

theorem mixedPayment_positive_of_response (r : Row) (lam Y rho u y theta P lo hi L : ℝ)
    (hdelta : 0 ≤ delta r lam) (hadm : Admissible lam u y)
    (hJL : childJ lam u ≤ L)
    (hpos : 0 < responsePolynomial (p lam Y*tangentN r lam Y rho theta P/lo)
      (p lam Y*beta r lam*rho) (p lam Y*(2*P-alpha r lam-beta r lam))
      (gamma r lam-delta r lam-p lam Y*hi*P) (delta r lam) L (childH u) y) :
    0 < mixedPayment r lam Y rho u y theta P lo hi := by
  exact hpos.trans_le (mixedPayment_response_lower_bound r lam Y rho u y theta P lo hi L
    hdelta hadm hJL)

end F4Heavy.Analysis
