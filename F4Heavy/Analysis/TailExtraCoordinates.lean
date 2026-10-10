module

public import F4Heavy.Analysis.TailIdentityCoordinates
public import F4Heavy.Analysis.TailPolynomialForms

@[expose] public section
set_option autoImplicit false
namespace F4Heavy.Analysis
open F4Unified F4Heavy.Finite

def reflectTailExtraDPrice : PolynomialExpr := (.const ⟨(8), 5⟩)

theorem reflectTailExtraDPrice_value (v x : ℝ) : reflectTailExtraDPrice.value v x = (rowData .D).price := by
  norm_num [reflectTailExtraDPrice, PolynomialExpr.value, fractionValue, rowData, tailEta]

def reflectTailExtraDEta : PolynomialExpr := (.const ⟨(1), 5⟩)

theorem reflectTailExtraDEta_value (v x : ℝ) : reflectTailExtraDEta.value v x = tailEta .D := by
  norm_num [reflectTailExtraDEta, PolynomialExpr.value, fractionValue, rowData, tailEta]

def reflectTailExtraE1Price : PolynomialExpr := (.const ⟨(17), 10⟩)

theorem reflectTailExtraE1Price_value (v x : ℝ) : reflectTailExtraE1Price.value v x = (rowData .E1).price := by
  norm_num [reflectTailExtraE1Price, PolynomialExpr.value, fractionValue, rowData, tailEta]

def reflectTailExtraE1Eta : PolynomialExpr := (.const ⟨(0), 1⟩)

theorem reflectTailExtraE1Eta_value (v x : ℝ) : reflectTailExtraE1Eta.value v x = tailEta .E1 := by
  norm_num [reflectTailExtraE1Eta, PolynomialExpr.value, fractionValue, rowData, tailEta]

def reflectTailExtraE2Price : PolynomialExpr := (.const ⟨(17), 10⟩)

theorem reflectTailExtraE2Price_value (v x : ℝ) : reflectTailExtraE2Price.value v x = (rowData .E2).price := by
  norm_num [reflectTailExtraE2Price, PolynomialExpr.value, fractionValue, rowData, tailEta]

def reflectTailExtraE2Eta : PolynomialExpr := (.const ⟨(0), 1⟩)

theorem reflectTailExtraE2Eta_value (v x : ℝ) : reflectTailExtraE2Eta.value v x = tailEta .E2 := by
  norm_num [reflectTailExtraE2Eta, PolynomialExpr.value, fractionValue, rowData, tailEta]

def reflectTailExtraHPrice : PolynomialExpr := (.const ⟨(2), 1⟩)

theorem reflectTailExtraHPrice_value (v x : ℝ) : reflectTailExtraHPrice.value v x = (rowData .H).price := by
  norm_num [reflectTailExtraHPrice, PolynomialExpr.value, fractionValue, rowData, tailEta]

def reflectTailExtraHEta : PolynomialExpr := (.const ⟨(1), 10⟩)

theorem reflectTailExtraHEta_value (v x : ℝ) : reflectTailExtraHEta.value v x = tailEta .H := by
  norm_num [reflectTailExtraHEta, PolynomialExpr.value, fractionValue, rowData, tailEta]

end F4Heavy.Analysis
