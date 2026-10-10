module

public import F4Heavy.Analysis.PolynomialIdentity
public import F4Heavy.Analysis.TailDefinitions

@[expose] public section
set_option autoImplicit false
namespace F4Heavy.Analysis
open F4Unified F4Heavy.Finite

def reflectTailDAlpha : PolynomialExpr :=
  (.mul (.add (.const ⟨(46809), 1⟩) (.mul (.const ⟨(3327), 1⟩) (.add .parent (.mul (.const ⟨(-1), 1⟩) (.const ⟨(269), 256⟩))))) (.const ⟨(1), 65536⟩))

theorem reflectTailDAlpha_value (v x : ℝ) : reflectTailDAlpha.value v x = alpha .D x := by
  norm_num [reflectTailDAlpha, PolynomialExpr.value, fractionValue, alpha, beta, gamma, delta, field, rowData]
  <;> ring

def reflectTailDBeta : PolynomialExpr :=
  (.mul (.add (.const ⟨(35136), 1⟩) (.mul (.const ⟨(3086), 1⟩) (.add .parent (.mul (.const ⟨(-1), 1⟩) (.const ⟨(269), 256⟩))))) (.const ⟨(1), 65536⟩))

theorem reflectTailDBeta_value (v x : ℝ) : reflectTailDBeta.value v x = beta .D x := by
  norm_num [reflectTailDBeta, PolynomialExpr.value, fractionValue, alpha, beta, gamma, delta, field, rowData]
  <;> ring

def reflectTailDGamma : PolynomialExpr :=
  (.mul (.add (.const ⟨(14520), 1⟩) (.mul (.const ⟨(13694), 1⟩) (.add .parent (.mul (.const ⟨(-1), 1⟩) (.const ⟨(269), 256⟩))))) (.const ⟨(1), 65536⟩))

theorem reflectTailDGamma_value (v x : ℝ) : reflectTailDGamma.value v x = gamma .D x := by
  norm_num [reflectTailDGamma, PolynomialExpr.value, fractionValue, alpha, beta, gamma, delta, field, rowData]
  <;> ring

def reflectTailDDelta : PolynomialExpr :=
  (.mul (.add (.const ⟨(1835), 1⟩) (.mul (.const ⟨(1340), 1⟩) (.add .parent (.mul (.const ⟨(-1), 1⟩) (.const ⟨(269), 256⟩))))) (.const ⟨(1), 65536⟩))

theorem reflectTailDDelta_value (v x : ℝ) : reflectTailDDelta.value v x = delta .D x := by
  norm_num [reflectTailDDelta, PolynomialExpr.value, fractionValue, alpha, beta, gamma, delta, field, rowData]
  <;> ring

def reflectTailDScale : PolynomialExpr :=
  (.const ⟨(16), 5⟩)

theorem reflectTailDScale_value (v x : ℝ) : reflectTailDScale.value v x = tailScale .D := by
  norm_num [reflectTailDScale, PolynomialExpr.value, fractionValue, tailScale]
  <;> ring

def reflectTailDLo : PolynomialExpr :=
  (.add (.add (.const ⟨(188099060), 100000000⟩) (.mul (.add .parent (.mul (.const ⟨(-1), 1⟩) (.const ⟨(21), 20⟩))) (.const ⟨(20), 41⟩))) (.mul (.const ⟨(-1), 1⟩) (.mul (.add (.const ⟨(1), 2⟩) (.const ⟨(8405), 139968⟩)) (.pow (.mul (.add .parent (.mul (.const ⟨(-1), 1⟩) (.const ⟨(21), 20⟩))) (.const ⟨(20), 41⟩)) 2))))

theorem reflectTailDLo_value (v x : ℝ) : reflectTailDLo.value v x = tailTauLo .D x := by
  norm_num [reflectTailDLo, PolynomialExpr.value, fractionValue, tailTauLo, tailTauHi, tailLogLo, tailLogHi, tailCoordinate, tailEpsilon, tailRadius, tailMid, rowData]
  <;> ring

def reflectTailDHi : PolynomialExpr :=
  (.add (.add (.const ⟨(188099061), 100000000⟩) (.mul (.add .parent (.mul (.const ⟨(-1), 1⟩) (.const ⟨(21), 20⟩))) (.const ⟨(20), 41⟩))) (.mul (.const ⟨(-1), 1⟩) (.mul (.add (.const ⟨(1), 2⟩) (.mul (.const ⟨(-1), 1⟩) (.const ⟨(8405), 139968⟩))) (.pow (.mul (.add .parent (.mul (.const ⟨(-1), 1⟩) (.const ⟨(21), 20⟩))) (.const ⟨(20), 41⟩)) 2))))

theorem reflectTailDHi_value (v x : ℝ) : reflectTailDHi.value v x = tailTauHi .D x := by
  norm_num [reflectTailDHi, PolynomialExpr.value, fractionValue, tailTauLo, tailTauHi, tailLogLo, tailLogHi, tailCoordinate, tailEpsilon, tailRadius, tailMid, rowData]
  <;> ring

def reflectTailE1Alpha : PolynomialExpr :=
  (.mul (.add (.const ⟨(44917), 1⟩) (.mul (.const ⟨(29958), 1⟩) (.add .parent (.mul (.const ⟨(-1), 1⟩) (.const ⟨(11), 8⟩))))) (.const ⟨(1), 65536⟩))

theorem reflectTailE1Alpha_value (v x : ℝ) : reflectTailE1Alpha.value v x = alpha .E1 x := by
  norm_num [reflectTailE1Alpha, PolynomialExpr.value, fractionValue, alpha, beta, gamma, delta, field, rowData]
  <;> ring

def reflectTailE1Beta : PolynomialExpr :=
  (.mul (.add (.const ⟨(28533), 1⟩) (.mul (.const ⟨(57271), 1⟩) (.add .parent (.mul (.const ⟨(-1), 1⟩) (.const ⟨(11), 8⟩))))) (.const ⟨(1), 65536⟩))

theorem reflectTailE1Beta_value (v x : ℝ) : reflectTailE1Beta.value v x = beta .E1 x := by
  norm_num [reflectTailE1Beta, PolynomialExpr.value, fractionValue, alpha, beta, gamma, delta, field, rowData]
  <;> ring

def reflectTailE1Gamma : PolynomialExpr :=
  (.mul (.add (.const ⟨(17821), 1⟩) (.mul (.const ⟨(20483), 1⟩) (.add .parent (.mul (.const ⟨(-1), 1⟩) (.const ⟨(11), 8⟩))))) (.const ⟨(1), 65536⟩))

theorem reflectTailE1Gamma_value (v x : ℝ) : reflectTailE1Gamma.value v x = gamma .E1 x := by
  norm_num [reflectTailE1Gamma, PolynomialExpr.value, fractionValue, alpha, beta, gamma, delta, field, rowData]
  <;> ring

def reflectTailE1Delta : PolynomialExpr :=
  (.mul (.add (.const ⟨(3064), 1⟩) (.mul (.const ⟨(-4423), 1⟩) (.add .parent (.mul (.const ⟨(-1), 1⟩) (.const ⟨(11), 8⟩))))) (.const ⟨(1), 65536⟩))

theorem reflectTailE1Delta_value (v x : ℝ) : reflectTailE1Delta.value v x = delta .E1 x := by
  norm_num [reflectTailE1Delta, PolynomialExpr.value, fractionValue, alpha, beta, gamma, delta, field, rowData]
  <;> ring

def reflectTailE1Scale : PolynomialExpr :=
  (.const ⟨(4), 1⟩)

theorem reflectTailE1Scale_value (v x : ℝ) : reflectTailE1Scale.value v x = tailScale .E1 := by
  norm_num [reflectTailE1Scale, PolynomialExpr.value, fractionValue, tailScale]
  <;> ring

def reflectTailE1Lo : PolynomialExpr :=
  (.add (.add (.const ⟨(225129179), 100000000⟩) (.mul (.add .parent (.mul (.const ⟨(-1), 1⟩) (.const ⟨(11), 8⟩))) (.const ⟨(8), 19⟩))) (.mul (.const ⟨(-1), 1⟩) (.mul (.add (.const ⟨(1), 2⟩) (.const ⟨(9025), 778688⟩)) (.pow (.mul (.add .parent (.mul (.const ⟨(-1), 1⟩) (.const ⟨(11), 8⟩))) (.const ⟨(8), 19⟩)) 2))))

theorem reflectTailE1Lo_value (v x : ℝ) : reflectTailE1Lo.value v x = tailTauLo .E1 x := by
  norm_num [reflectTailE1Lo, PolynomialExpr.value, fractionValue, tailTauLo, tailTauHi, tailLogLo, tailLogHi, tailCoordinate, tailEpsilon, tailRadius, tailMid, rowData]
  <;> ring

def reflectTailE1Hi : PolynomialExpr :=
  (.add (.add (.const ⟨(225129180), 100000000⟩) (.mul (.add .parent (.mul (.const ⟨(-1), 1⟩) (.const ⟨(11), 8⟩))) (.const ⟨(8), 19⟩))) (.mul (.const ⟨(-1), 1⟩) (.mul (.add (.const ⟨(1), 2⟩) (.mul (.const ⟨(-1), 1⟩) (.const ⟨(9025), 778688⟩))) (.pow (.mul (.add .parent (.mul (.const ⟨(-1), 1⟩) (.const ⟨(11), 8⟩))) (.const ⟨(8), 19⟩)) 2))))

theorem reflectTailE1Hi_value (v x : ℝ) : reflectTailE1Hi.value v x = tailTauHi .E1 x := by
  norm_num [reflectTailE1Hi, PolynomialExpr.value, fractionValue, tailTauLo, tailTauHi, tailLogLo, tailLogHi, tailCoordinate, tailEpsilon, tailRadius, tailMid, rowData]
  <;> ring

def reflectTailE2Alpha : PolynomialExpr :=
  (.mul (.add (.const ⟨(45775), 1⟩) (.mul (.const ⟨(22238), 1⟩) (.add .parent (.mul (.const ⟨(-1), 1⟩) (.const ⟨(195), 128⟩))))) (.const ⟨(1), 65536⟩))

theorem reflectTailE2Alpha_value (v x : ℝ) : reflectTailE2Alpha.value v x = alpha .E2 x := by
  norm_num [reflectTailE2Alpha, PolynomialExpr.value, fractionValue, alpha, beta, gamma, delta, field, rowData]
  <;> ring

def reflectTailE2Beta : PolynomialExpr :=
  (.mul (.add (.const ⟨(30825), 1⟩) (.mul (.const ⟨(10297), 1⟩) (.add .parent (.mul (.const ⟨(-1), 1⟩) (.const ⟨(195), 128⟩))))) (.const ⟨(1), 65536⟩))

theorem reflectTailE2Beta_value (v x : ℝ) : reflectTailE2Beta.value v x = beta .E2 x := by
  norm_num [reflectTailE2Beta, PolynomialExpr.value, fractionValue, alpha, beta, gamma, delta, field, rowData]
  <;> ring

def reflectTailE2Gamma : PolynomialExpr :=
  (.mul (.add (.const ⟨(19913), 1⟩) (.mul (.const ⟨(13978), 1⟩) (.add .parent (.mul (.const ⟨(-1), 1⟩) (.const ⟨(195), 128⟩))))) (.const ⟨(1), 65536⟩))

theorem reflectTailE2Gamma_value (v x : ℝ) : reflectTailE2Gamma.value v x = gamma .E2 x := by
  norm_num [reflectTailE2Gamma, PolynomialExpr.value, fractionValue, alpha, beta, gamma, delta, field, rowData]
  <;> ring

def reflectTailE2Delta : PolynomialExpr :=
  (.mul (.add (.const ⟨(3161), 1⟩) (.mul (.const ⟨(4340), 1⟩) (.add .parent (.mul (.const ⟨(-1), 1⟩) (.const ⟨(195), 128⟩))))) (.const ⟨(1), 65536⟩))

theorem reflectTailE2Delta_value (v x : ℝ) : reflectTailE2Delta.value v x = delta .E2 x := by
  norm_num [reflectTailE2Delta, PolynomialExpr.value, fractionValue, alpha, beta, gamma, delta, field, rowData]
  <;> ring

def reflectTailE2Scale : PolynomialExpr :=
  (.const ⟨(4), 1⟩)

theorem reflectTailE2Scale_value (v x : ℝ) : reflectTailE2Scale.value v x = tailScale .E2 := by
  norm_num [reflectTailE2Scale, PolynomialExpr.value, fractionValue, tailScale]
  <;> ring

def reflectTailE2Lo : PolynomialExpr :=
  (.add (.add (.const ⟨(231253542), 100000000⟩) (.mul (.add .parent (.mul (.const ⟨(-1), 1⟩) (.const ⟨(61), 40⟩))) (.const ⟨(40), 101⟩))) (.mul (.const ⟨(-1), 1⟩) (.mul (.add (.const ⟨(1), 2⟩) (.const ⟨(10201), 941192⟩)) (.pow (.mul (.add .parent (.mul (.const ⟨(-1), 1⟩) (.const ⟨(61), 40⟩))) (.const ⟨(40), 101⟩)) 2))))

theorem reflectTailE2Lo_value (v x : ℝ) : reflectTailE2Lo.value v x = tailTauLo .E2 x := by
  norm_num [reflectTailE2Lo, PolynomialExpr.value, fractionValue, tailTauLo, tailTauHi, tailLogLo, tailLogHi, tailCoordinate, tailEpsilon, tailRadius, tailMid, rowData]
  <;> ring

def reflectTailE2Hi : PolynomialExpr :=
  (.add (.add (.const ⟨(231253543), 100000000⟩) (.mul (.add .parent (.mul (.const ⟨(-1), 1⟩) (.const ⟨(61), 40⟩))) (.const ⟨(40), 101⟩))) (.mul (.const ⟨(-1), 1⟩) (.mul (.add (.const ⟨(1), 2⟩) (.mul (.const ⟨(-1), 1⟩) (.const ⟨(10201), 941192⟩))) (.pow (.mul (.add .parent (.mul (.const ⟨(-1), 1⟩) (.const ⟨(61), 40⟩))) (.const ⟨(40), 101⟩)) 2))))

theorem reflectTailE2Hi_value (v x : ℝ) : reflectTailE2Hi.value v x = tailTauHi .E2 x := by
  norm_num [reflectTailE2Hi, PolynomialExpr.value, fractionValue, tailTauLo, tailTauHi, tailLogLo, tailLogHi, tailCoordinate, tailEpsilon, tailRadius, tailMid, rowData]
  <;> ring

def reflectTailHAlpha : PolynomialExpr :=
  (.mul (.add (.const ⟨(51799), 1⟩) (.mul (.const ⟨(8158), 1⟩) (.add .parent (.mul (.const ⟨(-1), 1⟩) (.const ⟨(523), 256⟩))))) (.const ⟨(1), 65536⟩))

theorem reflectTailHAlpha_value (v x : ℝ) : reflectTailHAlpha.value v x = alpha .H x := by
  norm_num [reflectTailHAlpha, PolynomialExpr.value, fractionValue, alpha, beta, gamma, delta, field, rowData]
  <;> ring

def reflectTailHBeta : PolynomialExpr :=
  (.mul (.add (.const ⟨(20496), 1⟩) (.mul (.const ⟨(41265), 1⟩) (.add .parent (.mul (.const ⟨(-1), 1⟩) (.const ⟨(523), 256⟩))))) (.const ⟨(1), 65536⟩))

theorem reflectTailHBeta_value (v x : ℝ) : reflectTailHBeta.value v x = beta .H x := by
  norm_num [reflectTailHBeta, PolynomialExpr.value, fractionValue, alpha, beta, gamma, delta, field, rowData]
  <;> ring

def reflectTailHGamma : PolynomialExpr :=
  (.mul (.add (.const ⟨(29750), 1⟩) (.mul (.const ⟨(4333), 1⟩) (.add .parent (.mul (.const ⟨(-1), 1⟩) (.const ⟨(523), 256⟩))))) (.const ⟨(1), 65536⟩))

theorem reflectTailHGamma_value (v x : ℝ) : reflectTailHGamma.value v x = gamma .H x := by
  norm_num [reflectTailHGamma, PolynomialExpr.value, fractionValue, alpha, beta, gamma, delta, field, rowData]
  <;> ring

def reflectTailHDelta : PolynomialExpr :=
  (.mul (.add (.const ⟨(9083), 1⟩) (.mul (.const ⟨(-11181), 1⟩) (.add .parent (.mul (.const ⟨(-1), 1⟩) (.const ⟨(523), 256⟩))))) (.const ⟨(1), 65536⟩))

theorem reflectTailHDelta_value (v x : ℝ) : reflectTailHDelta.value v x = delta .H x := by
  norm_num [reflectTailHDelta, PolynomialExpr.value, fractionValue, alpha, beta, gamma, delta, field, rowData]
  <;> ring

def reflectTailHScale : PolynomialExpr :=
  (.const ⟨(4), 1⟩)

theorem reflectTailHScale_value (v x : ℝ) : reflectTailHScale.value v x = tailScale .H := by
  norm_num [reflectTailHScale, PolynomialExpr.value, fractionValue, tailScale]
  <;> ring

def reflectTailHLo : PolynomialExpr :=
  (.add (.add (.const ⟨(249869997), 100000000⟩) (.mul (.add .parent (.mul (.const ⟨(-1), 1⟩) (.const ⟨(49), 24⟩))) (.const ⟨(24), 73⟩))) (.mul (.const ⟨(-1), 1⟩) (.mul (.add (.const ⟨(1), 2⟩) (.const ⟨(37303), 862488⟩)) (.pow (.mul (.add .parent (.mul (.const ⟨(-1), 1⟩) (.const ⟨(49), 24⟩))) (.const ⟨(24), 73⟩)) 2))))

theorem reflectTailHLo_value (v x : ℝ) : reflectTailHLo.value v x = tailTauLo .H x := by
  norm_num [reflectTailHLo, PolynomialExpr.value, fractionValue, tailTauLo, tailTauHi, tailLogLo, tailLogHi, tailCoordinate, tailEpsilon, tailRadius, tailMid, rowData]
  <;> ring

def reflectTailHHi : PolynomialExpr :=
  (.add (.add (.const ⟨(249869998), 100000000⟩) (.mul (.add .parent (.mul (.const ⟨(-1), 1⟩) (.const ⟨(49), 24⟩))) (.const ⟨(24), 73⟩))) (.mul (.const ⟨(-1), 1⟩) (.mul (.add (.const ⟨(1), 2⟩) (.mul (.const ⟨(-1), 1⟩) (.const ⟨(37303), 862488⟩))) (.pow (.mul (.add .parent (.mul (.const ⟨(-1), 1⟩) (.const ⟨(49), 24⟩))) (.const ⟨(24), 73⟩)) 2))))

theorem reflectTailHHi_value (v x : ℝ) : reflectTailHHi.value v x = tailTauHi .H x := by
  norm_num [reflectTailHHi, PolynomialExpr.value, fractionValue, tailTauLo, tailTauHi, tailLogLo, tailLogHi, tailCoordinate, tailEpsilon, tailRadius, tailMid, rowData]
  <;> ring

end F4Heavy.Analysis
