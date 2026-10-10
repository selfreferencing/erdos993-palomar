module

public import Erdos993Lean.BCFG.Generated.FHeavyH1.IntegerInputs
public import Erdos993Lean.BCFG.Generated.FHeavyH1.IntegerBasis
public import Erdos993Lean.F4Fast.IntegerNormalization
public import Erdos993Lean.F4Fast.RangeAll

/-! Integer output checks for rows 11 through 15; the unchanged original predicates follow through exact adapters. -/

@[expose] public section

set_option autoImplicit false

namespace Erdos993Lean.BCFG.CertData.FHeavyH1

theorem integer_normalization_checks02 :
    (List.range 5).all (fun j =>
      decide (certificateDenInt.getD (11+j) 0 ≠ 0) &&
      (List.range (M+1)).all (fun k =>
        decide ((certificateSourceDenInt.getD (11+j) []).getD k 0 ≠ 0) &&
        decide ((certificateSourceNumInt.getD (11+j) []).getD k 0 *
          certificateDenInt.getD (11+j) 0 =
          (certificateInt.getD (11+j) []).getD k 0 *
          (certificateSourceDenInt.getD (11+j) []).getD k 0)) &&
      IUni.checkEq
        (IUni.scale (certificateDenInt.getD (11+j) 0)
          (IUni.cachedNormalizedRow N compositionInt outerInt (11+j)))
        (IUni.scale (compositionDenInt * outerDenInt)
          (IUni.cachedBernVector M basisInt (certificateInt.getD (11+j) [])))) = true := by
  decide +kernel

theorem normalization_chunk_rows02 :
    ∀ j < 5,
      Uni.checkEq (Bi.normalizedRow N p qc rq a b (11+j))
        (Uni.bernVector M (A.getD (11+j) [])) = true := by
  intro j hj
  have hiN : 11+j < N+1 := by simp only [N]; omega
  have ho := Erdos993Lean.F4Fast.forall_lt_of_range_all
    integer_normalization_checks02 j hj
  have hs := Bool.and_eq_true_iff.mp ho
  have hs' := Bool.and_eq_true_iff.mp hs.1
  have hDA := of_decide_eq_true hs'.1
  have hrows := hs'.2
  have hdens : ∀ k < M+1,
      (certificateSourceDenInt.getD (11+j) []).getD k 1 ≠ 0 := by
    intro k hk
    rw [integer_source_den_default (11+j) k hiN hk]
    have hr := List.all_eq_true.mp hrows k (List.mem_range.mpr hk)
    exact of_decide_eq_true (Bool.and_eq_true_iff.mp hr).1
  have hcross : ∀ k < M+1,
      (certificateSourceNumInt.getD (11+j) []).getD k 0 *
          certificateDenInt.getD (11+j) 0 =
        (certificateInt.getD (11+j) []).getD k 0 *
          (certificateSourceDenInt.getD (11+j) []).getD k 1 := by
    intro k hk
    rw [integer_source_den_default (11+j) k hiN hk]
    have hr := List.all_eq_true.mp hrows k (List.mem_range.mpr hk)
    exact of_decide_eq_true (Bool.and_eq_true_iff.mp hr).2
  have hA := IUni.ratioMatrix_row_coeffs N M A certificateSourceNumInt
    certificateSourceDenInt (certificateInt.getD (11+j) [])
    (certificateDenInt.getD (11+j) 0) (11+j) hiN
    integer_source_A hDA hdens hcross
  exact Bi.normalizedRow_checkEq_of_integer_clear N M p (A.getD (11+j) [])
    qc rq a b compositionInt outerInt basisInt (certificateInt.getD (11+j) [])
    (11+j) compositionDenInt outerDenInt (certificateDenInt.getD (11+j) 0)
    integer_composition_den_ne_zero integer_outer_den_ne_zero hDA
    integer_composition_checked integer_outer_checked integer_basis_checked hA hs.2

theorem normalization_chunk_checks02 :
    (List.range 5).all (fun j =>
      Uni.checkEq (Bi.normalizedRow N p qc rq a b (11+j))
        (Uni.bernVector M (A.getD (11+j) []))) = true := by
  apply List.all_eq_true.mpr
  intro j hj
  exact normalization_chunk_rows02 j (List.mem_range.mp hj)

end Erdos993Lean.BCFG.CertData.FHeavyH1
