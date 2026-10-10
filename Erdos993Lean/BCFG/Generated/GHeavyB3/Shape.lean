module

public import Erdos993Lean.BCFG.Generated.GHeavyB3.Data

/-! Generated transcription of G.heavy.b3
from the coefficient data of rows B, C, F, G.
No Python polynomial arithmetic or certificate replay is performed.
-/

@[expose] public section

set_option autoImplicit false
namespace Erdos993Lean.BCFG.CertData.GHeavyB3

theorem p_rows : p.length = N+1 := by decide +kernel
theorem p_columns : p.all (fun r => decide (r.length = M+1)) = true := by decide +kernel
theorem source_nonzero_count : (p.flatten.filter (fun c => c != 0)).length = 247 := by decide +kernel
theorem norm_rows : A.length = N+1 := by decide +kernel
theorem norm_columns : A.all (fun r => decide (r.length = M+1)) = true := by decide +kernel
theorem norm_entry_count : A.flatten.length = 374 := by decide +kernel
theorem lower_length : lower.length = M+1 := by decide +kernel
theorem interval_count : intervals.length = 3 := by decide +kernel
theorem interval_lengths : intervals.all (fun I => decide (I.coeffs.length = M+1)) = true := by decide +kernel
theorem interval_coefficient_count : (intervals.map (fun I => I.coeffs.length)).sum = 102 := by decide +kernel
theorem clearing_scale_positive : 0 < clearingScale := by decide +kernel

end Erdos993Lean.BCFG.CertData.GHeavyB3
