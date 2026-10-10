module

public import Erdos993Lean.ExactComparisons.F3All.Data

/-! Generated from the F3 text of version 2.10 of the manuscript.
No Python certificate evaluation is used; the checks are done by the Lean kernel. -/

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 400000
namespace Erdos993Lean.ExactComparisons.F3All.Validity001

def records : List Bool := [
  -- A001.m_range
  decide (0 ≤ a001.m ∧ a001.m ≤ (49/100 : Rat)),
  -- A002.m_range
  decide (0 ≤ a002.m ∧ a002.m ≤ (49/100 : Rat)),
  -- A003.m_range
  decide (0 ≤ a003.m ∧ a003.m ≤ (49/100 : Rat)),
  -- A004.m_range
  decide (0 ≤ a004.m ∧ a004.m ≤ (49/100 : Rat)),
  -- A005.m_range
  decide (0 ≤ a005.m ∧ a005.m ≤ (49/100 : Rat)),
  -- A006.m_range
  decide (0 ≤ a006.m ∧ a006.m ≤ (49/100 : Rat)),
  -- A007.m_range
  decide (0 ≤ a007.m ∧ a007.m ≤ (49/100 : Rat)),
  -- A008.m_range
  decide (0 ≤ a008.m ∧ a008.m ≤ (49/100 : Rat)),
  -- A009.m_range
  decide (0 ≤ a009.m ∧ a009.m ≤ (49/100 : Rat)),
  -- A010.m_range
  decide (0 ≤ a010.m ∧ a010.m ≤ (49/100 : Rat)),
  -- A011.m_range
  decide (0 ≤ a011.m ∧ a011.m ≤ (49/100 : Rat)),
  -- A012.m_range
  decide (0 ≤ a012.m ∧ a012.m ≤ (49/100 : Rat)),
  -- A013.m_range
  decide (0 ≤ a013.m ∧ a013.m ≤ (49/100 : Rat)),
  -- A014.m_range
  decide (0 ≤ a014.m ∧ a014.m ≤ (49/100 : Rat)),
  -- A015.m_range
  decide (0 ≤ a015.m ∧ a015.m ≤ (49/100 : Rat)),
  -- A016.m_range
  decide (0 ≤ a016.m ∧ a016.m ≤ (49/100 : Rat)),
  -- A017.m_range
  decide (0 ≤ a017.m ∧ a017.m ≤ (49/100 : Rat)),
  -- A018.m_range
  decide (0 ≤ a018.m ∧ a018.m ≤ (49/100 : Rat)),
  -- A019.m_range
  decide (0 ≤ a019.m ∧ a019.m ≤ (49/100 : Rat)),
  -- A020.m_range
  decide (0 ≤ a020.m ∧ a020.m ≤ (49/100 : Rat)),
  -- A021.m_range
  decide (0 ≤ a021.m ∧ a021.m ≤ (49/100 : Rat)),
  -- A022.m_range
  decide (0 ≤ a022.m ∧ a022.m ≤ (49/100 : Rat)),
  -- A023.m_range
  decide (0 ≤ a023.m ∧ a023.m ≤ (49/100 : Rat)),
  -- A024.m_range
  decide (0 ≤ a024.m ∧ a024.m ≤ (49/100 : Rat)),
  -- A025.m_range
  decide (0 ≤ a025.m ∧ a025.m ≤ (49/100 : Rat)),
  -- A026.m_range
  decide (0 ≤ a026.m ∧ a026.m ≤ (49/100 : Rat)),
  -- A027.m_range
  decide (0 ≤ a027.m ∧ a027.m ≤ (49/100 : Rat)),
  -- A028.m_range
  decide (0 ≤ a028.m ∧ a028.m ≤ (49/100 : Rat)),
  -- A029.m_range
  decide (0 ≤ a029.m ∧ a029.m ≤ (49/100 : Rat)),
  -- A030.m_range
  decide (0 ≤ a030.m ∧ a030.m ≤ (49/100 : Rat)),
  -- A031.m_range
  decide (0 ≤ a031.m ∧ a031.m ≤ (49/100 : Rat)),
  -- A032.m_range
  decide (0 ≤ a032.m ∧ a032.m ≤ (49/100 : Rat)),
  -- A033.m_range
  decide (0 ≤ a033.m ∧ a033.m ≤ (49/100 : Rat)),
  -- A034.m_range
  decide (0 ≤ a034.m ∧ a034.m ≤ (49/100 : Rat)),
  -- A035.m_range
  decide (0 ≤ a035.m ∧ a035.m ≤ (49/100 : Rat)),
  -- A036.m_range
  decide (0 ≤ a036.m ∧ a036.m ≤ (49/100 : Rat)),
  -- A037.m_range
  decide (0 ≤ a037.m ∧ a037.m ≤ (49/100 : Rat)),
  -- A038.m_range
  decide (0 ≤ a038.m ∧ a038.m ≤ (49/100 : Rat)),
  -- A039.m_range
  decide (0 ≤ a039.m ∧ a039.m ≤ (49/100 : Rat)),
  -- A040.m_range
  decide (0 ≤ a040.m ∧ a040.m ≤ (49/100 : Rat)),
  -- A041.m_range
  decide (0 ≤ a041.m ∧ a041.m ≤ (49/100 : Rat)),
  -- A042.m_range
  decide (0 ≤ a042.m ∧ a042.m ≤ (49/100 : Rat)),
  -- A043.m_range
  decide (0 ≤ a043.m ∧ a043.m ≤ (49/100 : Rat)),
  -- A044.m_range
  decide (0 ≤ a044.m ∧ a044.m ≤ (49/100 : Rat)),
  -- A045.m_range
  decide (0 ≤ a045.m ∧ a045.m ≤ (49/100 : Rat)),
  -- A046.m_range
  decide (0 ≤ a046.m ∧ a046.m ≤ (49/100 : Rat)),
  -- A047.m_range
  decide (0 ≤ a047.m ∧ a047.m ≤ (49/100 : Rat)),
  -- A048.m_range
  decide (0 ≤ a048.m ∧ a048.m ≤ (49/100 : Rat)),
  -- A049.m_range
  decide (0 ≤ a049.m ∧ a049.m ≤ (49/100 : Rat)),
  -- A050.m_range
  decide (0 ≤ a050.m ∧ a050.m ≤ (49/100 : Rat)),
  -- A051.m_range
  decide (0 ≤ a051.m ∧ a051.m ≤ (49/100 : Rat)),
  -- A052.m_range
  decide (0 ≤ a052.m ∧ a052.m ≤ (49/100 : Rat)),
  -- A053.m_range
  decide (0 ≤ a053.m ∧ a053.m ≤ (49/100 : Rat)),
  -- A054.m_range
  decide (0 ≤ a054.m ∧ a054.m ≤ (49/100 : Rat)),
  -- A055.m_range
  decide (0 ≤ a055.m ∧ a055.m ≤ (49/100 : Rat)),
  -- A056.m_range
  decide (0 ≤ a056.m ∧ a056.m ≤ (49/100 : Rat)),
  -- A057.m_range
  decide (0 ≤ a057.m ∧ a057.m ≤ (49/100 : Rat)),
  -- A058.m_range
  decide (0 ≤ a058.m ∧ a058.m ≤ (49/100 : Rat)),
  -- A059.m_range
  decide (0 ≤ a059.m ∧ a059.m ≤ (49/100 : Rat)),
  -- A060.m_range
  decide (0 ≤ a060.m ∧ a060.m ≤ (49/100 : Rat)),
  -- A061.m_range
  decide (0 ≤ a061.m ∧ a061.m ≤ (49/100 : Rat)),
  -- A062.m_range
  decide (0 ≤ a062.m ∧ a062.m ≤ (49/100 : Rat)),
  -- A063.m_range
  decide (0 ≤ a063.m ∧ a063.m ≤ (49/100 : Rat)),
  -- A064.m_range
  decide (0 ≤ a064.m ∧ a064.m ≤ (49/100 : Rat))
]
theorem checked : records.all id = true := by decide +kernel
theorem record_count : records.length = 64 := by decide +kernel
end Erdos993Lean.ExactComparisons.F3All.Validity001
