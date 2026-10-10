module

public import Erdos993Lean.ExactComparisons.F3All.Data

/-! Generated from the F3 text of version 2.10 of the manuscript.
No Python certificate evaluation is used; the checks are done by the Lean kernel. -/

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 400000
namespace Erdos993Lean.ExactComparisons.F3All.Validity002

def records : List Bool := [
  -- A065.m_range
  decide (0 ≤ a065.m ∧ a065.m ≤ (49/100 : Rat)),
  -- A066.m_range
  decide (0 ≤ a066.m ∧ a066.m ≤ (49/100 : Rat)),
  -- A067.m_range
  decide (0 ≤ a067.m ∧ a067.m ≤ (49/100 : Rat)),
  -- A068.m_range
  decide (0 ≤ a068.m ∧ a068.m ≤ (49/100 : Rat)),
  -- A069.m_range
  decide (0 ≤ a069.m ∧ a069.m ≤ (49/100 : Rat)),
  -- A070.m_range
  decide (0 ≤ a070.m ∧ a070.m ≤ (49/100 : Rat)),
  -- A071.m_range
  decide (0 ≤ a071.m ∧ a071.m ≤ (49/100 : Rat)),
  -- A072.m_range
  decide (0 ≤ a072.m ∧ a072.m ≤ (49/100 : Rat)),
  -- A073.m_range
  decide (0 ≤ a073.m ∧ a073.m ≤ (49/100 : Rat)),
  -- A074.m_range
  decide (0 ≤ a074.m ∧ a074.m ≤ (49/100 : Rat)),
  -- A075.m_range
  decide (0 ≤ a075.m ∧ a075.m ≤ (49/100 : Rat)),
  -- A076.m_range
  decide (0 ≤ a076.m ∧ a076.m ≤ (49/100 : Rat)),
  -- A077.m_range
  decide (0 ≤ a077.m ∧ a077.m ≤ (49/100 : Rat)),
  -- A078.m_range
  decide (0 ≤ a078.m ∧ a078.m ≤ (49/100 : Rat)),
  -- A079.m_range
  decide (0 ≤ a079.m ∧ a079.m ≤ (49/100 : Rat)),
  -- A080.m_range
  decide (0 ≤ a080.m ∧ a080.m ≤ (49/100 : Rat)),
  -- A081.m_range
  decide (0 ≤ a081.m ∧ a081.m ≤ (49/100 : Rat)),
  -- A082.m_range
  decide (0 ≤ a082.m ∧ a082.m ≤ (49/100 : Rat)),
  -- A083.m_range
  decide (0 ≤ a083.m ∧ a083.m ≤ (49/100 : Rat)),
  -- A084.m_range
  decide (0 ≤ a084.m ∧ a084.m ≤ (49/100 : Rat)),
  -- A085.m_range
  decide (0 ≤ a085.m ∧ a085.m ≤ (49/100 : Rat)),
  -- A086.m_range
  decide (0 ≤ a086.m ∧ a086.m ≤ (49/100 : Rat)),
  -- A087.m_range
  decide (0 ≤ a087.m ∧ a087.m ≤ (49/100 : Rat)),
  -- A088.m_range
  decide (0 ≤ a088.m ∧ a088.m ≤ (49/100 : Rat)),
  -- A089.m_range
  decide (0 ≤ a089.m ∧ a089.m ≤ (49/100 : Rat)),
  -- A090.m_range
  decide (0 ≤ a090.m ∧ a090.m ≤ (49/100 : Rat)),
  -- A091.m_range
  decide (0 ≤ a091.m ∧ a091.m ≤ (49/100 : Rat)),
  -- A092.m_range
  decide (0 ≤ a092.m ∧ a092.m ≤ (49/100 : Rat)),
  -- A093.m_range
  decide (0 ≤ a093.m ∧ a093.m ≤ (49/100 : Rat)),
  -- A094.m_range
  decide (0 ≤ a094.m ∧ a094.m ≤ (49/100 : Rat)),
  -- A095.m_range
  decide (0 ≤ a095.m ∧ a095.m ≤ (49/100 : Rat)),
  -- A096.m_range
  decide (0 ≤ a096.m ∧ a096.m ≤ (49/100 : Rat)),
  -- A097.m_range
  decide (0 ≤ a097.m ∧ a097.m ≤ (49/100 : Rat)),
  -- A098.m_range
  decide (0 ≤ a098.m ∧ a098.m ≤ (49/100 : Rat)),
  -- A099.m_range
  decide (0 ≤ a099.m ∧ a099.m ≤ (49/100 : Rat)),
  -- A100.m_range
  decide (0 ≤ a100.m ∧ a100.m ≤ (49/100 : Rat)),
  -- A101.m_range
  decide (0 ≤ a101.m ∧ a101.m ≤ (49/100 : Rat)),
  -- A102.m_range
  decide (0 ≤ a102.m ∧ a102.m ≤ (49/100 : Rat)),
  -- A103.m_range
  decide (0 ≤ a103.m ∧ a103.m ≤ (49/100 : Rat)),
  -- A104.m_range
  decide (0 ≤ a104.m ∧ a104.m ≤ (49/100 : Rat)),
  -- A105.m_range
  decide (0 ≤ a105.m ∧ a105.m ≤ (49/100 : Rat)),
  -- A106.m_range
  decide (0 ≤ a106.m ∧ a106.m ≤ (49/100 : Rat)),
  -- A107.m_range
  decide (0 ≤ a107.m ∧ a107.m ≤ (49/100 : Rat)),
  -- A108.m_range
  decide (0 ≤ a108.m ∧ a108.m ≤ (49/100 : Rat)),
  -- A109.m_range
  decide (0 ≤ a109.m ∧ a109.m ≤ (49/100 : Rat)),
  -- A110.m_range
  decide (0 ≤ a110.m ∧ a110.m ≤ (49/100 : Rat)),
  -- A111.m_range
  decide (0 ≤ a111.m ∧ a111.m ≤ (49/100 : Rat)),
  -- A112.m_range
  decide (0 ≤ a112.m ∧ a112.m ≤ (49/100 : Rat)),
  -- A113.m_range
  decide (0 ≤ a113.m ∧ a113.m ≤ (49/100 : Rat)),
  -- A114.m_range
  decide (0 ≤ a114.m ∧ a114.m ≤ (49/100 : Rat)),
  -- A115.m_range
  decide (0 ≤ a115.m ∧ a115.m ≤ (49/100 : Rat)),
  -- A116.m_range
  decide (0 ≤ a116.m ∧ a116.m ≤ (49/100 : Rat)),
  -- A117.m_range
  decide (0 ≤ a117.m ∧ a117.m ≤ (49/100 : Rat)),
  -- A118.m_range
  decide (0 ≤ a118.m ∧ a118.m ≤ (49/100 : Rat)),
  -- A119.m_range
  decide (0 ≤ a119.m ∧ a119.m ≤ (49/100 : Rat)),
  -- A120.m_range
  decide (0 ≤ a120.m ∧ a120.m ≤ (49/100 : Rat)),
  -- A121.m_range
  decide (0 ≤ a121.m ∧ a121.m ≤ (49/100 : Rat)),
  -- A122.m_range
  decide (0 ≤ a122.m ∧ a122.m ≤ (49/100 : Rat)),
  -- A123.m_range
  decide (0 ≤ a123.m ∧ a123.m ≤ (49/100 : Rat)),
  -- A124.m_range
  decide (0 ≤ a124.m ∧ a124.m ≤ (49/100 : Rat)),
  -- A125.m_range
  decide (0 ≤ a125.m ∧ a125.m ≤ (49/100 : Rat)),
  -- A126.m_range
  decide (0 ≤ a126.m ∧ a126.m ≤ (49/100 : Rat)),
  -- A127.m_range
  decide (0 ≤ a127.m ∧ a127.m ≤ (49/100 : Rat)),
  -- A128.m_range
  decide (0 ≤ a128.m ∧ a128.m ≤ (49/100 : Rat))
]
theorem checked : records.all id = true := by decide +kernel
theorem record_count : records.length = 64 := by decide +kernel
end Erdos993Lean.ExactComparisons.F3All.Validity002
