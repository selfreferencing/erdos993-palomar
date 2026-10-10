module

public import Erdos993Lean.ExactComparisons.F3All.Data

/-! Generated from the F3 text of version 2.10 of the manuscript.
No Python certificate evaluation is used; the checks are done by the Lean kernel. -/

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 400000
namespace Erdos993Lean.ExactComparisons.F3All.Validity003

def records : List Bool := [
  -- A129.m_range
  decide (0 ≤ a129.m ∧ a129.m ≤ (49/100 : Rat)),
  -- A130.m_range
  decide (0 ≤ a130.m ∧ a130.m ≤ (49/100 : Rat)),
  -- A131.m_range
  decide (0 ≤ a131.m ∧ a131.m ≤ (49/100 : Rat)),
  -- A132.m_range
  decide (0 ≤ a132.m ∧ a132.m ≤ (49/100 : Rat)),
  -- A133.m_range
  decide (0 ≤ a133.m ∧ a133.m ≤ (49/100 : Rat)),
  -- A134.m_range
  decide (0 ≤ a134.m ∧ a134.m ≤ (49/100 : Rat)),
  -- A135.m_range
  decide (0 ≤ a135.m ∧ a135.m ≤ (49/100 : Rat)),
  -- A136.m_range
  decide (0 ≤ a136.m ∧ a136.m ≤ (49/100 : Rat)),
  -- A137.m_range
  decide (0 ≤ a137.m ∧ a137.m ≤ (49/100 : Rat)),
  -- A138.m_range
  decide (0 ≤ a138.m ∧ a138.m ≤ (49/100 : Rat)),
  -- A139.m_range
  decide (0 ≤ a139.m ∧ a139.m ≤ (49/100 : Rat)),
  -- A140.m_range
  decide (0 ≤ a140.m ∧ a140.m ≤ (49/100 : Rat)),
  -- A141.m_range
  decide (0 ≤ a141.m ∧ a141.m ≤ (49/100 : Rat)),
  -- A142.m_range
  decide (0 ≤ a142.m ∧ a142.m ≤ (49/100 : Rat)),
  -- A143.m_range
  decide (0 ≤ a143.m ∧ a143.m ≤ (49/100 : Rat)),
  -- A144.m_range
  decide (0 ≤ a144.m ∧ a144.m ≤ (49/100 : Rat)),
  -- A145.m_range
  decide (0 ≤ a145.m ∧ a145.m ≤ (49/100 : Rat)),
  -- A146.m_range
  decide (0 ≤ a146.m ∧ a146.m ≤ (49/100 : Rat)),
  -- A147.m_range
  decide (0 ≤ a147.m ∧ a147.m ≤ (49/100 : Rat)),
  -- A148.m_range
  decide (0 ≤ a148.m ∧ a148.m ≤ (49/100 : Rat)),
  -- A149.m_range
  decide (0 ≤ a149.m ∧ a149.m ≤ (49/100 : Rat)),
  -- A150.m_range
  decide (0 ≤ a150.m ∧ a150.m ≤ (49/100 : Rat)),
  -- A151.m_range
  decide (0 ≤ a151.m ∧ a151.m ≤ (49/100 : Rat)),
  -- A152.m_range
  decide (0 ≤ a152.m ∧ a152.m ≤ (49/100 : Rat)),
  -- A153.m_range
  decide (0 ≤ a153.m ∧ a153.m ≤ (49/100 : Rat)),
  -- A154.m_range
  decide (0 ≤ a154.m ∧ a154.m ≤ (49/100 : Rat)),
  -- A155.m_range
  decide (0 ≤ a155.m ∧ a155.m ≤ (49/100 : Rat)),
  -- A156.m_range
  decide (0 ≤ a156.m ∧ a156.m ≤ (49/100 : Rat)),
  -- A157.m_range
  decide (0 ≤ a157.m ∧ a157.m ≤ (49/100 : Rat)),
  -- A158.m_range
  decide (0 ≤ a158.m ∧ a158.m ≤ (49/100 : Rat)),
  -- A159.m_range
  decide (0 ≤ a159.m ∧ a159.m ≤ (49/100 : Rat)),
  -- C.cover1
  coverOK (0 : Rat) (21/25 : Rat) [((0 : Rat), (21/50 : Rat)), ((21/50 : Rat), (63/100 : Rat)), ((63/100 : Rat), (273/400 : Rat)), ((273/400 : Rat), (147/200 : Rat)), ((147/200 : Rat), (63/80 : Rat)), ((63/80 : Rat), (21/25 : Rat))],
  -- C.cover2
  coverOK (0 : Rat) (23/25 : Rat) [((0 : Rat), (23/50 : Rat)), ((23/50 : Rat), (69/100 : Rat)), ((69/100 : Rat), (299/400 : Rat)), ((299/400 : Rat), (161/200 : Rat)), ((161/200 : Rat), (23/25 : Rat))],
  -- C.cover3
  coverOK (0 : Rat) (51/50 : Rat) [((0 : Rat), (51/100 : Rat)), ((51/100 : Rat), (51/80 : Rat)), ((51/80 : Rat), (153/200 : Rat)), ((153/200 : Rat), (663/800 : Rat)), ((663/800 : Rat), (357/400 : Rat)), ((357/400 : Rat), (51/50 : Rat))],
  -- C.cover4
  coverOK (0 : Rat) (11/10 : Rat) [((0 : Rat), (11/20 : Rat)), ((11/20 : Rat), (11/16 : Rat)), ((11/16 : Rat), (121/160 : Rat)), ((121/160 : Rat), (33/40 : Rat)), ((33/40 : Rat), (55/64 : Rat)), ((55/64 : Rat), (143/160 : Rat)), ((143/160 : Rat), (77/80 : Rat)), ((77/80 : Rat), (11/10 : Rat))],
  -- C.cover5
  coverOK (0 : Rat) (121/100 : Rat) [((0 : Rat), (121/400 : Rat)), ((121/400 : Rat), (121/200 : Rat)), ((121/200 : Rat), (121/160 : Rat)), ((121/160 : Rat), (2541/3200 : Rat)), ((2541/3200 : Rat), (5203/6400 : Rat)), ((5203/6400 : Rat), (1331/1600 : Rat)), ((1331/1600 : Rat), (1089/1280 : Rat)), ((1089/1280 : Rat), (11011/12800 : Rat)), ((11011/12800 : Rat), (2783/3200 : Rat)), ((2783/3200 : Rat), (11253/12800 : Rat)), ((11253/12800 : Rat), (5687/6400 : Rat)), ((5687/6400 : Rat), (363/400 : Rat)), ((363/400 : Rat), (5929/6400 : Rat)), ((5929/6400 : Rat), (121/128 : Rat)), ((121/128 : Rat), (1573/1600 : Rat)), ((1573/1600 : Rat), (3267/3200 : Rat)), ((3267/3200 : Rat), (847/800 : Rat)), ((847/800 : Rat), (121/100 : Rat))],
  -- A.cover1
  coverOK (0 : Rat) (3 : Rat) [((0 : Rat), (3/32 : Rat)), ((3/32 : Rat), (3/16 : Rat)), ((3/16 : Rat), (15/64 : Rat)), ((15/64 : Rat), (9/32 : Rat)), ((9/32 : Rat), (3/8 : Rat)), ((3/8 : Rat), (15/32 : Rat)), ((15/32 : Rat), (9/16 : Rat)), ((9/16 : Rat), (3/4 : Rat)), ((3/4 : Rat), (15/16 : Rat)), ((15/16 : Rat), (9/8 : Rat)), ((9/8 : Rat), (21/16 : Rat)), ((21/16 : Rat), (3/2 : Rat)), ((3/2 : Rat), (15/8 : Rat)), ((15/8 : Rat), (9/4 : Rat)), ((9/4 : Rat), (3 : Rat))],
  -- A.cover2
  coverOK (0 : Rat) (3 : Rat) [((0 : Rat), (3/16 : Rat)), ((3/16 : Rat), (9/32 : Rat)), ((9/32 : Rat), (21/64 : Rat)), ((21/64 : Rat), (3/8 : Rat)), ((3/8 : Rat), (27/64 : Rat)), ((27/64 : Rat), (15/32 : Rat)), ((15/32 : Rat), (9/16 : Rat)), ((9/16 : Rat), (21/32 : Rat)), ((21/32 : Rat), (3/4 : Rat)), ((3/4 : Rat), (27/32 : Rat)), ((27/32 : Rat), (15/16 : Rat)), ((15/16 : Rat), (9/8 : Rat)), ((9/8 : Rat), (21/16 : Rat)), ((21/16 : Rat), (3/2 : Rat)), ((3/2 : Rat), (27/16 : Rat)), ((27/16 : Rat), (15/8 : Rat)), ((15/8 : Rat), (9/4 : Rat)), ((9/4 : Rat), (3 : Rat))],
  -- A.cover3
  coverOK (0 : Rat) (3 : Rat) [((0 : Rat), (3/16 : Rat)), ((3/16 : Rat), (9/32 : Rat)), ((9/32 : Rat), (3/8 : Rat)), ((3/8 : Rat), (27/64 : Rat)), ((27/64 : Rat), (15/32 : Rat)), ((15/32 : Rat), (33/64 : Rat)), ((33/64 : Rat), (9/16 : Rat)), ((9/16 : Rat), (39/64 : Rat)), ((39/64 : Rat), (21/32 : Rat)), ((21/32 : Rat), (45/64 : Rat)), ((45/64 : Rat), (3/4 : Rat)), ((3/4 : Rat), (51/64 : Rat)), ((51/64 : Rat), (27/32 : Rat)), ((27/32 : Rat), (15/16 : Rat)), ((15/16 : Rat), (33/32 : Rat)), ((33/32 : Rat), (9/8 : Rat)), ((9/8 : Rat), (39/32 : Rat)), ((39/32 : Rat), (21/16 : Rat)), ((21/16 : Rat), (45/32 : Rat)), ((45/32 : Rat), (3/2 : Rat)), ((3/2 : Rat), (51/32 : Rat)), ((51/32 : Rat), (27/16 : Rat)), ((27/16 : Rat), (15/8 : Rat)), ((15/8 : Rat), (33/16 : Rat)), ((33/16 : Rat), (9/4 : Rat)), ((9/4 : Rat), (21/8 : Rat)), ((21/8 : Rat), (3 : Rat))],
  -- A.cover4
  coverOK (0 : Rat) (3 : Rat) [((0 : Rat), (3/8 : Rat)), ((3/8 : Rat), (27/64 : Rat)), ((27/64 : Rat), (15/32 : Rat)), ((15/32 : Rat), (63/128 : Rat)), ((63/128 : Rat), (33/64 : Rat)), ((33/64 : Rat), (69/128 : Rat)), ((69/128 : Rat), (9/16 : Rat)), ((9/16 : Rat), (75/128 : Rat)), ((75/128 : Rat), (39/64 : Rat)), ((39/64 : Rat), (81/128 : Rat)), ((81/128 : Rat), (21/32 : Rat)), ((21/32 : Rat), (87/128 : Rat)), ((87/128 : Rat), (45/64 : Rat)), ((45/64 : Rat), (93/128 : Rat)), ((93/128 : Rat), (3/4 : Rat)), ((3/4 : Rat), (99/128 : Rat)), ((99/128 : Rat), (51/64 : Rat)), ((51/64 : Rat), (105/128 : Rat)), ((105/128 : Rat), (27/32 : Rat)), ((27/32 : Rat), (111/128 : Rat)), ((111/128 : Rat), (57/64 : Rat)), ((57/64 : Rat), (15/16 : Rat)), ((15/16 : Rat), (63/64 : Rat)), ((63/64 : Rat), (33/32 : Rat)), ((33/32 : Rat), (69/64 : Rat)), ((69/64 : Rat), (9/8 : Rat)), ((9/8 : Rat), (75/64 : Rat)), ((75/64 : Rat), (39/32 : Rat)), ((39/32 : Rat), (81/64 : Rat)), ((81/64 : Rat), (21/16 : Rat)), ((21/16 : Rat), (87/64 : Rat)), ((87/64 : Rat), (45/32 : Rat)), ((45/32 : Rat), (93/64 : Rat)), ((93/64 : Rat), (3/2 : Rat)), ((3/2 : Rat), (99/64 : Rat)), ((99/64 : Rat), (51/32 : Rat)), ((51/32 : Rat), (27/16 : Rat)), ((27/16 : Rat), (57/32 : Rat)), ((57/32 : Rat), (15/8 : Rat)), ((15/8 : Rat), (63/32 : Rat)), ((63/32 : Rat), (33/16 : Rat)), ((33/16 : Rat), (9/4 : Rat)), ((9/4 : Rat), (21/8 : Rat)), ((21/8 : Rat), (3 : Rat))],
  -- A.cover5
  coverOK (0 : Rat) (3 : Rat) [((0 : Rat), (3/8 : Rat)), ((3/8 : Rat), (9/16 : Rat)), ((9/16 : Rat), (21/32 : Rat)), ((21/32 : Rat), (3/4 : Rat)), ((3/4 : Rat), (27/32 : Rat)), ((27/32 : Rat), (15/16 : Rat)), ((15/16 : Rat), (33/32 : Rat)), ((33/32 : Rat), (9/8 : Rat)), ((9/8 : Rat), (39/32 : Rat)), ((39/32 : Rat), (21/16 : Rat)), ((21/16 : Rat), (45/32 : Rat)), ((45/32 : Rat), (3/2 : Rat)), ((3/2 : Rat), (27/16 : Rat)), ((27/16 : Rat), (15/8 : Rat)), ((15/8 : Rat), (33/16 : Rat)), ((33/16 : Rat), (9/4 : Rat)), ((9/4 : Rat), (21/8 : Rat)), ((21/8 : Rat), (3 : Rat))],
  -- A.cover6
  coverOK (0 : Rat) (3 : Rat) [((0 : Rat), (3/8 : Rat)), ((3/8 : Rat), (9/16 : Rat)), ((9/16 : Rat), (3/4 : Rat)), ((3/4 : Rat), (15/16 : Rat)), ((15/16 : Rat), (9/8 : Rat)), ((9/8 : Rat), (21/16 : Rat)), ((21/16 : Rat), (3/2 : Rat)), ((3/2 : Rat), (27/16 : Rat)), ((27/16 : Rat), (15/8 : Rat)), ((15/8 : Rat), (33/16 : Rat)), ((33/16 : Rat), (9/4 : Rat)), ((9/4 : Rat), (21/8 : Rat)), ((21/8 : Rat), (3 : Rat))],
  -- A.cover8
  coverOK (0 : Rat) (3 : Rat) [((0 : Rat), (3/8 : Rat)), ((3/8 : Rat), (3/4 : Rat)), ((3/4 : Rat), (9/8 : Rat)), ((9/8 : Rat), (21/16 : Rat)), ((21/16 : Rat), (3/2 : Rat)), ((3/2 : Rat), (27/16 : Rat)), ((27/16 : Rat), (15/8 : Rat)), ((15/8 : Rat), (33/16 : Rat)), ((33/16 : Rat), (9/4 : Rat)), ((9/4 : Rat), (21/8 : Rat)), ((21/8 : Rat), (3 : Rat))],
  -- pt001.coordinates
  pointOK pt001,
  -- pt002.coordinates
  pointOK pt002,
  -- pt003.coordinates
  pointOK pt003,
  -- pt004.coordinates
  pointOK pt004,
  -- pt005.coordinates
  pointOK pt005,
  -- pt006.coordinates
  pointOK pt006,
  -- pt007.coordinates
  pointOK pt007,
  -- pt008.coordinates
  pointOK pt008,
  -- pt009.coordinates
  pointOK pt009,
  -- pt010.coordinates
  pointOK pt010,
  -- pt011.coordinates
  pointOK pt011,
  -- pt012.coordinates
  pointOK pt012,
  -- pt013.coordinates
  pointOK pt013,
  -- pt014.coordinates
  pointOK pt014,
  -- pt015.coordinates
  pointOK pt015,
  -- pt016.coordinates
  pointOK pt016,
  -- pt017.coordinates
  pointOK pt017,
  -- pt018.coordinates
  pointOK pt018,
  -- pt019.coordinates
  pointOK pt019,
  -- pt020.coordinates
  pointOK pt020,
  -- pt021.coordinates
  pointOK pt021
]
theorem checked : records.all id = true := by decide +kernel
theorem record_count : records.length = 64 := by decide +kernel
end Erdos993Lean.ExactComparisons.F3All.Validity003
