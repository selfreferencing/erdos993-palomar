module

public import Erdos993Lean.F4Fast.P04RateInputAdapter
public import Erdos993Lean.F4Fast.RangeAll
public import Erdos993Lean.Analytic.V213.P04Rates.Data

/-! Pure Int/Nat source custody and comparisons for all55 original rate inputs.
The original literal definitions and proposition statements are preserved.
-/

@[expose] public section
set_option autoImplicit false

namespace Erdos993Lean.Analytic.V213.ZeroTiltLaplace.PrintedRates.IntInput
open Erdos993Lean.F4Fast.P04Int

def inputLoRaw : List FractionPair := [(1, 3), (9, 25), (2, 5), (9, 20), (1, 2), (11, 20), (3, 5), (13, 20), (7, 10), (3, 4), (39, 50), (4, 5), (21, 25), (43, 50), (87, 100), (22, 25), (89, 100), (91, 100), (23, 25), (93, 100), (47, 50), (24, 25), (97, 100), (99, 100), (1, 1), (103, 100), (26, 25), (21, 20), (107, 100), (27, 25), (11, 10), (28, 25), (57, 50), (29, 25), (59, 50), (6, 5), (49, 40), (5, 4), (13, 10), (27, 20), (7, 5), (57, 40), (29, 20), (3, 2), (8, 5), (33, 20), (17, 10), (7, 4), (9, 5), (37, 20), (19, 10), (39, 20), (2, 1), (41, 20), (9, 4)]
def inputHiRaw : List FractionPair := [(9, 25), (2, 5), (9, 20), (1, 2), (11, 20), (3, 5), (13, 20), (7, 10), (3, 4), (39, 50), (4, 5), (21, 25), (43, 50), (87, 100), (22, 25), (89, 100), (91, 100), (23, 25), (93, 100), (47, 50), (24, 25), (97, 100), (99, 100), (1, 1), (103, 100), (26, 25), (21, 20), (107, 100), (27, 25), (11, 10), (28, 25), (57, 50), (29, 25), (59, 50), (6, 5), (49, 40), (5, 4), (13, 10), (27, 20), (7, 5), (57, 40), (29, 20), (3, 2), (8, 5), (33, 20), (17, 10), (7, 4), (9, 5), (37, 20), (19, 10), (39, 20), (2, 1), (41, 20), (9, 4), (7, 3)]
def inputRateRaw : List FractionPair := [(619, 2500), (1309, 5000), (2793, 10000), (751, 2500), (643, 2000), (339, 1000), (3531, 10000), (459, 1250), (953, 2500), (1959, 5000), (817, 2000), (4059, 10000), (4129, 10000), (4129, 10000), (171, 400), (4199, 10000), (851, 2000), (217, 500), (871, 2000), (173, 400), (871, 2000), (441, 1000), (879, 2000), (889, 2000), (881, 2000), (449, 1000), (901, 2000), (449, 1000), (907, 2000), (113, 250), (907, 2000), (4481, 10000), (4481, 10000), (1129, 2500), (1129, 2500), (1129, 2500), (1129, 2500), (4551, 10000), (23, 50), (37, 80), (4481, 10000), (4481, 10000), (4481, 10000), (1129, 2500), (939, 2000), (47, 100), (941, 2000), (941, 2000), (47, 100), (47, 100), (47, 100), (2223, 5000), (2223, 5000), (269, 625), (1129, 2500)]
def groupLoRaw : List FractionPair := [(1, 3), (9, 25), (2, 5), (9, 20), (1, 2), (11, 20), (3, 5), (13, 20), (7, 10), (3, 4), (39, 50), (87, 100), (91, 100), (23, 25), (24, 25), (99, 100), (103, 100), (26, 25), (107, 100), (5, 4), (8, 5), (19, 10), (39, 20)]
def groupHiRaw : List FractionPair := [(9, 25), (2, 5), (9, 20), (1, 2), (11, 20), (3, 5), (13, 20), (7, 10), (3, 4), (39, 50), (87, 100), (91, 100), (23, 25), (24, 25), (99, 100), (103, 100), (26, 25), (107, 100), (5, 4), (8, 5), (19, 10), (39, 20), (7, 3)]
def groupBarRaw : List FractionPair := [(619, 2500), (1309, 5000), (2793, 10000), (751, 2500), (643, 2000), (339, 1000), (3531, 10000), (459, 1250), (953, 2500), (1959, 5000), (4129, 10000), (171, 400), (217, 500), (871, 2000), (441, 1000), (889, 2000), (449, 1000), (901, 2000), (907, 2000), (37, 80), (941, 2000), (47, 100), (1129, 2500)]
def groupOfRaw : List Nat := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 10, 10, 10, 11, 11, 11, 12, 13, 13, 13, 14, 14, 15, 15, 16, 17, 17, 18, 18, 18, 18, 18, 18, 18, 18, 18, 19, 19, 19, 19, 19, 19, 19, 20, 20, 20, 20, 20, 20, 21, 22, 22, 22, 22]
def n44LoRaw : List FractionPair := [(1, 3), (9, 25), (2, 5), (9, 20), (1, 2), (11, 20), (3, 5), (13, 20), (7, 10), (3, 4), (39, 50), (4, 5), (21, 25), (43, 50), (87, 100), (22, 25), (89, 100), (91, 100), (23, 25), (93, 100), (47, 50), (24, 25), (97, 100), (99, 100), (1, 1), (103, 100), (26, 25), (21, 20), (107, 100), (27, 25), (11, 10), (28, 25), (57, 50), (29, 25), (59, 50), (6, 5), (49, 40), (5, 4), (13, 10), (27, 20), (7, 5), (57, 40), (29, 20), (3, 2), (8, 5), (33, 20), (17, 10), (7, 4), (9, 5), (37, 20), (19, 10), (39, 20), (2, 1), (41, 20), (9, 4)]
def n44HiRaw : List FractionPair := [(9, 25), (2, 5), (9, 20), (1, 2), (11, 20), (3, 5), (13, 20), (7, 10), (3, 4), (39, 50), (4, 5), (21, 25), (43, 50), (87, 100), (22, 25), (89, 100), (91, 100), (23, 25), (93, 100), (47, 50), (24, 25), (97, 100), (99, 100), (1, 1), (103, 100), (26, 25), (21, 20), (107, 100), (27, 25), (11, 10), (28, 25), (57, 50), (29, 25), (59, 50), (6, 5), (49, 40), (5, 4), (13, 10), (27, 20), (7, 5), (57, 40), (29, 20), (3, 2), (8, 5), (33, 20), (17, 10), (7, 4), (9, 5), (37, 20), (19, 10), (39, 20), (2, 1), (41, 20), (9, 4), (7, 3)]
def n44RatesRaw : List (List FractionPair) := [[(619, 2500), (2353, 10000), (551, 2500), (489, 2500), (169, 1000)], [(1309, 5000), (613, 2500), (2327, 10000), (509, 2500), (439, 2500)], [(2793, 10000), (2617, 10000), (2451, 10000), (271, 1250), (467, 2500)], [(751, 2500), (563, 2000), (1333, 5000), (291, 1250), (1001, 5000)], [(643, 2000), (3013, 10000), (2821, 10000), (1231, 5000), (1067, 5000)], [(339, 1000), (1589, 5000), (119, 400), (1297, 5000), (139, 625)], [(3531, 10000), (3343, 10000), (3129, 10000), (1363, 5000), (146, 625)], [(459, 1250), (139, 400), (3253, 10000), (177, 625), (97, 400)], [(953, 2500), (1787, 5000), (669, 2000), (182, 625), (623, 2500)], [(1959, 5000), (3673, 10000), (3437, 10000), (187, 625), (2559, 10000)], [(817, 2000), (3673, 10000), (3437, 10000), (187, 625), (2559, 10000)], [(4059, 10000), (761, 2000), (3561, 10000), (192, 625), (1313, 5000)], [(4129, 10000), (3871, 10000), (3623, 10000), (5, 16), (267, 1000)], [(4129, 10000), (3871, 10000), (3623, 10000), (5, 16), (267, 1000)], [(171, 400), (3871, 10000), (3623, 10000), (5, 16), (267, 1000)], [(4199, 10000), (3937, 10000), (921, 2500), (1589, 5000), (679, 2500)], [(851, 2000), (3937, 10000), (921, 2500), (1589, 5000), (679, 2500)], [(217, 500), (3937, 10000), (921, 2500), (1589, 5000), (679, 2500)], [(871, 2000), (4003, 10000), (743, 2000), (202, 625), (1369, 5000)], [(173, 400), (4003, 10000), (743, 2000), (202, 625), (1369, 5000)], [(871, 2000), (4003, 10000), (743, 2000), (202, 625), (1369, 5000)], [(441, 1000), (1009, 2500), (236, 625), (1629, 5000), (1391, 5000)], [(879, 2000), (1009, 2500), (236, 625), (1629, 5000), (1391, 5000)], [(889, 2000), (1009, 2500), (236, 625), (1629, 5000), (1391, 5000)], [(881, 2000), (4069, 10000), (3807, 10000), (657, 2000), (701, 2500)], [(449, 1000), (4069, 10000), (3807, 10000), (657, 2000), (701, 2500)], [(901, 2000), (827, 2000), (1919, 5000), (207, 625), (1413, 5000)], [(449, 1000), (827, 2000), (1919, 5000), (207, 625), (1413, 5000)], [(907, 2000), (827, 2000), (1919, 5000), (207, 625), (1413, 5000)], [(113, 250), (521, 1250), (3869, 10000), (1669, 5000), (178, 625)], [(907, 2000), (521, 1250), (3869, 10000), (1669, 5000), (178, 625)], [(4481, 10000), (4201, 10000), (39, 100), (841, 2500), (178, 625)], [(4481, 10000), (4201, 10000), (39, 100), (841, 2500), (178, 625)], [(1129, 2500), (2117, 5000), (3931, 10000), (3391, 10000), (2871, 10000)], [(1129, 2500), (2117, 5000), (3931, 10000), (3391, 10000), (2871, 10000)], [(1129, 2500), (2117, 5000), (3931, 10000), (841, 2500), (2871, 10000)], [(1129, 2500), (2117, 5000), (3931, 10000), (841, 2500), (2871, 10000)], [(4551, 10000), (2117, 5000), (1981, 5000), (3391, 10000), (2871, 10000)], [(23, 50), (827, 2000), (1919, 5000), (207, 625), (701, 2500)], [(37, 80), (827, 2000), (1919, 5000), (207, 625), (701, 2500)], [(4481, 10000), (521, 1250), (3869, 10000), (207, 625), (701, 2500)], [(4481, 10000), (521, 1250), (3869, 10000), (207, 625), (701, 2500)], [(4481, 10000), (521, 1250), (3869, 10000), (207, 625), (701, 2500)], [(1129, 2500), (4201, 10000), (39, 100), (1669, 5000), (701, 2500)], [(939, 2000), (2051, 5000), (3807, 10000), (202, 625), (679, 2500)], [(47, 100), (2051, 5000), (3807, 10000), (202, 625), (679, 2500)], [(941, 2000), (2051, 5000), (3807, 10000), (202, 625), (679, 2500)], [(941, 2000), (2051, 5000), (3807, 10000), (202, 625), (679, 2500)], [(47, 100), (2051, 5000), (3807, 10000), (202, 625), (679, 2500)], [(47, 100), (2051, 5000), (3807, 10000), (202, 625), (679, 2500)], [(47, 100), (2051, 5000), (3807, 10000), (641, 2000), (2693, 10000)], [(2223, 5000), (2051, 5000), (3807, 10000), (641, 2000), (2693, 10000)], [(2223, 5000), (2051, 5000), (3807, 10000), (641, 2000), (2693, 10000)], [(269, 625), (397, 1000), (921, 2500), (1549, 5000), (651, 2500)], [(1129, 2500), (521, 1250), (3869, 10000), (657, 2000), (1369, 5000)]]

theorem source_inputLo (i : Nat) :
    inputLo i = fraction (inputLoRaw.getD i (0,1)) := by
  rw [← ratioList_getD]
  simp only [inputLo, inputLoRaw, ratioList, fraction, List.map_cons, List.map_nil, Int.cast_ofNat, Nat.cast_ofNat, Int.cast_one, Nat.cast_one, div_one]

theorem source_inputHi (i : Nat) :
    inputHi i = fraction (inputHiRaw.getD i (0,1)) := by
  rw [← ratioList_getD]
  simp only [inputHi, inputHiRaw, ratioList, fraction, List.map_cons, List.map_nil, Int.cast_ofNat, Nat.cast_ofNat, Int.cast_one, Nat.cast_one, div_one]

theorem source_inputRate (i : Nat) :
    inputRate i = fraction (inputRateRaw.getD i (0,1)) := by
  rw [← ratioList_getD]
  rfl

theorem source_groupLo (i : Nat) :
    groupLo i = fraction (groupLoRaw.getD i (0,1)) := by
  rw [← ratioList_getD]
  rfl

theorem source_groupHi (i : Nat) :
    groupHi i = fraction (groupHiRaw.getD i (0,1)) := by
  rw [← ratioList_getD]
  rfl

theorem source_groupBar (i : Nat) :
    groupBar i = fraction (groupBarRaw.getD i (0,1)) := by
  rw [← ratioList_getD]
  rfl

theorem source_groupOf (i : Nat) : groupOf i = groupOfRaw.getD i 0 := rfl

theorem source_n44Lo (i : Nat) :
    N44.Data.pieceLo.getD i 0 = fraction (n44LoRaw.getD i (0,1)) := by
  have hs : N44.Data.pieceLo = mkRatList n44LoRaw := by rfl
  rw [hs, mkRatList_eq_ratioList, ratioList_getD]

theorem source_n44Hi (i : Nat) :
    N44.Data.pieceHi.getD i 0 = fraction (n44HiRaw.getD i (0,1)) := by
  have hs : N44.Data.pieceHi = mkRatList n44HiRaw := by rfl
  rw [hs, mkRatList_eq_ratioList, ratioList_getD]

theorem source_n44Rate (i : Nat) :
    (N44.Data.rates44.getD i []).getD 0 0 = fraction ((n44RatesRaw.getD i []).getD 0 (0,1)) := by
  have hs : N44.Data.rates44 = mkRatMatrix n44RatesRaw := by rfl
  rw [hs, mkRatMatrix_eq_ratioMatrix, ratioMatrix_getD_getD]

abbrev inputGuard (i : Nat) : Prop :=
  let g := groupOfRaw.getD i 0
  let il := inputLoRaw.getD i (0,1)
  let ih := inputHiRaw.getD i (0,1)
  let ir := inputRateRaw.getD i (0,1)
  let gl := groupLoRaw.getD g (0,1)
  let gh := groupHiRaw.getD g (0,1)
  let gb := groupBarRaw.getD g (0,1)
  let nl := n44LoRaw.getD i (0,1)
  let nh := n44HiRaw.getD i (0,1)
  let nr := (n44RatesRaw.getD i []).getD 0 (0,1)
  0 < il.2 ∧ 0 < ih.2 ∧ 0 < ir.2 ∧ 0 < gl.2 ∧ 0 < gh.2 ∧ 0 < gb.2 ∧
  0 < nl.2 ∧ 0 < nh.2 ∧ 0 < nr.2 ∧
  il.1*(nl.2 : Int) = nl.1*(il.2 : Int) ∧
  ih.1*(nh.2 : Int) = nh.1*(ih.2 : Int) ∧
  ir.1*(nr.2 : Int) = nr.1*(ir.2 : Int) ∧
  gl.1*(il.2 : Int) ≤ il.1*(gl.2 : Int) ∧
  ih.1*(gh.2 : Int) ≤ gh.1*(ih.2 : Int) ∧
  ir.1*(gb.2 : Int) ≤ gb.1*(ir.2 : Int) ∧ g < 23

theorem integer_inputs_checked :
    (List.range 55).all (fun i => decide (inputGuard i)) = true := by
  decide +kernel

theorem original_input_fact (i : Nat) (hi : i < 55) :
    inputLo i=N44.Data.pieceLo.getD i 0 ∧
    inputHi i=N44.Data.pieceHi.getD i 0 ∧
    inputRate i=(N44.Data.rates44.getD i []).getD 0 0 ∧
    groupLo (groupOf i) ≤ inputLo i ∧ inputHi i ≤ groupHi (groupOf i) ∧
    inputRate i ≤ groupBar (groupOf i) ∧ groupOf i < 23 := by
  have hg : inputGuard i := of_decide_eq_true
    (Erdos993Lean.F4Fast.forall_lt_of_range_all integer_inputs_checked i hi)
  dsimp only [inputGuard] at hg
  rcases hg with ⟨hIL,hIH,hIR,hGL,hGH,hGB,hNL,hNH,hNR,hEL,hEH,hER,hL,hH,hR,hG⟩
  refine ⟨?_,?_,?_,?_,?_,?_,?_⟩
  · rw [source_inputLo, source_n44Lo]
    exact fractionPair_eq _ _ (Nat.ne_of_gt hIL) (Nat.ne_of_gt hNL) hEL
  · rw [source_inputHi, source_n44Hi]
    exact fractionPair_eq _ _ (Nat.ne_of_gt hIH) (Nat.ne_of_gt hNH) hEH
  · rw [source_inputRate, source_n44Rate]
    exact fractionPair_eq _ _ (Nat.ne_of_gt hIR) (Nat.ne_of_gt hNR) hER
  · rw [source_groupLo, source_inputLo, source_groupOf]
    exact fractionPair_le _ _ hGL hIL hL
  · rw [source_inputHi, source_groupHi, source_groupOf]
    exact fractionPair_le _ _ hIH hGH hH
  · rw [source_inputRate, source_groupBar, source_groupOf]
    exact fractionPair_le _ _ hIR hGB hR
  · rw [source_groupOf]
    exact hG

end Erdos993Lean.Analytic.V213.ZeroTiltLaplace.PrintedRates.IntInput

#print axioms Erdos993Lean.Analytic.V213.ZeroTiltLaplace.PrintedRates.IntInput.source_inputLo
#print axioms Erdos993Lean.Analytic.V213.ZeroTiltLaplace.PrintedRates.IntInput.source_inputHi
#print axioms Erdos993Lean.Analytic.V213.ZeroTiltLaplace.PrintedRates.IntInput.source_inputRate
#print axioms Erdos993Lean.Analytic.V213.ZeroTiltLaplace.PrintedRates.IntInput.source_groupLo
#print axioms Erdos993Lean.Analytic.V213.ZeroTiltLaplace.PrintedRates.IntInput.source_groupHi
#print axioms Erdos993Lean.Analytic.V213.ZeroTiltLaplace.PrintedRates.IntInput.source_groupBar
#print axioms Erdos993Lean.Analytic.V213.ZeroTiltLaplace.PrintedRates.IntInput.source_groupOf
#print axioms Erdos993Lean.Analytic.V213.ZeroTiltLaplace.PrintedRates.IntInput.source_n44Lo
#print axioms Erdos993Lean.Analytic.V213.ZeroTiltLaplace.PrintedRates.IntInput.source_n44Hi
#print axioms Erdos993Lean.Analytic.V213.ZeroTiltLaplace.PrintedRates.IntInput.source_n44Rate
#print axioms Erdos993Lean.Analytic.V213.ZeroTiltLaplace.PrintedRates.IntInput.integer_inputs_checked
#print axioms Erdos993Lean.Analytic.V213.ZeroTiltLaplace.PrintedRates.IntInput.original_input_fact
