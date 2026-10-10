module
public import Erdos993Lean.F4U.Light.Checker

@[expose] public section
/-! Literal source: D_mono_r1_hi; all 6 controls, including directly checked faces. -/
namespace F4U.Light.Data.D_mono_r1_hi
def sourceSHA256 : String := "4466dfedb2e437978aa75373ae7a7f7dd78cb26234eacc14931adfa05bf30768"
def dataSHA256 : String := "a57199bbbe88c7071b02320d564e2447de877c8447c432de68a069325b01b1c9"
def rows : List (List Int) := [
  [(-524385792), 77690491008, (-267821445312), 353652056032, (-143077058224), (-105224274696), 124444576288, (-41566637248), 4305465141, (-26041725)],
  [0, 131096448, (-104288352192), 273906825600, (-185634879664), (-168688803096), 288390137628, (-128038537588), 17221609809, (-130208625)],
  [0, 0, 0, 35749027488, (-45990415440), (-74573710104), 204052331604, (-134715789276), 25831787826, (-260417250)],
  [0, 0, 0, 0, (-1210366800), (-11109181704), 40712555476, (-51582514780), 17220356034, (-260417250)],
  [0, 0, 0, 0, 0, 0, 605785212, (-3338625844), 4304462121, (-130208625)],
  [0, 0, 0, 0, 0, 0, 0, 0, (-250755), (-26041725)]]
def ctls : List F4U.Light.Ctl := [⟨0, .quad⟩, ⟨1, .quad⟩, ⟨2, .quad⟩, ⟨3, .quad⟩, ⟨4, .quad⟩, ⟨5, .quad⟩]
def fn : F4U.Light.Fn :=
  { m := 5, toQ := false, a1 := 4, a2 := 9, b1 := 13, b2 := 23,
    c := 209, rad := 25, D := 414, rows := rows, ctls := ctls }

theorem geom : F4U.Light.geomOK fn = true := by decide +kernel
theorem shape : F4U.Light.shapeOK fn = true := by decide +kernel
theorem c0 : F4U.Light.checkCtl fn ⟨0, .quad⟩ = true := by decide +kernel
theorem c1 : F4U.Light.checkCtl fn ⟨1, .quad⟩ = true := by decide +kernel
theorem c2 : F4U.Light.checkCtl fn ⟨2, .quad⟩ = true := by decide +kernel
theorem c3 : F4U.Light.checkCtl fn ⟨3, .quad⟩ = true := by decide +kernel
theorem c4 : F4U.Light.checkCtl fn ⟨4, .quad⟩ = true := by decide +kernel
theorem c5 : F4U.Light.checkCtl fn ⟨5, .quad⟩ = true := by decide +kernel

/-- Assembly uses the already checked controls without a second arithmetic evaluation. -/
theorem checked : F4U.Light.checkFn fn = true := by
  simp only [F4U.Light.checkFn, geom, shape, Bool.true_and]
  change ctls.all (F4U.Light.checkCtl fn) = true
  simp only [ctls, List.all_cons, List.all_nil, c0, c1, c2, c3, c4, c5, Bool.and_self]

end F4U.Light.Data.D_mono_r1_hi
