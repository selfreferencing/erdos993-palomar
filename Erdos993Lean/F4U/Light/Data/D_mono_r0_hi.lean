module
public import Erdos993Lean.F4U.Light.Checker

@[expose] public section
/-! Literal source: D_mono_r0_hi; all 6 controls, including directly checked faces. -/
namespace F4U.Light.Data.D_mono_r0_hi
def sourceSHA256 : String := "9b8148b1c13965ec5edf124e20cb3eef4b3c9f80ff4ac78bc2c070502a155d6b"
def dataSHA256 : String := "7776716fe99bf68c1c760acc7d0ba90181f57a2ec994140631e48b00d0878292"
def rows : List (List Int) := [
  [(-174795264), 28195786656, (-97811911224), 128482131084, (-50815765668), (-38729127492), 44817518116, (-14856057076), 1537678147, (-8680575)],
  [0, 43698816, (-36487001304), 97375496400, (-66051902928), (-61245291672), 103593925716, (-45777171316), 6150629003, (-43402875)],
  [0, 0, 0, 12203712036, (-16472928060), (-26170715628), 72937225488, (-48195171492), 9225734542, (-86805750)],
  [0, 0, 0, 0, (-403455600), (-3654551448), 14362746292, (-18483057340), 6150211078, (-86805750)],
  [0, 0, 0, 0, 0, 0, 201928404, (-1209000088), 1537343807, (-43402875)],
  [0, 0, 0, 0, 0, 0, 0, 0, (-83585), (-8680575)]]
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

end F4U.Light.Data.D_mono_r0_hi
