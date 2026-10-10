module
public import Erdos993Lean.F4U.Light.Checker

@[expose] public section
/-! Literal source: E1_guard_r_lo; all 7 controls, including directly checked faces. -/
namespace F4U.Light.Data.E1_guard_r_lo
def sourceSHA256 : String := "d281813bb604427fec8d71fa8b8714bb863f7aa0d97d5de9ff80ec71567ce771"
def dataSHA256 : String := "a4adbaf53887af9dfbb13e98ac6ea3e08a2c38642f2a1dc875e7f34477965b1b"
def rows : List (List Int) := [
  [(-1436866560), (-5899295232), 3254381568, 61981230848, 154014347488, 184115630192, 110127689280, 15620716248, (-20590202326), (-13412550178), (-3253018977), (-288168360)],
  [0, 359216640, (-1810861056), (-28871461632), (-108448099424), (-194136457328), (-182615364664), (-76934745880), 8111336590, 21946289566, 8085743090, 967311440],
  [0, 0, 0, 1262725632, 13531353120, 48731045712, 81324267544, 65448421160, 17386300908, (-8697733372), (-6708338075), (-1192379960)],
  [0, 0, 0, 0, (-42388128), (-1721471952), (-8290158632), (-14430567688), (-9974897772), (-752338876), 2019431516, 641026400],
  [0, 0, 0, 0, 0, 0, 40402248, 515299808, 1021852746, 558986270, (-138962151), (-132497560)],
  [0, 0, 0, 0, 0, 0, 0, 0, (-8776642), (-9708770), (-4441678), 3888720],
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-413725), 819320]]
def ctls : List F4U.Light.Ctl := [⟨0, .norm⟩, ⟨1, .norm⟩, ⟨2, .norm⟩, ⟨3, .norm⟩, ⟨4, .norm⟩, ⟨5, .norm⟩, ⟨6, .norm⟩]
def fn : F4U.Light.Fn :=
  { m := 6, toQ := false, a1 := 13, a2 := 10, b1 := 29, b2 := 20,
    c := 55, rad := 3, D := 40, rows := rows, ctls := ctls }

theorem geom : F4U.Light.geomOK fn = true := by decide +kernel
theorem shape : F4U.Light.shapeOK fn = true := by decide +kernel
theorem c0 : F4U.Light.checkCtl fn ⟨0, .norm⟩ = true := by decide +kernel
theorem c1 : F4U.Light.checkCtl fn ⟨1, .norm⟩ = true := by decide +kernel
theorem c2 : F4U.Light.checkCtl fn ⟨2, .norm⟩ = true := by decide +kernel
theorem c3 : F4U.Light.checkCtl fn ⟨3, .norm⟩ = true := by decide +kernel
theorem c4 : F4U.Light.checkCtl fn ⟨4, .norm⟩ = true := by decide +kernel
theorem c5 : F4U.Light.checkCtl fn ⟨5, .norm⟩ = true := by decide +kernel
theorem c6 : F4U.Light.checkCtl fn ⟨6, .norm⟩ = true := by decide +kernel

/-- Assembly uses the already checked controls without a second arithmetic evaluation. -/
theorem checked : F4U.Light.checkFn fn = true := by
  simp only [F4U.Light.checkFn, geom, shape, Bool.true_and]
  change ctls.all (F4U.Light.checkCtl fn) = true
  simp only [ctls, List.all_cons, List.all_nil, c0, c1, c2, c3, c4, c5, c6, Bool.and_self]

end F4U.Light.Data.E1_guard_r_lo
