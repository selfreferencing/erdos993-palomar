module
public import Erdos993Lean.F4U.Light.Checker

@[expose] public section
/-! Literal source: E2_guard_r_hi; all 7 controls, including directly checked faces. -/
namespace F4U.Light.Data.E2_guard_r_hi
def sourceSHA256 : String := "92b169594d02e9b15963498ea4b6e3eedff39091e6d516c9a9e6d8c602bad8df"
def dataSHA256 : String := "2b1c62fa6759ab3cf6eb8076de058d46b32ace4cb41534dc47d063b908db2484"
def rows : List (List Int) := [
  [1220410368, 53648810880, 333620023584, 914189319152, 1373036506800, 1213841616712, 620371515752, 142906362768, (-22512172210), (-24476038534), (-6177766599), (-546638208)],
  [0, (-305102592), (-51966434016), (-364148733120), (-1021762321472), (-1473813836872), (-1180454335216), (-513822704272), (-89473106534), 18353970858, 11407088246, 1516787456],
  [0, 0, 0, 14425739472, 131452819632, 407713325400, 581917670464, 420500189280, 150798236172, 18824168556, (-4041714997), (-1262685312)],
  [0, 0, 0, 0, (-394164576), (-15655157400), (-66881277360), (-98718562416), (-62874006524), (-18001174516), (-2246074412), 77672960],
  [0, 0, 0, 0, 0, 0, 392042424, 4222606224, 6270610886, 3286326298, 1075777279, 303224192],
  [0, 0, 0, 0, 0, 0, 0, 0, (-96595838), 8861258, (-16867402), (-92834048)],
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-442115), 4472960]]
def ctls : List F4U.Light.Ctl := [⟨0, .norm⟩, ⟨1, .norm⟩, ⟨2, .norm⟩, ⟨3, .norm⟩, ⟨4, .norm⟩, ⟨5, .norm⟩, ⟨6, .norm⟩]
def fn : F4U.Light.Fn :=
  { m := 6, toQ := true, a1 := 29, a2 := 49, b1 := 8, b2 := 13,
    c := 769, rad := 15, D := 1274, rows := rows, ctls := ctls }

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

end F4U.Light.Data.E2_guard_r_hi
