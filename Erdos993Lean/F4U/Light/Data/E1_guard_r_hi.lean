module
public import Erdos993Lean.F4U.Light.Checker

@[expose] public section
/-! Literal source: E1_guard_r_hi; all 7 controls, including directly checked faces. -/
namespace F4U.Light.Data.E1_guard_r_hi
def sourceSHA256 : String := "5f2868a73d7916e7804b1443c18a6f0f9397c3939e94e16aff697e59926ac1df"
def dataSHA256 : String := "63310df2c55f5190b35d5ca68f98d55348171a231ea14330ea28cacb2b4e9fc0"
def rows : List (List Int) := [
  [(-1436866560), (-6863139072), (-3829869504), 40929599008, 122686618016, 162893219872, 112061661784, 30128312396, (-9401366490), (-9243104284), (-2464072635), (-227550264)],
  [0, 359216640, (-1087978176), (-22905068352), (-89814811648), (-167314040560), (-168675522464), (-85454622648), (-7760319426), 13057517792, 5819281404, 745045088],
  [0, 0, 0, 1142245152, 11990257344, 42913119648, 72754769024, 62654595472, 22811921908, (-2643054320), (-4391092135), (-882554136)],
  [0, 0, 0, 0, (-42388128), (-1587111120), (-7481133120), (-13105757640), (-9908491420), (-2128009528), 1025439560, 438966080],
  [0, 0, 0, 0, 0, 0, 40402248, 470968356, 917460166, 595668172, 18398975, (-71879464)],
  [0, 0, 0, 0, 0, 0, 0, 0, (-8776642), (-6073192), (-7541444), (-2846624)],
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

end F4U.Light.Data.E1_guard_r_hi
