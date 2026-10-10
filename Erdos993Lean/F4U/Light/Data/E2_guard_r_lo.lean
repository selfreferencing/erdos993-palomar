module
public import Erdos993Lean.F4U.Light.Checker

@[expose] public section
/-! Literal source: E2_guard_r_lo; all 7 controls, including directly checked faces. -/
namespace F4U.Light.Data.E2_guard_r_lo
def sourceSHA256 : String := "e38ad6e95c8eecfa5fe0e8428cda72218cefc966e0a1f461c905eb0cb7cabaca"
def dataSHA256 : String := "16818ddd7bae24d81551fc1271dc9fa5016052d7a62ee845edec955f9d1de189"
def rows : List (List Int) := [
  [1220410368, 58626621696, 366622713600, 1000342664320, 1479713345568, 1260547002320, 584613279360, 82197132360, (-59218181738), (-36250163278), (-8184231663), (-691006848)],
  [0, (-305102592), (-55699792128), (-391002403584), (-1091532383392), (-1547613280592), (-1183827382664), (-449107686376), (-26336058574), 46033881010, 17417673310, 2046139136],
  [0, 0, 0, 15047965824, 138009956832, 426445000560, 596723525672, 405814212504, 117745013396, (-3353885860), (-10599498469), (-2000569472)],
  [0, 0, 0, 0, (-394164576), (-16190088048), (-68908238872), (-98922964728), (-57212807956), (-10961473252), 901285636, 558901760],
  [0, 0, 0, 0, 0, 0, 392042424, 4291220800, 6037162102, 2497246962, 444392663, 158855552],
  [0, 0, 0, 0, 0, 0, 0, 0, (-96595838), 30508338, 20820638, (-76793088)],
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

end F4U.Light.Data.E2_guard_r_lo
