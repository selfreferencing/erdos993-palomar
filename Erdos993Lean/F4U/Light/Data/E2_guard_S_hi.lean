module
public import Erdos993Lean.F4U.Light.Checker

@[expose] public section
/-! Literal source: E2_guard_S_hi; all 6 controls, including directly checked faces. -/
namespace F4U.Light.Data.E2_guard_S_hi
def sourceSHA256 : String := "49109adea2f984309acd30fb9b2c3f6522aeaa8af40837a3334bbda80f9700f6"
def dataSHA256 : String := "4606e49e8a7d2fb2082df593f65259ed938636870b693d8126f129b70348f941"
def rows : List (List Int) := [
  [(-317330581380172255369728), (-3004382462181203713198464), (-9219731958439258143570048), (-11367145555296405683609664), (-2286985756027076578414704), 8507927648466539743905240, 9639202613591309730344960, 4754932714964277607462576, 1223258938518493169780895, 154420353321088792205392, 7007276609677485639680],
  [0, 79332645345043063842432, 1823983083806703964036992, 6806607816599422737095808, 7727902612213466655801456, (-1882614583888731727543320), (-10551149435842569880365612), (-8661020692307578211965616), (-3157911493075685037878217), (-528541057477442001491760), (-30721470837818533427200)],
  [0, 0, 0, (-335764632546433991045952), (-1672883197034996787368976), (-1576578034374324097182264), 1934320265922318037215324, 4077912268442558875661808, 2452985852990251751802482, 600877007638003942848608, 48702023268998345093120],
  [0, 0, 0, 0, 4388991206573971470096, 156827994207749957830584, 136170740381719984906556, (-374729843612548686180944), (-580164178806339526114206), (-251852349918463396217504), (-33471416118449938370560)],
  [0, 0, 0, 0, 0, 0, (-2170865609537843329356), (-358792952093115599264), 16441379439453528531951, 24976401521417039544144, 8686262732791546972160],
  [0, 0, 0, 0, 0, 0, 0, 0, (-9845830728809335705), 119644915395623111120, (-202675655198905907200)]]
def ctls : List F4U.Light.Ctl := [⟨0, .norm⟩, ⟨1, .norm⟩, ⟨2, .norm⟩, ⟨3, .norm⟩, ⟨4, .norm⟩, ⟨5, .norm⟩]
def fn : F4U.Light.Fn :=
  { m := 5, toQ := true, a1 := 29, a2 := 49, b1 := 8, b2 := 13,
    c := 769, rad := 15, D := 1274, rows := rows, ctls := ctls }

theorem geom : F4U.Light.geomOK fn = true := by decide +kernel
theorem shape : F4U.Light.shapeOK fn = true := by decide +kernel
theorem c0 : F4U.Light.checkCtl fn ⟨0, .norm⟩ = true := by decide +kernel
theorem c1 : F4U.Light.checkCtl fn ⟨1, .norm⟩ = true := by decide +kernel
theorem c2 : F4U.Light.checkCtl fn ⟨2, .norm⟩ = true := by decide +kernel
theorem c3 : F4U.Light.checkCtl fn ⟨3, .norm⟩ = true := by decide +kernel
theorem c4 : F4U.Light.checkCtl fn ⟨4, .norm⟩ = true := by decide +kernel
theorem c5 : F4U.Light.checkCtl fn ⟨5, .norm⟩ = true := by decide +kernel

/-- Assembly uses the already checked controls without a second arithmetic evaluation. -/
theorem checked : F4U.Light.checkFn fn = true := by
  simp only [F4U.Light.checkFn, geom, shape, Bool.true_and]
  change ctls.all (F4U.Light.checkCtl fn) = true
  simp only [ctls, List.all_cons, List.all_nil, c0, c1, c2, c3, c4, c5, Bool.and_self]

end F4U.Light.Data.E2_guard_S_hi
