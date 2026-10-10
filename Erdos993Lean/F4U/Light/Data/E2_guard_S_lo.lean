module
public import Erdos993Lean.F4U.Light.Checker

@[expose] public section
/-! Literal source: E2_guard_S_lo; all 6 controls, including directly checked faces. -/
namespace F4U.Light.Data.E2_guard_S_lo
def sourceSHA256 : String := "fc2dae9b2d571e6132151308a4555dcb5f34a321f5c6ebb845cedb827fc36589"
def dataSHA256 : String := "b52b672287fa0dac9e62696f1f0344ff796a7ecfb0425fb5dcfb164d6daefe4b"
def rows : List (List Int) := [
  [(-45611708294799830767104), (-432656461080423799028352), (-1329745843403196557652864), (-1647416462580406366229952), (-355913579043290922630672), 1188811385635541749129320, 1360633351163406990049280, 673379601428961446780368, 173694506552357583182985, 21989400848180090315056, 1001039515668212234240],
  [0, 11402927073699957691776, 266121350605883743433856, 998538021948337328156544, 1154748099240940339400208, (-213590252549834203934760), (-1468963375098851195766516), (-1220820745863084275995088), (-447431952960451895054031), (-75196121561319371641680), (-4388781548259790489600)],
  [0, 0, 0, (-50231771056963004435136), (-251160473707981958195568), (-248361051670878725311752), 253647627992245852459332, 569452299105346405094544, 346266455570038623828926, 85348542989445500406944, 6957431895571192156160],
  [0, 0, 0, 0, 717034449724984495728, 23813817437809048261512, 22507585851633022129508, (-50477629267956480882992), (-81245216376522295873458), (-35641437502004668031072), (-4781630874064276910080)],
  [0, 0, 0, 0, 0, 0, (-354656766099316189908), (-113558162254227942752), 2232194772697651575993, 3480479653503874220592, 1240894676113078138880],
  [0, 0, 0, 0, 0, 0, 0, 0, (-1608524484656690815), 19135572194574730160, (-28953665028415129600)]]
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

end F4U.Light.Data.E2_guard_S_lo
