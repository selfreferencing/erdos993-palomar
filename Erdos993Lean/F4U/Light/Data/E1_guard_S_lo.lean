module
public import Erdos993Lean.F4U.Light.Checker

@[expose] public section
/-! Literal source: E1_guard_S_lo; all 6 controls, including directly checked faces. -/
namespace F4U.Light.Data.E1_guard_S_lo
def sourceSHA256 : String := "66877249219ff341df3413e1f9b4bf5ecd13572222bbeef82c2f4cc81f0629dd"
def dataSHA256 : String := "3becda81555fca4c7bca185b64526fb9633d1419625e7f92a7a91207fd6af75f"
def rows : List (List Int) := [
  [9943964055119267804160, 53973618657318196998912, 109323802231607132983296, 90656644845138893548416, 9045901028886288808560, (-13474955816277904251480), 27142187614117227634976, 38960221584125650594496, 17946301985100235227645, 3552342298076623331104, 257887559364827094976],
  [0, (-2485991013779816951040), (-17047167078463841378304), (-42082040541235139650944), (-45873709461717349385136), (-24788855189983901083752), (-31151362542388423420260), (-51594586242897472862576), (-36117059254072284329611), (-10175355912370448795104), (-976666034557284169280)],
  [0, 0, 0, 740082096573171994368, 5083437750796237352976, 13483970905044742003512, 16303954903526506967988, 19308569982022028225232, 20177490916795894620470, 9470655124806530298816, 1360123595463026902144],
  [0, 0, 0, 0, 51206818503676393008, (-140360360440272221880), (-2306608348359056157292), (-2767848127454358249616), (-2815691929524932806938), (-2909634661765794102848), (-825020632144918681472)],
  [0, 0, 0, 0, 0, 0, (-23204374391650908324), 232825968413962825840, 88385014923881511629, 58386962356428975392, 186896819305757858752],
  [0, 0, 0, 0, 0, 0, 0, 0, (-999597858411370075), 3606188896660292640, (-3221307431409005120)]]
def ctls : List F4U.Light.Ctl := [⟨0, .norm⟩, ⟨1, .norm⟩, ⟨2, .norm⟩, ⟨3, .norm⟩, ⟨4, .norm⟩, ⟨5, .norm⟩]
def fn : F4U.Light.Fn :=
  { m := 5, toQ := false, a1 := 13, a2 := 10, b1 := 29, b2 := 20,
    c := 55, rad := 3, D := 40, rows := rows, ctls := ctls }

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

end F4U.Light.Data.E1_guard_S_lo
