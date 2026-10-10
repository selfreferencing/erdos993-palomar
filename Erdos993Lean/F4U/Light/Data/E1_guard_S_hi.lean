module
public import Erdos993Lean.F4U.Light.Checker

@[expose] public section
/-! Literal source: E1_guard_S_hi; all 6 controls, including directly checked faces. -/
namespace F4U.Light.Data.E1_guard_S_hi
def sourceSHA256 : String := "b0b21eba0ef1362aec75dd1d5e77ad068a12b111ebe5d7c852ada265523811d9"
def dataSHA256 : String := "c4d4d4525c7b701f865e75b72d43f44c4f1fce8eaa46d5202706ecaded49cfee"
def rows : List (List Int) := [
  [9756559656381347804160, 52760731402707892998912, 106276275676306268983296, 87422006879504909548416, 8987961307229016808560, (-10367092086572260251480), 30085603511058747634976, 40164719837801458594496, 18178024975693556727645, 3569452105140427331104, 257887559364827094976],
  [0, (-2439139914095336951040), (-16763345153971553378304), (-41465536142860547650944), (-45950549564867341385136), (-27289709098552553083752), (-35041027857628309420260), (-54043245304296568862576), (-36783722905025902829611), (-10240153793502068795104), (-976666034557284169280)],
  [0, 0, 0, 802489528298355994368, 5352523748343877352976, 14102278740957418003512, 17562883129230928967988, 20688307234165460225232, 20803384384758475620470, 9560893879861706298816, 1360123595463026902144],
  [0, 0, 0, 0, 45678315118180393008, (-183467049530100221880), (-2376593298087386157292), (-2946463904933406249616), (-3013421342423495806938), (-2964371477587482102848), (-825020632144918681472)],
  [0, 0, 0, 0, 0, 0, (-20699132587312908324), 227991830853346825840, 95053699433323011629, 70786818041736975392, 186896819305757858752],
  [0, 0, 0, 0, 0, 0, 0, 0, (-891677071573870075), 3392468045680292640, (-3221307431409005120)]]
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

end F4U.Light.Data.E1_guard_S_hi
