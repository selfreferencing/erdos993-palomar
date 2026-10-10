module
public import Erdos993Lean.F4U.Light.Checker

@[expose] public section
/-! Literal source: H_mono_s1; all 6 controls, including directly checked faces. -/
namespace F4U.Light.Data.H_mono_s1
def sourceSHA256 : String := "9b9626853decae888ab53832f3905559f0eb31ff3ab44c748f9e06e9f5ab342f"
def dataSHA256 : String := "821f58f7d3b783a45c7d1f5ca6191e1ca75b4e0c91b25a44f5681a2d486cea0f"
def rows : List (List Int) := [
  [4694778017965289963520, (-12355508192089357569024), 8551233315634032652032, (-3245075245455111876096), 10078573799132122763136, (-7896165135121733559600), (-4536320913616797743320), 6608967188047848035872, (-1988413893079677714736), 108608419981029984495, 2549409779553107625],
  [0, (-1173694504491322490880), (-96938469205309709568), (-1461842195359686372864), 14033973979809026740608, (-11812241116472396150160), (-11063825844940852541352), 17285774110191999993460, (-6244146610125395697884), 430010622431579493075, 12747048897765538125],
  [0, 0, 0, (-2300321680574496768), 3981653896596302237184, (-4027123429591453977168), (-8650465078632723561864), 14967946457061878484348, (-6800434028093590285876), 633958289916018127350, 25494097795531076250],
  [0, 0, 0, 0, 60449857871398259712, (-111047448240791386608), (-2156838941375241140152), 4514439335739149131804, (-2820561354325173817684), 407895334968877268550, 25494097795531076250],
  [0, 0, 0, 0, 0, 0, (-33878794066572376320), 223299800821422605044, (-274337599472770995596), 90916190010868204875, 12747048897765538125],
  [0, 0, 0, 0, 0, 0, 0, 0, 1522443804530519360, (-4423057492540444905), 2549409779553107625]]
def ctls : List F4U.Light.Ctl := [⟨0, .quad⟩, ⟨1, .quad⟩, ⟨2, .quad⟩, ⟨3, .quad⟩, ⟨4, .quad⟩, ⟨5, .quad⟩]
def fn : F4U.Light.Fn :=
  { m := 5, toQ := false, a1 := 7, a2 := 11, b1 := 7, b2 := 10,
    c := 147, rad := 7, D := 220, rows := rows, ctls := ctls }

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

end F4U.Light.Data.H_mono_s1
