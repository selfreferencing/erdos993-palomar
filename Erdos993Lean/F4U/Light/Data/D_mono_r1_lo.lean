module
public import Erdos993Lean.F4U.Light.Checker

@[expose] public section
/-! Literal source: D_mono_r1_lo; all 7 controls, including directly checked faces. -/
namespace F4U.Light.Data.D_mono_r1_lo
def sourceSHA256 : String := "916692fad1553de162c87a67a85536711ea1eba896818c22f5cb9a47f13c1b18"
def dataSHA256 : String := "2573b52c6ce9b228f1ac38a5ec3d0f191d3f6ff21fda40404a25c9d4383438c2"
def rows : List (List Int) := [
  [(-1048771584), 154332210432, (-637435560576), 918604451264, (-148547181792), (-770529391440), 569675330784, 27374976456, (-151453844790), 48917524528, (-4357548591), 26041725],
  [0, 262192896, (-207790125696), 570653004672, (-121361208800), (-1225879274736), 1255846245224, 17211612016, (-489513423234), 198956138996, (-21787492200), 156250350],
  [0, 0, 0, 71366958528, (-6388736928), (-517766543088), 830421825400, (-43266164448), (-560423487684), 306649310704, (-43574232135), 390625875],
  [0, 0, 0, 0, (-2420733600), (-57972205392), 146672848184, (-28667259120), (-258728371548), 215386343416, (-43572978360), 520834500],
  [0, 0, 0, 0, 0, 0, 2421937224, 4435540888, (-36970749030), 62061688064, (-21785235405), 390625875],
  [0, 0, 0, 0, 0, 0, 0, 0, (-606286722), 3286040884, (-4356294816), 156250350],
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 250755, 26041725]]
def ctls : List F4U.Light.Ctl := [⟨0, .quad⟩, ⟨1, .quad⟩, ⟨2, .quad⟩, ⟨3, .quad⟩, ⟨4, .quad⟩, ⟨5, .quad⟩, ⟨6, .quad⟩]
def fn : F4U.Light.Fn :=
  { m := 6, toQ := false, a1 := 4, a2 := 9, b1 := 13, b2 := 23,
    c := 209, rad := 25, D := 414, rows := rows, ctls := ctls }

theorem geom : F4U.Light.geomOK fn = true := by decide +kernel
theorem shape : F4U.Light.shapeOK fn = true := by decide +kernel
theorem c0 : F4U.Light.checkCtl fn ⟨0, .quad⟩ = true := by decide +kernel
theorem c1 : F4U.Light.checkCtl fn ⟨1, .quad⟩ = true := by decide +kernel
theorem c2 : F4U.Light.checkCtl fn ⟨2, .quad⟩ = true := by decide +kernel
theorem c3 : F4U.Light.checkCtl fn ⟨3, .quad⟩ = true := by decide +kernel
theorem c4 : F4U.Light.checkCtl fn ⟨4, .quad⟩ = true := by decide +kernel
theorem c5 : F4U.Light.checkCtl fn ⟨5, .quad⟩ = true := by decide +kernel
theorem c6 : F4U.Light.checkCtl fn ⟨6, .quad⟩ = true := by decide +kernel

/-- Assembly uses the already checked controls without a second arithmetic evaluation. -/
theorem checked : F4U.Light.checkFn fn = true := by
  simp only [F4U.Light.checkFn, geom, shape, Bool.true_and]
  change ctls.all (F4U.Light.checkCtl fn) = true
  simp only [ctls, List.all_cons, List.all_nil, c0, c1, c2, c3, c4, c5, c6, Bool.and_self]

end F4U.Light.Data.D_mono_r1_lo
