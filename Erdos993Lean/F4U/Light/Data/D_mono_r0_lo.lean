module
public import Erdos993Lean.F4U.Light.Checker

@[expose] public section
/-! Literal source: D_mono_r0_lo; all 7 controls, including directly checked faces. -/
namespace F4U.Light.Data.D_mono_r0_lo
def sourceSHA256 : String := "dde94516285e8e2eebdaafc814c00f32006eb4cbf43121aab451e0a3afe9cdc6"
def dataSHA256 : String := "fd5697dc78d0cf7172589d2b43651b98a795c6092aba8599476b675e5a96d4f9"
def rows : List (List Int) := [
  [(-349590528), 56041982784, (-235694218032), 337550460168, (-48845245944), (-285023339100), 205129120868, 12081615012, (-54945495430), 17511399036, (-1555039297), 8680575],
  [0, 87397632, (-72711809712), 204669783504, (-39813972720), (-449045068332), 451612563948, 11060110492, (-177332880458), 71237067912, (-7775112900), 52083450],
  [0, 0, 0, 24363725256, (-3458379096), (-185202819396), 298061765460, (-12886869156), (-202527764368), 109834281288, (-15549975045), 130208625],
  [0, 0, 0, 0, (-806911200), (-19514419764), 52385634788, (-10627609740), (-93040964656), 77194426752, (-15549557120), 173611500],
  [0, 0, 0, 0, 0, 0, 807312408, 1237754896, (-13102680890), 22277286108, (-7774360635), 130208625],
  [0, 0, 0, 0, 0, 0, 0, 0, (-202095574), 1191471768, (-1554621372), 52083450],
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 83585, 8680575]]
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

end F4U.Light.Data.D_mono_r0_lo
