module
public import Erdos993Lean.F4U.Light.Checker

@[expose] public section
/-! Literal source: H_mono_r1_lo; all 7 controls, including directly checked faces. -/
namespace F4U.Light.Data.H_mono_r1_lo
def sourceSHA256 : String := "4ae90094fc297a0d7a66e4d0598120045444b7e6e58b7b37a4d33e966e510824"
def dataSHA256 : String := "0f11b8780d7b7246e2200110a4682e6c654351f554fc5ce4a3c73c88da4a91ff"
def rows : List (List Int) := [
  [(-130087065600), 1642026023424, (-3343970260224), 870069108096, 2991286870944, (-2500945724112), (-98683978592), 862414748136, (-347609407154), 27854536584, 5809055419, (-106014825)],
  [0, 32521766400, (-1365256159488), 1153102811904, 3821556252000, (-5090132473584), 130272331320, 2478853085264, (-1222334939686), 110306086548, 29179023120, (-636088950)],
  [0, 0, 0, 368171872128, 931780894176, (-2974558014576), 457129202280, 2479564871808, (-1584592105484), 162678980352, 58759284315, (-1590222375)],
  [0, 0, 0, 0, (-10620987360), (-404911917648), 239435860648, 972229480368, (-895860749876), 104745787608, 59428014440, (-2120296500)],
  [0, 0, 0, 0, 0, 0, 11262968280, 109102945688, (-189237906274), 23406297432, 30382737345, (-1590222375)],
  [0, 0, 0, 0, 0, 0, 0, 0, (-3243729350), (-1112059788), 6477785544, (-636088950)],
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 133746025, (-106014825)]]
def ctls : List F4U.Light.Ctl := [⟨0, .quad⟩, ⟨1, .quad⟩, ⟨2, .quad⟩, ⟨3, .quad⟩, ⟨4, .quad⟩, ⟨5, .quad⟩, ⟨6, .quad⟩]
def fn : F4U.Light.Fn :=
  { m := 6, toQ := false, a1 := 7, a2 := 11, b1 := 7, b2 := 10,
    c := 147, rad := 7, D := 220, rows := rows, ctls := ctls }

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

end F4U.Light.Data.H_mono_r1_lo
