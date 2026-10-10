module
public import Erdos993Lean.F4U.Light.Checker

@[expose] public section
/-! Literal source: H_mono_r0_lo; all 7 controls, including directly checked faces. -/
namespace F4U.Light.Data.H_mono_r0_lo
def sourceSHA256 : String := "460b5280f62f3a350c8d81de28c686a65504bee866e97cb056ae222658f0a8d7"
def dataSHA256 : String := "f1e8c646f9835e1af372e9d2010ad8f9f5ed6a9a7dd8f0f23542f56f50404e3f"
def rows : List (List Int) := [
  [(-182121891840), 2679234743808, (-5578006899456), 1319531648640, 5171447872992, (-4033927399152), (-386732637856), 1445389417656, (-513376301446), 24988446648, 10842967769, (-148420755)],
  [0, 45530472960, (-2196657356544), 1740625111296, 6547914847008, (-8172803423568), (-301743365016), 4154807939056, (-1815234239234), 97037668476, 54402083280, (-890524530)],
  [0, 0, 0, 562990409856, 1548485092512, (-4726582549200), 390099915384, 4143721567872, (-2369986130116), 138266207424, 109365899865, (-2226311325)],
  [0, 0, 0, 0, (-14869382304), (-620274279024), 320878798136, 1604576989200, (-1352315969404), 82457077896, 110302122040, (-2968415100)],
  [0, 0, 0, 0, 0, 0, 15768155592, 170273942728, (-288728998166), 13323974184, 56087283195, (-2226311325)],
  [0, 0, 0, 0, 0, 0, 0, 0, (-4541221090), (-2916118116), 11779189944, (-890524530)],
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 187244435, (-148420755)]]
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

end F4U.Light.Data.H_mono_r0_lo
