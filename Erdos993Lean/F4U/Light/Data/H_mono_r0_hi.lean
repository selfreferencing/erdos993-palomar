module
public import Erdos993Lean.F4U.Light.Checker

@[expose] public section
/-! Literal source: H_mono_r0_hi; all 6 controls, including directly checked faces. -/
namespace F4U.Light.Data.H_mono_r0_hi
def sourceSHA256 : String := "a5de5d07b2fed71c20673732db023d37879226623d8630c43c37fa8a663951a3"
def dataSHA256 : String := "8845622132b29e780570fd117475e1ae8c80b7e740be6e186e6aeb4019652aff"
def rows : List (List Int) := [
  [(-91060945920), 1430678317824, (-3492118127232), 2470631359296, 688315853424, (-1591565134920), 632644567600, (-51421002232), (-10546126259), 148420755],
  [0, 22765236480, (-1166624387712), 1913255195904, 809447430672, (-2875436121240), 1535878959372, (-151424535940), (-42371749471), 742103775],
  [0, 0, 0, 292877823168, 129980763216, (-1445771667672), 1177990948164, (-145747594428), (-64025735294), 1484207550],
  [0, 0, 0, 0, (-7434691152), (-161900681352), 278923288612, (-42905589964), (-43307971646), 1484207550],
  [0, 0, 0, 0, 0, 0, 4166732220, 2838470756, (-11295103999), 742103775],
  [0, 0, 0, 0, 0, 0, 0, 0, (-187244435), 148420755]]
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

end F4U.Light.Data.H_mono_r0_hi
