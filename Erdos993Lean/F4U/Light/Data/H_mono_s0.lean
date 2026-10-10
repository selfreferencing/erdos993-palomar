module
public import Erdos993Lean.F4U.Light.Checker

@[expose] public section
/-! Literal source: H_mono_s0; all 6 controls, including directly checked faces. -/
namespace F4U.Light.Data.H_mono_s0
def sourceSHA256 : String := "8efb5fd464329094f7480b710909d11a715fbfb44a1f1597cba22e3eb6db64f3"
def dataSHA256 : String := "caec867219e3ca7140fdfc24ac7c92dc5ebb3b60e2bdf3cf0b6cad7e9f0c9d1f"
def rows : List (List Int) := [
  [1570996735716429987840, (-4134631637090052523008), 2868748828296144217344, (-1112907180139437292032), 3387356443381107587712, (-2624555292920577853200), (-1531808658320265914440), 2209995181250082678624, (-663230843518625904912), 36192911943343328165, 849803259851035875],
  [0, (-392749183929107496960), (-13975099983636569856), (-528115145636162124288), 4714311400334208913536, (-3918172175434798716720), (-3736595553386417513784), 5783320175387999997820, (-2083074570381065232628), 143287400558859831025, 4249016299255179375],
  [0, 0, 0, (-10385756088724832256), 1336201841669700745728, (-1326010715645684659056), (-2921968290493841187288), 5011465190254492828116, (-2269318685800930095292), 211220482802006042450, 8498032598510358750],
  [0, 0, 0, 0, 20645598700599419904, (-32393833131463795536), (-728752108931213713384), 1512950579345316377268, (-941817070302657939228), 135866164486292422850, 8498032598510358750],
  [0, 0, 0, 0, 0, 0, (-11570713503524125440), 74810383228740868348, (-91822147133656998532), 30255923085289401625, 4249016299255179375],
  [0, 0, 0, 0, 0, 0, 0, 0, 519964230510173120, (-1484247214513481635), 849803259851035875]]
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

end F4U.Light.Data.H_mono_s0
