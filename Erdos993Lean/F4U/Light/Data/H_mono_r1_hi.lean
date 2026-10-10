module
public import Erdos993Lean.F4U.Light.Checker

@[expose] public section
/-! Literal source: H_mono_r1_hi; all 6 controls, including directly checked faces. -/
namespace F4U.Light.Data.H_mono_r1_hi
def sourceSHA256 : String := "d9d90a986cc78e87eae0440951641d75d9b1c0388da5bbf3a433ccac0fc1daf4"
def dataSHA256 : String := "3d6a32a52ebd86d67f6c874d1c5240c86cd71c189298248d5eadab92c624b921"
def rows : List (List Int) := [
  [(-65043532800), 886056544512, (-2126706973056), 1535890984128, 365277780048, (-967795798872), 413361061328, (-42863090312), (-5597025769), 106014825],
  [0, 16260883200, (-731410729344), 1217954969856, 423405474864, (-1758247152840), 1004933555748, (-127532673548), (-22521849101), 530074125],
  [0, 0, 0, 192216377664, 62587527408, (-895515162120), 772760164812, (-125419478772), (-34117138714), 1060148250],
  [0, 0, 0, 0, (-5310493680), (-105063808152), 184163907692, (-39693298148), (-23190579226), 1060148250],
  [0, 0, 0, 0, 0, 0, 2976237300, 1056597388, (-6132009869), 530074125],
  [0, 0, 0, 0, 0, 0, 0, 0, (-133746025), 106014825]]
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

end F4U.Light.Data.H_mono_r1_hi
