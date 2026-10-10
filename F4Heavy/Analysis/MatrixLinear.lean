module

public import F4Heavy.Analysis.MatrixSemantics

@[expose] public section
set_option autoImplicit false

namespace F4Heavy.Analysis
open F4Heavy.Finite

noncomputable def realCoefficients (p : List (List Fraction)) : List (List ℝ) :=
  p.map (fun row => row.map fractionValue)

noncomputable def realMatrixValue (p : List (List ℝ)) (v x : ℝ) : ℝ :=
  realHorner (p.map (fun row => realHorner row x)) v

def realMatrixAdd (p q : List (List ℝ)) : List (List ℝ) :=
  p.zipWith (fun a b => a.zipWith (· + ·) b) q

def realMatrixScale (c : ℝ) (p : List (List ℝ)) : List (List ℝ) :=
  p.map (fun row => row.map (c * ·))

theorem realMatrixValue_coefficients (p : List (List Fraction)) (v x : ℝ) :
    realMatrixValue (realCoefficients p) v x = matrixValue p v x := by
  simp only [realMatrixValue, realCoefficients, matrixValue, List.map_map, Function.comp_def]

theorem realHorner_zipWith_add (p q : List ℝ) (x : ℝ) (hlen : p.length = q.length) :
    realHorner (p.zipWith (· + ·) q) x = realHorner p x+realHorner q x := by
  induction p generalizing q with
  | nil => cases q <;> simp_all [realHorner]
  | cons a p ih =>
    cases q with
    | nil => simp at hlen
    | cons b q =>
      have ht : p.length = q.length := Nat.succ.inj hlen
      simp only [List.zipWith_cons_cons, realHorner_cons, ih q ht]
      ring

theorem realMatrixValue_add (p q : List (List ℝ)) (v x : ℝ)
    (hshape : p.map List.length = q.map List.length) :
    realMatrixValue (realMatrixAdd p q) v x = realMatrixValue p v x+realMatrixValue q v x := by
  induction p generalizing q with
  | nil => cases q <;> simp_all [realMatrixValue, realMatrixAdd, realHorner]
  | cons a p ih =>
    cases q with
    | nil => simp at hshape
    | cons b q =>
      obtain ⟨hlen, htail⟩ := List.cons.inj hshape
      change realHorner (a.zipWith (· + ·) b) x + v*realMatrixValue (realMatrixAdd p q) v x =
        (realHorner a x+v*realMatrixValue p v x)+(realHorner b x+v*realMatrixValue q v x)
      rw [realHorner_zipWith_add a b x hlen, ih q htail]
      ring

theorem realMatrixValue_scale (c : ℝ) (p : List (List ℝ)) (v x : ℝ) :
    realMatrixValue (realMatrixScale c p) v x = c*realMatrixValue p v x := by
  unfold realMatrixValue realMatrixScale
  simp only [List.map_map, Function.comp_def, realHorner_map_scale]
  simpa only [List.map_map, Function.comp_def] using
    realHorner_map_scale (p.map (fun row => realHorner row x)) c v

end F4Heavy.Analysis
