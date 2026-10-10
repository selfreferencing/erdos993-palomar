module

public import Erdos993Lean.Analytic.V213.LowMeanCoreChecker

/-!
Cheaper kernel check for the low-mean fiber groups.

`lowMeanFiberCheck` verifies every witness tree against its specified formula by
(1) checking the witness arithmetic, (2) erasing the witnesses into a second tree,
(3) building the specified shape, (4) comparing the two trees with the derived
`DecidableEq`.  Steps (2) and (4) are the largest cost in all three kernels.
`fastFiberCheck` replaces them by one structural walk `eraseMatch` over the witness tree
and the specified shape together; nothing is erased and no derived equality is run.
It also walks the rank window directly instead of looking every rank up by index, and it
runs the witness arithmetic on the recursor with direct `Int`/`Nat` steps and the native
`Nat.pow` (`fastExprCheck`), which about halves that part in all three kernels.
`fastFiberCheck_sound` proves that the fast check implies the original one, so the
original group theorems follow with their exact statements.
-/

@[expose] public section

namespace Erdos993Lean.LowMeanFast
open Erdos993Lean.Analytic.V213

/-- Integer equality by constructor match and the kernel's native `Nat.beq`. -/
def intBeq : ℤ → ℤ → Bool
  | .ofNat a, .ofNat b => Nat.beq a b
  | .negSucc a, .negSucc b => Nat.beq a b
  | _, _ => false

theorem intBeq_eq {a b : ℤ} (h : intBeq a b = true) : a = b := by
  cases a <;> cases b
  · simp only [intBeq] at h
    exact congrArg Int.ofNat (Nat.eq_of_beq_eq_true h)
  · simp [intBeq] at h
  · simp [intBeq] at h
  · simp only [intBeq] at h
    exact congrArg Int.negSucc (Nat.eq_of_beq_eq_true h)

def fracBeq (x y : lowMeanFraction) : Bool := intBeq x.1 y.1 && Nat.beq x.2 y.2

theorem fracBeq_eq {x y : lowMeanFraction} (h : fracBeq x y = true) : x = y := by
  simp only [fracBeq, Bool.and_eq_true] at h
  exact Prod.ext (intBeq_eq h.1) (Nat.eq_of_beq_eq_true h.2)

/-! ### Structural match of a witness tree against a specified shape, on the recursor -/

/-- `eraseMatch e s = true` implies `lowMeanIntegerExprErase e = s`, without building the erased tree.
Written directly on the recursor: the kernels then pay one iota step per node. -/
noncomputable def eraseMatch : LowMeanIntegerExpr → LowMeanIntegerShape → Bool :=
  @LowMeanIntegerExpr.rec (fun _ => LowMeanIntegerShape → Bool)
    (fun x s => match s with | .atom y => fracBeq x y | _ => false)
    (fun _ _ _ ihx ihy s => match s with | .add sx sy => ihx sx && ihy sy | _ => false)
    (fun _ _ ihx s => match s with | .neg sx => ihx sx | _ => false)
    (fun _ _ _ ihx ihy s => match s with | .mul sx sy => ihx sx && ihy sy | _ => false)
    (fun _ _ _ ihx ihy s => match s with | .div sx sy => ihx sx && ihy sy | _ => false)
    (fun _ _ n ihx s => match s with | .pow sx m => Nat.beq n m && ihx sx | _ => false)
    (fun _ _ ihx s => match s with | .abs sx => ihx sx | _ => false)
    (fun _ _ _ ihx ihy s => match s with | .minimum sx sy => ihx sx && ihy sy | _ => false)
    (fun _ _ _ ihx ihy s => match s with | .maximum sx sy => ihx sx && ihy sy | _ => false)
    (fun _ _ _ _ _ ihx ihy iha ihb s => match s with
      | .selectLE sx sy sa sb => ihx sx && ihy sy && iha sa && ihb sb | _ => false)
    (fun _ _ _ _ _ ihx ihy iha ihb s => match s with
      | .selectLT sx sy sa sb => ihx sx && ihy sy && iha sa && ihb sb | _ => false)

theorem eraseMatch_sound (e : LowMeanIntegerExpr) :
    ∀ s : LowMeanIntegerShape, eraseMatch e s = true → lowMeanIntegerExprErase e = s := by
  induction e with
  | atom x =>
    intro s h
    cases s with
    | atom y =>
      have h' : fracBeq x y = true := h
      simp only [lowMeanIntegerExprErase]
      rw [fracBeq_eq h']
    | _ => exact absurd h Bool.false_ne_true
  | add z x y ihx ihy =>
    intro s h
    cases s with
    | add sx sy =>
      have h' : (eraseMatch x sx && eraseMatch y sy) = true := h
      simp only [Bool.and_eq_true] at h'
      simp only [lowMeanIntegerExprErase]
      rw [ihx sx h'.1, ihy sy h'.2]
    | _ => exact absurd h Bool.false_ne_true
  | neg z x ihx =>
    intro s h
    cases s with
    | neg sx =>
      have h' : eraseMatch x sx = true := h
      simp only [lowMeanIntegerExprErase]
      rw [ihx sx h']
    | _ => exact absurd h Bool.false_ne_true
  | mul z x y ihx ihy =>
    intro s h
    cases s with
    | mul sx sy =>
      have h' : (eraseMatch x sx && eraseMatch y sy) = true := h
      simp only [Bool.and_eq_true] at h'
      simp only [lowMeanIntegerExprErase]
      rw [ihx sx h'.1, ihy sy h'.2]
    | _ => exact absurd h Bool.false_ne_true
  | div z x y ihx ihy =>
    intro s h
    cases s with
    | div sx sy =>
      have h' : (eraseMatch x sx && eraseMatch y sy) = true := h
      simp only [Bool.and_eq_true] at h'
      simp only [lowMeanIntegerExprErase]
      rw [ihx sx h'.1, ihy sy h'.2]
    | _ => exact absurd h Bool.false_ne_true
  | pow z x n ihx =>
    intro s h
    cases s with
    | pow sx m =>
      have h' : (Nat.beq n m && eraseMatch x sx) = true := h
      simp only [Bool.and_eq_true] at h'
      simp only [lowMeanIntegerExprErase]
      rw [ihx sx h'.2, Nat.eq_of_beq_eq_true h'.1]
    | _ => exact absurd h Bool.false_ne_true
  | abs z x ihx =>
    intro s h
    cases s with
    | abs sx =>
      have h' : eraseMatch x sx = true := h
      simp only [lowMeanIntegerExprErase]
      rw [ihx sx h']
    | _ => exact absurd h Bool.false_ne_true
  | minimum z x y ihx ihy =>
    intro s h
    cases s with
    | minimum sx sy =>
      have h' : (eraseMatch x sx && eraseMatch y sy) = true := h
      simp only [Bool.and_eq_true] at h'
      simp only [lowMeanIntegerExprErase]
      rw [ihx sx h'.1, ihy sy h'.2]
    | _ => exact absurd h Bool.false_ne_true
  | maximum z x y ihx ihy =>
    intro s h
    cases s with
    | maximum sx sy =>
      have h' : (eraseMatch x sx && eraseMatch y sy) = true := h
      simp only [Bool.and_eq_true] at h'
      simp only [lowMeanIntegerExprErase]
      rw [ihx sx h'.1, ihy sy h'.2]
    | _ => exact absurd h Bool.false_ne_true
  | selectLE z x y a b ihx ihy iha ihb =>
    intro s h
    cases s with
    | selectLE sx sy sa sb =>
      have h' : (eraseMatch x sx && eraseMatch y sy && eraseMatch a sa && eraseMatch b sb) = true := h
      simp only [Bool.and_eq_true] at h'
      simp only [lowMeanIntegerExprErase]
      rw [ihx sx h'.1.1.1, ihy sy h'.1.1.2, iha sa h'.1.2, ihb sb h'.2]
    | _ => exact absurd h Bool.false_ne_true
  | selectLT z x y a b ihx ihy iha ihb =>
    intro s h
    cases s with
    | selectLT sx sy sa sb =>
      have h' : (eraseMatch x sx && eraseMatch y sy && eraseMatch a sa && eraseMatch b sb) = true := h
      simp only [Bool.and_eq_true] at h'
      simp only [lowMeanIntegerExprErase]
      rw [ihx sx h'.1.1.1, ihy sy h'.1.1.2, iha sa h'.1.2, ihb sb h'.2]
    | _ => exact absurd h Bool.false_ne_true

/-! ### Witness arithmetic on the recursor, with direct `Int`/`Nat` steps -/

/-- Witness value of the root, on the recursor. -/
noncomputable def valR : LowMeanIntegerExpr → lowMeanFraction :=
  @LowMeanIntegerExpr.rec (fun _ => lowMeanFraction)
    (fun x => x) (fun z _ _ _ _ => z) (fun z _ _ => z) (fun z _ _ _ _ => z) (fun z _ _ _ _ => z)
    (fun z _ _ _ => z) (fun z _ _ => z) (fun z _ _ _ _ => z) (fun z _ _ _ _ => z)
    (fun z _ _ _ _ _ _ _ _ => z) (fun z _ _ _ _ _ _ _ _ => z)

theorem valR_eq (e : LowMeanIntegerExpr) : valR e = lowMeanIntegerExprValue e := by
  cases e <;> rfl

/-- Integer power through the kernel's native `Nat.pow` (the library power costs one `Int.mul` per unit
of the exponent). -/
def intPow (a : ℤ) (n : ℕ) : ℤ :=
  match a with
  | .ofNat m => .ofNat (Nat.pow m n)
  | .negSucc m =>
      if Nat.mod n 2 = 0 then .ofNat (Nat.pow (Nat.succ m) n) else Int.negOfNat (Nat.pow (Nat.succ m) n)

theorem intPow_eq (a : ℤ) (n : ℕ) : intPow a n = a ^ n := by
  cases a with
  | ofNat m =>
    show ((m ^ n : ℕ) : ℤ) = (m : ℤ) ^ n
    exact Nat.cast_pow m n
  | negSucc m =>
    show (if n % 2 = 0 then (((m + 1) ^ n : ℕ) : ℤ) else Int.negOfNat ((m + 1) ^ n)) = (Int.negSucc m) ^ n
    have hneg : Int.negSucc m = -(((m + 1 : ℕ)) : ℤ) := rfl
    rw [hneg]
    by_cases h0 : n % 2 = 0
    · rw [ite_eq_left h0, (Nat.even_iff.mpr h0).neg_pow]
      exact Nat.cast_pow (m + 1) n
    · rw [ite_eq_right h0, (Nat.odd_iff.mpr (by omega)).neg_pow, ← Nat.cast_pow]
      rfl

/-- `z` is a valid fraction equal to `n / d`: one validity test and one cross multiplication. -/
def nodeEq (z : lowMeanFraction) (n : ℤ) (d : ℕ) : Bool :=
  Nat.blt 0 z.2 && intBeq (Int.mul z.1 (Int.ofNat d)) (Int.mul n (Int.ofNat z.2))

theorem nodeEq_sound {z : lowMeanFraction} {n : ℤ} {d : ℕ} (h : nodeEq z n d = true) :
    lowMeanFractionValid z ∧ lowMeanFractionEq z (n, d) := by
  simp only [nodeEq, Bool.and_eq_true] at h
  exact ⟨Nat.le_of_ble_eq_true h.1, intBeq_eq h.2⟩

def fracEqB (x y : lowMeanFraction) : Bool :=
  intBeq (Int.mul x.1 (Int.ofNat y.2)) (Int.mul y.1 (Int.ofNat x.2))

theorem fracEqB_sound {x y : lowMeanFraction} (h : fracEqB x y = true) : lowMeanFractionEq x y :=
  intBeq_eq h

def stepAdd (z vx vy : lowMeanFraction) : Bool :=
  nodeEq z (Int.add (Int.mul vx.1 (Int.ofNat vy.2)) (Int.mul vy.1 (Int.ofNat vx.2))) (Nat.mul vx.2 vy.2)
def stepNeg (z vx : lowMeanFraction) : Bool := nodeEq z (Int.neg vx.1) vx.2
def stepMul (z vx vy : lowMeanFraction) : Bool := nodeEq z (Int.mul vx.1 vy.1) (Nat.mul vx.2 vy.2)
def stepDiv (z vx vy : lowMeanFraction) : Bool :=
  Nat.blt 0 z.2 && decide (vy.1 ≠ 0) &&
    intBeq (Int.mul (Int.mul z.1 vy.1) (Int.ofNat vx.2)) (Int.mul vx.1 (Int.ofNat (Nat.mul z.2 vy.2)))
def stepPow (z vx : lowMeanFraction) (n : ℕ) : Bool := nodeEq z (intPow vx.1 n) (Nat.pow vx.2 n)
def stepAbs (z vx : lowMeanFraction) : Bool :=
  decide (lowMeanFractionValid z ∧ lowMeanFractionEq z (lowMeanFractionAbs vx))
def stepMin (z vx vy : lowMeanFraction) : Bool :=
  nodeEq z (if lowMeanFractionLE vx vy then vx else vy).1 (if lowMeanFractionLE vx vy then vx else vy).2
def stepMax (z vx vy : lowMeanFraction) : Bool :=
  nodeEq z (if lowMeanFractionLE vx vy then vy else vx).1 (if lowMeanFractionLE vx vy then vy else vx).2

theorem stepAdd_sound {z vx vy : lowMeanFraction} (h : stepAdd z vx vy = true) :
    lowMeanFractionValid z ∧ lowMeanFractionEq z (lowMeanFractionAdd vx vy) := nodeEq_sound h
theorem stepNeg_sound {z vx : lowMeanFraction} (h : stepNeg z vx = true) :
    lowMeanFractionValid z ∧ lowMeanFractionEq z (lowMeanFractionNeg vx) := nodeEq_sound h
theorem stepMul_sound {z vx vy : lowMeanFraction} (h : stepMul z vx vy = true) :
    lowMeanFractionValid z ∧ lowMeanFractionEq z (lowMeanFractionMul vx vy) := nodeEq_sound h
theorem stepDiv_sound {z vx vy : lowMeanFraction} (h : stepDiv z vx vy = true) :
    lowMeanFractionValid z ∧ vy.1 ≠ 0 ∧ lowMeanFractionEq (lowMeanFractionMul z vy) vx := by
  simp only [stepDiv, Bool.and_eq_true] at h
  exact ⟨Nat.le_of_ble_eq_true h.1.1, of_decide_eq_true h.1.2, intBeq_eq h.2⟩
theorem stepPow_sound {z vx : lowMeanFraction} {n : ℕ} (h : stepPow z vx n = true) :
    lowMeanFractionValid z ∧ lowMeanFractionEq z (lowMeanFractionPow vx n) := by
  have h' : lowMeanFractionValid z ∧ lowMeanFractionEq z (intPow vx.1 n, Nat.pow vx.2 n) := nodeEq_sound h
  rw [intPow_eq] at h'
  exact h'
theorem stepMin_sound {z vx vy : lowMeanFraction} (h : stepMin z vx vy = true) :
    lowMeanFractionValid z ∧ lowMeanFractionEq z (if lowMeanFractionLE vx vy then vx else vy) :=
  nodeEq_sound h
theorem stepMax_sound {z vx vy : lowMeanFraction} (h : stepMax z vx vy = true) :
    lowMeanFractionValid z ∧ lowMeanFractionEq z (if lowMeanFractionLE vx vy then vy else vx) :=
  nodeEq_sound h

/-- The witness arithmetic of `lowMeanIntegerExprCheck`, on the recursor. -/
noncomputable def fastExprCheck : LowMeanIntegerExpr → Bool :=
  @LowMeanIntegerExpr.rec (fun _ => Bool)
    (fun x => Nat.blt 0 x.2)
    (fun z x y ihx ihy => ihx && ihy && stepAdd z (valR x) (valR y))
    (fun z x ihx => ihx && stepNeg z (valR x))
    (fun z x y ihx ihy => ihx && ihy && stepMul z (valR x) (valR y))
    (fun z x y ihx ihy => ihx && ihy && stepDiv z (valR x) (valR y))
    (fun z x n ihx => ihx && stepPow z (valR x) n)
    (fun z x ihx => ihx && stepAbs z (valR x))
    (fun z x y ihx ihy => ihx && ihy && stepMin z (valR x) (valR y))
    (fun z x y ihx ihy => ihx && ihy && stepMax z (valR x) (valR y))
    (fun z x y yes no ihx ihy ihyes ihno => ihx && ihy && Nat.blt 0 z.2 &&
      (if lowMeanFractionLE (valR x) (valR y) then ihyes && fracEqB z (valR yes)
        else ihno && fracEqB z (valR no)))
    (fun z x y yes no ihx ihy ihyes ihno => ihx && ihy && Nat.blt 0 z.2 &&
      (if lowMeanFractionLT (valR x) (valR y) then ihyes && fracEqB z (valR yes)
        else ihno && fracEqB z (valR no)))

theorem fastExprCheck_sound (e : LowMeanIntegerExpr) (h : fastExprCheck e = true) :
    lowMeanIntegerExprCheck e = true := by
  induction e with
  | atom x =>
    have h' : Nat.blt 0 x.2 = true := h
    simp only [lowMeanIntegerExprCheck]
    exact decide_eq_true (Nat.le_of_ble_eq_true h')
  | add z x y ihx ihy =>
    have h' : (fastExprCheck x && fastExprCheck y && stepAdd z (valR x) (valR y)) = true := h
    simp only [Bool.and_eq_true, valR_eq] at h'
    simp only [lowMeanIntegerExprCheck, Bool.and_eq_true]
    exact ⟨⟨ihx h'.1.1, ihy h'.1.2⟩, decide_eq_true (stepAdd_sound h'.2)⟩
  | neg z x ihx =>
    have h' : (fastExprCheck x && stepNeg z (valR x)) = true := h
    simp only [Bool.and_eq_true, valR_eq] at h'
    simp only [lowMeanIntegerExprCheck, Bool.and_eq_true]
    exact ⟨ihx h'.1, decide_eq_true (stepNeg_sound h'.2)⟩
  | mul z x y ihx ihy =>
    have h' : (fastExprCheck x && fastExprCheck y && stepMul z (valR x) (valR y)) = true := h
    simp only [Bool.and_eq_true, valR_eq] at h'
    simp only [lowMeanIntegerExprCheck, Bool.and_eq_true]
    exact ⟨⟨ihx h'.1.1, ihy h'.1.2⟩, decide_eq_true (stepMul_sound h'.2)⟩
  | div z x y ihx ihy =>
    have h' : (fastExprCheck x && fastExprCheck y && stepDiv z (valR x) (valR y)) = true := h
    simp only [Bool.and_eq_true, valR_eq] at h'
    simp only [lowMeanIntegerExprCheck, Bool.and_eq_true]
    exact ⟨⟨ihx h'.1.1, ihy h'.1.2⟩, decide_eq_true (stepDiv_sound h'.2)⟩
  | pow z x n ihx =>
    have h' : (fastExprCheck x && stepPow z (valR x) n) = true := h
    simp only [Bool.and_eq_true, valR_eq] at h'
    simp only [lowMeanIntegerExprCheck, Bool.and_eq_true]
    exact ⟨ihx h'.1, decide_eq_true (stepPow_sound h'.2)⟩
  | abs z x ihx =>
    have h' : (fastExprCheck x && stepAbs z (valR x)) = true := h
    simp only [Bool.and_eq_true, valR_eq] at h'
    simp only [lowMeanIntegerExprCheck, Bool.and_eq_true]
    exact ⟨ihx h'.1, h'.2⟩
  | minimum z x y ihx ihy =>
    have h' : (fastExprCheck x && fastExprCheck y && stepMin z (valR x) (valR y)) = true := h
    simp only [Bool.and_eq_true, valR_eq] at h'
    simp only [lowMeanIntegerExprCheck, Bool.and_eq_true]
    exact ⟨⟨ihx h'.1.1, ihy h'.1.2⟩, decide_eq_true (stepMin_sound h'.2)⟩
  | maximum z x y ihx ihy =>
    have h' : (fastExprCheck x && fastExprCheck y && stepMax z (valR x) (valR y)) = true := h
    simp only [Bool.and_eq_true, valR_eq] at h'
    simp only [lowMeanIntegerExprCheck, Bool.and_eq_true]
    exact ⟨⟨ihx h'.1.1, ihy h'.1.2⟩, decide_eq_true (stepMax_sound h'.2)⟩
  | selectLE z x y yes no ihx ihy ihyes ihno =>
    have h' : (fastExprCheck x && fastExprCheck y && Nat.blt 0 z.2 &&
        (if lowMeanFractionLE (valR x) (valR y) then fastExprCheck yes && fracEqB z (valR yes)
          else fastExprCheck no && fracEqB z (valR no))) = true := h
    simp only [Bool.and_eq_true, valR_eq] at h'
    simp only [lowMeanIntegerExprCheck, Bool.and_eq_true]
    refine ⟨⟨⟨ihx h'.1.1.1, ihy h'.1.1.2⟩, decide_eq_true (Nat.le_of_ble_eq_true h'.1.2)⟩, ?_⟩
    have h2 := h'.2
    by_cases hc : lowMeanFractionLE (lowMeanIntegerExprValue x) (lowMeanIntegerExprValue y)
    · rw [ite_eq_left hc] at h2 ⊢
      simp only [Bool.and_eq_true] at h2 ⊢
      exact ⟨ihyes h2.1, decide_eq_true (fracEqB_sound h2.2)⟩
    · rw [ite_eq_right hc] at h2 ⊢
      simp only [Bool.and_eq_true] at h2 ⊢
      exact ⟨ihno h2.1, decide_eq_true (fracEqB_sound h2.2)⟩
  | selectLT z x y yes no ihx ihy ihyes ihno =>
    have h' : (fastExprCheck x && fastExprCheck y && Nat.blt 0 z.2 &&
        (if lowMeanFractionLT (valR x) (valR y) then fastExprCheck yes && fracEqB z (valR yes)
          else fastExprCheck no && fracEqB z (valR no))) = true := h
    simp only [Bool.and_eq_true, valR_eq] at h'
    simp only [lowMeanIntegerExprCheck, Bool.and_eq_true]
    refine ⟨⟨⟨ihx h'.1.1.1, ihy h'.1.1.2⟩, decide_eq_true (Nat.le_of_ble_eq_true h'.1.2)⟩, ?_⟩
    have h2 := h'.2
    by_cases hc : lowMeanFractionLT (lowMeanIntegerExprValue x) (lowMeanIntegerExprValue y)
    · rw [ite_eq_left hc] at h2 ⊢
      simp only [Bool.and_eq_true] at h2 ⊢
      exact ⟨ihyes h2.1, decide_eq_true (fracEqB_sound h2.2)⟩
    · rw [ite_eq_right hc] at h2 ⊢
      simp only [Bool.and_eq_true] at h2 ⊢
      exact ⟨ihno h2.1, decide_eq_true (fracEqB_sound h2.2)⟩

noncomputable def fastShapeCheck (e : LowMeanIntegerExpr) (s : LowMeanIntegerShape) : Bool :=
  fastExprCheck e && eraseMatch e s

theorem fastShapeCheck_sound {e : LowMeanIntegerExpr} {s : LowMeanIntegerShape}
    (h : fastShapeCheck e s = true) : lowMeanIntegerShapeCheck e s = true := by
  simp only [fastShapeCheck, Bool.and_eq_true] at h
  simp only [lowMeanIntegerShapeCheck, Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨fastExprCheck_sound e h.1, eraseMatch_sound e s h.2⟩

noncomputable def fastPositiveCheck (e : LowMeanIntegerExpr) (s : LowMeanIntegerShape) (bound : lowMeanFraction) : Bool :=
  fastShapeCheck e s && decide (lowMeanFractionValid bound ∧ lowMeanFractionLT bound (lowMeanIntegerExprValue e))
noncomputable def fastLowerCheck (e : LowMeanIntegerExpr) (s : LowMeanIntegerShape) (bound : lowMeanFraction) : Bool :=
  fastShapeCheck e s && decide (lowMeanFractionValid bound ∧ lowMeanFractionLE bound (lowMeanIntegerExprValue e))
noncomputable def fastEqualityCheck (e : LowMeanIntegerExpr) (s : LowMeanIntegerShape) (value : lowMeanFraction) : Bool :=
  fastShapeCheck e s && decide (lowMeanIntegerExprValue e = value)

theorem fastPositiveCheck_sound {e : LowMeanIntegerExpr} {s : LowMeanIntegerShape} {bound : lowMeanFraction}
    (h : fastPositiveCheck e s bound = true) : lowMeanIntegerPositiveCheck e s bound = true := by
  simp only [fastPositiveCheck, Bool.and_eq_true] at h
  simp only [lowMeanIntegerPositiveCheck, Bool.and_eq_true]
  exact ⟨fastShapeCheck_sound h.1, h.2⟩
theorem fastLowerCheck_sound {e : LowMeanIntegerExpr} {s : LowMeanIntegerShape} {bound : lowMeanFraction}
    (h : fastLowerCheck e s bound = true) : lowMeanIntegerLowerCheck e s bound = true := by
  simp only [fastLowerCheck, Bool.and_eq_true] at h
  simp only [lowMeanIntegerLowerCheck, Bool.and_eq_true]
  exact ⟨fastShapeCheck_sound h.1, h.2⟩
theorem fastEqualityCheck_sound {e : LowMeanIntegerExpr} {s : LowMeanIntegerShape} {value : lowMeanFraction}
    (h : fastEqualityCheck e s value = true) : lowMeanIntegerEqualityCheck e s value = true := by
  simp only [fastEqualityCheck, Bool.and_eq_true] at h
  simp only [lowMeanIntegerEqualityCheck, Bool.and_eq_true]
  exact ⟨fastShapeCheck_sound h.1, h.2⟩

noncomputable def fastGeometryCheck (f : LowMeanFiberInput) : Bool :=
  let c := lowMeanFiberCertificate f
  fastEqualityCheck f.gLExpr (lowMeanShapeClosedMaximum f.M (.atom c.l)) f.gL &&
  fastEqualityCheck f.gRExpr (lowMeanShapeClosedMaximum f.M (lowMeanShapeSub (lowMeanShapeInt 1) (.atom c.h))) f.gR &&
  fastLowerCheck f.leftSide (lowMeanShapeCoreLeftSide c f.M f.lo) (0, 1) &&
  fastLowerCheck f.rightSide (lowMeanShapeCoreRightSide c f.M f.hi) (0, 1) &&
  fastLowerCheck f.leftTail (lowMeanShapeCoreLeftTail c f.M f.lo f.zeta) (0, 1) &&
  fastLowerCheck f.rightTail (lowMeanShapeCoreRightTail c f.M f.hi f.zeta) (0, 1)

theorem fastGeometryCheck_sound (f : LowMeanFiberInput) (h : fastGeometryCheck f = true) :
    lowMeanFiberGeometryCheck f = true := by
  simp only [fastGeometryCheck, Bool.and_eq_true] at h
  simp only [lowMeanFiberGeometryCheck, Bool.and_eq_true]
  exact ⟨⟨⟨⟨⟨fastEqualityCheck_sound h.1.1.1.1.1, fastEqualityCheck_sound h.1.1.1.1.2⟩,
    fastLowerCheck_sound h.1.1.1.2⟩, fastLowerCheck_sound h.1.1.2⟩, fastLowerCheck_sound h.1.2⟩,
    fastLowerCheck_sound h.2⟩

noncomputable def fastRankCheck (f : LowMeanFiberInput) (w : LowMeanCoreRankWitness) : Bool :=
  let c := lowMeanFiberCertificate f
  decide (w.state ≤ 2) &&
  if w.state = 0 then fastLowerCheck w.first (.neg (lowMeanShapeCoreFirst c f.M w.j f.zeta f.gL f.gR)) (0, 1)
  else if w.state = 1 then fastLowerCheck w.second (.neg (lowMeanShapeCoreSecond c f.M w.j f.zeta)) (0, 1)
  else fastPositiveCheck w.first (lowMeanShapeCoreFirst c f.M w.j f.zeta f.gL f.gR) (0, 1) &&
    fastPositiveCheck w.second (lowMeanShapeCoreSecond c f.M w.j f.zeta) (0, 1)

theorem fastRankCheck_sound (f : LowMeanFiberInput) (w : LowMeanCoreRankWitness)
    (h : fastRankCheck f w = true) : lowMeanCoreRankCheck f w = true := by
  simp only [fastRankCheck, Bool.and_eq_true] at h
  simp only [lowMeanCoreRankCheck, Bool.and_eq_true]
  refine ⟨h.1, ?_⟩
  have h2 := h.2
  by_cases h0 : w.state = 0
  · simp only [h0, ite_true] at h2 ⊢
    exact fastLowerCheck_sound h2
  · by_cases h1 : w.state = 1
    · simp only [h1, ite_true, ite_false, show ¬ (1 : ℕ) = 0 by decide] at h2 ⊢
      exact fastLowerCheck_sound h2
    · simp only [h0, h1, ite_false, Bool.and_eq_true] at h2 ⊢
      exact ⟨fastPositiveCheck_sound h2.1, fastPositiveCheck_sound h2.2⟩

/-- The rank window walked directly: one pass over the rank list with a running integer rank.
The original walks `List.range` and looks every rank up by index, which costs the kernels
far more than linear time on the long windows. -/
noncomputable def fastWindowGo (f : LowMeanFiberInput) : List LowMeanCoreRankWitness → ℤ → Bool
  | [], _ => true
  | w :: ws, j =>
      (decide (w.j = j ∧ (w.state = 2 ↔ w.j ∈ f.core)) && fastRankCheck f w) && fastWindowGo f ws (j + 1)

theorem fastWindowGo_sound (f : LowMeanFiberInput) (d : LowMeanCoreRankWitness) :
    ∀ (ws : List LowMeanCoreRankWitness) (j : ℤ), fastWindowGo f ws j = true →
      ∀ k, k < ws.length →
        ((ws.getD k d).j = j + (k : ℤ) ∧ ((ws.getD k d).state = 2 ↔ (ws.getD k d).j ∈ f.core)) ∧
          lowMeanCoreRankCheck f (ws.getD k d) = true := by
  intro ws
  induction ws with
  | nil =>
    intro j _ k hk
    exact absurd hk (Nat.not_lt_zero k)
  | cons w ws ih =>
    intro j h k hk
    simp only [fastWindowGo, Bool.and_eq_true, decide_eq_true_eq] at h
    cases k with
    | zero =>
      simp only [List.getD_cons_zero, Nat.cast_zero, add_zero]
      exact ⟨h.1.1, fastRankCheck_sound f w h.1.2⟩
    | succ k =>
      have hk' : k < ws.length := Nat.lt_of_succ_lt_succ hk
      have hrec := ih (j + 1) h.2 k hk'
      simp only [List.getD_cons_succ]
      have hc : j + ((k + 1 : ℕ) : ℤ) = j + 1 + (k : ℤ) := by omega
      rw [hc]
      exact hrec

noncomputable def fastWindowCheck (f : LowMeanFiberInput) : Bool := fastWindowGo f f.ranks f.lo

theorem fastWindowCheck_sound (f : LowMeanFiberInput) (h : fastWindowCheck f = true) :
    lowMeanFiberWindowCheck f = true := by
  unfold lowMeanFiberWindowCheck
  rw [List.all_eq_true]
  intro k hk
  have hk' : k < f.ranks.length := List.mem_range.mp hk
  simp only [lowMeanCoreRankAt, Bool.and_eq_true]
  have hs := fastWindowGo_sound f
    { j := 0, state := 0, first := .atom (0, 1), second := .atom (0, 1) } f.ranks f.lo h k hk'
  exact ⟨decide_eq_true hs.1, hs.2⟩

noncomputable def fastFiberCheck (f : LowMeanFiberInput) : Bool :=
  lowMeanFiberMetaCheck f && fastGeometryCheck f && fastWindowCheck f

theorem fastFiberCheck_sound (f : LowMeanFiberInput) (h : fastFiberCheck f = true) :
    lowMeanFiberCheck f = true := by
  simp only [fastFiberCheck, Bool.and_eq_true] at h
  simp only [lowMeanFiberCheck, Bool.and_eq_true]
  exact ⟨⟨h.1.1, fastGeometryCheck_sound f h.1.2⟩, fastWindowCheck_sound f h.2⟩

/-- A group that passes the fast check passes the original check. -/
theorem fastGroup_sound (g : List LowMeanFiberInput) (h : g.all fastFiberCheck = true) :
    g.all lowMeanFiberCheck = true := by
  rw [List.all_eq_true] at h ⊢
  exact fun f hf => fastFiberCheck_sound f (h f hf)

end Erdos993Lean.LowMeanFast

#print axioms Erdos993Lean.LowMeanFast.fastGroup_sound
