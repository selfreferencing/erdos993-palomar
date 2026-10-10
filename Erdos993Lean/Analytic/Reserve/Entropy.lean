module

public import Erdos993Lean.Analytic.Reserve.Defs
public import Erdos993Lean.Analytic.Reserve.EntropyPinsker

/-!
# The entropy facts of the two-generation reserve (`EntropyOK`)

O1 by the two-generation reserve.
Sources: the two-generation reserve proof, "Convexity transports
the positive reserve", (3) and (3a); the sharp first-four reserve proof (binary Pinsker).


Write `p = msg λ Y`, `y₀ = lmass λ Y` (the parent) and `s = msg λ T`, `y = lmass λ T` (the child).
The message algebra gives `log (1 − p) = −y₀` and `log p = log λ − Y − y₀` (`log_one_sub_msg`,
`log_msg`), hence the divergence of the two occupation laws is

  `KL(Ber p ‖ Ber s) = p (T − Y) + y − y₀`                                    (`kl_msg`)

and the exact entropy ledger (3a) holds:

  `E · y = KL(Ber p ‖ Ber s) + (Y − y)(p + y₀ / Y)`                      (`coefE_mul_lmass`).

With binary Pinsker (`Entropy.binary_pinsker`) this gives `entropyOK : EntropyOK`: for `λ > 0`,
`T ≥ 0` and `lmass λ T ≤ Y`, `E ≥ 0` and `E · y ≥ 2 (p − s)² + (Y − y)(p + y₀ / Y)`.

The message facts `msg_pos`, `msg_lt_one`, `one_sub_msg`, `lmass_pos` (namespace
`Erdos993Lean.Analytic.Reserve.Entropy`) are reused by the analytic tails.

Scalarity: `E` is attached to one actual parent–child message pair; by (3a) its object is the
divergence between the parent's and the child's occupation laws plus the sibling log-mass `Y − y`.
Producer: the messages `p, s` of the tree recursion; consumer: the `α` payment of the reserve step
(`E ≥ 0`) and the cell checker (both parts as floors for `E`).
-/

@[expose] public section

namespace Erdos993Lean.Analytic.Reserve

open Real

namespace Entropy

variable {lam : ℝ}

/-- `λ e^{−X} > 0`. -/
theorem lamExp_pos (hlam : 0 < lam) (X : ℝ) : 0 < lam * exp (-X) := mul_pos hlam (exp_pos _)

theorem msg_pos (hlam : 0 < lam) (X : ℝ) : 0 < msg lam X := by
  unfold msg; have := lamExp_pos hlam X; positivity

theorem msg_lt_one (hlam : 0 < lam) (X : ℝ) : msg lam X < 1 := by
  unfold msg; have := lamExp_pos hlam X; rw [div_lt_one (by linarith)]; linarith

/-- `1 − p = 1 / (1 + λ e^{−X})`. -/
theorem one_sub_msg (hlam : 0 < lam) (X : ℝ) : 1 - msg lam X = (1 + lam * exp (-X))⁻¹ := by
  unfold msg; have := lamExp_pos hlam X; field_simp; ring

theorem lmass_pos (hlam : 0 < lam) (X : ℝ) : 0 < lmass lam X := by
  unfold lmass; apply Real.log_pos; have := lamExp_pos hlam X; linarith

/-- `log (1 − p) = −y₀`. -/
theorem log_one_sub_msg (hlam : 0 < lam) (X : ℝ) : log (1 - msg lam X) = -lmass lam X := by
  rw [one_sub_msg hlam, Real.log_inv]; rfl

/-- `log p = log λ − X − y₀`. -/
theorem log_msg (hlam : 0 < lam) (X : ℝ) : log (msg lam X) = log lam - X - lmass lam X := by
  unfold msg lmass
  have h1 := lamExp_pos hlam X
  rw [Real.log_div h1.ne' (by linarith), Real.log_mul hlam.ne' (exp_pos _).ne', Real.log_exp]
  ring

/-- The divergence of the parent and child occupation laws:
`KL(Ber p ‖ Ber s) = p (T − Y) + y − y₀`. -/
theorem kl_msg (hlam : 0 < lam) (T Y : ℝ) :
    msg lam Y * (log (msg lam Y) - log (msg lam T)) +
        (1 - msg lam Y) * (log (1 - msg lam Y) - log (1 - msg lam T)) =
      msg lam Y * (T - Y) + lmass lam T - lmass lam Y := by
  rw [log_msg hlam, log_msg hlam, log_one_sub_msg hlam, log_one_sub_msg hlam]; ring

/-- **The entropy ledger (3a)**: `E · y = [p (T − Y) + y − y₀] + (Y − y)(p + y₀ / Y)`, the bracket
being `KL(Ber p ‖ Ber s)` (`kl_msg`). -/
theorem coefE_mul_lmass (hlam : 0 < lam) (T Y : ℝ) (hY : Y ≠ 0) :
    coefE lam T Y * lmass lam T = (msg lam Y * (T - Y) + lmass lam T - lmass lam Y) +
      (Y - lmass lam T) * (msg lam Y + lmass lam Y / Y) := by
  unfold coefE
  have hy := (lmass_pos hlam T).ne'
  field_simp
  ring

end Entropy

open Entropy in
/-- **The entropy facts** (identities (3) and (3a) with binary Pinsker): for `λ > 0`, `T ≥ 0` and
`lmass λ T ≤ Y`, `E ≥ 0` and `E · y ≥ 2 (p − s)² + (Y − y)(p + y₀ / Y)`. -/
theorem entropyOK : EntropyOK := by
  intro lam T Y hlam _ hY
  have hy := lmass_pos hlam T
  have hYpos : 0 < Y := lt_of_lt_of_le hy hY
  have hid := coefE_mul_lmass hlam T Y hYpos.ne'
  have hkl := kl_msg hlam T Y
  have hP := binary_pinsker (msg_pos hlam Y) (msg_lt_one hlam Y) (msg_pos hlam T)
    (msg_lt_one hlam T)
  have hrest : 0 ≤ (Y - lmass lam T) * (msg lam Y + lmass lam Y / Y) := by
    apply mul_nonneg (by linarith)
    have := msg_pos hlam Y; have := lmass_pos hlam Y; positivity
  have h2 : 2 * (msg lam Y - msg lam T) ^ 2 + (Y - lmass lam T) * (msg lam Y + lmass lam Y / Y) ≤
      coefE lam T Y * lmass lam T := by
    rw [hid]; linarith
  refine ⟨?_, h2⟩
  have h3 : 0 ≤ coefE lam T Y * lmass lam T := by
    nlinarith [sq_nonneg (msg lam Y - msg lam T)]
  exact (mul_nonneg_iff_of_pos_right hy).mp h3

end Erdos993Lean.Analytic.Reserve
