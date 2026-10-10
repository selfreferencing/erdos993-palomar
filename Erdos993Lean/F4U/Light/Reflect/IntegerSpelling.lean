module
public import Mathlib.Data.Int.Basic

/-! Exact integer emission avoiding large literal hash collisions.

Lean hashes a natural-number literal by its low 64 bits, so distinct literals that are multiples of `2^64` all share one
hash. The generated Reflect data (`gen_family.py`) therefore write every stored integer of magnitude at least `2^64` with
at least 32 trailing zero bits as an odd part times a power of two: `zp m k = m * 2^k`, `zn m k = -(m * 2^k)`.
These are the two definitions of the former `Short3/IntegerSpelling.lean`, in this package's namespace. -/
@[expose] public section
namespace F4U.Light.Reflect.IntegerSpelling

def zp (m k : Nat) : Int := Int.ofNat (Nat.mul m (Nat.pow 2 k))
def zn (m k : Nat) : Int := Int.neg (Int.ofNat (Nat.mul m (Nat.pow 2 k)))

end F4U.Light.Reflect.IntegerSpelling
