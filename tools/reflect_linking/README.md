# Reflective linking for the light core: generator and scripts

The Lean files of this package live under `Erdos993Lean/F4U/Light/Reflect/`:

- `Core.lean`, `KernelRfl.lean`: hand-written. The checker, its soundness proof, and the tactic `kernel_rfl`.
- `IntegerSpelling.lean`: hand-written. `zp m k = m * 2^k`, `zn m k = -(m * 2^k)`. The generator writes every stored integer
  of magnitude at least 2^64 with at least 32 trailing zero bits through these (odd part times a power of two, never a
  shift), because Lean hashes a Nat literal by its low 64 bits and the exporter's table of written expressions goes
  quadratic on thousands of literals that are multiples of 2^64. `consts` / `constsR` stay plain literals.
- `<FAMILY>/Data.lean`, `P_*.lean`, `Roots.lean`, `Program.lean`, `Interface.lean`: generated, one set per family
  (`DAG_{D,E1,E2,H}_{A,B}_01`).

Scripts here:

- `gen_family.py` (with `bipoly.py`, `parse_family.py`): the generator; its usage is the docstring at its top. Needs `python-flint`.
  It checks itself while it runs: every node of every program is compared with the stored pair of the original family, and it stops on the first difference.
- `regenerate.sh <repository root> <output root>`: all eight families with the splits used for the package
  (four programs for the A families and for D_B and H_B, twelve for E1_B and E2_B; chosen by measurement).
- `check_untouched.sh <repository root> [ref ...]`: shows that unpacking the bundle overwrites no tracked or existing file.
- `consumer_test.sh <FAMILY>`: compiles every consumer of a family (`Linking/CheckedNumerators/<root>`,
  `Construction/ActualPositivity/<root>`) against the reflective `Program`, using copies under
  `Erdos993Lean/F4U/Light/Reflect/ConsumerTest/` so that no existing file is edited.

Switching a family over (what a consumer changes): in each `Erdos993Lean/F4U/Light/Linking/CheckedNumerators/<root>.lean`
of the family, the import line

    public import Erdos993Lean.F4U.Light.Short3.<FAMILY>_P10.Program

becomes

    public import Erdos993Lean.F4U.Light.Reflect.<FAMILY>.Program

and nothing else: `Reflect/<FAMILY>/Program.lean` declares `<root>_pair`, `<root>_expression` and `<root>_sound` in the
namespace `F4U.Light.Short3.<FAMILY>_P10`, so the existing `open F4U.Light.Short3.<FAMILY>_P10` lines keep working.
Because the names coincide, the two `Program` modules of one family must never be imported together.
(`Reflect/<FAMILY>/Roots.lean` has the same three names per root in the namespace `F4U.Light.Reflect.<FAMILY>` for anyone
who prefers a separate namespace; then the `open` lines change too.)

`Interface.lean` of each family holds the compiled comparisons with the ORIGINAL `Program`
(`example : @new = @old := rfl` for every root, under both names). It imports the original proof chain and is not part of
production.
