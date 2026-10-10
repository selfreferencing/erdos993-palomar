#!/usr/bin/env python3
"""Reflective linking: generate one whole family as a drop-in replacement of its Program module.

usage: gen_family.py FAMILY SRC_DIR OUT_ROOT SPLIT [--short3-suffix _P10]

  FAMILY    e.g. DAG_H_B_01
  SRC_DIR   directory holding the ORIGINAL generated family (Expressions.lean, Checks*.lean, Program.lean),
            i.e. <repo>/Erdos993Lean/F4U/Light/Linking/Generated/<FAMILY>
  OUT_ROOT  repository root to write into; files go to OUT_ROOT/Erdos993Lean/F4U/Light/Reflect/<FAMILY>/
  SPLIT     how the public roots are grouped into programs (one kernel evaluation each):
              key     one program per name stem (root name without its last index)   [12 programs for a B family, 4 for an A family]
              pair    one program per first two fields of the stem (1_0, 1_1, 2_0, 2_1)      [4 programs]
              mv      like pair, but the M roots and the V roots apart (1_0_M, 1_0_V, ...)     [8 programs for a B family]
              single  one program per root
              one     one program for the family
              <n>     consecutive chunks of n roots inside each name stem

Files written (all new; nothing existing is touched):
  Data.lean       the stored pairs of the public roots: the lines of the original Checks modules, every integer unchanged in
                  value; an integer of magnitude >= 2^64 with at least 32 trailing zero bits is written as odd part times a
                  power of two, `(IntegerSpelling.zp m k)` = m * 2^k or `(IntegerSpelling.zn m k)` = -(m * 2^k)
  P_<stem>.lean   one program each: data, ONE `decide +kernel`, TWO `kernel_rfl` facts (divisors, root values), the root theorems
  Roots.lean      the public names in the namespace F4U.Light.Reflect.<FAMILY>
  Program.lean    the same names in the namespace F4U.Light.Short3.<FAMILY><suffix> (drop-in for the Short3 Program)
  Interface.lean  compiled `example : @new = @old := rfl` against the ORIGINAL Program (imports the original chain; not for production)

The generator replays the Lean checker's arithmetic exactly (rational scalar outside, numerator by ring operations only,
exponent lists over a table of atom polynomials found by trial division) and emits the hints the checker verifies.
Nothing emitted is trusted: a wrong hint makes the Boolean check false.

Integer spelling.  Lean hashes a Nat literal by its low 64 bits, and `leanexport` keeps a hash table of the expressions it
has written; thousands of distinct literals that are multiples of 2^64 would all fall into one bucket and make the export
quadratic.  So every stored integer (pairs, atoms, base, instruction hints, root hints) of magnitude >= 2^64 with at least
32 trailing zero bits is emitted through `Reflect/IntegerSpelling.lean` (hand-written; `zp m k`, `zn m k`, m odd), never as
a shift.  With this rule no two literals of the generated files share their low 64 bits.  The lists `consts` / `constsR`
(the rational constants of the expressions, matched by `norm_num` and by `kernel_rfl` against real literals) stay plain."""
import sys, os, re, glob, math, pickle
from fractions import Fraction
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from bipoly import *
from parse_family import parse

MOD = "Erdos993Lean.F4U.Light.Reflect"
NS = "F4U.Light.Reflect"
sys.setrecursionlimit(100000)

SPELL_MIN_BITS = 64      # respell only integers of magnitude >= 2^64 ...
SPELL_MIN_TZ = 32        # ... with at least this many trailing zero bits
def Z(n):
    """`(IntegerSpelling.zp m k)` / `(IntegerSpelling.zn m k)` (m odd, n = +-m * 2^k) if n falls under the rule, else None."""
    a = abs(n)
    if (a >> SPELL_MIN_BITS) == 0 or (a & ((1 << SPELL_MIN_TZ) - 1)) != 0: return None
    k = (a & -a).bit_length() - 1
    assert (a >> k) & 1 == 1 and (a >> k) << k == a
    return f"(IntegerSpelling.{'zp' if n > 0 else 'zn'} {a >> k} {k})"
def Iplain(n): return str(n) if n >= 0 else f"({n})"      # a plain literal, in parentheses if negative
def I(n): return Z(n) or Iplain(n)                         # an Int argument
def S(n): return Z(n) or str(n)                            # an Int inside a list or an anonymous constructor
def L(xs): return "[" + ", ".join(str(x) for x in xs) + "]"
def rowsLit(rows): return "[" + ", ".join("[" + ", ".join(S(c) for c in r) + "]" for r in rows) + "]"
PAIR_INT = re.compile(r'-?\d+')
def respell_pair_line(line):
    """`def nNNNNN_pair : RationalPair := <...>`: the same line with the integers that fall under the rule respelled."""
    head, body = line.split(' := ', 1)
    assert '(' not in body and ')' not in body
    return head + ' := ' + PAIR_INT.sub(lambda m: Z(int(m.group(0))) or m.group(0), body)
def mass(p): return sum(abs(v) for v in p.cells().values())
def rowlens(p):
    c = p.cells()
    if not c: return []
    dt = max(j for (_, j) in c)
    return [max([i for (i, jj) in c if jj == j], default=-1) + 1 for j in range(dt + 1)]
def addE(p, q):
    n = max(len(p), len(q)); return [(p[k] if k < len(p) else 0) + (q[k] if k < len(q) else 0) for k in range(n)]
def split_min(e1, e2):
    Lm = min(len(e1), len(e2)); m = [min(e1[k], e2[k]) for k in range(Lm)]
    u1 = [e1[k] - (m[k] if k < Lm else 0) for k in range(len(e1))]
    u2 = [e2[k] - (m[k] if k < Lm else 0) for k in range(len(e2))]
    assert addE(m, u1) == e1 and addE(m, u2) == e2
    return m, u1, u2
def divides(p, a):
    q, r = divmod(p.f, a.f)
    if r != 0: return None
    cq = [e for e, v in enumerate(q.coeffs()) if v != 0]; ca = [e for e, v in enumerate(a.f.coeffs()) if v != 0]
    cp = [e for e, v in enumerate(p.f.coeffs()) if v != 0]
    if max(e % K for e in cq) + max(e % K for e in ca) != max(e % K for e in cp): return None
    return P(q)

class V:
    __slots__ = ('c', 'N', 'e', 'nb')
    def __init__(s, c, N, e, nb): s.c, s.N, s.e, s.nb = c, N, e, nb

def make_program(d, family, names, tag):
    """One program for the roots `names`; returns (lean text, statistics)."""
    nodes, pairs, roots, divisors = d['nodes'], d['pairs'], dict(d['roots']), d['divisors']
    root_nodes = [roots[n] for n in names]
    need = set()
    def cone(i):
        if i in need: return
        need.add(i); n = nodes[i]
        if n[0] in ('add', 'sub', 'mul', 'div'): cone(n[1]); cone(n[2])
        elif n[0] == 'pow': cone(n[1])
    for r in root_nodes: cone(r)
    order = sorted(need); pos = {i: k for k, i in enumerate(order)}
    atoms = []; amass = []
    def factor_over_atoms(M):
        c0 = M.content_signed(); R = M.divexact_int(c0); f = [0] * len(atoms)
        for k, a in enumerate(atoms):
            while True:
                q = divides(R, a)
                if q is None: break
                R = q; f[k] += 1
        if not R.is_const():
            atoms.append(R); amass.append(mass(R)); f.append(1)
        else:
            c0 *= int(R.f[0])
        return c0, f
    def atomMass(u):
        r = 1
        for k, x in enumerate(u): r *= amass[k] ** x
        return r
    st = dict(rowpairs=0)
    def account(p, q): st['rowpairs'] += len(rowlens(p)) * len(rowlens(q))
    def mulAtoms(N, u):
        for k, x in enumerate(u):
            for _ in range(x):
                account(N, atoms[k]); N = N * atoms[k]
        return N
    vals = {}; instrs = []; consts = []; constsR = []; bounds = []; divnodes = []
    for j, i in enumerate(order):
        n = nodes[i]; rel = lambda a: j - 1 - pos[a]
        if n[0] == 'x': v = V(Fraction(1), X, [], 1); ins = ".x"
        elif n[0] == 't': v = V(Fraction(1), T, [], 1); ins = ".t"
        elif n[0] == 'const':
            a, b = n[1], n[2]; assert b > 0
            consts.append(f"({Iplain(a)}, {b})")
            constsR.append(f"({a} : ℝ)/({b} : ℝ)" if a >= 0 else f"(({a}) : ℝ)/({b} : ℝ)")
            v = V(Fraction(a, b), ONE, [], 1); ins = f".const {len(consts) - 1}"
        elif n[0] in ('add', 'sub'):
            p, q = vals[n[1]], vals[n[2]]
            m, u1, u2 = split_min(p.e, q.e)
            c1, c2 = p.c, (q.c if n[0] == 'add' else -q.c)
            if c1 == 0 and c2 == 0: k1, k2, c = 0, 0, Fraction(0)
            else:
                den = c1.denominator * c2.denominator // math.gcd(c1.denominator, c2.denominator)
                a1, a2 = int(c1 * den), int(c2 * den); g = math.gcd(a1, a2)
                k1, k2, c = a1 // g, a2 // g, Fraction(g, den)
            assert c1 == c * k1 and c2 == c * k2
            N = mulAtoms(p.N, u2) * k1 + mulAtoms(q.N, u1) * k2
            v = V(c, N, addE(p.e, u2), abs(k1) * (p.nb * atomMass(u2)) + abs(k2) * (q.nb * atomMass(u1)))
            ins = f".{n[0]} {rel(n[1])} {rel(n[2])} {I(k1)} {I(k2)} {I(c.numerator)} {I(c.denominator)} {L(m)} {L(u1)} {L(u2)}"
        elif n[0] == 'mul':
            p, q = vals[n[1]], vals[n[2]]
            sw = sum(rowlens(p.N)) < sum(rowlens(q.N))          # second factor = the one with fewer slots
            if sw: account(q.N, p.N)
            else: account(p.N, q.N)
            c = p.c * q.c
            v = V(c, p.N * q.N, addE(p.e, q.e), p.nb * q.nb)
            ins = f".mul {rel(n[1])} {rel(n[2])} {'true' if sw else 'false'} {I(c.numerator)} {I(c.denominator)}"
        elif n[0] == 'div':
            p, q = vals[n[1]], vals[n[2]]
            assert q.c != 0
            c0, f = factor_over_atoms(q.N)
            g = addE(p.e, f)
            m, u2, w = split_min(q.e, g)
            c = p.c / (q.c * c0)
            bounds.append(q.nb + abs(c0) * atomMass(f))
            v = V(c, mulAtoms(p.N, u2), w, p.nb * atomMass(u2))
            ins = f".div {rel(n[1])} {rel(n[2])} {I(c.numerator)} {I(c.denominator)} {I(c0)} {L(f)} {L(m)} {L(u2)} {L(w)}"
            divnodes.append(n[2])
        elif n[0] == 'pow':
            p = vals[n[1]]; k = n[2]; N = ONE
            for _ in range(k): account(N, p.N); N = N * p.N
            c = p.c ** k
            v = V(c, N, [x * k for x in p.e], p.nb ** k)
            ins = f".pow {rel(n[1])} {k} {I(c.numerator)} {I(c.denominator)}"
        # self-test: the value equals the stored reduced pair of this node
        if v.c != 0:
            den = ONE
            for k_, x_ in enumerate(v.e):
                for _ in range(x_): den = den * atoms[k_]
            sn, sd = P.from_rows(pairs[i][0]), P.from_rows(pairs[i][1])
            assert v.N * sd * v.c.numerator == sn * den * v.c.denominator, f"node {i} differs from its stored pair"
        vals[i] = v; instrs.append(ins)
    def root_hint(i):
        v = vals[i]; Ns, Ds = P.from_rows(pairs[i][0]), P.from_rows(pairs[i][1])
        assert v.c != 0 and not v.N.is_zero()
        cs = Ns.content_signed(); prim = Ns.divexact_int(cs)
        Q = divides(v.N, prim); assert Q is not None, "stored numerator does not divide the computed numerator"
        Aexp = ONE
        for k, x in enumerate(v.e):
            for _ in range(x): Aexp = Aexp * atoms[k]
        R = Q * Ds
        cR, cA = R.cells(), Aexp.cells(); key = next(iter(cA))
        lam0 = Fraction(cR[key], cA[key])
        assert R * lam0.denominator == Aexp * lam0.numerator
        t = lam0.denominator
        G = Q * t; mu = cs * t; lam = lam0.numerator
        assert v.N * mu == G * Ns and Aexp * lam == G * Ds
        assert mu * v.c.denominator == v.c.numerator * lam, "scalar mismatch"
        bounds.append(abs(mu) * v.nb + mass(G) * mass(Ns))
        bounds.append(abs(lam) * atomMass(v.e) + mass(G) * mass(Ds))
        account(G, Ns); account(G, Ds)
        return G, lam, mu
    hints = [root_hint(i) for i in root_nodes]
    W = ((max(b.bit_length() for b in bounds) + 1 + 63) // 64) * 64
    B = 1 << W
    assert all(b < B for b in bounds)
    last = len(order) - 1
    ns = f"{NS}.{family}.{tag}"
    o = ["module",
         f"public import {MOD}.Core",
         f"public import {MOD}.KernelRfl",
         f"public import {MOD}.IntegerSpelling",
         f"public import {MOD}.{family}.Data",
         "@[expose] public section",
         "set_option maxRecDepth 1000000",
         "set_option linter.unusedVariables false",
         f"/-! Generated by gen_family.py. Family {family}, program {tag}: {len(names)} public roots, {len(order)} instructions,",
         f"{len(divnodes)} divisions, {len(atoms)} atoms, base 2^{W}. One kernel evaluation (`checked`). -/",
         f"namespace {ns}",
         f"open F4U.Light.Linking F4U.Light.Linking.Generated.{family}",
         "noncomputable section",
         f"def BB : Int := {S(B)}",
         "def atoms : List Polynomial2.Rows := [" + ", ".join(rowsLit(a.rows()) for a in atoms) + "]",
         "def consts : List (Int × Int) := [" + ", ".join(consts) + "]",
         "def constsR : List ℝ := [" + ", ".join(constsR) + "]",
         "def prog : List Instr := [\n  " + ",\n  ".join(instrs) + "]"]
    for (G, lam, mu), i, nm in zip(hints, root_nodes, names):
        o.append(f"def rs_{nm} : RootSpec := ⟨{last - pos[i]}, n{i:05d}_pair, {rowsLit(G.rows())}, {S(lam)}, {S(mu)}⟩")
    o.append("def rootSpecs : List RootSpec := [" + ", ".join(f"rs_{nm}" for nm in names) + "]")
    o.append("theorem checked : checkFamily BB atoms consts prog rootSpecs = true := by decide +kernel")
    o.append("theorem constsOK : ConstsOK consts constsR := constsOK_of_map (by norm_num [consts, constsR])")
    dl = ", ".join(f"n{k:05d}_expression x t" for k in divnodes)
    o.append(f"theorem divs (x t : ℝ) : divisorVals constsR x t prog [] = [{dl}] := by kernel_rfl")
    for k in sorted(set(divnodes)):
        o.append(f"theorem dne_{k:05d} (x t : ℝ) (hnz : DivisorsNonzero x t) : n{k:05d}_expression x t ≠ 0 := by\n  simpa only [divisorExpression] using hnz ⟨{divisors.index(k)}, by decide⟩")
    chain = "allNe_nil"
    for k in reversed(divnodes): chain = f"allNe_cons (dne_{k:05d} x t hnz) ({chain})"
    o.append("theorem divok (x t : ℝ) (hnz : DivisorsNonzero x t) : DivOK constsR x t prog [] := by\n  apply divOK_of_vals\n  rw [divs x t]\n  exact " + chain)
    o.append("theorem sems (x t : ℝ) : rootVals constsR x t prog [" + ", ".join(f"rs_{nm}.pos" for nm in names) + "] = ["
             + ", ".join(f"n{i:05d}_expression x t" for i in root_nodes) + "] := by kernel_rfl")
    for idx, (nm, i) in enumerate(zip(names, root_nodes)):
        mem = "List.mem_cons_self"
        for _ in range(idx): mem = f"List.mem_cons_of_mem _ ({mem})"
        pick = "sems x t"
        for _ in range(idx): pick = f"tl_eq ({pick})"
        o.append(f"theorem sem_{nm} (x t : ℝ) : (runR constsR x t prog []).getD rs_{nm}.pos 0 = n{i:05d}_expression x t := hd_eq ({pick})")
        o.append(f"theorem {nm}_sound (x t : ℝ) (hnz : DivisorsNonzero x t) : n{i:05d}_pair.NonzeroDenominator x t ∧ n{i:05d}_pair.value x t = n{i:05d}_expression x t := by\n  have h := checkFamily_sound checked constsOK x t (divok x t hnz) rs_{nm} ({mem})\n  rw [sem_{nm} x t] at h\n  exact h")
    o.append("end")
    o.append(f"end {ns}")
    mx = dict(dx=0, dt=0, cells=0, bits=0, nb=0)
    for i in order:
        s_ = vals[i].N.stats()
        mx['dx'] = max(mx['dx'], s_[0]); mx['dt'] = max(mx['dt'], s_[1]); mx['cells'] = max(mx['cells'], s_[2])
        mx['bits'] = max(mx['bits'], s_[3]); mx['nb'] = max(mx['nb'], vals[i].nb.bit_length())
    stats = dict(tag=tag, roots=len(names), instructions=len(order), divisions=len(divnodes), atoms=len(atoms), base_bits=W,
                 rowpairs=st['rowpairs'], **mx)
    return "\n".join(o) + "\n", stats

def groups_for(names, family, split):
    stem_of = lambda n: n[len(family_prefix(family)):].rsplit('_', 1)[0]
    stems = []
    for n in names:
        if stem_of(n) not in stems: stems.append(stem_of(n))
    by = {s: [n for n in names if stem_of(n) == s] for s in stems}
    if split == 'one': return [('P_all', list(names))]
    if split == 'single': return [('P_' + n[len(family_prefix(family)):], [n]) for n in names]
    if split == 'key': return [('P_' + s, by[s]) for s in stems]
    if split == 'pair':
        ps = []
        for st in stems:
            k2 = '_'.join(st.split('_')[:2])
            if k2 not in ps: ps.append(k2)
        return [('P_' + k2, [n for n in names if '_'.join(stem_of(n).split('_')[:2]) == k2]) for k2 in ps]
    if split == 'mv':
        ks = []
        key = lambda st: '_'.join(st.split('_')[:2]) + '_' + st.split('_')[2][0]
        for st in stems:
            if key(st) not in ks: ks.append(key(st))
        return [('P_' + k_, [n for n in names if key(stem_of(n)) == k_]) for k_ in ks]
    k = int(split); out = []
    for s in stems:
        ch = [by[s][i:i + k] for i in range(0, len(by[s]), k)]
        for c, part in enumerate(ch): out.append((f"P_{s}" if len(ch) == 1 else f"P_{s}_{chr(ord('a') + c)}", part))
    return out

def family_prefix(family):          # DAG_H_B_01 -> H_B_
    return family[len('DAG_'):-len('_01')] + '_'

def main():
    args = [a for a in sys.argv[1:] if not a.startswith('--')]
    family, src, out_root, split = args[:4]
    suffix = '_P10'
    if '--short3-suffix' in sys.argv: suffix = sys.argv[sys.argv.index('--short3-suffix') + 1]
    d = parse(src)
    names = [n for n, _ in d['roots']]; roots = dict(d['roots'])
    outdir = os.path.join(out_root, 'Erdos993Lean', 'F4U', 'Light', 'Reflect', family)
    os.makedirs(outdir, exist_ok=True)
    def write(name, text):
        assert text.startswith("module\n") and text.count("\n") < 10000
        open(os.path.join(outdir, name), 'w').write(text)
    # Data: the stored pairs of the public roots, copied verbatim
    want = {roots[n] for n in names}; lines = {}
    for f in sorted(glob.glob(os.path.join(src, 'Checks*.lean'))):
        for line in open(f):
            m = re.match(r'def n(\d+)_pair : RationalPair := ', line)
            if m and int(m.group(1)) in want: lines[int(m.group(1))] = line.rstrip("\n")
    assert set(lines) == want
    data = ["module", f"public import Erdos993Lean.F4U.Light.Linking.Generated.{family}.Expressions",
            f"public import {MOD}.IntegerSpelling", "@[expose] public section",
            f"/-! Generated by gen_family.py. The stored pairs of the {len(want)} public root nodes of {family}: the lines of the original",
            "`Checks` modules, every integer unchanged in value; an integer of magnitude >= 2^64 with at least 32 trailing zero bits",
            "is written `(IntegerSpelling.zp m k)` = m * 2^k or `(IntegerSpelling.zn m k)` = -(m * 2^k), m odd. -/",
            f"namespace {NS}.{family}", "open F4U.Light.Linking", "noncomputable section"]
    data += [respell_pair_line(lines[i]) for i in sorted(lines)] + ["end", f"end {NS}.{family}"]
    write('Data.lean', "\n".join(data) + "\n")
    groups = groups_for(names, family, split)
    where = {}; allstats = []
    for tag, part in groups:
        text, stats = make_program(d, family, part, tag)
        write(tag + '.lean', text); allstats.append(stats)
        for n in part: where[n] = tag
    # Roots: public names in our own namespace
    r = ["module"] + [f"public import {MOD}.{family}.{tag}" for tag, _ in groups] + ["@[expose] public section",
         f"/-! Generated by gen_family.py. The {len(names)} public roots of {family}, proved by reflective normalization. -/",
         f"namespace {NS}.{family}", f"open F4U.Light.Linking F4U.Light.Linking.Generated.{family}", "noncomputable section"]
    for n in names:
        i = roots[n]
        r += [f"abbrev {n}_pair := n{i:05d}_pair", f"abbrev {n}_expression := n{i:05d}_expression",
              f"theorem {n}_sound (x t : ℝ) (hnz : DivisorsNonzero x t) : n{i:05d}_pair.NonzeroDenominator x t ∧ n{i:05d}_pair.value x t = n{i:05d}_expression x t := {where[n]}.{n}_sound x t hnz",
              f"#print axioms {n}_sound"]
    r += ["end", f"end {NS}.{family}"]
    write('Roots.lean', "\n".join(r) + "\n")
    # Program: the same names where the Short3 Program put them (drop-in)
    s3 = f"F4U.Light.Short3.{family}{suffix}"
    p = ["module", f"public import {MOD}.{family}.Roots", "@[expose] public section",
         f"/-! Generated by gen_family.py. Drop-in for `Erdos993Lean.F4U.Light.Short3.{family}{suffix}.Program`: the same public names",
         f"in the same namespace `{s3}`. Never import this module together with that one. -/",
         f"namespace {s3}", f"open F4U.Light.Linking F4U.Light.Linking.Generated.{family}", "noncomputable section"]
    for n in names:
        i = roots[n]
        p += [f"abbrev n{i:05d}_pair := {NS}.{family}.n{i:05d}_pair"]
    for n in names:
        i = roots[n]
        p += [f"abbrev {n}_pair := n{i:05d}_pair", f"abbrev {n}_expression := n{i:05d}_expression",
              f"theorem {n}_sound (x t : ℝ) (hnz : DivisorsNonzero x t) : n{i:05d}_pair.NonzeroDenominator x t ∧ n{i:05d}_pair.value x t = n{i:05d}_expression x t := {NS}.{family}.{n}_sound x t hnz"]
    p += ["end", f"end {s3}"]
    write('Program.lean', "\n".join(p) + "\n")
    # Interface: compiled comparisons with the ORIGINAL Program (not for production)
    og = f"F4U.Light.Linking.Generated.{family}"
    it = ["module", f"public import {MOD}.{family}.Program", f"public import Erdos993Lean.F4U.Light.Linking.Generated.{family}.Program",
          "@[expose] public section",
          f"/-! Generated by gen_family.py. Every public root of {family}: the reflective theorem, under both names, has the statement of the",
          "original one; pairs and expressions are the original ones. This module imports the original proof chain: keep it out of production. -/",
          f"namespace {NS}.{family}.Interface"]
    for n in names:
        it += [f"example : @{NS}.{family}.{n}_sound = @{og}.{n}_sound := rfl",
               f"example : @{s3}.{n}_sound = @{og}.{n}_sound := rfl",
               f"example : {s3}.{n}_pair = {og}.{n}_pair := rfl",
               f"example : @{s3}.{n}_expression = @{og}.{n}_expression := rfl"]
    it += [f"end {NS}.{family}.Interface"]
    write('Interface.lean', "\n".join(it) + "\n")
    tot = dict(family=family, split=split, programs=len(groups), roots=len(names),
               instructions=sum(s['instructions'] for s in allstats), rowpairs=sum(s['rowpairs'] for s in allstats),
               max_base_bits=max(s['base_bits'] for s in allstats), max_nb=max(s['nb'] for s in allstats),
               max_cells=max(s['cells'] for s in allstats), max_atoms=max(s['atoms'] for s in allstats),
               bytes=sum(os.path.getsize(os.path.join(outdir, f)) for f in os.listdir(outdir)))
    sd = os.environ.get('GEN_STATS_DIR')
    if sd:
        import json
        os.makedirs(sd, exist_ok=True)
        json.dump(dict(total=tot, programs=allstats, groups=groups), open(os.path.join(sd, f'{family}.{split}.json'), 'w'), indent=1)
    print(tot)
    # module and root lists for the measurement queue
    print("MODULE", f"{MOD}.{family}.Program")
    print("ROOTS", " ".join(f"{s3}.{n}_sound" for n in names))

if __name__ == '__main__':
    main()
