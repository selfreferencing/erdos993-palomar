"""Bivariate integer polynomials on top of flint.fmpz_poly via t = x^K (dense Kronecker in the exponent)."""
import math
from flint import fmpz_poly
K = 1024
class P:
    __slots__ = ('f',)
    def __init__(s, f): s.f = f
    @staticmethod
    def from_rows(rows):
        n = len(rows)
        if n == 0: return P(fmpz_poly([]))
        c = [0] * (n * K)
        for j, r in enumerate(rows):
            assert len(r) <= K
            for i, v in enumerate(r): c[j * K + i] = v
        return P(fmpz_poly(c))
    @staticmethod
    def const(c): return P(fmpz_poly([c]))
    def cells(s):
        """dict (i,j)->int of nonzero coefficients"""
        out = {}
        cs = s.f.coeffs()
        for e, v in enumerate(cs):
            if v != 0: out[(e % K, e // K)] = int(v)
        return out
    def rows(s):
        c = s.cells()
        if not c: return []
        dt = max(j for (_, j) in c)
        rows = []
        for j in range(dt + 1):
            dx = max((i for (i, jj) in c if jj == j), default=-1)
            rows.append([c.get((i, j), 0) for i in range(dx + 1)])
        return rows
    def stats(s):
        c = s.cells()
        if not c: return (-1, -1, 0, 0)
        dx = max(i for (i, _) in c); dt = max(j for (_, j) in c)
        assert dx < K // 2, dx
        return (dx, dt, len(c), max(abs(v).bit_length() for v in c.values()))
    def is_zero(s): return s.f.degree() < 0
    def is_const(s): return s.f.degree() <= 0
    def __mul__(s, o): return P(s.f * (o.f if isinstance(o, P) else o))
    def __add__(s, o): return P(s.f + o.f)
    def __sub__(s, o): return P(s.f - o.f)
    def __eq__(s, o): return s.f == o.f
    def __hash__(s): return hash(tuple(int(v) for v in s.f.coeffs()))
    def content_signed(s):
        g = 0
        cs = [int(v) for v in s.f.coeffs()]
        for v in cs:
            if v: g = math.gcd(g, v)
        if cs and cs[-1] < 0: g = -g     # leading (highest t, then highest x) coefficient positive
        return g
    def divexact_int(s, g): return P(fmpz_poly([int(v) // g for v in s.f.coeffs()]))
ONE = P.const(1); ZERO = P(fmpz_poly([]))
X = P(fmpz_poly([0, 1])); T = P(fmpz_poly([0] * K + [1]))
