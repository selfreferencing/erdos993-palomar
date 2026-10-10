#!/usr/bin/env python3
"""Parse a generated light-core linking family (Expressions.lean, Checks*.lean, Program.lean)
into a pickle: SLP nodes, stored pairs, public roots, divisor list."""
import re, sys, glob, os, pickle, ast
getattr(sys, "set_int_max_str_digits", lambda n: None)(0)
def parse(dirpath):
    ex = open(os.path.join(dirpath, 'Expressions.lean')).read()
    nodes = {}
    for m in re.finditer(r'^def n(\d+)_expression \(x t : ℝ\) : ℝ := (.*)$', ex, re.M):
        i = int(m.group(1)); rhs = m.group(2).strip()
        if rhs == 'x': nodes[i] = ('x',)
        elif rhs == 't': nodes[i] = ('t',)
        else:
            mc = re.fullmatch(r'\(\(?(-?\d+)\)? : ℝ\)/\((\d+) : ℝ\)', rhs)
            if mc: nodes[i] = ('const', int(mc.group(1)), int(mc.group(2))); continue
            mb = re.fullmatch(r'n(\d+)_expression x t ([-+*/]) n(\d+)_expression x t', rhs)
            if mb: nodes[i] = ({'+':'add','-':'sub','*':'mul','/':'div'}[mb.group(2)], int(mb.group(1)), int(mb.group(3))); continue
            mp = re.fullmatch(r'n(\d+)_expression x t \^ (\d+)', rhs)
            if mp: nodes[i] = ('pow', int(mp.group(1)), int(mp.group(2))); continue
            raise ValueError(rhs)
    divisors = [int(a) for a in re.findall(r'^\s*\| \d+ => n(\d+)_expression x t', ex, re.M)]
    pairs = {}
    for f in sorted(glob.glob(os.path.join(dirpath, 'Checks*.lean'))):
        for line in open(f):
            if line.startswith('def n') and '_pair : RationalPair := ' in line:
                m = re.match(r'def n(\d+)_pair : RationalPair := ⟨(.*)⟩\s*$', line)
                body = m.group(2)
                # split at top-level "], [" between numerator and denominator: parse as python tuple
                body = body.replace('(', '').replace(')', '')
                num, den = ast.literal_eval('(' + body + ')')
                pairs[int(m.group(1))] = (num, den)
    prog = open(os.path.join(dirpath, 'Program.lean')).read()
    roots = [(m.group(1), int(m.group(2))) for m in re.finditer(r'^abbrev (\S+)_pair := n(\d+)_pair', prog, re.M)]
    return dict(nodes=nodes, pairs=pairs, roots=roots, divisors=divisors)
if __name__ == '__main__':
    d = parse(sys.argv[1])
    print(len(d['nodes']), len(d['pairs']), len(d['roots']), len(d['divisors']))
    pickle.dump(d, open(sys.argv[2], 'wb'))
