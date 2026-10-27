#!/usr/bin/env python3
"""c6: LPS(p=5) x Z_m labels, equivariant under conjugation by omega=(1+i+j+k)/2 (quaternion cycle
(a0,a1,a2,a3)->(a0,a3,a1,a2)).  Cycles found from the quaternions; cycle labels (t, r t, r^2 t) mod m.
usage: gen_c6.py q m t2 rsel     (rsel in {0,1}: r = the rsel-th element of order 3 mod m; t1 = 1)
Prints lines "a b c d z" for haar_ecc pgl."""
import subprocess, sys, os
HERE = os.path.dirname(os.path.abspath(__file__))
LPS = '/home/user/degree-diameter/research/theorems/haar_families/lps_haar'

def lps_gens(q):
    out = subprocess.run([LPS, '5', str(q), '-v'], capture_output=True, text=True).stdout
    gens = []
    for line in out.splitlines():
        if line.startswith('gen '):
            quat = line[line.index('quat (') + 6: line.index(')', line.index('quat ('))]
            quat = tuple(int(x) for x in quat.split(','))
            mat = line[line.index('mat(') + 4: line.index(')', line.index('mat('))]
            mat = tuple(int(x) for x in mat.split(','))
            gens.append((quat, mat))
    return gens

def cycles(gens):
    idx = {g[0]: i for i, g in enumerate(gens)}
    alpha = lambda t: (t[0], t[3], t[1], t[2])
    seen, cyc = set(), []
    for i, g in enumerate(gens):
        if i in seen: continue
        c, j = [], i
        while j not in seen:
            seen.add(j); c.append(j); j = idx[alpha(gens[j][0])]
        cyc.append(c)
    return cyc

def order3(m):
    return [r for r in range(2, m) if pow(r, 3, m) == 1 and r != 1]

def labels(gens, m, t2, rsel):
    cyc = cycles(gens)
    assert len(cyc) == 2 and all(len(c) == 3 for c in cyc), cyc
    rs = order3(m)
    r = rs[rsel]
    z = {}
    for t, c in zip((1, t2), cyc):
        for k, i in enumerate(c):
            z[i] = t * pow(r, k, m) % m
    return z

def emit(q, m, t2, rsel):
    gens = lps_gens(q)
    z = labels(gens, m, t2, rsel)
    lines = []
    for i, (quat, mat) in enumerate(gens):
        a, b, c, d = mat
        lines.append(f"{a} {b} {c} {d} {z[i]}")
    return "\n".join(lines) + "\n"

if __name__ == '__main__':
    q, m, t2, rsel = map(int, sys.argv[1:5])
    sys.stdout.write(emit(q, m, t2, rsel))
