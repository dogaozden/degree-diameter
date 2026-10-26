#!/usr/bin/env python3
"""c7 (wildcard): closed-form G-equivariant labellings, no search.
Row t = g^j p_s (point orbit s, exponent j; g = gQ of order M=31 on H(5)).  Copy c marks
  P_c(t) = g^(j + eP_c(s)) p_(piP_c(s))   and   L_c(t) = g^(j + eL_c(s)) l_(piL_c(s)),
i.e. every copy is a g-equivariant bijection of rows onto points/lines.  All parameters are closed-form
functions of (c, s); nothing is searched.  Usage: sweep.py FAMILY [args]  (see FAMILIES below)."""
import sys, os, subprocess, math

SH = '/home/user/degree-diameter/research/squads/table-audit-2-r1/shared'
HEX, GFILE, EVAL = f'{SH}/h5.txt', f'{SH}/g5.txt', f'{SH}/omega_eval'
HERE = os.path.dirname(os.path.abspath(__file__))
N, C, D = 3906, 20, 8
gl = list(map(int, open(GFILE).read().split()))

def orbits(w):
    base = w * N; seen = [-1] * N; jj = [0] * N; mem = []
    for x in range(N):
        if seen[x] < 0:
            s = len(mem); y = x; j = 0; ms = []
            while True:
                seen[y] = s; jj[y] = j; ms.append(y); j += 1
                y = gl[base + y] - base
                if y == x: break
            mem.append(ms)
    return seen, jj, mem

sP, jP, MP = orbits(0)
sL, jL, ML = orbits(1)
M = len(MP[0]); R = len(MP)
assert M == 31 and R == 126 and all(len(x) == M for x in MP) and all(len(x) == M for x in ML)
UNITS = [u for u in range(1, R) if math.gcd(u, R) == 1]

def write_lab(path, fn):
    P = [0] * (C * N); L = [0] * (C * N)
    for c in range(C):
        for t in range(N):
            s, j = sP[t], jP[t]
            sp, ep, sl, el = fn(c, s)
            P[c * N + t] = MP[sp][(j + ep) % M]
            L[c * N + t] = ML[sl][(j + el) % M]
    with open(path, 'w') as f:
        for i in range(0, C * N, N): f.write(' '.join(map(str, P[i:i + N])) + '\n')
        for i in range(0, C * N, N): f.write(' '.join(map(str, L[i:i + N])) + '\n')

def run(name, types, inner, fn):
    lab = os.path.join(HERE, 'lab', f'{name}.lab')
    write_lab(lab, fn)
    out = subprocess.run(['timeout', '900', 'nice', '-n', '10', EVAL, HEX, types, inner, lab, str(D), 'hubs0'],
                         capture_output=True, text=True).stdout.strip()
    far = int(out.split('far(>8)=')[1].split()[0]); ecc = out.split('maxecc=')[1].split()[0]
    print(f'{name:28s} {types} {inner} far={far} maxecc={ecc}', flush=True)
    return far, lab

I = lambda c, s: (s, 0, s, 0)  # identity-marking (equivariant), copy-independent

FAMILIES = {
    # copy-dependent point/line exponents, linear in c*s
    'eP_lin':   lambda a: (lambda c, s: (s, (a * c * s) % M, s, 0)),
    'eL_lin':   lambda a: (lambda c, s: (s, 0, s, (a * c * s) % M)),
    'eP_eL_lin': lambda a, b: (lambda c, s: (s, (a * c * s) % M, s, (b * c * s) % M)),
    # constant per-copy point shift (not an automorphism because lines stay put)
    'eP_const': lambda a: (lambda c, s: (s, (a * c) % M, s, 0)),
    # copy-dependent orbit permutations (translation and multiplication of orbit indices)
    'piP_shift': lambda d: (lambda c, s: ((s + c * d) % R, 0, s, 0)),
    'piP_mult':  lambda: (lambda c, s: ((UNITS[(c * 7) % len(UNITS)] * s) % R, 0, s, 0)),
    'piPL_mult': lambda: (lambda c, s: ((UNITS[(c * 7) % len(UNITS)] * s) % R, 0,
                                        (UNITS[(c * 5 + 3) % len(UNITS)] * s) % R, 0)),
    # quadratic exponents
    'eP_quad':  lambda a: (lambda c, s: (s, (a * c * c * s + c * s * s) % M, s, 0)),
    'eP_eL_quad': lambda a: (lambda c, s: (s, (a * c * s * s) % M, s, ((c * c + a) * s) % M)),
}

if __name__ == '__main__':
    fam = sys.argv[1]; types = sys.argv[2] if len(sys.argv) > 2 else 'abab'
    inner = sys.argv[3] if len(sys.argv) > 3 else 'LLLL'
    res = []
    if fam == 'sanity':
        res.append(run('id_equiv', types, inner, lambda c, s: (s, 0, s, 0)))
    elif fam == 'eP_lin':
        for a in map(int, sys.argv[4].split(',')):
            res.append(run(f'eP_lin_a{a}', types, inner, FAMILIES['eP_lin'](a)))
    elif fam == 'eL_lin':
        for a in map(int, sys.argv[4].split(',')):
            res.append(run(f'eL_lin_b{a}', types, inner, FAMILIES['eL_lin'](a)))
    elif fam == 'eP_eL_lin':
        for a, b in [tuple(map(int, x.split(':'))) for x in sys.argv[4].split(',')]:
            res.append(run(f'eP_eL_lin_{a}_{b}', types, inner, FAMILIES['eP_eL_lin'](a, b)))
    elif fam == 'eP_const':
        for a in map(int, sys.argv[4].split(',')):
            res.append(run(f'eP_const_a{a}', types, inner, FAMILIES['eP_const'](a)))
    elif fam == 'piP_shift':
        for d in map(int, sys.argv[4].split(',')):
            res.append(run(f'piP_shift_d{d}', types, inner, FAMILIES['piP_shift'](d)))
    elif fam == 'piP_mult':
        res.append(run('piP_mult', types, inner, FAMILIES['piP_mult']()))
    elif fam == 'piPL_mult':
        res.append(run('piPL_mult', types, inner, FAMILIES['piPL_mult']()))
    elif fam == 'eP_quad':
        for a in map(int, sys.argv[4].split(',')):
            res.append(run(f'eP_quad_a{a}', types, inner, FAMILIES['eP_quad'](a)))
    elif fam == 'eP_eL_quad':
        for a in map(int, sys.argv[4].split(',')):
            res.append(run(f'eP_eL_quad_a{a}', types, inner, FAMILIES['eP_eL_quad'](a)))
    best = min(res) if res else None
    if best: print('BEST', best[0], best[1])
