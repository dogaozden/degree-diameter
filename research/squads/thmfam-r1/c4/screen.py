#!/usr/bin/env python3
"""Screen c4 candidates (X, Y in SL(2,Z) entries in [-2,2], up to sign; u in 1..m-1; r or R) with haar_ecc.
Usage: screen.py m q1,q2,.. out.jsonl [--sample N --seed S] [--cap K]
Prints per-candidate mean excess over the given q list (excess = diam - log_6 |G|, |G| = |PSL| m)."""
import sys, itertools, math, subprocess, json, random, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from gen_c4 import gens
HE = '/home/user/degree-diameter/research/theorems/haar_families/haar_ecc'

def sl2_reps():
    out = []
    for m_ in itertools.product(range(-2, 3), repeat=4):
        a, b, c, d = m_
        if a*d - b*c != 1: continue
        # sign normalize (PSL): first nonzero entry positive
        lead = next(x for x in m_ if x != 0)
        if lead > 0: out.append(m_)
    return out

def excess(q, m, X, Y, u, rc):
    G = gens(q, m, X, Y, u, rc)
    txt = ''.join(f'{a} {b} {c} {d} {z}\n' for (a, b, c, d), z in G)
    r = subprocess.run([HE, 'psl', str(q), str(m)], input=txt, capture_output=True, text=True)
    import re
    mm = re.search(r'compA=(\d+) compB=(\d+) order=(\d+) connected=(\w+) diam=(\d+)', r.stdout)
    if not mm: return None
    cA, cB, order, conn, diam = mm.groups()
    if cA != cB or conn != 'yes' or int(cA) != int(order): return None
    Gsz = int(cA)//2
    return int(diam) - math.log(Gsz)/math.log(6)

def main():
    m = int(sys.argv[1]); qs = [int(x) for x in sys.argv[2].split(',')]; out = sys.argv[3]
    args = sys.argv[4:]
    sample = int(args[args.index('--sample')+1]) if '--sample' in args else 0
    seed = int(args[args.index('--seed')+1]) if '--seed' in args else 1
    reps = sl2_reps()
    cands = []
    us = ['r', 'r2'] if m == 1 else (list(range(1, m)) + ['r', 'r2'])
    if m == 1: us = ['1']  # ignored for m=1
    for X in reps:
        for Y in reps:
            for u in us:
                for rc in (['r', 'R'] if m > 1 else ['r']):
                    if m > 1 and u in ('r', 'r2') and rc == 'R': continue  # avoid duplicates
                    cands.append((X, Y, u, rc))
    if sample:
        random.Random(seed).shuffle(cands); cands = cands[:sample]
    print('candidates', len(cands), file=sys.stderr)
    with open(out, 'w') as f:
        for X, Y, u, rc in cands:
            ex = []
            for q in qs:
                e = excess(q, m, X, Y, u, rc)
                if e is None: ex = None; break
                ex.append(e)
            if ex is None: continue
            rec = {'m': m, 'X': X, 'Y': Y, 'u': u, 'r': rc, 'qs': qs, 'mean': sum(ex)/len(ex), 'ex': ex}
            f.write(json.dumps(rec) + '\n'); f.flush()

if __name__ == '__main__':
    main()
