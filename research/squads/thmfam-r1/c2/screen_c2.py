#!/usr/bin/env python3
"""Screen card c2 candidates: S = {F} u O(X) u O(Y) with X, Y integer det-1 matrices, entries in [-3,3].

Enumerates the distinct integer orbits O(X) (up to sign), all unordered pairs of distinct orbits, and F in {I,w,w2}.
Each candidate is scored with haar_ecc (psl) on the primes given by --qs; screen score = mean over those primes of
excess = diam - log_6(|PSL(2,q)|).  Candidates whose 7 elements are not distinct in PSL(2,q) for some screening prime
are skipped.  Output: TSV lines sorted by screen score, written to --out.

Usage: screen_c2.py --qs 29,41,53 --out screen.tsv [--top 40]
"""
import argparse, itertools, math, os, re, subprocess, sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from gen_c2 import family_lines, orbit, psl_key, det, LETTERS  # noqa: E402

HAAR = '/home/user/degree-diameter/research/theorems/haar_families/haar_ecc'
PAT = re.compile(r'Delta=(\d+) ecc_A=(\d+) ecc_B=(\d+) compA=(\d+) compB=(\d+) order=(\d+) connected=(\w+) diam=(\d+)')


def int_orbits():
    """Distinct integer orbits (as sets of PSL keys over Z) of det-1 matrices with entries in [-3,3]."""
    mats = [M for M in itertools.product(range(-3, 4), repeat=4) if det(M) == 1]
    seen = {}
    for X in mats:
        O = orbit(X)
        sig = tuple(sorted(set(psl_key(Z, 10**9 + 7) for Z in O)))  # large modulus: exact integer identity up to sign
        if sig not in seen:
            seen[sig] = X
    return list(seen.values())


def score(lines, q):
    inp = ''.join('%d %d %d %d 0\n' % Z for Z in lines)
    r = subprocess.run([HAAR, 'psl', str(q), '1'], input=inp, capture_output=True, text=True, timeout=600)
    m = PAT.search(r.stdout)
    if not m:
        return None
    d, eA, eB, cA, cB, order, conn, diam = m.groups()
    if conn != 'yes' or cA != cB:
        return None
    G = int(cA) // 2
    return int(diam) - math.log(G) / math.log(int(d) - 1)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--qs', default='29,41,53')
    ap.add_argument('--out', required=True)
    ap.add_argument('--top', type=int, default=40)
    a = ap.parse_args()
    qs = [int(x) for x in a.qs.split(',')]
    orbs = int_orbits()
    print('orbits:', len(orbs), file=sys.stderr)
    rows = []
    for F in LETTERS:
        for X, Y in itertools.combinations(orbs, 2):
            cand = (F, X, Y)
            vals = []
            ok = True
            for q in qs:
                try:
                    lines = family_lines(q, F, X, Y)
                except ValueError:
                    ok = False
                    break
                s = score(lines, q)
                if s is None:
                    ok = False
                    break
                vals.append(s)
            if ok:
                rows.append((sum(vals) / len(vals), vals, F, X, Y))
    rows.sort()
    with open(a.out, 'w') as f:
        for mean, vals, F, X, Y in rows:
            f.write('%.4f\t%s\t%s\t%s\t%s\t%s\n' % (mean, ','.join('%.3f' % v for v in vals), F,
                                                 ','.join(map(str, X)), ','.join(map(str, Y)), len(rows)))
    print('screened ok:', len(rows), file=sys.stderr)
    for row in rows[:a.top]:
        print('%.4f' % row[0], row[2], ','.join(map(str, row[3])), ','.join(map(str, row[4])), ','.join('%.3f' % v for v in row[1]))


if __name__ == '__main__':
    main()
