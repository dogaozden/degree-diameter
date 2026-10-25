"""Do the solving S sit at the j-patterns with the most walk values?  For every solving group Z_p x|_r Z_k of the
Delta=3 scans (runs/frob_d3D*/meta_p_k_r.txt), compute for EVERY admissible pattern j = (0, j1, j2) the fibre count
F(j) = min over start side, target side and J of |W_J| (cyclobound.ball_bound with FIBER, divided by k), and report
where the solution patterns rank.  Usage: python3 jfibre.py runs/frob_d3D9/meta_*.txt ..."""
import os, sys
from math import gcd
import cyclobound
cyclobound.FIBER = True
for fn in sys.argv[1:]:
    D = int(fn.split('frob_d3D')[1].split('/')[0])
    p, k, r = map(int, os.path.basename(fn)[5:-4].split('_'))
    o = 1; x = r % p
    while x != 1:
        x = x * r % p; o += 1
    sols = set()
    for line in open(fn):
        if line.startswith('SOL'):
            s = list(map(int, line.split()[1:]))
            (a1, j1), (a2, j2) = divmod(s[1], k), divmod(s[2], k)
            assert a1 == 0 and a2 == 1, line
            sols.add((j1, j2))
    rows = []
    for j1 in range(k):
        if j1 % o == 0:
            continue
        for j2 in range(k):
            if gcd(gcd(j1, j2), k) != 1:
                continue
            F = cyclobound.ball_bound(3, D, k, o, (0, j1, j2)) // k
            rows.append((F, (j1, j2) in sols))
    rows.sort(reverse=True)
    Fs = [F for F, _ in rows]
    solF = [F for F, s in rows if s]
    # rank of solutions: fraction of patterns with F strictly greater than the solution's F
    ranks = [sum(1 for F in Fs if F > f) / len(Fs) for f in solF]
    valid = sum(1 for F in Fs if F >= p)
    print(f'D={D} Z{p} x|_{r} Z{k} (o={o}, N={p*k}): {len(rows)} admissible j, {len(solF)} solutions; '
          f'max F={max(Fs)}, p={p}; patterns with F >= p: {valid}; solution F: min {min(solF)} mean {sum(solF)/len(solF):.1f}; '
          f'all-pattern mean F {sum(Fs)/len(Fs):.1f}; solutions in top {100*max(ranks):.0f}% (best {100*min(ranks):.0f}%)', flush=True)
