"""Theorem 14 (CHART_LIFTS.md): universal k-letter charts exist over F_q^4 for every k >= 3 and every prime power
q > 28 k (k-1)^3 + 4 (k-1); hence n_b(kq, 5) >= 2 m q^4 for every exact k-regular controller with m vertices per side.

Checks made here:
1. Every nonbacktracking 4-pattern with k letters uses at most 4 distinct letters; an order-preserving relabelling onto
   0..3 (letter 0 goes to 0 when it occurs) is a nonbacktracking k = 4 pattern, and its polynomial is the k-letter one
   with the variables renamed (and, if letter 0 does not occur, with A_0 specialised to I, which can only lose
   non-vanishing).  integer_witness.py showed every k = 4 pattern polynomial is nonzero modulo every prime.  We list the
   relabelled pattern of every k-letter pattern for k <= 8 and check it is one of the 216 witnessed k = 4 patterns.
2. Exact controllers (every same-side pair, a vertex with itself included, joined by a nonbacktracking 4-walk):
   K_{k,k} for every k >= 3 (checked by brute force for k = 3..8), and the voltage controllers of the earlier session
   (runs/exact*.volt), re-evaluated with ctrl_search and the flags charts/nbonly_k*.flags (cost must be 0).
Output: r3/allk_family.out"""
import itertools, subprocess, os
W = '/tmp/claude-0/-home-user-degree-diameter/8e7a80fa-6b09-58cb-8199-8d05845bbe55/scratchpad/w'
ok4 = {p for p in itertools.product(range(4), repeat=4) if p[0] != p[1] and p[1] != p[2] and p[2] != p[3]}
assert len(ok4) == 108          # per side; integer_witness.py covers both sides (216)
out = []
for k in range(3, 9):
    pats = [p for p in itertools.product(range(k), repeat=4) if p[0] != p[1] and p[1] != p[2] and p[2] != p[3]]
    bad = 0
    for p in pats:
        L = sorted(set(p)); phi = {l: i for i, l in enumerate(L)}   # order-preserving onto 0..|L|-1
        r = tuple(phi[x] for x in p)
        if r not in ok4: bad += 1
    q0 = 28 * k * (k - 1) ** 3 + 4 * (k - 1)
    out.append('k=%d: %d nonbacktracking patterns per side, all relabel to witnessed k=4 patterns: %s; q0(k) = %d' % (k, len(pats), bad == 0, q0))
def kkk_exact(k):
    A = range(k); Bv = range(k)   # K_{k,k}: a_i ~ b_j for all i, j
    for i in A:
        reach = set()
        for x in Bv:
            for y in A:
                if y == i: continue
                for z in Bv:
                    if z == x: continue
                    for j in A:
                        if j == y: continue
                        reach.add(j)
        if reach != set(A): return False
    return True
for k in range(3, 9): out.append('K_{%d,%d} exact (m = %d): %s' % (k, k, k, kkk_exact(k)))
for f, base, flags, grp in [('runs/exact3_z6.volt', None, 'charts/nbonly_k3.flags', 'cyclic:6'), ('runs/exact54.volt', None, 'charts/nbonly_k4.flags', 'cyclic:18'),
                            ('runs/exact5_z29.volt', None, 'charts/nbonly_k5.flags', 'cyclic:29'), ('runs/exact6_z40.volt', None, 'charts/nbonly_k6.flags', 'cyclic:40')]:
    rows = [l.split() for l in open(f) if l.strip()]
    r, k, g = map(int, rows[0]); base = '%s/base_%s.txt' % (W, os.path.basename(f))
    with open(base, 'w') as fb:
        fb.write('%d\n' % r); fb.writelines('%s %s %s\n' % (a, b, c) for a, b, c, v in rows[1:])
    volt = ','.join(v for a, b, c, v in rows[1:])
    res = subprocess.run([W + '/ctrl_search', base, 'cyclic:%d' % g, flags, '1', '1'], env=dict(os.environ, VOLT=volt), capture_output=True, text=True).stdout.strip()
    out.append('%s: r=%d k=%d |G|=%d m=%d -> %s' % (f, r, k, g, r * g, res))
open('r3/allk_family.out', 'w').write('\n'.join(out) + '\n'); print('\n'.join(out))
