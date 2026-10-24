"""Direct test of Theorem 1(b): for random pairs of OPPOSITE chambers C, C' of a real building (built by
polar_flags.py), the four vertices odd(C), even(C), odd(C'), even(C') must satisfy
   h even: d(same parts) = h,  d(different parts) = h - 1;     h odd: d(same parts) = h - 1, d(different parts) = h.
Opposition, from the geometry: PG(n,q): V_i + V'_{n+1-i} = whole space for all i (types reversed by w0);
polar spaces (types B_n/C_n, w0 = -1): V_i and V'_i opposite, i.e. V_i meets V'_i^perp only in 0, for all i.
usage: python3 opposite_check.py GEOM n q PAIRS"""
import sys, runpy, random
from collections import deque
geom, n, q, pairs = sys.argv[1], int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4])
sys.argv = ['polar_flags.py', geom, str(n), str(q)]
import io, contextlib
with contextlib.redirect_stdout(io.StringIO()):
    G = runpy.run_path('polar_flags.py', run_name='__main__')
chambers, odd, even, adj, mem, idx, vecs, top = (G[k] for k in ('chambers', 'odd', 'even', 'adj', 'mem', 'idx', 'vecs', 'top'))
No = len(odd)
h = {'PG': n + 1, 'Sp': 2 * n, 'O': 2 * n, 'Om': 2 * n, 'U': 2 * (n // 2)}[geom]
zero_bit = 1 << idx[tuple([0] * len(vecs[0]))]
def members(mask): return mem[mask]
def meet_trivial(a, b): return (a & b) == zero_bit
def sum_is_all(a, b):
    # dim(a + b) = dim a + dim b - dim(a meet b); here: check that the span of a and b is the whole space
    # via the meet: a + b = V iff dim a + dim b - dim(a & b) = dim V
    import math
    da = int(round(math.log(bin(a).count('1'), q))); db = int(round(math.log(bin(b).count('1'), q)))
    dm = int(round(math.log(bin(a & b).count('1'), q)))
    return da + db - dm == len(vecs[0])
f = G['f']
def perp_mask(mask):
    ms = members(mask); out = 0
    for i, v in enumerate(vecs):
        if all(f(v, m) == 0 for m in ms): out |= 1 << i
    return out
def opposite(c1, c2):
    if geom == 'PG':
        return all(sum_is_all(c1[i], c2[top - 1 - i]) for i in range(top))
    return all(meet_trivial(c1[i], perp_mask(c2[i])) for i in range(top))
def parts(c):
    return odd[tuple(c[i] for i in range(0, top, 2))], No + even[tuple(c[i] for i in range(1, top, 2))]
def bfs(s):
    dist = [-1] * len(adj); dist[s] = 0; dq = deque([s])
    while dq:
        u = dq.popleft()
        for w in adj[u]:
            if dist[w] < 0: dist[w] = dist[u] + 1; dq.append(w)
    return dist
random.seed(7)
found = 0; tries = 0; bad = 0; seen = set()
while found < pairs and tries < 200000:
    tries += 1
    c1, c2 = random.choice(chambers), random.choice(chambers)
    if not opposite(c1, c2): continue
    found += 1
    o1, e1 = parts(c1); o2, e2 = parts(c2)
    for src, a_is_odd in ((o1, True), (e1, False)):
        dist = bfs(src)
        for tgt, b_is_odd in ((o2, True), (e2, False)):
            same = a_is_odd == b_is_odd
            want = (h if same else h - 1) if h % 2 == 0 else (h - 1 if same else h)
            got = dist[tgt]; seen.add((same, got))
            if got != want: bad += 1
print(f"{geom} n={n} q={q} (h={h}): {found} random opposite chamber pairs (from {tries} random pairs), "
      f"distances seen {sorted(seen)} (same-part?, distance); mismatches with Theorem 1(b): {bad}")
