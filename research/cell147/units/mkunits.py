"""Build matchings for the polygon cover GH(q) + j matchings over Z_{2j+1} (Delorme-Gomez-Quisquater lift) with
"units": a unit (p, t) deletes the lifted matching edges ((p,c),(l,c+h_t)), l = sigma_t(p), in every copy c and adds
two new vertices z ~ {(p,c)} and z' ~ {(l,c)}. The unit is valid when
  (1') every point opposite p lies on a line sigma_t(x) with x at distance 4 from p, and
  (2') every line opposite l passes through a point sigma_t^-1(y) with y a line at distance 4 from l.
For a line M through p, F1 = {lines L: d(L,M)=4, d(L,p)=5} partitions the points opposite p (11 points each);
for a point N on l, F2 = {points P: d(P,N)=4, d(P,l)=5} partitions the lines opposite l. So it suffices that
sigma_t(S4(p)) contains F1 and sigma_t(F2) lies in S4(l).
Usage: python3 mkunits.py [--n N] GHFILE j SEED OUTSTATE UNITFILE p1:t1 [p2:t2 ...]
   N = 6 for generalized hexagons (default, D = 7), N = 4 for generalized quadrangles (D = 5): distances 4,5,6 become N-2, N-1, N.
   (t in 1..j; the remaining matchings and assignments are random). Writes a glift state file and the unit list.
"""
import sys, random, collections
sys.path.insert(0, '..')
sys.path.insert(0, '.')
from ghtools import load_gh

def bfs_dist(adj, srcs, maxd=6):
    n = len(adj); d = [-1] * n; dq = collections.deque()
    for s in srcs: d[s] = 0; dq.append(s)
    while dq:
        x = dq.popleft()
        if d[x] >= maxd: continue
        for y in adj[x]:
            if d[y] < 0: d[y] = d[x] + 1; dq.append(y)
    return d

def main():
    args = sys.argv[1:]
    n = 6
    if args[0] == '--n': n = int(args[1]); args = args[2:]
    ghf, j, seed, outst, unitf = args[0], int(args[1]), int(args[2]), args[3], args[4]
    units = [tuple(map(int, a.split(':'))) for a in args[5:]]
    rng = random.Random(seed)
    P, q, lines, adj = load_gh(ghf)
    m = 2 * j + 1
    sig = [[-1] * P for _ in range(j)]       # sig[t][p] = line index
    used = [set() for _ in range(j)]        # lines already assigned per matching
    prev_line_dists = []
    for (p, t) in units:
        t -= 1
        dp = bfs_dist(adj, [p])
        # l = sigma_t(p): a line at distance 5 from p, not yet used
        if sig[t][p] >= 0: raise SystemExit('point %d already assigned in matching %d' % (p, t + 1))
        cand_l = [L for L in range(P) if dp[P + L] == n - 1 and L not in used[t] and all(dprev[P + L] <= n - 2 for dprev in prev_line_dists)]
        if not cand_l: raise SystemExit('no line at distance 5 from p within distance 4 of the earlier unit lines')
        l = rng.choice(cand_l)
        dl = bfs_dist(adj, [P + l])
        prev_line_dists.append(dl)
        # M: a line through p with d(M, l) = 6;  N: a point on l with d(N, p) = 6
        Ms = [L for L in range(P) if p in lines[L] and dl[P + L] == n]
        Ns = [x for x in lines[l] if dp[x] == n]
        M = rng.choice(Ms); N = rng.choice(Ns)
        dM = bfs_dist(adj, [P + M]); dN = bfs_dist(adj, [N])
        A = [x for x in range(P) if dp[x] == n - 2 and sig[t][x] < 0]                 # S4(p), free points
        F1 = [L for L in range(P) if dM[P + L] == n - 2 and dp[P + L] == n - 1]          # lines to cover with
        B = [x for x in range(P) if dN[x] == n - 2 and dl[x] == n - 1]                   # F2
        C = set(L for L in range(P) if dl[P + L] == n - 2)                           # S4(l) as line indices
        Aset, Bset, F1set = set(A), set(B), set(F1)
        assert p not in Bset and l not in F1set and l not in C
        sig[t][p] = l; used[t].add(l)
        # lines of F1 already covered by an earlier assignment from a point in S4(p)?
        F1_need = [L for L in F1 if L not in used[t]]
        F1_bad = [L for L in F1 if L in used[t] and not any(sig[t][x] == L for x in A if False)]
        # points of B already assigned must already map into C
        for x in B:
            if sig[t][x] >= 0 and sig[t][x] not in C:
                raise SystemExit('conflict: point %d of F2 already mapped outside S4(l)' % x)
        B_need = [x for x in B if sig[t][x] < 0]
        rng.shuffle(F1_need); rng.shuffle(B_need)
        AB = [x for x in A if x in Bset]
        AnB = [x for x in A if x not in Bset]
        F1C = [L for L in F1_need if L in C]
        F1nC = [L for L in F1_need if L not in C]
        rng.shuffle(AB); rng.shuffle(AnB)
        # step 1: F1 ∩ C lines with A ∩ B points
        k1 = min(len(F1C), len(AB))
        for i in range(k1):
            sig[t][AB[i]] = F1C[i]; used[t].add(F1C[i])
        rest_F1 = F1C[k1:] + F1nC
        if len(rest_F1) > len(AnB): raise SystemExit('step 2 infeasible: %d lines, %d points' % (len(rest_F1), len(AnB)))
        for i, L in enumerate(rest_F1):
            sig[t][AnB[i]] = L; used[t].add(L)
        # step 3: remaining B points into C \ used
        Cfree = [L for L in C if L not in used[t]]
        rng.shuffle(Cfree)
        rest_B = [x for x in B_need if sig[t][x] < 0]
        if len(rest_B) > len(Cfree): raise SystemExit('step 3 infeasible: %d points, %d lines' % (len(rest_B), len(Cfree)))
        for i, x in enumerate(rest_B):
            sig[t][x] = Cfree[i]; used[t].add(Cfree[i])
        print('unit p=%d t=%d l=%d M=%d N=%d |A|=%d |F1|=%d |B|=%d |C|=%d |A&B|=%d |F1&C|=%d' % (
            p, t + 1, l, M, N, len(A), len(F1), len(B), len(C), len(AB), len(F1C)), file=sys.stderr)
    # complete every matching randomly
    for t in range(j):
        free_pts = [x for x in range(P) if sig[t][x] < 0]
        free_lines = [L for L in range(P) if L not in used[t]]
        rng.shuffle(free_lines)
        assert len(free_pts) == len(free_lines)
        for x, L in zip(free_pts, free_lines): sig[t][x] = L
        assert sorted(sig[t]) == list(range(P))
    with open(outst, 'w') as f:
        f.write('glift %d %d %d %d\ncyc %d\n' % (q, j, m, n + 1, m))
        for x in range(P):
            f.write(' '.join('%d %d' % (sig[t][x], (t + 1) % m) for t in range(j)) + '\n')
        for L in range(P):
            f.write(' '.join('0' for _ in range(q + 1)) + '\n')
    with open(unitf, 'w') as f:
        for (p, t) in units: f.write('%d %d\n' % (p, t))
main()
