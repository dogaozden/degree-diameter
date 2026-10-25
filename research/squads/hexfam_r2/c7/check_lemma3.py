"""Independent checker for the Lemma 3 condition (THEOREM.md, hexagon-family) on a pair list.
Uses only the incidence data of hex_qQ.bin (points 0..N-1, lines 0..L-1). Pure Python BFS.
Usage: python3 -I check_lemma3.py HEXBIN PAIRFILE [--pure]
PAIRFILE: lines "r s" (point id, line id). Checks:
 1. R distinct, S distinct, R pairwise non-collinear (distance != 2), S pairwise non-concurrent;
 2. d(r,r') = d(s,s') for all pairs, in {4,6} (distance in the incidence graph);
 3. midpoint z of each distance-4 pair (unique common point at distance 2 of both); for every midpoint z with
    group G_z = {r in R : d(r,z)=2}, |G_z| >= 2: tau(G_z) = S cap Gamma2(w) for ONE line w = mu(z) (computed
    from scratch by set intersection); mu injective (distinct midpoints -> distinct midlines);
 4. builds sigma: P -> L explicitly as in the proof of Lemma 3 and checks it is a bijection with
    sigma(Gamma2(r)) = Gamma2(sigma(r)) for every r in R (condition R2 itself).
Prints one line: 'VALID |R|=k' or 'INVALID reason'."""
import sys, struct
from collections import deque

def load(fn):
    raw = open(fn, 'rb').read()
    q, N, L = struct.unpack('3i', raw[:12])
    LP = []
    o = 12
    for l in range(L):
        LP.append([struct.unpack('<i', raw[o + 4 * (l * (q + 1) + k): o + 4 * (l * (q + 1) + k) + 4])[0] for k in range(q + 1)])
    PL = [[] for _ in range(N)]
    for l in range(L):
        for p in LP[l]:
            PL[p].append(l)
    return q, N, L, LP, PL

def main():
    args = [a for a in sys.argv[1:] if not a.startswith('--')]
    pure = '--pure' in sys.argv
    hexfn, pairfn = args[0], args[1]
    q, N, L, LP, PL = load(hexfn)
    assert N == L
    pairs = []
    for line in open(pairfn):
        t = line.split()
        if len(t) >= 2 and not t[0].startswith('#'):
            pairs.append((int(t[0]), int(t[1])))
    R = [p for p, _ in pairs]; S = [s for _, s in pairs]
    k = len(pairs)
    def fail(msg):
        print('INVALID ' + msg); sys.exit(0)
    if len(set(R)) != k or len(set(S)) != k: fail('R or S not injective')
    if any(not (0 <= r < N) for r in R) or any(not (0 <= s < L) for s in S): fail('id out of range')

    # generic BFS in the incidence graph: nodes ('p', i) and ('l', j) encoded as i and N+j
    def bfs(src):
        dist = {src: 0}; par = {src: None}; dq = deque([src])
        while dq:
            v = dq.popleft()
            if dist[v] >= 6: continue
            nbrs = [N + l for l in PL[v]] if v < N else [p for p in LP[v - N]]
            for w in nbrs:
                if w not in dist:
                    dist[w] = dist[v] + 1; par[w] = v; dq.append(w)
        return dist
    def pdist(d, node): return d.get(node, 99)
    dR = [bfs(r) for r in R]           # distances from each r (points and lines)
    dS = [bfs(N + s) for s in S]       # distances from each s
    # sanity: hexagon basics on the first point
    d0 = dR[0]
    gam2 = {v for v, dd in d0.items() if dd == 2}
    if len(gam2) != q * (q + 1) or max(d0.values()) != 6: fail('hexagon sanity failed')
    # distance matrices
    DR = [[pdist(dR[i], R[j]) for j in range(k)] for i in range(k)]
    DS = [[pdist(dS[i], N + S[j]) for j in range(k)] for i in range(k)]
    for i in range(k):
        for j in range(k):
            if i == j: continue
            if DR[i][j] == 2: fail('collinear points %d %d' % (R[i], R[j]))
            if DS[i][j] == 2: fail('concurrent lines %d %d' % (S[i], S[j]))
            if DR[i][j] not in (4, 6): fail('point distance %d' % DR[i][j])
            if DR[i][j] != DS[i][j]: fail('distance mismatch (%d,%d): %d vs %d' % (i, j, DR[i][j], DS[i][j]))
            if pure and DR[i][j] != 6: fail('pure mode: distance 4 pair')
    # Gamma2 sets (independent of the distance matrices): points at distance 2 from each r, lines from each s
    G2P = [{v for v, dd in dR[i].items() if dd == 2 and v < N} for i in range(k)]
    G2L = [{v - N for v, dd in dS[i].items() if dd == 2 and v >= N} for i in range(k)]
    for i in range(k):
        if len(G2P[i]) != q * (q + 1) or len(G2L[i]) != q * (q + 1): fail('Gamma2 size')
    # midpoints of R: points z with d(r,z)=2 for at least two r in R
    cnt = {}
    for i in range(k):
        for z in G2P[i]: cnt.setdefault(z, []).append(i)
    mids = {z: G for z, G in cnt.items() if len(G) >= 2}
    cntL = {}
    for i in range(k):
        for w in G2L[i]: cntL.setdefault(w, []).append(i)
    midl = {w: G for w, G in cntL.items() if len(G) >= 2}
    # every pair at distance 4 has exactly one midpoint, and it is in mids
    for i in range(k):
        for j in range(i + 1, k):
            if DR[i][j] == 4:
                common = G2P[i] & G2P[j]
                if len(common) != 1: fail('midpoint not unique for %d %d' % (R[i], R[j]))
                if list(common)[0] not in mids: fail('midpoint missing')
            else:
                if G2P[i] & G2P[j]: fail('d=6 pair with common Gamma2 point')
    mu = {}
    for z, G in mids.items():
        T = {S[i] for i in G}
        # the line w concurrent with all of T: intersection of Gamma2 of two members
        a, b = G[0], G[1]
        cands = G2L[a] & G2L[b]
        if len(cands) != 1: fail('midline not unique')
        w = list(cands)[0]
        if {S[i] for i in range(k) if w in G2L[i]} != T: fail('tau(Gamma2(z) cap R) != S cap Gamma2(mu z)')
        mu[z] = w
    if len(set(mu.values())) != len(mu): fail('mu not injective')
    if set(mu.values()) != set(midl.keys()): fail('mu not onto the midlines of S')
    # build sigma (proof of Lemma 3)
    tau = {R[i]: S[i] for i in range(k)}
    sigma = {}
    for z, w in mu.items(): sigma[z] = w
    for i in range(k): sigma[R[i]] = S[i]
    for i in range(k):
        r = R[i]
        free_pts = sorted(z for z in G2P[i] if z not in mids)
        free_lines = sorted(w for w in G2L[i] if w not in midl)
        if len(free_pts) != len(free_lines): fail('count mismatch at %d' % r)
        for z, w in zip(free_pts, free_lines):
            if z in sigma: fail('point assigned twice')
            sigma[z] = w
    # remaining points to remaining lines (any bijection)
    used = set(sigma.values())
    rest_lines = [w for w in range(L) if w not in used]
    rest_pts = [p for p in range(N) if p not in sigma]
    if len(rest_lines) != len(rest_pts): fail('remainder count mismatch')
    for p, w in zip(rest_pts, rest_lines): sigma[p] = w
    if len(sigma) != N or len(set(sigma.values())) != N: fail('sigma not a bijection')
    # check R2: sigma(Gamma2(r)) = Gamma2(sigma(r)) for every r in R
    for i in range(k):
        r = R[i]
        img = {sigma[z] for z in G2P[i]}
        if img != G2L[i]: fail('R2 fails at point %d' % r)
        # sigma(r) must have Gamma2 equal to the image computed from the line side
    # also check sigma(r) is the image line of the right distance class (sanity)
    print('VALID |R|=%d (pairs %d, midpoints %d, midlines %d, max mult %d)' % (k, k, len(mids), len(midl), max(len(G) for G in mids.values()) if mids else 0))

main()
