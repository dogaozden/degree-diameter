#!/usr/bin/env python3
"""Independent count of condition (A) failures for a flag labelling nu of W(q) (d06, job beyond r2).
For every ordered source s (point or line) BFS in the incidence graph B, count shortest paths to each vertex by
ν-parity; an opposite same-colour pair (distance 4) is BAD when all q+1 geodesics have the same parity.
usage: audit_A.py GQBIN DMFILE [SIGSEED OUT_DM]
  DMFILE is a dmfast/lift2 DM file (nu = (token // 3) & 1).  With SIGSEED and OUT_DM, also writes a copy of the
  DM file whose sigma (both copies) is a random bijection with that seed (sigma does not enter (A))."""
import sys, struct, random

def load_gq(path):
    raw = open(path, 'rb').read()
    q, N, L = struct.unpack('<3i', raw[:12])
    pl = struct.unpack('<%di' % (L * (q + 1)), raw[12:12 + 4 * L * (q + 1)])
    return q, N, L, pl

def main():
    gqbin, dmf = sys.argv[1], sys.argv[2]
    q, N, L, pl = load_gq(gqbin)
    Q1 = q + 1
    tok = open(dmf).read().split()
    assert int(tok[0]) == q
    pos = 7
    sig = [int(x) for x in tok[pos:pos + N]]
    nu_pos = pos + 2 * N + 2 * N
    nu = [(int(x) // 3) & 1 for x in tok[nu_pos:nu_pos + L * Q1]]
    assert len(nu) == L * Q1
    # vertices: points 0..N-1, lines N..N+L-1; flag index l*Q1+k joins point pl[l*Q1+k] and line N+l
    adj = [[] for _ in range(N + L)]
    for l in range(L):
        for k in range(Q1):
            p = pl[l * Q1 + k]; f = nu[l * Q1 + k]
            adj[p].append((N + l, f)); adj[N + l].append((p, f))
    bad = 0; badpairs = []
    for s in range(N + L):
        dist = [-1] * (N + L); ce = [0] * (N + L); co = [0] * (N + L)
        dist[s] = 0; ce[s] = 1; frontier = [s]; d = 0
        while frontier and d < 4:
            nxt = []
            for x in frontier:
                for (y, f) in adj[x]:
                    if dist[y] < 0:
                        dist[y] = d + 1; nxt.append(y)
            for x in frontier:
                for (y, f) in adj[x]:
                    if dist[y] == d + 1:
                        if (ce[x] or co[x]):
                            # parity of paths to x, shifted by flag f
                            if f: ce[y] += co[x]; co[y] += ce[x]
                            else: ce[y] += ce[x]; co[y] += co[x]
            frontier = nxt; d += 1
        same = range(0, N) if s < N else range(N, N + L)
        for u in same:
            if u <= s or dist[u] != 4: continue
            if ce[u] == 0 or co[u] == 0:
                bad += 1; badpairs.append((s, u))
    print(f"q={q} points={N} lines={L} opposite-pair (A) failures={bad}")
    for s, u in badpairs[:10]:
        print("bad pair", s, u)
    if len(sys.argv) > 4:
        seed, outdm = int(sys.argv[3]), sys.argv[4]
        rng = random.Random(seed); s2 = list(range(N)); rng.shuffle(s2)
        out = tok[:]
        for t in range(2):
            for p in range(N): out[pos + t * N + p] = str(s2[p])
        open(outdm, 'w').write(' '.join(out) + '\n')
        print("wrote", outdm, "with sigma seed", seed)
main()
