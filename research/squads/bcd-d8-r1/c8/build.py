"""Build the step-1 lift spec from a proper 7-colouring col (values 0..6, f = col+1 in Z_8).
usage: build.py COLFILE SPECFILE [seed]. Points are base ids 0..N-1, line L is base id N+L."""
import sys, random
sys.path.insert(0, '/home/user/degree-diameter/research/projects/bigcheck-dist/d8')
import hexspec as hs
H = hs.Hex('/tmp/bcdt/hex/hex_q5.bin')
N = H.N
col = [int(x) for x in open(sys.argv[1]).read().split()]
spec = sys.argv[2]
rng = random.Random(int(sys.argv[3]) if len(sys.argv) > 3 else 1)
M = 8
f = [c + 1 for c in col]                      # voltages in Z_8 \ {0}
gamma = []                                    # value missed by each line
for L in range(N):
    vals = [f[int(p)] for p in H.lines[L]]
    assert len(set(vals)) == 6, "line not rainbow"
    miss = [v for v in range(1, 8) if v not in vals]
    assert len(miss) == 1
    gamma.append(miss[0])
lines_by_gamma, pts_by_f = {}, {}
for L in range(N):
    lines_by_gamma.setdefault(gamma[L], []).append(L)
for p in range(N):
    pts_by_f.setdefault(f[p], []).append(p)
sigma = [None] * N                            # sigma[p] = line index
online = [set(map(int, H.plines[p])) for p in range(N)]
for v in range(1, 8):
    P = pts_by_f[v]
    Lam = lines_by_gamma[(-v) % M][:]
    assert len(P) == len(Lam), (v, len(P), len(Lam))
    rng.shuffle(Lam)
    for p, L in zip(P, Lam):
        sigma[p] = L
    for _ in range(200000):
        bad = [p for p in P if sigma[p] in online[p]]
        if not bad:
            break
        p = rng.choice(bad); p2 = rng.choice(P)
        sigma[p], sigma[p2] = sigma[p2], sigma[p]
    assert not [p for p in P if sigma[p] in online[p]], "could not avoid incidences"
assert sorted(sigma) == list(range(N))
f3_fail = sum(1 for p in range(N) if len(set(gamma[int(L)] for L in H.plines[p])) == 1)
print("F3 failures (points whose 6 lines all miss one value):", f3_fail)
edges = []
for L in range(N):
    for p in H.lines[L]:
        edges.append((int(p), N + L, 0))
for p in range(N):
    edges.append((p, N + sigma[p], f[p] % M))
hs.write_spec(spec, H, M, edges, tau_invariant=False)
print("wrote", spec, "edges", len(edges))
