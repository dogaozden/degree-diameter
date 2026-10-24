"""Colour-voltage lift of the Z_5 polygon cover X of H(q): properly edge-colour X (bipartite, Delta = q+3 colours,
Delta perfect matchings), give an edge of colour d the voltage d in Z_K (K = Delta by default) from its point end.
Then Y = Z_5 x Z_K lift of H(q)+2 matchings where the Z_5 part is the polygon cover and the Z_K part is the colour.
Diameter of Y (and orders) are printed.  Optional third arg: K."""
import random, subprocess, sys
import gh
from models import perfect_matching, SCR
q = int(sys.argv[1]); seed = int(sys.argv[2]) if len(sys.argv) > 2 else 1
H = gh.load(q); N = H.N
Delta = q + 3
K = int(sys.argv[3]) if len(sys.argv) > 3 else Delta
rng = random.Random(seed)
s1 = list(range(N)); rng.shuffle(s1); s2 = list(range(N)); rng.shuffle(s2)
# X = Z_5 cover: vertices (v, i); point p level i: neighbours (L, i) for L on p, (s1 p, i+1), (s2 p, i+2)
# bipartite: points (p,i) vs lines (L,i). Build adjacency lists of X for edge colouring.
PX = N * 5
def pid(p, i): return p * 5 + i % 5
def lid(L, i): return L * 5 + i % 5        # L in 0..N-1 (line index)
nbr = [[] for _ in range(PX)]  # point -> list of (line vertex id, tag)
for p in range(N):
    for i in range(5):
        for L in H.through[p]:
            nbr[pid(p, i)].append((lid(int(L), i), ('g', int(L))))
        nbr[pid(p, i)].append((lid(s1[p], i + 1), ('h1',)))
        nbr[pid(p, i)].append((lid(s2[p], i + 2), ('h2',)))
# proper edge colouring by repeated perfect matchings in a Delta-regular bipartite multigraph
remaining = [list(range(len(nbr[x]))) for x in range(PX)]   # indices of uncoloured edges at point x
colour = [[None] * len(nbr[x]) for x in range(PX)]
for c in range(Delta):
    # build bipartite graph point -> available line ids (with edge index)
    lists = [[nbr[x][e][0] for e in remaining[x]] for x in range(PX)]
    m = perfect_matching(PX, lists, rng)
    for x in range(PX):
        # find an uncoloured edge from x to m[x]
        for e in remaining[x]:
            if nbr[x][e][0] == m[x]:
                colour[x][e] = c; remaining[x].remove(e); break
        else:
            raise SystemExit('colouring failed')
# lift: base = H(q) + hops, group Z_5 x Z_K; but colours live on edges of X (depend on level i).
# So build Y directly as a Z_K lift of X: base X (2*PX vertices), dart point->line voltage colour.
E = []
for x in range(PX):
    for e, (y, tag) in enumerate(nbr[x]):
        E.append((x, PX + y, colour[x][e] % K, 0))
path = f'{SCR}/colourlift_q{q}_K{K}_s{seed}.txt'
gh.write_base(path, 2 * PX, K, 1, E)
print(f'q={q} Delta={Delta} K={K}: |X|={2*PX}, |Y|={2*PX*K}; DGQ value {5 * ((q + 5) // 2) * 2 * N}')
for D in (8,):
    out = subprocess.run(['./liftdiam', path, str(D), '4'], capture_output=True, text=True).stdout.strip().split('\n')
    print(' ', out[0][:100], '|', out[1])
