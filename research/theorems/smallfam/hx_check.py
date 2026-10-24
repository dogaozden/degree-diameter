"""Independent check of hx: for each plan line (s1, s2) of a table group, compute with igraph the exact diameter of
H(G, {e, s1, s2, s3}) for every s3 and compare the set of s3 with diameter <= D against hx's SOL lines.
Usage: python3 hx_check.py TABLE PLAN HX_OUTPUT D"""
import sys
import igraph as ig
tab = open(sys.argv[1]).read().split('\n')
N, e = map(int, tab[0].split())
T = [list(map(int, tab[1 + x].split())) for x in range(N)]
plan = [tuple(map(int, l.split())) for l in open(sys.argv[2]) if l.strip()]
hx = {tuple(map(int, l.split()[1:])) for l in open(sys.argv[3]) if l.startswith('SOL')}
D = int(sys.argv[4])
mism = 0; tot = 0
for (s1, s2) in plan:
    for s3 in range(N):
        if s3 in (e, s1, s2):
            continue
        S = [e, s1, s2, s3]
        G = ig.Graph(n=2 * N, edges=[(g, N + T[s][g]) for g in range(N) for s in S])
        ok = G.is_connected() and G.diameter() <= D
        claimed = tuple(S) in hx or (e, s1, s2, s3) in hx
        tot += 1
        if ok != claimed:
            mism += 1
            print('MISMATCH', S, 'igraph ok', ok, 'hx', claimed)
print(f'{tot} sets checked, {sum(1 for x in hx)} hx solutions, mismatches: {mism}')
