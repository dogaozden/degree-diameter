"""The (3,8) record is not a Haar graph: distance profiles of its vertices.

Usage: python3 lift38_profiles.py

Builds the 288-vertex lift from research/lifts/sols/c1r_d3D8_n288_b2_3_0_aff302108_s1.txt with the lift builder of
research/lifts/coordinator_check/build.py, runs BFS from every vertex, and counts the vertices by (colour class, number
of vertices at distance 6, number at distance 8, eccentricity). In a Haar graph the right translations act
transitively on each colour class (HAAR_D8_10.md, Lemma 1.2(b)), so all vertices of a class have the same profile.
"""
import collections
import os

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.join(HERE, "../../..")

src = open(os.path.join(ROOT, "research/lifts/coordinator_check/build.py")).read()
ns = {}
exec(src.split("if sys.argv[1] == 'meta'")[0], ns)          # the builder's functions, without its command line
base = []
for ln in open(os.path.join(ROOT, "research/lifts/sols/c1r_d3D8_n288_b2_3_0_aff302108_s1.txt")):
    if ln.startswith("e "):
        _, u, w, _, v = ln.split()
        base.append((int(u), int(w), tuple(map(int, v.split(",")))))
out = "/tmp/lift38_edges.txt"
ns["lift"](3, (0, 2, 1, 0), 8, base, 4, out)                 # group "aff 3 0 2 1 0 8": Z_3^2 x| Z_8, matrix [[0,2],[1,0]]
lines = open(out).read().split("\n")
n = int(lines[0])
adj = collections.defaultdict(list)
for ln in lines[1:]:
    if ln.strip():
        u, v = map(int, ln.split())
        adj[u].append(v)
        adj[v].append(u)
col, q = {0: 0}, [0]
for u in q:
    for v in adj[u]:
        if v not in col:
            col[v] = 1 - col[u]
            q.append(v)
assert len(col) == n and all(col[u] != col[v] for u in adj for v in adj[u])
prof = collections.Counter()
for s in range(n):
    d, q = {s: 0}, [s]
    for u in q:
        for v in adj[u]:
            if v not in d:
                d[v] = d[u] + 1
                q.append(v)
    c = collections.Counter(d.values())
    prof[(col[s], c[6], c[8], max(d.values()))] += 1
print(f"n = {n}, degrees {sorted({len(a) for a in adj.values()})}")
for (cl, d6, d8, ecc), cnt in sorted(prof.items()):
    print(f"class {cl}: {cnt} vertices with {d6} at distance 6, {d8} at distance 8, eccentricity {ecc}")
