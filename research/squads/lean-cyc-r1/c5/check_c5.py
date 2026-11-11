#!/usr/bin/env python3
"""Card c5 of squad lean-cyc-r1: independent check of lean/BipartiteDD/Haar/CycLift/N192382.lean.

Written from research/squads/lean-cyc-r1/SPEC.md only (the generators were not read).
Checks: parse outA; build the lift; degree/loops; edge file vs lift through the Haar map
(bijection, set equality); bipartiteness; BFS diameter in the edge-file graph from vertex 0 and
vertex N (must be exactly 13); 50 random BFS sources (all <= 13); lift-level BFS from 0 and N
whose distance arrays must agree with the edge-file ones under the map.
"""
import gzip
import os
import random
import re
import sys

LEAN = "/home/user/degree-diameter/lean/BipartiteDD/Haar/CycLift/N192382.lean"
EDGES = "/home/user/degree-diameter/research/frontier/beyond/graphs/d4D13_n192382_meta2237_43_1984.edges.gz"
LOG = os.path.join(os.path.dirname(os.path.abspath(__file__)), "check_c5.out")

N = 192382      # vertices
M = 2237        # lift modulus
K = 43          # Haar fibre size (group Z_2237 x| Z_43)
R = 1984        # action exponent: (a, j)(b, l) = (a + R^j b, j + l)
NB = 86         # base vertices: A_0..A_42 = 0..42, B_0..B_42 = 43..85
D = 13          # stated diameter
DEG = 4         # stated degree
HALF = M * K    # 96191; the Haar group has this many elements per side

logf = open(LOG, "w")


def say(*parts):
    line = " ".join(str(p) for p in parts)
    print(line, flush=True)
    logf.write(line + "\n")
    logf.flush()


results = []


def check(name, ok, detail=""):
    results.append((name, bool(ok)))
    say(("PASS" if ok else "FAIL"), name, detail)
    return ok


# ---------------------------------------------------------------- parsing the Lean data
def parse_outA(path):
    text = open(path, encoding="utf-8").read()
    i = text.index("def outA192382")
    j = text.index("def side192382")
    block = text[i:j]
    rows = []
    for mt in re.finditer(r"\[((?:\s*\(\s*\d+\s*,\s*\d+\s*\)\s*,?)+)\s*\]", block):
        pairs = [(int(a), int(b)) for a, b in
                 re.findall(r"\(\s*(\d+)\s*,\s*(\d+)\s*\)", mt.group(1))]
        rows.append(pairs)
    return rows


rows = parse_outA(LEAN)
ok_rows = len(rows) == NB and all(len(r) == DEG for r in rows)
ok_rows = ok_rows and all(0 <= u < NB and 0 <= b < M for r in rows for (u, b) in r)
check("parse_outA_86_rows_of_4_arcs_in_range", ok_rows,
      f"rows={len(rows)} arcs={sum(len(r) for r in rows)}")
if not ok_rows:
    say("cannot continue")
    sys.exit(1)

# ---------------------------------------------------------------- the lift (SPEC semantics)
# vertex v = w*M + x, w = v // M, x = v % M; neighbours (u*M + (x+beta) % M) % N for (u, beta) in row w.
adj = [set() for _ in range(N)]
loops = 0
for v in range(N):
    w, x = divmod(v, M)
    for u, beta in rows[w]:
        nb = (u * M + (x + beta) % M) % N
        if nb == v:
            loops += 1
        else:
            adj[v].add(nb)
            adj[nb].add(v)
degs = [len(s) for s in adj]
ok_lift = loops == 0 and all(d == DEG for d in degs)
check("lift_no_loops_all_degree_4", ok_lift,
      f"loops={loops} degree_hist={ {d: degs.count(d) for d in set(degs)} }")

L = set()
for v in range(N):
    for nb in adj[v]:
        if v < nb:
            L.add((v, nb))
check("lift_edge_count", len(L) == N * DEG // 2, f"edges={len(L)} expected={N * DEG // 2}")

# ---------------------------------------------------------------- the edge file
with gzip.open(EDGES, "rt") as f:
    header = int(f.readline())
    raw = []
    for line in f:
        a, b = line.split()
        raw.append((int(a), int(b)))
check("edge_file_header_is_N", header == N, f"header={header}")

E = []
edge_loops = 0
for a, b in raw:
    if a == b:
        edge_loops += 1
    E.append((a, b) if a < b else (b, a))
E_set = set(E)
ok_edge_simple = edge_loops == 0 and len(E_set) == len(E) and len(E) == N * DEG // 2 \
    and all(0 <= a < N and 0 <= b < N for a, b in E)
check("edge_file_simple_no_duplicates", ok_edge_simple,
      f"lines={len(raw)} distinct={len(E_set)} loops={edge_loops}")

adjE = [[] for _ in range(N)]
for a, b in E_set:
    adjE[a].append(b)
    adjE[b].append(a)
degE = [len(x) for x in adjE]
check("edge_file_all_degree_4", all(d == DEG for d in degE),
      f"degree_hist={ {d: degE.count(d) for d in set(degE)} }")

# ---------------------------------------------------------------- Haar map (SPEC, Haar numbering)
# element (a, j): idx = a*K + j; side A vertex idx -> lift j*M + (R^-j a mod M);
# side B vertex N + idx -> (K + j)*M + (R^-j a mod M).
inv_pow = [pow(R, -j, M) for j in range(K)]          # R^(-j) mod M
assert (R * 2069) % M == 1                            # sanity: 2069 = R^-1 mod M


def haar_to_lift(vid):
    side, idx = divmod(vid, HALF)                     # side 0 = A, 1 = B
    a, j = divmod(idx, K)
    w = K * side + j
    return w * M + (inv_pow[j] * a) % M


img = [haar_to_lift(v) for v in range(N)]
bij = len(set(img)) == N and min(img) == 0 and max(img) == N - 1
check("haar_map_is_bijection_on_vertices", bij, f"distinct_images={len(set(img))}")

mapped = set()
for a, b in E:
    p, q = img[a], img[b]
    mapped.add((p, q) if p < q else (q, p))
ok_map = len(mapped) == len(E) and mapped == L
check("mapped_edge_file_equals_lift_edge_set", ok_map,
      f"mapped={len(mapped)} lift={len(L)} equal={mapped == L}")
check("haar_map_sends_identities_0_and_HALF_to_themselves", img[0] == 0 and img[HALF] == HALF,
      f"img[0]={img[0]} img[HALF]={img[HALF]}")

# ---------------------------------------------------------------- bipartiteness
adjL = [list(s) for s in adj]


def two_colour(adjl):
    colour = [-1] * N
    for s in range(N):
        if colour[s] >= 0:
            continue
        colour[s] = 0
        stack = [s]
        while stack:
            v = stack.pop()
            for u in adjl[v]:
                if colour[u] < 0:
                    colour[u] = 1 - colour[v]
                    stack.append(u)
                elif colour[u] == colour[v]:
                    return False
    return True


check("bipartite_lift_BFS_2colouring", two_colour(adjL))
check("bipartite_edge_file_BFS_2colouring", two_colour(adjE))


# ---------------------------------------------------------------- BFS
def bfs(adjl, src):
    dist = [-1] * N
    dist[src] = 0
    q = [src]
    i = 0
    while i < len(q):
        v = q[i]
        i += 1
        dv = dist[v] + 1
        for u in adjl[v]:
            if dist[u] < 0:
                dist[u] = dv
                q.append(u)
    return dist, len(q), dist[q[-1]]


dist0E, reach0E, ecc0E = bfs(adjE, 0)
distNE, reachNE, eccNE = bfs(adjE, HALF)   # Haar N = M*K = 96191 is the B-side identity
check("edge_file_connected", reach0E == N and reachNE == N, f"reached={reach0E},{reachNE}")
diamE = max(ecc0E, eccNE)
check("edge_file_diameter_exactly_13", diamE == D,
      f"ecc(vertex 0)={ecc0E} ecc(vertex HALF={HALF})={eccNE}")
profile0 = [0] * (ecc0E + 1)
for d in dist0E:
    profile0[d] += 1
say("distance profile from vertex 0 (edge file):", profile0)

rng = random.Random(20260701)
cands = [v for v in range(N) if v != 0 and v != HALF]
sample = rng.sample(cands, 50)
eccs = []
conn_ok = True
for s in sample:
    _, rch, e = bfs(adjE, s)
    eccs.append(e)
    conn_ok = conn_ok and rch == N
sample_ok = conn_ok and max(eccs) <= D
check("random_50_sources_ecc_le_13", sample_ok,
      f"max={max(eccs)} min={min(eccs)} on_A_side={sum(1 for s in sample if s < HALF)}")

# lift-level BFS from lift vertices 0 and N, compared with the edge-file distances under the map
distL0, reachL0, eccL0 = bfs(adjL, 0)
distLN, reachLN, eccLN = bfs(adjL, HALF)
agree = all(distL0[img[v]] == dist0E[v] and distLN[img[v]] == distNE[v] for v in range(N))
check("lift_BFS_from_0_and_HALF_matches_edge_file_under_map", agree and reachL0 == N and reachLN == N,
      f"lift ecc(0)={eccL0} lift ecc(HALF)={eccLN}")
check("lift_diameter_exactly_13", max(eccL0, eccLN) == D, f"max={max(eccL0, eccLN)}")

# ---------------------------------------------------------------- verdict
failed = [name for name, ok in results if not ok]
score = 1 if not failed else 0
say("SUMMARY checks=%d failed=%s" % (len(results), failed if failed else "none"))
say("SCORE", score)
logf.close()
