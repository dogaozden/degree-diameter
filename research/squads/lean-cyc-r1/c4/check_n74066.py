#!/usr/bin/env python3
"""c4: independent check of lean/BipartiteDD/Haar/CycLift/N74066.lean against its edge file.

Lean semantics: outA74066 rows (58 base vertices), lift on n = 58*1277 = 74066 vertices, fibre modulus m = 1277.
Edge file: Haar numbering M=1277, K=29, R=964; (a,j) on side A -> j*M + R^-j*a, side B -> (K+j)*M + R^-j*a.
Checks: parse, lift simple/no loops/4-regular, edge file simple/4-regular, map is a bijection and sends
edge file onto lift edge set, bipartite (BFS 2-colouring + explicit sides), diameter 12 from vertices 0 and N,
plus 50 random sanity BFS (all <= 12).
"""
import gzip
import hashlib
import random
import re
import sys
from collections import deque

LEAN = "/home/user/degree-diameter/lean/BipartiteDD/Haar/CycLift/N74066.lean"
EDGES = "/home/user/degree-diameter/research/frontier/beyond/graphs/d4D12_n74066_meta1277_29_964.edges.gz"
N, M, K, R, D, DEG = 74066, 1277, 29, 964, 12, 4
ROWS_EXPECTED = 58
NH = M * K  # 37033, size of each side in Haar numbering
results = {}


def check(name, ok, detail=""):
    results[name] = bool(ok)
    print(f"{'PASS' if ok else 'FAIL'} {name} {detail}".rstrip(), flush=True)


def parse_lean(path):
    txt = open(path, encoding="utf-8").read()
    i = txt.index("def outA74066")
    j = txt.index("/-- Side A", i)
    block = txt[i:j]
    rows = []
    for mt in re.finditer(r"\[((?:\(\d+, \d+\)(?:, )?)+)\]", block):
        rows.append([(int(a), int(b)) for a, b in re.findall(r"\((\d+), (\d+)\)", mt.group(1))])
    return rows


def lift(rows, m, n):
    """Arcs of the lift, per the Lean semantics: v = w*m + x, neighbours (u*m + (x+beta)%m) % n."""
    arcs = []
    for w, row in enumerate(rows):
        for x in range(m):
            v = w * m + x
            for u, beta in row:
                arcs.append((v, (u * m + (x + beta) % m) % n))
    return arcs


def read_edges(path):
    with gzip.open(path, "rt") as fh:
        n = int(fh.readline())
        edges = []
        for line in fh:
            parts = line.split()
            if len(parts) == 2:
                edges.append((int(parts[0]), int(parts[1])))
    return n, edges


def bfs(adj, src):
    dist = [-1] * len(adj)
    dist[src] = 0
    q = deque([src])
    while q:
        v = q.popleft()
        dv = dist[v] + 1
        for u in adj[v]:
            if dist[u] < 0:
                dist[u] = dv
                q.append(u)
    return dist


def two_colour(adj):
    col = [-1] * len(adj)
    for s in range(len(adj)):
        if col[s] >= 0:
            continue
        col[s] = 0
        q = deque([s])
        while q:
            v = q.popleft()
            for u in adj[v]:
                if col[u] < 0:
                    col[u] = 1 - col[v]
                    q.append(u)
                elif col[u] == col[v]:
                    return None
    return col


def main():
    # 1. Parse the Lean data and build the lift.
    rows = parse_lean(LEAN)
    check("lean_rows_58", len(rows) == ROWS_EXPECTED, f"rows={len(rows)}")
    check("lean_row_arcs_4", all(len(r) == DEG for r in rows), f"arc_counts={sorted({len(r) for r in rows})}")
    check("lean_n_eq_b_times_m", ROWS_EXPECTED * M == N, f"b*m={ROWS_EXPECTED * M}")
    arcs = lift(rows, M, N)
    loops = sum(1 for v, t in arcs if v == t)
    check("lift_no_loop_arcs", loops == 0, f"loop_arcs={loops}")
    lift_adj = [set() for _ in range(N)]
    for v, t in arcs:
        if v != t:
            lift_adj[v].add(t)
            lift_adj[t].add(v)
    degs = {len(s) for s in lift_adj}
    check("lift_4_regular", degs == {DEG}, f"degree_values={sorted(degs)}")
    lift_edges = set()
    for v in range(N):
        for t in lift_adj[v]:
            lift_edges.add((v, t) if v < t else (t, v))
    check("lift_edge_count", len(lift_edges) == N * DEG // 2, f"edges={len(lift_edges)}")
    lift_adj = [sorted(s) for s in lift_adj]

    # 2. Edge file: simple, 4-regular, right size.
    n_file, edges = read_edges(EDGES)
    check("file_n", n_file == N, f"n={n_file}")
    check("file_edge_count", len(edges) == N * DEG // 2, f"edges={len(edges)}")
    check("file_no_loops", all(a != b for a, b in edges))
    file_set = set()
    for a, b in edges:
        file_set.add((a, b) if a < b else (b, a))
    check("file_simple", len(file_set) == len(edges), f"distinct={len(file_set)}")
    file_adj = [[] for _ in range(N)]
    for a, b in edges:
        file_adj[a].append(b)
        file_adj[b].append(a)
    check("file_4_regular", all(len(x) == DEG for x in file_adj),
          f"degree_values={sorted({len(x) for x in file_adj})}")

    # 3. Haar coordinate map (spec): (a,j) on A -> j*M + R^-j a; on B -> (K+j)*M + R^-j a.
    Rinv = pow(R, -1, M)
    Rinv_pow = [pow(Rinv, j, M) for j in range(K)]
    assert all((R * Rinv) % M == 1 for _ in [0])

    def f(v):
        side, u = (0, v) if v < NH else (1, v - NH)
        a, j = divmod(u, K)
        return (K * side + j) * M + (Rinv_pow[j] * a) % M

    image = [f(v) for v in range(N)]
    check("map_bijection", len(set(image)) == N and min(image) == 0 and max(image) == N - 1)
    mapped = set()
    for a, b in edges:
        x, y = f(a), f(b)
        mapped.add((x, y) if x < y else (y, x))
    check("map_edges_equal_lift", len(mapped) == len(edges) and mapped == lift_edges,
          f"mapped={len(mapped)} lift={len(lift_edges)} missing={len(lift_edges - mapped)} extra={len(mapped - lift_edges)}")

    # 4. Bipartite: BFS 2-colouring, plus the explicit side split of the lift (rows 0..28 vs 29..57).
    col_file = two_colour(file_adj)
    check("file_bipartite_bfs", col_file is not None)
    side_ok = all((v // M >= K) != (t // M >= K) for v, t in arcs if v != t)
    check("lift_sides_explicit", side_ok, "every lift arc joins rows 0..28 and 29..57")
    col_lift = two_colour(lift_adj)
    check("lift_bipartite_bfs", col_lift is not None)

    # 5. Diameter of the edge-file graph: BFS from 0 and N (group transitive on each side).
    d0 = bfs(file_adj, 0)
    dN = bfs(file_adj, NH)  # vertex N in the spec's numbering = first B vertex (index NH here)
    connected = min(d0) >= 0 and min(dN) >= 0
    check("file_connected", connected)
    e0, eN = max(d0), max(dN)
    check("diameter_from_0_is_D", e0 == D, f"ecc(0)={e0}")
    check("diameter_from_N_is_D", eN == D, f"ecc(N)={eN}")
    check("diameter_exact_D", max(e0, eN) == D and connected, f"max_ecc={max(e0, eN)}")

    # 6. Sanity: 50 random BFS sources, all eccentricities <= D.
    rng = random.Random(4)
    srcs = rng.sample([v for v in range(N) if v not in (0, NH)], 50)
    worst = 0
    for s in srcs:
        dist = bfs(file_adj, s)
        if min(dist) < 0:
            worst = 10**9
            break
        worst = max(worst, max(dist))
    check("random50_ecc_le_D", worst <= D, f"max_ecc_over_50={worst}")

    score = int(all(results.values()))
    failed = [k for k, v in results.items() if not v]
    print(f"SCORE {score} failed={failed if failed else 'none'}", flush=True)
    return score


if __name__ == "__main__":
    sys.exit(0 if main() == 1 else 1)
