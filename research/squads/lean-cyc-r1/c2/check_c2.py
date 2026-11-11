#!/usr/bin/env python3
"""Card c2: independent check of lean/BipartiteDD/Haar/CycLift/N5706.lean (stated degree 3, diameter 14).

Checks (SPEC checks 1-4 for a lift):
 1. Parse outA5706 from the .lean text; build the lift (vertex v = w*317 + x, neighbours (u*317 + (x+b)%317) % 5706);
    symmetric closure without loops; simple; every vertex has degree exactly 3.
 2. Lift edge set == edge-file edge set (edge file: first line n, then "a b" per edge, gzip).
 3. Bipartite (BFS 2-colouring); also checks the side5706 list from the file is a proper 2-colouring.
 4. Diameter: BFS from every vertex of the edge-file graph; graph connected; max eccentricity must be exactly 14.
"""
import gzip
import json
import re
import time
from collections import Counter

LEAN = "/home/user/degree-diameter/lean/BipartiteDD/Haar/CycLift/N5706.lean"
EDGES = ("/home/user/degree-diameter/research/frontier/beyond/graphs/"
         "d3D14_n5706_lift_pappus_Z317.edges.gz")
M = 317
B = 18
N = 5706
DEG = 3
DIAM = 14


def parse_lean(path):
    txt = open(path, encoding="utf-8").read()
    i = txt.index("def outA5706")
    j = txt.index("/--", i)
    block = txt[i:j]
    row_txts = re.findall(r"\[((?:\s*\(\s*\d+\s*,\s*\d+\s*\)\s*,?)+)\s*\]", block)
    rows = [[(int(a), int(b)) for a, b in re.findall(r"\(\s*(\d+)\s*,\s*(\d+)\s*\)", r)] for r in row_txts]
    k = txt.index("def side5706")
    line = txt[k:txt.index("\n", k)]
    side_txt = re.search(r"\[(.*)\]", line).group(1)
    side = [s.strip() == "true" for s in side_txt.split(",")]
    return rows, side


def lift_arcs(rows):
    """Directed arcs (v, t) exactly as the Lean liftGraph formula produces them (loops kept for inspection)."""
    n = len(rows) * M
    arcs = []
    for v in range(n):
        w, x = divmod(v, M)
        for u, beta in rows[w]:
            t = (u * M + (x + beta) % M) % n
            arcs.append((v, t))
    return arcs


def read_edges(path):
    with gzip.open(path, "rt") as f:
        lines = f.read().split("\n")
    n = int(lines[0])
    es = []
    for ln in lines[1:]:
        if ln.strip() == "":
            continue
        a, b = ln.split()
        es.append((int(a), int(b)))
    return n, es


def bfs_ecc(adj, s, n):
    dist = [-1] * n
    dist[s] = 0
    q = [s]
    head = 0
    while head < len(q):
        v = q[head]
        head += 1
        dv = dist[v] + 1
        for t in adj[v]:
            if dist[t] < 0:
                dist[t] = dv
                q.append(t)
    if len(q) != n:
        return -1
    return dist[q[-1]]


def main():
    t0 = time.time()
    res = {"card": "c2", "file": "N5706.lean", "n": N, "m": M, "D_stated": DIAM, "deg_stated": DEG}

    # ---- 1. parse Lean data and build the lift
    rows, side = parse_lean(LEAN)
    res["lean_rows"] = len(rows)
    res["lean_row_lengths"] = sorted(Counter(len(r) for r in rows).items())
    res["lean_side_len"] = len(side)
    assert len(rows) == B, len(rows)
    n_lift = len(rows) * M
    assert n_lift == N

    arcs = lift_arcs(rows)
    res["raw_arcs"] = len(arcs)
    res["raw_loops"] = sum(1 for v, t in arcs if v == t)
    raw_out_sets = [set() for _ in range(N)]
    for v, t in arcs:
        raw_out_sets[v].add(t)
    res["raw_outdeg_distinct_all_3"] = all(len(s) == DEG for s in raw_out_sets)
    arcset = set(arcs)
    res["raw_arcs_symmetric"] = all((t, v) in arcset for v, t in arcs)

    lift_nb = [set() for _ in range(N)]
    for v, t in arcs:
        if v != t:
            lift_nb[v].add(t)
            lift_nb[t].add(v)
    deg_hist = Counter(len(s) for s in lift_nb)
    res["lift_degree_hist"] = sorted(deg_hist.items())
    res["lift_degree_all_stated"] = all(len(s) == DEG for s in lift_nb)
    lift_edges = set()
    for v in range(N):
        for t in lift_nb[v]:
            lift_edges.add((min(v, t), max(v, t)))
    res["lift_undirected_edges"] = len(lift_edges)
    res["lift_simple_no_loops"] = res["raw_loops"] == 0 and res["lift_degree_all_stated"]

    # ---- 2. edge file vs lift
    n_file, file_edges_list = read_edges(EDGES)
    res["edgefile_n"] = n_file
    res["edgefile_lines_edges"] = len(file_edges_list)
    assert n_file == N
    file_edge_set = set()
    dup = 0
    bad_range = 0
    loops_file = 0
    for a, b in file_edges_list:
        if not (0 <= a < N and 0 <= b < N):
            bad_range += 1
            continue
        if a == b:
            loops_file += 1
            continue
        key = (min(a, b), max(a, b))
        if key in file_edge_set:
            dup += 1
        file_edge_set.add(key)
    res["edgefile_duplicates"] = dup
    res["edgefile_out_of_range"] = bad_range
    res["edgefile_loops"] = loops_file
    res["edgefile_unique_edges"] = len(file_edge_set)
    res["lift_eq_edgefile"] = lift_edges == file_edge_set
    res["lift_minus_file"] = len(lift_edges - file_edge_set)
    res["file_minus_lift"] = len(file_edge_set - lift_edges)

    # adjacency from the edge file (the graph whose diameter is measured)
    adj = [[] for _ in range(N)]
    for a, b in file_edge_set:
        adj[a].append(b)
        adj[b].append(a)
    file_deg = Counter(len(x) for x in adj)
    res["edgefile_degree_hist"] = sorted(file_deg.items())
    res["edgefile_degree_all_stated"] = all(len(x) == DEG for x in adj)

    # ---- 3. bipartite
    color = [-1] * N
    color[0] = 0
    q = [0]
    head = 0
    while head < len(q):
        v = q[head]
        head += 1
        for t in adj[v]:
            if color[t] < 0:
                color[t] = 1 - color[v]
                q.append(t)
            elif color[t] == color[v]:
                res["bipartite_conflict"] = [v, t]
    res["connected_colouring_reach"] = len(q)
    bip_ok = len(q) == N and all(color[a] != color[b] for a, b in file_edge_set)
    res["bipartite_2colouring_ok"] = bip_ok
    # side5706 from the Lean file as a proper 2-colouring
    # side is indexed by base vertex w; lift vertex v has base vertex v // M
    side_ok = all(side[a // M] != side[b // M] for a, b in file_edge_set)
    res["lean_side5706_is_proper_colouring"] = side_ok
    res["side5706_true_count"] = sum(side)

    # ---- 4. diameter: BFS from every vertex
    t1 = time.time()
    ecc_hist = Counter()
    disconnected = 0
    max_ecc = -1
    for s in range(N):
        e = bfs_ecc(adj, s, N)
        if e < 0:
            disconnected += 1
            continue
        ecc_hist[e] += 1
        if e > max_ecc:
            max_ecc = e
    res["bfs_sources"] = N
    res["disconnected_sources"] = disconnected
    res["ecc_hist"] = sorted(ecc_hist.items())
    res["max_ecc_diameter"] = max_ecc
    res["bfs_seconds"] = round(time.time() - t1, 1)

    checks = {
        "n_5706": n_lift == N,
        "simple_no_loops": res["lift_simple_no_loops"] and res["raw_outdeg_distinct_all_3"],
        "degree_3_all_vertices": res["lift_degree_all_stated"] and res["edgefile_degree_all_stated"],
        "lift_eq_edgefile": res["lift_eq_edgefile"] and res["edgefile_duplicates"] == 0
                             and res["edgefile_loops"] == 0 and res["edgefile_out_of_range"] == 0,
        "bipartite": bip_ok,
        "connected": disconnected == 0,
        "diameter_exactly_14": max_ecc == DIAM,
    }
    res["checks"] = checks
    res["raw_arcs_symmetric_flag"] = res["raw_arcs_symmetric"]
    res["score"] = 1 if all(checks.values()) else 0
    res["failed"] = [k for k, v in checks.items() if not v]
    res["total_seconds"] = round(time.time() - t0, 1)

    out = "/home/user/degree-diameter/research/squads/lean-cyc-r1/c2/result_c2.json"
    with open(out, "w") as f:
        json.dump(res, f, indent=1)
    print(json.dumps(res, indent=1))


if __name__ == "__main__":
    main()
