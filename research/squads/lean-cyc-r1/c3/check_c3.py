#!/usr/bin/env python3
"""Card c3 of squad lean-cyc-r1: independent check of N30334.lean (degree 4, diameter 11).

Written from research/squads/lean-cyc-r1/SPEC.md only. Lean semantics:
  outA30334 rows give arcs (u, beta) per base vertex w; lift vertex v = w*M + x,
  neighbour (u*M + (x+beta) % M) % n, symmetric closure, no loops.
  Haar numbering (M=523, K=29, R=9): edge-file vertex v < N is side A element (a, j) with
  a = (v // K), j = v % K; lift image j*M + (R^-j * a mod M). v >= N is side B, image (K+j)*M + ...
"""
import gzip
import json
import random
import re
import sys
from collections import deque

import numpy as np

LEAN = "/home/user/degree-diameter/lean/BipartiteDD/Haar/CycLift/N30334.lean"
EDGES = "/home/user/degree-diameter/research/lean-haarD/cyclift/d4D11_n30334_meta523_29_9.edges.gz"
OUT = "/home/user/degree-diameter/research/squads/lean-cyc-r1/c3/result.json"

M, K, R = 523, 29, 9
NB = 58                 # base vertices (rows of outA)
NV = NB * M             # 30334
N = M * K               # 15167 vertices per side
DEG = 4
D_STATED = 11

results = {}
fails = []


def check(name, ok, detail=""):
    results[name] = {"ok": bool(ok), "detail": str(detail)}
    if not ok:
        fails.append(name)
    print(("PASS " if ok else "FAIL ") + name + ((" :: " + str(detail)) if detail != "" else ""), flush=True)


# ---------- 1. parse outA from the Lean text ----------
def parse_outA():
    text = open(LEAN, encoding="utf-8").read()
    s = text.index("def outA30334")
    e = text.index("def side30334")
    block = text[s:e]
    rows = []
    for m in re.finditer(r"\[((?:\s*\(\s*\d+\s*,\s*\d+\s*\)\s*,?)+)\s*\]", block):
        rows.append([(int(a), int(b)) for a, b in re.findall(r"\(\s*(\d+)\s*,\s*(\d+)\s*\)", m.group(1))])
    return rows


rows = parse_outA()
check("parse_58_rows", len(rows) == NB, f"rows={len(rows)}")
check("parse_4_arcs_per_row", all(len(r) == DEG for r in rows), f"lens={sorted(set(len(r) for r in rows))}")
check("parse_ranges", all(0 <= u < NB and 0 <= b < M for r in rows for (u, b) in r))


# ---------- lift graph (symmetric closure, no loops) ----------
def lift_adj():
    adj = [set() for _ in range(NV)]
    loops = 0
    dup_raw = 0
    for v in range(NV):
        w, x = divmod(v, M)
        seen = set()
        for (u, beta) in rows[w]:
            t = (u * M + (x + beta) % M) % NV
            if t in seen:
                dup_raw += 1
            seen.add(t)
            if t == v:
                loops += 1
                continue
            adj[v].add(t)
            adj[t].add(v)
    return adj, loops, dup_raw


ladj, loops, dup_raw = lift_adj()
check("lift_no_loops", loops == 0, f"loops={loops}")
check("lift_no_dup_raw_arcs", dup_raw == 0, f"dup_raw={dup_raw}")
degs = [len(s) for s in ladj]
check("lift_degree_exactly_4", all(d == DEG for d in degs), f"degset={sorted(set(degs))}")
lift_edges = set()
for v in range(NV):
    for t in ladj[v]:
        if v < t:
            lift_edges.add((v, t))
check("lift_edge_count", len(lift_edges) == NV * DEG // 2, f"edges={len(lift_edges)}")


# ---------- 2. edge file and Haar map ----------
with gzip.open(EDGES, "rt") as f:
    header = f.readline().split()
    n_file = int(header[0]) if len(header) == 1 else -1
    file_edges = []
    for line in f:
        p = line.split()
        file_edges.append((int(p[0]), int(p[1])))
check("edge_file_header_n", n_file == NV and len(header) == 1, f"n={n_file}")
check("edge_file_count", len(file_edges) == NV * DEG // 2, f"count={len(file_edges)}")
check("edge_file_in_range", all(0 <= a < NV and 0 <= b < NV for a, b in file_edges))
check("edge_file_no_loops", all(a != b for a, b in file_edges))
file_undirected = {(min(a, b), max(a, b)) for a, b in file_edges}
check("edge_file_no_dups", len(file_undirected) == len(file_edges), f"unique={len(file_undirected)}")

RINV = pow(R, -1, M)
check("Rinv_is_465", RINV == 465, f"R^-1 mod M={RINV}")


def haar_map(v):
    side_b = v >= N
    u = v - N if side_b else v
    a, j = divmod(u, K)
    y = (pow(RINV, j, M) * a) % M          # R^(-j) * a mod M
    w = (K + j) if side_b else j
    return w * M + y


# R^(-j) is the inverse of R^j: cross-check the two ways of computing it
check("Rminusj_consistent",
      all(pow(RINV, j, M) == pow(pow(R, j, M), -1, M) for j in range(K)))

images = [haar_map(v) for v in range(NV)]
check("map_is_bijection", len(set(images)) == NV and min(images) == 0 and max(images) == NV - 1,
      f"distinct={len(set(images))}")

mapped = set()
for a, b in file_edges:
    x, y = haar_map(a), haar_map(b)
    mapped.add((min(x, y), max(x, y)))
check("mapped_edges_equal_lift_edges", mapped == lift_edges,
      f"mapped={len(mapped)} lift={len(lift_edges)} onlymapped={len(mapped - lift_edges)} "
      f"onlylift={len(lift_edges - mapped)}")


# ---------- 3. degree of the file graph and bipartiteness ----------
fadj = [[] for _ in range(NV)]
for a, b in file_edges:
    fadj[a].append(b)
    fadj[b].append(a)
check("file_degree_exactly_4", all(len(x) == DEG for x in fadj),
      f"degset={sorted(set(len(x) for x in fadj))}")


def two_colour(adj):
    col = [-1] * NV
    for s in range(NV):
        if col[s] != -1:
            continue
        col[s] = 0
        q = deque([s])
        while q:
            v = q.popleft()
            for t in adj[v]:
                if col[t] == -1:
                    col[t] = 1 - col[v]
                    q.append(t)
                elif col[t] == col[v]:
                    return None
    return col


fcol = two_colour(fadj)
check("file_graph_bipartite", fcol is not None)
lcol = two_colour([list(s) for s in ladj])
check("lift_bipartite", lcol is not None)
if fcol is not None:
    sideA_ok = all(fcol[v] == fcol[0] for v in range(N)) and all(fcol[v] != fcol[0] for v in range(N, NV))
    check("file_bipartition_is_sides", sideA_ok, f"classes={sum(1 for c in fcol if c == 0)}/{sum(1 for c in fcol if c == 1)}")


# ---------- 4. diameter ----------
def bfs(adj, s):
    dist = [-1] * NV
    dist[s] = 0
    q = deque([s])
    while q:
        v = q.popleft()
        dv = dist[v] + 1
        for t in adj[v]:
            if dist[t] < 0:
                dist[t] = dv
                q.append(t)
    return dist


def ecc(adj, s):
    d = bfs(adj, s)
    if min(d) < 0:
        return None
    return max(d)


e0 = ecc(fadj, 0)
eN = ecc(fadj, N)
check("connected_from_0_and_N", e0 is not None and eN is not None, f"ecc0={e0} eccN={eN}")
check("max_ecc_0_N_equals_D", e0 is not None and eN is not None and max(e0, eN) == D_STATED,
      f"ecc0={e0} eccN={eN} stated={D_STATED}")

rng = random.Random(20261101)
pool = [v for v in range(NV) if v not in (0, N)]
samp = rng.sample(pool, 50)
samp_eccs = [ecc(fadj, s) for s in samp]
check("random50_all_le_D", all(e is not None and e <= D_STATED for e in samp_eccs),
      f"max={max(e for e in samp_eccs if e is not None)} min={min(e for e in samp_eccs if e is not None)}")

# extra: exact all-pairs diameter by bit-parallel BFS (every source at once)
nb = np.array(fadj, dtype=np.int64)
W = (NV + 63) // 64
reach = np.zeros((NV, W), dtype=np.uint64)
idx = np.arange(NV)
reach[idx, idx // 64] = np.uint64(1) << (idx % 64).astype(np.uint64)
full = np.full(W, np.uint64(0xFFFFFFFFFFFFFFFF), dtype=np.uint64)
rem = NV - 64 * (W - 1)
full[-1] = np.uint64((1 << rem) - 1)
k = 0
exact_diam = None
while k <= 40:
    if bool((reach == full[None, :]).all()):
        exact_diam = k
        break
    new = reach.copy()
    for i in range(DEG):
        new |= reach[nb[:, i]]
    reach = new
    k += 1
    del new
check("all_pairs_exact_diameter_equals_D", exact_diam == D_STATED, f"exact_diameter={exact_diam}")

# ---------- summary ----------
score = 1 if not fails else 0
summary = {
    "card": "c3",
    "file": "N30334.lean",
    "edges": EDGES,
    "stated": {"degree": DEG, "diameter": D_STATED, "M": M, "K": K, "R": R},
    "score": score,
    "failed": fails,
    "ecc_from_0": e0,
    "ecc_from_N": eN,
    "all_pairs_exact_diameter": exact_diam,
    "checks": results,
}
with open(OUT, "w", encoding="utf-8") as fh:
    json.dump(summary, fh, indent=1)
print("SCORE", score, "FAILED", fails, flush=True)
sys.exit(0)
