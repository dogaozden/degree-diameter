#!/usr/bin/env python3
"""Card c1 of round lean-cyc-r1: independent check of lean/BipartiteDD/Haar/CycLift/N3400.lean.

Stdlib only, one thread. Parses outA3400 from the Lean text, builds the lift with the
formula  nbrs(v) = [ (u*m + (x+beta) % m) % n  for (u,beta) in outA[v//m] ],  x = v % m,
takes the symmetric closure without loops, and compares it with the edge file.
Checks: parse/shape, simple + degree 3, edge file == lift, bipartite (BFS 2-colouring and
the Lean side3400 colouring), all-pairs BFS diameter == 13 (connected).
"""
import gzip
import re
import sys
import time
from collections import Counter, deque

REPO = "/home/user/degree-diameter"
LEAN = REPO + "/lean/BipartiteDD/Haar/CycLift/N3400.lean"
EDGES = REPO + "/research/frontier/beyond/graphs/d3D13_n3400_lift_gp10_Z170.edges.gz"
N, M, DEG, D = 3400, 170, 3, 13

failed = []


def check(name, ok, detail=""):
    print(("PASS " if ok else "FAIL ") + name + ((" :: " + detail) if detail else ""), flush=True)
    if not ok:
        failed.append(name)
    return ok


def parse_lean(text):
    start = text.index("def outA3400")
    end = text.index("/--", start)
    block = text[start:end]
    rows = re.findall(r"\[((?:\s*\(\s*\d+\s*,\s*\d+\s*\)\s*,?)+)\s*\]", block)
    outA = []
    for r in rows:
        outA.append([(int(a), int(b)) for a, b in re.findall(r"\(\s*(\d+)\s*,\s*(\d+)\s*\)", r)])
    # Lean colouring side3400 : List Bool
    s0 = text.index("def side3400")
    s1 = text.index("]", s0)
    side_txt = text[s0:s1]
    side = [t == "true" for t in re.findall(r"\b(true|false)\b", side_txt)]
    return outA, side


def main():
    t0 = time.time()
    text = open(LEAN, encoding="utf-8").read()
    outA, side = parse_lean(text)
    b = len(outA)
    check("parse: outA3400 has 20 rows", b == 20, "rows=%d" % b)
    check("parse: each row has 3 arcs", all(len(r) == 3 for r in outA),
          "row lengths=%s" % sorted(Counter(len(r) for r in outA).items()))
    check("shape: n == b*m", N == b * M, "n=%d b=%d m=%d" % (N, b, M))
    check("shape: all u < b and beta < m",
          all(u < b and beta < M for r in outA for (u, beta) in r))
    check("parse: side3400 has 20 entries", len(side) == b, "len=%d" % len(side))

    # ---- lift: directed arcs (v -> t) exactly as Lean nbrs ----
    arcs = []
    for v in range(N):
        w, x = divmod(v, M)
        for (u, beta) in outA[w]:
            arcs.append((v, (u * M + (x + beta) % M) % N))
    loops_raw = sum(1 for v, t in arcs if v == t)
    print("info: directed arcs=%d, raw loops=%d" % (len(arcs), loops_raw), flush=True)

    # per-vertex out-list must have no loop and no repeat (so no parallel arcs)
    out_lists = [[] for _ in range(N)]
    for v, t in arcs:
        out_lists[v].append(t)
    out_ok = all(len(set(l)) == len(l) and v not in l for v, l in enumerate(out_lists))
    check("simple: each out-list is loop-free with distinct targets", out_ok)

    # symmetric closure without loops
    adj = [set() for _ in range(N)]
    for v, t in arcs:
        if v != t:
            adj[v].add(t)
            adj[t].add(v)
    check("simple: no loop in symmetric closure", all(v not in adj[v] for v in range(N)))
    sym = {(min(v, t), max(v, t)) for v in range(N) for t in adj[v]}
    check("lift: symmetric edge count == 5100 (3400*3/2)", len(sym) == N * DEG // 2, "|E|=%d" % len(sym))
    degs = Counter(len(adj[v]) for v in range(N))
    check("degree: every vertex has exactly 3 neighbours", degs == Counter({DEG: N}), "degree counts=%s" % dict(degs))

    # ---- edge file ----
    with gzip.open(EDGES, "rt") as f:
        lines = f.read().split("\n")
    hdr = int(lines[0].strip())
    check("edge file: first line is n=3400", hdr == N, "header=%d" % hdr)
    fe_raw = []
    for line in lines[1:]:
        if line.strip():
            a, c = line.split()
            fe_raw.append((int(a), int(c)))
    file_loops = sum(1 for a, c in fe_raw if a == c)
    file_set = {(min(a, c), max(a, c)) for a, c in fe_raw if a != c}
    check("edge file: 5100 edge lines, no loops, no duplicates",
          len(fe_raw) == 5100 and file_loops == 0 and len(file_set) == len(fe_raw),
          "lines=%d loops=%d distinct=%d" % (len(fe_raw), file_loops, len(file_set)))
    only_lift = sym - file_set
    only_file = file_set - sym
    check("edge file == lift edge set", sym == file_set,
          "only_in_lift=%d only_in_file=%d" % (len(only_lift), len(only_file)))
    check("vertices in edge file all in 0..n-1", all(0 <= a < N and 0 <= c < N for a, c in fe_raw))

    # ---- bipartite: BFS 2-colouring on the lift ----
    col = [-1] * N
    bip = True
    for s in range(N):
        if col[s] != -1:
            continue
        col[s] = 0
        dq = deque([s])
        while dq and bip:
            v = dq.popleft()
            for t in adj[v]:
                if col[t] == -1:
                    col[t] = 1 - col[v]
                    dq.append(t)
                elif col[t] == col[v]:
                    bip = False
                    break
    check("bipartite: BFS 2-colouring exists", bip)
    side_ok = all(side[v // M] != side[t // M] for v, t in sym)
    check("bipartite: Lean side3400 (by base vertex) is a proper colouring", side_ok)

    # ---- diameter: BFS from every vertex on the edge-file graph (= lift) ----
    nbr = [sorted(adj[v]) for v in range(N)]
    ecc_max = 0
    ecc_min = 10 ** 9
    disconnected = False
    for s in range(N):
        dist = [-1] * N
        dist[s] = 0
        dq = deque([s])
        seen = 1
        last = 0
        while dq:
            v = dq.popleft()
            dv = dist[v] + 1
            for t in nbr[v]:
                if dist[t] == -1:
                    dist[t] = dv
                    seen += 1
                    last = dv
                    dq.append(t)
        if seen != N:
            disconnected = True
            break
        ecc_max = max(ecc_max, last)
        ecc_min = min(ecc_min, last)
    check("connected: BFS from every vertex reaches all 3400 vertices", not disconnected)
    check("diameter: max eccentricity == %d (all-pairs BFS)" % D, ecc_max == D,
          "diameter=%d radius=%d" % (ecc_max, ecc_min))

    print("time: %.1fs" % (time.time() - t0), flush=True)
    score = 1 if not failed else 0
    print("FAILED: %s" % (failed if failed else "none"))
    print("SCORE %d" % score)
    return score


if __name__ == "__main__":
    sys.exit(0 if main() == 1 else 1)
