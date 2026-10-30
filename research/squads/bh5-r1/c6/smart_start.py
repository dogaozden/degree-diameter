#!/usr/bin/env python3
"""Smart surgery start for (5,5): take a 5-regular bipartite record graph, add one vertex pair (x on side B, y on side A)
by deleting a set of edges and rewiring, and choose the deletion set by simulated annealing on the far-pair count.
mode 5: delete a 5-matching (a_i,b_i); x~a_i, y~b_i (degrees stay 5, x and y not adjacent).
mode 4: delete a 4-matching; x~y, x~a_i, y~b_i (i=1..4).
usage: smart_start.py IN_EDGES OUT_EDGES MODE SEED EVALS
"""
import random, sys
import numpy as np

inp, out, mode, seed, evals = sys.argv[1], sys.argv[2], int(sys.argv[3]), int(sys.argv[4]), int(sys.argv[5])
random.seed(seed)
D = 5
lines = [l for l in open(inp) if l.strip()]
n = int(lines[0]); E = [tuple(map(int, l.split()[:2])) for l in lines[1:]]
adj = [set() for _ in range(n)]
for u, v in E: adj[u].add(v); adj[v].add(u)
col = [-1] * n; col[0] = 0; st = [0]
while st:
    x = st.pop()
    for y in adj[x]:
        if col[y] < 0: col[y] = 1 - col[x]; st.append(y)
EA = sorted((u, v) if col[u] == 0 else (v, u) for u, v in E)   # (a in side A, b in side B)
K = 5 if mode == 5 else 4
N = n + 2
x, y = n, n + 1          # x: side B (adjacent to A-vertices), y: side A

def build(dele):
    """edge set of the new graph for deletion set dele (list of (a,b))."""
    S = set(EA)
    for (a, b) in dele: S.discard((a, b))
    for (a, b) in dele:
        pass
    ed = set(S)
    A_ends = [a for a, b in dele]; B_ends = [b for a, b in dele]
    for a in A_ends: ed.add((a, x))
    for b in B_ends: ed.add((y, b))
    if mode == 4:
        ed.discard((A_ends[0], x)); ed.discard((y, B_ends[0]))  # placeholder, fixed below
        ed = set(S)
        for a in A_ends: ed.add((a, x))
        for b in B_ends: ed.add((y, b))
        ed.add((y, x))
    return ed

def ok(dele):
    A_ends = [a for a, b in dele]; B_ends = [b for a, b in dele]
    return len(set(A_ends)) == K and len(set(B_ends)) == K

def far(ed):
    M = np.zeros((N, N), dtype=np.float32)
    for u, v in ed:
        M[u, v] = 1; M[v, u] = 1
    I = np.eye(N, dtype=np.float32)
    R = I + M
    P = I.copy()
    for _ in range(D):
        P = (P @ R > 0).astype(np.float32)
    return int(N * N - P.sum())

def cost(dele):
    return far(build(dele))

def random_set():
    while True:
        cand = random.sample(EA, K * 20)
        dele = []; ua = set(); ub = set()
        for (a, b) in cand:
            if a in ua or b in ub: continue
            dele.append((a, b)); ua.add(a); ub.add(b)
            if len(dele) == K: break
        if len(dele) == K: return dele

best_global = None
T0, T1 = 3.0, 0.2
cur = random_set(); cc = cost(cur)
best = (cc, list(cur))
tries = 0
while tries < evals:
    T = T0 * (T1 / T0) ** (tries / max(1, evals))
    i = random.randrange(K)
    cand_edge = random.choice(EA)
    new = list(cur); new[i] = cand_edge
    if not ok(new) or cand_edge in cur: tries += 1; continue
    nc = cost(new); tries += 1
    if nc <= cc or random.random() < np.exp(-(nc - cc) / T):
        cur, cc = new, nc
        if cc < best[0]:
            best = (cc, list(cur))
            print(f"try {tries} best {best[0]}", file=sys.stderr)
bc, bd = best
ed = build(bd)
with open(out, 'w') as f:
    f.write(f"{N}\n")
    for u, v in sorted(ed): f.write(f"{u} {v}\n")
print(f"mode {mode} seed {seed} start far pairs {bc} deleted {bd} edges {len(ed)}")
