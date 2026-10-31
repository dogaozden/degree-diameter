"""Quotient state (fixsa format) of a cubic bipartite graph with an order-3 automorphism s.
usage: quot.py EDGES AUTS_FILE INDEX OUT_STATE
AUTS_FILE: first line n, then one permutation per line (from auts.py). INDEX selects the permutation (0-based)."""
import sys
from collections import deque

def read_graph(path):
    with open(path) as f:
        toks = f.read().split()
    n = int(toks[0])
    N = [[] for _ in range(n)]
    for i in range(1, len(toks), 2):
        a, b = int(toks[i]), int(toks[i + 1])
        N[a].append(b); N[b].append(a)
    return n, N

def main():
    edges, autf, idx, outp = sys.argv[1], sys.argv[2], int(sys.argv[3]), sys.argv[4]
    n, N = read_graph(edges)
    with open(autf) as f:
        lines = f.read().split("\n")
    perm = list(map(int, lines[1 + idx].split()))
    s = perm
    s2 = [s[s[v]] for v in range(n)]
    assert all(s2[s[v]] == s[s2[v]] for v in range(n))
    assert all(s[s[s[v]]] == v for v in range(n)), "not order 3"
    col = [-1] * n; col[0] = 0; dq = deque([0])
    while dq:
        x = dq.popleft()
        for y in N[x]:
            if col[y] < 0:
                col[y] = 1 - col[x]; dq.append(y)
    # orbits
    orb_id = [-1] * n; pw = [0] * n; reps = []; fixed = []
    for v in range(n):
        if orb_id[v] >= 0: continue
        o = [v, s[v], s2[v]]
        if s[v] == v:
            orb_id[v] = -2 - len(fixed); fixed.append(v); continue
        k = len(reps); reps.append(v)
        for i in range(3):
            orb_id[o[i]] = k; pw[o[i]] = i
    # regular orbit index on each side: reps with colour
    A_reps = [r for r in reps if col[r] == 0]
    B_reps = [r for r in reps if col[r] == 1]
    A_index = {r: i for i, r in enumerate(A_reps)}
    B_index = {r: i for i, r in enumerate(B_reps)}
    def aorb(v):   # A regular orbit index of vertex v
        return A_index[reps[orb_id[v]]]
    def borb(v):
        return B_index[reps[orb_id[v]]]
    A_fixed = [v for v in fixed if col[v] == 0]
    B_fixed = [v for v in fixed if col[v] == 1]
    FA, FB = len(A_fixed), len(B_fixed)
    qa, qb, qt = [], [], []
    fb_att = {}
    for r in A_reps:
        ao = A_index[r]
        for w in N[r]:
            if orb_id[w] >= 0:            # regular
                qa.append(ao); qb.append(borb(w)); qt.append(pw[w])
            else:
                fb_att[w] = ao
    fa_att = []
    for f in A_fixed:
        bos = set(borb(w) for w in N[f])
        assert len(bos) == 1, "fixed vertex not adjacent to one orbit"
        fa_att.append(bos.pop())
    fb_list = [fb_att[w] for w in B_fixed]
    E = len(qa)
    assert 3 * len(A_reps) == E + FB and 3 * len(B_reps) == E + FA, "slot count mismatch"
    with open(outp, "w") as f:
        f.write("%d %d\n%d\n" % (FA, FB, E))
        for a, b, t in zip(qa, qb, qt):
            f.write("%d %d %d\n" % (a, b, t))
        for x in fa_att: f.write("%d\n" % x)
        for x in fb_list: f.write("%d\n" % x)
    m = len(A_reps) * 3 + FA
    print("state written: m=%d FA=%d FB=%d AR=%d BR=%d E=%d -> %s" % (m, FA, FB, len(A_reps), len(B_reps), E, outp))

main()
