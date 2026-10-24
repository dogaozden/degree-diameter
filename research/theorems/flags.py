"""Bipartite compatibility graph C(k,q) of Cames van Batenburg-Korsky (arXiv:2608.03965, §3) for k = 2:
V = GF(q)^5.  Odd vertices: partial flags (W1 < W3), even vertices: (W2 < W4) (W_i of dimension i).
(W1,W3) ~ (W2,W4) iff W1 < W2 < W3 < W4, i.e. the four form a complete flag.
(q+1)^2-regular, 2*[5]_q!/(q+1)^2 vertices; Isham-Lakhotia-Monroe-Petrini (arXiv:2608.27253, Thm 6.11) and
CvB-K (Lemma 2.1, odd-even sorting) give diameter 2k+1 = 5.
For q = 3: 16-regular, 31,460 vertices, diameter 5 -- above the (16,5) table value 27,300 (DS14v2).
Writes the edge list (n, then 'u v' lines; odd flags 0..n/2-1, even flags n/2..n-1) and checks the diameter by BFS
from one vertex of each side (GL(5,q) is transitive on each side) and the degrees.
usage: python3 flags.py q OUT.edges
"""
import itertools, sys
from collections import deque


def main():
    q = int(sys.argv[1]); out = sys.argv[2]
    assert q in (2, 3, 5, 7), "prime q only (mod-q arithmetic)"
    n = 5
    pts = [v for v in itertools.product(range(q), repeat=n) if next((c for c in v if c), 0) == 1]
    pidx = {v: i for i, v in enumerate(pts)}

    def norm(v):
        for c in v:
            if c:
                s = pow(c, q - 2, q)
                return tuple(s * x % q for x in v)
        return None

    def span(vecs):
        S = set()
        for coefs in itertools.product(range(q), repeat=len(vecs)):
            v = tuple(sum(c * w[k] for c, w in zip(coefs, vecs)) % q for k in range(n))
            nv = norm(v)
            if nv is not None:
                S.add(pidx[nv])
        return frozenset(S)

    sub = {1: [frozenset([i]) for i in range(len(pts))]}
    # generate with explicit bases instead
    def gen(d):
        res = {}
        for B in itertools.combinations(range(len(pts)), d):
            S = span([pts[i] for i in B])
            if len(S) == (q ** d - 1) // (q - 1):
                res[S] = True
        return list(res)
    # dims 1..4 (dim 4 = hyperplanes via kernels, dims 2,3 by spans; combinations of 3 points is ~ C(121,3) = 288k for q=3)
    sub[2] = gen(2)
    hyper = []
    for f in pts:
        hyper.append(frozenset(i for i, v in enumerate(pts) if sum(a * b for a, b in zip(f, v)) % q == 0))
    sub[4] = hyper
    # 3-spaces = intersections of two distinct hyperplanes
    s3 = set()
    for a in range(len(hyper)):
        for b in range(a + 1, len(hyper)):
            s3.add(hyper[a] & hyper[b])
    sub[3] = list(s3)
    cnt = {d: len(sub[d]) for d in sub}
    print("subspaces", cnt)
    # chambers
    s2_by_pt = {}
    for W in sub[2]:
        for p in W: s2_by_pt.setdefault(p, []).append(W)
    # containment 2 < 3: for each 3-space, its 2-subspaces are intersections with hyperplanes; use point-set subset test
    s2_set = sub[2]
    s3_list = sub[3]
    s3_of = {W: [] for W in s2_set}
    for U in s3_list:
        for W in s2_set:
            if W <= U:
                s3_of[W].append(U)
    s4_of = {U: [H for H in hyper if U <= H] for U in s3_list}
    odd_id, even_id = {}, {}
    edges = []
    for p in range(len(pts)):
        for W in s2_by_pt[p]:
            for U in s3_of[W]:
                for H in s4_of[U]:
                    o = odd_id.setdefault((p, U), len(odd_id))
                    e = even_id.setdefault((W, H), len(even_id))
                    edges.append((o, e))
    No, Ne = len(odd_id), len(even_id)
    print("chambers", len(edges), "odd flags", No, "even flags", Ne)
    nv = No + Ne
    adj = [[] for _ in range(nv)]
    for o, e in edges:
        adj[o].append(No + e); adj[No + e].append(o)
    degs = {len(a) for a in adj}
    ecc = []
    for s in (0, No):
        dist = [-1] * nv; dist[s] = 0; dq = deque([s])
        while dq:
            u = dq.popleft()
            for w in adj[u]:
                if dist[w] < 0: dist[w] = dist[u] + 1; dq.append(w)
        ecc.append((max(dist), sum(1 for x in dist if x < 0)))
    print("vertices", nv, "degrees", degs, "ecc (max dist, unreached) from an odd and an even vertex:", ecc)
    with open(out, 'w') as f:
        f.write(f"{nv}\n")
        for o, e in edges:
            f.write(f"{o} {No + e}\n")


if __name__ == '__main__':
    main()
