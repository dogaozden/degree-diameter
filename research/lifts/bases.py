"""Base-graph generator for lift.c (bipartite multigraphs, no loops).

Usage: python3 bases.py KIND ARGS... > base.txt
  dipole d                 2 vertices, d parallel edges (lifts = Haar graphs)
  kab a b [m]              K_{a,b}, every edge with multiplicity m (regular only if a = b)
  kaa_plus a d             K_{a,a} plus a multigraph of extra perfect matchings: degree d >= a; extra matchings i -> a+((i+t) mod a)
  cycle k d                cycle C_k (k even) with edge multiplicities as equal as possible to make it d-regular
  random k d seed          random connected d-regular bipartite multigraph on k = 2h vertices (union of d perfect matchings)
  heawood | pappus | moebius_kantor | cube | tutte8 | desargues   named cubic bipartite graphs (with optional "+m d": add matchings)
  incidence FILE           point-line incidence from a JSON {"lines": [[...], ...]} (points 0..P-1, lines P..)
Vertices 0..k-1; the colouring is computed by lift.c.
"""
import itertools
import json
import random
import sys


def out(k, edges, note=""):
    lines = [f"# {note}" if note else "# base graph", f"k {k}"]
    lines += [f"e {x} {y}" for x, y in edges]
    print("\n".join(lines))


def perfect_matchings_regular(h, d, rng):
    """d random perfect matchings between {0..h-1} and {h..2h-1}, connected union"""
    while True:
        edges = []
        for _ in range(d):
            p = list(range(h))
            rng.shuffle(p)
            edges += [(i, h + p[i]) for i in range(h)]
        # connectivity
        adj = {v: set() for v in range(2 * h)}
        for x, y in edges:
            adj[x].add(y)
            adj[y].add(x)
        seen, st = {0}, [0]
        while st:
            v = st.pop()
            for w in adj[v]:
                if w not in seen:
                    seen.add(w)
                    st.append(w)
        if len(seen) == 2 * h:
            return edges


def lcf(n, code):
    edges = set()
    for i in range(n):
        edges.add(tuple(sorted((i, (i + 1) % n))))
        edges.add(tuple(sorted((i, (i + code[i % len(code)]) % n))))
    return sorted(edges)


NAMED = {
    "heawood": (14, lambda: lcf(14, [5, -5])),
    "moebius_kantor": (16, lambda: lcf(16, [5, -5])),
    "pappus": (18, lambda: lcf(18, [5, 7, -7, 7, -7, -5])),
    "desargues": (20, lambda: lcf(20, [5, -5, 9, -9])),
    "tutte8": (30, lambda: lcf(30, [-13, -9, 7, -7, 9, 13])),
    "cube": (8, lambda: [(a, b) for a in range(8) for b in range(a + 1, 8) if bin(a ^ b).count("1") == 1]),
}


def main():
    kind = sys.argv[1]
    a = sys.argv[2:]
    if kind == "dipole":
        d = int(a[0])
        out(2, [(0, 1)] * d, f"dipole d={d}")
    elif kind == "kab":
        x, y = int(a[0]), int(a[1])
        m = int(a[2]) if len(a) > 2 else 1
        out(x + y, [(i, x + j) for i in range(x) for j in range(y) for _ in range(m)], f"K_{x},{y} mult {m}")
    elif kind == "kaa_plus":
        x, d = int(a[0]), int(a[1])
        edges = [(i, x + j) for i in range(x) for j in range(x)]
        for t in range(d - x):
            edges += [(i, x + (i + t) % x) for i in range(x)]
        out(2 * x, edges, f"K_{x},{x} + {d - x} matchings")
    elif kind == "cycle":
        k, d = int(a[0]), int(a[1])
        assert k % 2 == 0 and k >= 2
        if k == 2:
            out(2, [(0, 1)] * d)
            return
        # edges i,i+1; alternate multiplicities m1, m2 with m1 + m2 = d
        m1 = (d + 1) // 2
        m2 = d - m1
        edges = []
        for i in range(k):
            m = m1 if i % 2 == 0 else m2
            edges += [(i, (i + 1) % k)] * m
        out(k, edges, f"cycle C_{k} multiplicities {m1},{m2}")
    elif kind == "random":
        k, d, seed = int(a[0]), int(a[1]), int(a[2])
        assert k % 2 == 0
        rng = random.Random(seed)
        out(k, perfect_matchings_regular(k // 2, d, rng), f"random {d}-regular bipartite multigraph k={k} seed={seed}")
    elif kind in NAMED:
        n, f = NAMED[kind]
        edges = f()
        if len(a) >= 2 and a[0] == "+m":
            # add extra perfect matchings white->black to raise the degree to d
            d = int(a[1])
            col = {0: 0}
            adj = {v: [] for v in range(n)}
            for x, y in edges:
                adj[x].append(y)
                adj[y].append(x)
            st = [0]
            while st:
                v = st.pop()
                for w in adj[v]:
                    if w not in col:
                        col[w] = 1 - col[v]
                        st.append(w)
            W = [v for v in range(n) if col[v] == 0]
            B = [v for v in range(n) if col[v] == 1]
            rng = random.Random(int(a[2]) if len(a) > 2 else 1)
            for _ in range(d - 3):
                p = B[:]
                rng.shuffle(p)
                edges += list(zip(W, p))
        out(n, edges, kind)
    elif kind == "incidence":
        data = json.load(open(a[0]))
        lines = data["lines"]
        P = 1 + max(max(l) for l in lines)
        out(P + len(lines), [(p, P + j) for j, l in enumerate(lines) for p in l], f"incidence {a[0]}")
    else:
        sys.exit("unknown kind")


if __name__ == "__main__":
    main()
