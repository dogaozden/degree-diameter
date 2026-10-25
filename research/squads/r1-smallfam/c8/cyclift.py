#!/usr/bin/env python3
"""c8: simulated annealing over cyclic voltage lifts Z_m of a bipartite base (here 4-regular, 2+2 vertices).
Lift: vertices (y, g), y in 0..k-1 (white = first endpoint of each base edge, black = second), g in Z_m; base edge
(w, b, a) gives lift edges (w, g) ~ (b, g + a).  Lift has k*m vertices (4m for k = 4).
Cost = number of (source, vertex) pairs at distance > D, over the 4 base sources (the group Z_m acts by translation on
each fibre, so one source per base vertex suffices).  Walk-reachable sets are bitmasks over Z_m (exact ball of radius D).
Usage: cyclift.py BASE m D SECONDS SEED [OUTEDGES]
"""
import sys, random, math, time


def read_base(path):
    L = [l.split() for l in open(path) if l.strip() and not l.startswith('#')]
    k = int(L[0][0])
    E = []
    for t in L[1:]:
        E.append((int(t[0]), int(t[1]), len(t) > 2 and t[2] == '='))
    return k, E


def main():
    base, m, D = sys.argv[1], int(sys.argv[2]), int(sys.argv[3])
    secs, seed = float(sys.argv[4]), int(sys.argv[5])
    outp = sys.argv[6] if len(sys.argv) > 6 else None
    k, E = read_base(base)
    NE = len(E)
    free = [i for i, e in enumerate(E) if not e[2]]
    rng = random.Random(seed)
    FULL = (1 << m) - 1
    try:
        pc = int.bit_count
    except AttributeError:
        pc = lambda x: bin(x).count('1')
    groups = {}
    for i, (w, b, _) in enumerate(E):
        groups.setdefault((w, b), []).append(i)
    edges_of = {}
    for i, (w, b, _) in enumerate(E):
        edges_of.setdefault(i, [(w, b)])

    def rot(x, a):
        if a == 0:
            return x
        return ((x << a) | (x >> (m - a))) & FULL

    def evaluate(V):
        arcs = []  # (x, y, shift): walking x -> y adds shift to the fibre coordinate
        for i, (w, b, _) in enumerate(E):
            arcs.append((w, b, V[i] % m))
            arcs.append((b, w, (-V[i]) % m))
        total = 0
        for s in range(k):
            cur = [0] * k
            cur[s] = 1
            allr = cur[:]
            for _ in range(D):
                nxt = [0] * k
                for (x, y, sh) in arcs:
                    if cur[x]:
                        nxt[y] |= rot(cur[x], sh)
                cur = nxt
                for y in range(k):
                    allr[y] |= cur[y]
            for y in range(k):
                total += m - pc(allr[y])
        return total

    def parallel_ok(V, i):
        w, b, _ = E[i]
        vals = [V[j] for j in groups[(w, b)]]
        return len(set(vals)) == len(vals)

    V = [0] * NE
    for i in free:
        V[i] = rng.randrange(1, m)
    while not all(parallel_ok(V, i) for i in free):
        for i in free:
            V[i] = rng.randrange(1, m)
    c = evaluate(V)
    best, bestV = c, V[:]
    T0, T1 = 3.0, 0.05
    t0 = time.time()
    it = 0
    while time.time() - t0 < secs and best > 0:
        frac = (time.time() - t0) / secs
        T = T0 * (T1 / T0) ** frac
        i = rng.choice(free)
        old = V[i]
        if rng.random() < 0.3:
            V[i] = rng.randrange(1, m)
        else:
            V[i] = (old + rng.choice([1, -1]) * rng.randrange(1, 4)) % m
        if V[i] == 0 or not parallel_ok(V, i):
            V[i] = old
            continue
        c2 = evaluate(V)
        if c2 <= c or rng.random() < math.exp(-(c2 - c) / T):
            c = c2
            if c < best:
                best, bestV = c, V[:]
        else:
            V[i] = old
        it += 1
    print(f"RESULT base={base} m={m} D={D} seed={seed} best_cost={best} iters={it} secs={time.time()-t0:.0f} "
          f"voltages={[bestV[i] for i in free]}", flush=True)
    if best == 0 and outp:
        n = k * m
        with open(outp, 'w') as f:
            f.write(f"{n}\n")
            for i, (w, b, _) in enumerate(E):
                for g in range(m):
                    f.write(f"{w * m + g} {b * m + (g + bestV[i]) % m}\n")
        print(f"WROTE {outp} n={n}", flush=True)


if __name__ == '__main__':
    main()
