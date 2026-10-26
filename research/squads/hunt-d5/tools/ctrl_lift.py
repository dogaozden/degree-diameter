#!/usr/bin/env python3
"""Exhaustive search of cubic bipartite controllers that are voltage lifts of a small base (hunt-d5).
ctrl_lift.py BASE TABLE.bin [OUTPREFIX]
BASE: "b e" then e lines "u v" (u on side A = 0..b/2-1, v on side B = b/2..b-1), cubic bipartite multigraph.
Lift over the group G (table, identity 0): (u,x) ~ (v, g_e x).  Spanning-tree edges get e; all other voltage tuples
are enumerated (|G|^(e-b+1)).  Controller conditions: simple, same-side distance <= 4, every vertex on a 4-cycle.
Prints how many voltage tuples pass and writes the first passing controller as OUTPREFIX_m<m>.edges."""
import sys, struct, itertools, array
def load_table(fn):
    data = open(fn, 'rb').read(); N = struct.unpack('<i', data[:4])[0]
    T = array.array('H'); T.frombytes(data[4:4 + 2 * N * N]); return N, T
def main():
    bfile, tfile = sys.argv[1], sys.argv[2]; pref = sys.argv[3] if len(sys.argv) > 3 else None
    L = open(bfile).read().split('\n'); b, e = map(int, L[0].split()); E = [tuple(map(int, l.split())) for l in L[1:1 + e]]
    h = b // 2; N, T = load_table(tfile); m = h * N; n = 2 * m
    # spanning tree
    par = list(range(b))
    def f(x):
        while par[x] != x: par[x] = par[par[x]]; x = par[x]
        return x
    tree = set()
    for i, (u, v) in enumerate(E):
        if f(u) != f(v): par[f(u)] = f(v); tree.add(i)
    free = [i for i in range(e) if i not in tree]
    npass = 0; tot = 0
    for tup in itertools.product(range(N), repeat=len(free)):
        volt = [0] * e
        for i, g in zip(free, tup): volt[i] = g
        tot += 1
        # build adjacency as bitmasks over n = 2m vertices: A vertex (u,x) = u*N + x, B vertex (v,x) = m + (v-h)*N + x
        nb = [0] * n; ok = True
        for i, (u, v) in enumerate(E):
            g = volt[i]
            for x in range(N):
                a = u * N + x; bb = m + (v - h) * N + T[g * N + x]
                if (nb[a] >> bb) & 1: ok = False; break
                nb[a] |= 1 << bb; nb[bb] |= 1 << a
            if not ok: break
        if not ok: continue
        adjl = [[y for y in range(n) if (nb[x] >> y) & 1] for x in range(n)]
        # 4-cycles
        good = True
        for x in range(n):
            a = adjl[x]
            if not any(bin(nb[a[i]] & nb[a[j]]).count('1') >= 2 for i in range(3) for j in range(i + 1, 3)): good = False; break
        if not good: continue
        # same-side within 4
        for x in range(n):
            b2 = 0
            for y in adjl[x]: b2 |= nb[y]
            b3 = 0
            for y in range(n):
                if (b2 >> y) & 1: b3 |= nb[y]
            b4 = 0
            for y in range(n):
                if (b3 >> y) & 1: b4 |= nb[y]
            side = ((1 << m) - 1) if x < m else (((1 << m) - 1) << m)
            if (b4 & side) != side: good = False; break
        if not good: continue
        npass += 1
        if npass == 1 and pref:
            with open(f"{pref}_m{m}.edges", 'w') as fo:
                fo.write(f"{n}\n")
                for x in range(m):
                    for y in adjl[x]: fo.write(f"{x} {y}\n")
            print("voltages", volt, flush=True)
    print(f"RESULT base={bfile} table={tfile} m={m} tuples={tot} pass={npass}")
main()
