#!/usr/bin/env python3
"""canon_cmp.py: compare, up to isomorphism (nauty labelg), the graphs found by sdk (Haar graphs H(G,S) from SOL
lines + the G table) with those found by brute.c (Cayley graphs Cay(H,T) from HIT lines + the H table).
usage: canon_cmp.py G.ht SDK.out H1.hat BRUTE1.out [H2.hat BRUTE2.out ...]"""
import sys, subprocess, tempfile, os

def g6(nv, edges):
    bits = bytearray((nv * (nv - 1)) // 2)
    for a, b in edges:
        if a > b: a, b = b, a
        bits[b * (b - 1) // 2 + a] = 1
    out = [chr(126), chr(63 + ((nv >> 12) & 63)), chr(63 + ((nv >> 6) & 63)), chr(63 + (nv & 63))]
    pad = (-len(bits)) % 6
    bits += bytearray(pad)
    for i in range(0, len(bits), 6):
        v = 0
        for j in range(6): v = (v << 1) | bits[i + j]
        out.append(chr(63 + v))
    return "".join(out)

def canon(graphs):
    with tempfile.TemporaryDirectory() as d:
        fi, fo = os.path.join(d, "in.g6"), os.path.join(d, "out.g6")
        open(fi, "w").write("\n".join(graphs) + "\n")
        subprocess.run(["nauty-labelg", "-q", fi, fo], check=True)
        return [l.strip() for l in open(fo) if l.strip()]

def read_ints(path):
    return open(path).read().split()

def sdk_graphs(ht, out):
    t = read_ints(ht); n = int(t[0]); tab = list(map(int, t[2:2 + n * n]))
    gs = []
    for l in open(out):
        if l.startswith("SOL"):
            S = list(map(int, l.split()[2:]))
            gs.append(g6(2 * n, [(g, n + tab[s * n + g]) for g in range(n) for s in S]))
    return gs

def brute_graphs(hat, out):
    t = open(hat).read().split("\n"); N = int(t[0]); tab = [list(map(int, t[1 + i].split())) for i in range(N)]
    sub = list(map(int, t[1 + N].split()[1:]))
    gs = []
    for l in open(out):
        if l.startswith("HIT"):
            T = list(map(int, l.split()[3:]))
            gs.append(g6(N, [(x, tab[s][x]) for x in range(N) if sub[x] for s in T]))
    return gs

a = set(canon(sdk_graphs(sys.argv[1], sys.argv[2])))
print(f"sdk: {len(a)} isomorphism classes")
allb = set()
for i in range(3, len(sys.argv), 2):
    gs = brute_graphs(sys.argv[i], sys.argv[i + 1])
    b = set(canon(gs)) if gs else set()
    allb |= b
    print(f"{sys.argv[i]}: {len(gs)} hits, {len(b)} classes, missing from sdk: {len(b - a)}")
print(f"union of brute classes {len(allb)}; sdk classes not found by brute: {len(a - allb)}; brute classes missing from sdk: {len(allb - a)}")
print("RESULT", "MATCH" if a == allb else "DIFFER")
