#!/usr/bin/env python3
"""canon_cmp.py: compare, up to isomorphism (nauty labelg), the graphs found by sdk (Haar graphs H(G,S) from SOL
lines + the G table) with those found by brute.c (Cayley graphs Cay(H,T) from HIT lines + the H table).
usage: canon_cmp.py G.ht SDK.out H1.hat[:SUB] BRUTE1.out [H2.hat[:SUB] BRUTE2.out ...]  (SUB: index of the
index-2 subgroup in the .hat file, default 0)"""
import sys, subprocess, tempfile, os
import numpy as np

def g6(nv, edges):
    """graph6 string (nv > 62): upper triangle column by column, 6 bits per character"""
    bits = np.zeros((nv * (nv - 1)) // 2 + 6, dtype=np.uint8)
    e = np.array(edges, dtype=np.int64); a = np.minimum(e[:, 0], e[:, 1]); b = np.maximum(e[:, 0], e[:, 1])
    bits[b * (b - 1) // 2 + a] = 1
    L = ((nv * (nv - 1)) // 2 + 5) // 6
    v = bits[:6 * L].reshape(L, 6) @ np.array([32, 16, 8, 4, 2, 1], dtype=np.uint8) + 63
    head = chr(126) + chr(63 + ((nv >> 12) & 63)) + chr(63 + ((nv >> 6) & 63)) + chr(63 + (nv & 63))
    return head + v.astype(np.uint8).tobytes().decode()

def canon(graphs, chunk=500):
    res = set()
    with tempfile.TemporaryDirectory() as d:
        fi, fo = os.path.join(d, "in.g6"), os.path.join(d, "out.g6")
        for i in range(0, len(graphs), chunk):
            open(fi, "w").write("\n".join(graphs[i:i + chunk]) + "\n")
            subprocess.run(["nauty-labelg", "-q", fi, fo], check=True)
            res |= {l.strip() for l in open(fo) if l.strip()}
    return res

def read_ints(path):
    return open(path).read().split()

def sdk_graphs(ht, out):
    t = read_ints(ht); n = int(t[0]); tab = list(map(int, t[2:2 + n * n]))
    res = set(); gs = []
    for l in open(out):
        if l.startswith("SOL"):
            S = list(map(int, l.split()[2:]))
            gs.append(g6(2 * n, [(g, n + tab[s * n + g]) for g in range(n) for s in S]))
            if len(gs) >= 500: res |= canon(gs); gs = []
    return res | canon(gs)

def brute_graphs(hat, out, sub_index=0):
    t = open(hat).read().split("\n"); N = int(t[0]); tab = [list(map(int, t[1 + i].split())) for i in range(N)]
    sub = list(map(int, t[1 + N + sub_index].split()[1:]))
    res = set(); gs = []; nh = 0
    for l in open(out):
        if l.startswith("HIT"):
            T = list(map(int, l.split()[3:])); nh += 1
            gs.append(g6(N, [(x, tab[s][x]) for x in range(N) if sub[x] for s in T]))
            if len(gs) >= 500: res |= canon(gs); gs = []
    return nh, res | canon(gs)

a = sdk_graphs(sys.argv[1], sys.argv[2])
print(f"sdk: {len(a)} isomorphism classes")
allb = set()
for i in range(3, len(sys.argv), 2):
    h, _, si = sys.argv[i].partition(":")
    nh, b = brute_graphs(h, sys.argv[i + 1], int(si or 0))
    allb |= b
    print(f"{sys.argv[i]}: {nh} hits, {len(b)} classes, missing from sdk: {len(b - a)}")
print(f"union of brute classes {len(allb)}; sdk classes not found by brute: {len(a - allb)}; brute classes missing from sdk: {len(allb - a)}")
print("RESULT", "MATCH" if a == allb else "DIFFER")
