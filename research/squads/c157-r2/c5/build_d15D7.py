#!/usr/bin/env python3
"""Independent builder for the (15,7) hub graph (squad c157-r2, card c5).

Written from the construction description only, not from kcopy_hub.c.

N = 177156 (points = lines of H(11)), 7 copies c in Z_7, K freed flags, k = 3.
  point (p,c)           = c*2N + p
  line  (l,c)           = c*2N + N + l
  line-side hub  (a,j)  = 14N + 3a + (j-1)
  point-side hub (a,j)  = 14N + 3K + 3a + (j-1)          a = 0..K-1, j = 1..3

Edges:
  hexagon      (p,c)-(l,c)                    for p on l
  cross        (p,c)-(M[p], (c+j) mod 7)      j = 1,2,3, unless p is freed
  hub columns  line-side hub (a,j) ~ (p_a,c) for all c
               point-side hub (a,j) ~ (M[p_a],c) for all c
  hub graph    line-side hub (j_e,1) ~ point-side hub (k_e,1) for each hub edge (j_e,k_e) in the file

Output: first line n, then "u v" with u < v, sorted by (u, v).
Checks: no self loops, no duplicate edges, max degree 15, min degree >= 7.

Usage (run with python3 -I):
  python3 -I build_d15D7.py [--hex HEX] [--sol SOL] [--out OUT]
                            [--ref REF_EDGES] [--ref-sorted REF_SORTED]
"""
import argparse
import hashlib
import os

import numpy as np

COPIES = 7        # Z_7 copies
KC = 3            # k = 3: cross offsets j = 1..3, three hubs per flag and side
DEG_MAX, DEG_MIN = 15, 7

HERE = os.path.dirname(os.path.abspath(__file__))
HEX_DEFAULT = "/home/user/degree-diameter/research/d15D7/hex/hex_q11.bin"
SOL_DEFAULT = os.path.join(HERE, "d15D7_hex11_7copy_K8_n2480232.sol")
OUT_DEFAULT = os.path.join(HERE, "mine_edges.txt")
REF_SORTED_DEFAULT = os.path.join(HERE, "ref_sorted.txt")


def sha256_file(path):
    h = hashlib.sha256()
    with open(path, "rb") as f:
        for block in iter(lambda: f.read(1 << 24), b""):
            h.update(block)
    return h.hexdigest()


def read_hex(path):
    """int32 q, N, L; then L*(q+1) int32 point ids (points of each line); then N*7 uint8 coordinates (unused)."""
    hdr = np.fromfile(path, dtype="<i4", count=3)
    q, N, L = int(hdr[0]), int(hdr[1]), int(hdr[2])
    assert os.path.getsize(path) == 12 + 4 * L * (q + 1) + 7 * N, "hexagon file size mismatch"
    inc = np.fromfile(path, dtype="<i4", count=L * (q + 1), offset=12).reshape(L, q + 1)
    assert inc.min() >= 0 and inc.max() < N, "point id out of range"
    assert (np.bincount(inc.ravel(), minlength=N) == q + 1).all(), "a point is not on q+1 lines"
    assert (np.diff(np.sort(inc, axis=1), axis=1) > 0).all(), "a point repeats on a line"
    return q, N, L, inc


def read_sol(path, N):
    with open(path) as f:
        h1 = f.readline().split()
        h2 = f.readline().split()
        h3 = f.readline().split()
        rest = f.read().split()
    assert h1[0] == "d7hex" and int(h1[2]) == N, "solution header"
    K = int(h1[3])
    assert h2[0] == "freed" and len(h2) == 1 + K, "freed line"
    freed = np.array([int(x) for x in h2[1:]], dtype=np.int64)
    assert len(set(freed.tolist())) == K, "freed points not distinct"
    assert h3[0] == "hubedges"
    m = int(h3[1])
    assert len(h3) == 2 + 2 * m, "hubedges line length"
    pairs = [(int(h3[2 + 2 * i]), int(h3[3 + 2 * i])) for i in range(m)]
    assert all(0 <= j < K and 0 <= k < K for j, k in pairs), "hub index out of range"
    M = np.array([int(x) for x in rest], dtype=np.int64)
    assert M.size == N, "bijection length"
    assert (np.bincount(M, minlength=N) == 1).all(), "M is not a bijection"
    assert (freed >= 0).all() and (freed < N).all()
    return K, freed, pairs, M, h1


def build(N, L, q, inc, K, freed, pairs, M):
    NV = 2 * N                  # vertices per copy
    HB = COPIES * NV            # first hub id = 14N
    n = HB + 2 * KC * K         # 6K hubs
    U, V = [], []

    # hexagon edges in every copy
    pp = inc.ravel().astype(np.int64)                    # point of each incidence
    ll = np.repeat(np.arange(L, dtype=np.int64), q + 1)  # its line
    for c in range(COPIES):
        U.append((c * NV + pp).astype(np.int32))
        V.append((c * NV + N + ll).astype(np.int32))

    # cross edges for non-freed points
    freed_mask = np.zeros(N, dtype=bool)
    freed_mask[freed] = True
    P = np.flatnonzero(~freed_mask).astype(np.int64)
    LP = M[P]
    for c in range(COPIES):
        for j in range(1, KC + 1):
            a = c * NV + P
            b = ((c + j) % COPIES) * NV + N + LP
            U.append(np.minimum(a, b).astype(np.int32))
            V.append(np.maximum(a, b).astype(np.int32))

    # hub columns and hub graph (a few hundred edges, kept as Python lists)
    su, sv = [], []

    def add(x, y):
        su.append(min(x, y))
        sv.append(max(x, y))

    for a, p in enumerate(freed.tolist()):
        l = int(M[p])
        for j in range(1, KC + 1):
            hL = HB + 3 * a + (j - 1)
            hP = HB + 3 * K + 3 * a + (j - 1)
            for c in range(COPIES):
                add(hL, c * NV + p)
                add(hP, c * NV + N + l)
    for je, ke in pairs:
        add(HB + 3 * je, HB + 3 * K + 3 * ke)
    U.append(np.array(su, dtype=np.int32))
    V.append(np.array(sv, dtype=np.int32))
    return n, np.concatenate(U), np.concatenate(V)


def canonical(n, U, V):
    """Undirected edge list -> sorted keys lo*n+hi (lo < hi), degrees, self-loop and duplicate counts."""
    lo = np.minimum(U, V).astype(np.int64)
    hi = np.maximum(U, V).astype(np.int64)
    loops = int(np.count_nonzero(lo == hi))
    assert int(lo.min()) >= 0 and int(hi.max()) < n, "vertex id out of range"
    deg = np.bincount(lo, minlength=n) + np.bincount(hi, minlength=n)
    keys = lo
    keys *= n
    keys += hi
    del hi
    keys.sort()
    dups = int(np.count_nonzero(keys[1:] == keys[:-1]))
    return keys, deg, loops, dups


def write_sorted(path, n, keys):
    CH = 1 << 20
    with open(path, "w") as f:
        f.write(f"{n}\n")
        for s in range(0, keys.size, CH):
            blk = keys[s:s + CH]
            us = (blk // n).tolist()
            vs = (blk % n).tolist()
            f.write("".join([f"{a} {b}\n" for a, b in zip(us, vs)]))
    return sha256_file(path)


def read_ref(path):
    with open(path) as f:
        n_ref = int(f.readline())
        txt = f.read()
    arr = np.fromstring(txt, dtype=np.int64, sep=" ")
    del txt
    assert arr.size % 2 == 0, "reference edge list has an odd number of ids"
    return n_ref, arr[0::2].copy(), arr[1::2].copy()


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--hex", default=HEX_DEFAULT)
    ap.add_argument("--sol", default=SOL_DEFAULT)
    ap.add_argument("--out", default=OUT_DEFAULT)
    ap.add_argument("--ref", default=None, help="kcopy_hub edges output to compare with")
    ap.add_argument("--ref-sorted", default=REF_SORTED_DEFAULT)
    args = ap.parse_args()

    q, N, L, inc = read_hex(args.hex)
    K, freed, pairs, M, h1 = read_sol(args.sol, N)
    print(f"hex: q={q} N={N} L={L} | sol header: {' '.join(h1)} | K={K} hubedges={len(pairs)}")
    print(f"freed points: {freed.tolist()}")

    n, U, V = build(N, L, q, inc, K, freed, pairs, M)
    assert n == 14 * N + 6 * K
    keys, deg, loops, dups = canonical(n, U, V)
    del U, V
    ok = loops == 0 and dups == 0 and int(deg.max()) == DEG_MAX and int(deg.min()) >= DEG_MIN
    print(f"mine: n={n} edges={keys.size} self_loops={loops} duplicates={dups} "
          f"maxdeg={int(deg.max())} mindeg={int(deg.min())} degree_checks={'PASS' if ok else 'FAIL'}")
    sha_mine = write_sorted(args.out, n, keys)
    print(f"mine sorted: {args.out}\nmine sha256: {sha_mine}")

    if args.ref:
        n_ref, ru, rv = read_ref(args.ref)
        rkeys, rdeg, rloops, rdups = canonical(n_ref, ru, rv)
        del ru, rv
        print(f"ref:  n={n_ref} edges={rkeys.size} self_loops={rloops} duplicates={rdups} "
              f"maxdeg={int(rdeg.max())} mindeg={int(rdeg.min())}")
        sha_ref = write_sorted(args.ref_sorted, n_ref, rkeys)
        print(f"ref sorted: {args.ref_sorted}\nref sha256:  {sha_ref}")
        if sha_ref == sha_mine:
            print("RESULT: IDENTICAL edge sets (sha256 equal)")
        else:
            print("RESULT: DIFFERENT")
            if n_ref != n:
                print(f"  vertex counts differ: mine {n}, ref {n_ref}")
            m = min(keys.size, rkeys.size)
            d = np.flatnonzero(keys[:m] != rkeys[:m])
            if d.size:
                i = int(d[0])
                print(f"  first difference at sorted index {i}: mine ({int(keys[i] // n)} {int(keys[i] % n)}) "
                      f"vs ref ({int(rkeys[i] // n_ref)} {int(rkeys[i] % n_ref)})")
            elif keys.size != rkeys.size:
                print(f"  common prefix equal; edge counts differ: mine {keys.size}, ref {rkeys.size}")
            only_mine = np.setdiff1d(keys, rkeys, assume_unique=True)
            only_ref = np.setdiff1d(rkeys, keys, assume_unique=True)
            print(f"  edges only in mine: {only_mine.size}, only in ref: {only_ref.size}")
    import resource
    print(f"peak RSS: {resource.getrusage(resource.RUSAGE_SELF).ru_maxrss / 1024:.0f} MB")


if __name__ == "__main__":
    main()
