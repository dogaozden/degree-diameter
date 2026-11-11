"""Enumerate connected d-regular bipartite multigraphs on h + h vertices (no loops), up to isomorphism.

A base is an h x h biadjacency matrix with non-negative integer entries, all row and column sums d. Two matrices
are the same base if they differ by row/column permutations or transposition (colour swap).

Usage: python3 enum_bases.py h d OUTDIR [--maxmult m] [--simple]
Writes OUTDIR/b{h}_{d}_{i}.txt (lift.c base format) and prints the count.
--maxmult m: bound every edge multiplicity by m (default d). --simple: m = 1.
"""
import itertools
import os
import sys


def compositions_bounded(total, parts, bound, colcap):
    """rows: vectors of length `parts` with sum `total`, entry j <= min(bound, colcap[j])"""
    def rec(j, left):
        if j == parts - 1:
            if left <= min(bound, colcap[j]):
                yield (left,)
            return
        for x in range(min(left, bound, colcap[j]), -1, -1):
            for rest in rec(j + 1, left - x):
                yield (x,) + rest
    yield from rec(0, total)


def canon(M, h):
    best = None
    perms = list(itertools.permutations(range(h)))
    for A in (M, tuple(zip(*M))):
        for rp in perms:
            R = [A[i] for i in rp]
            # for a fixed row order the best column order is found by sorting columns lexicographically (descending)
            cols = sorted(zip(*R), reverse=True)
            key = tuple(zip(*cols))
            if best is None or key > best:
                best = key
    return best


def connected(M, h):
    seen = {0}
    st = [0]
    while st:
        v = st.pop()
        if v < h:
            nb = [h + j for j in range(h) if M[v][j]]
        else:
            nb = [i for i in range(h) if M[i][v - h]]
        for w in nb:
            if w not in seen:
                seen.add(w)
                st.append(w)
    return len(seen) == 2 * h


def main():
    h, d, outdir = int(sys.argv[1]), int(sys.argv[2]), sys.argv[3]
    bound = d
    if "--maxmult" in sys.argv:
        bound = int(sys.argv[sys.argv.index("--maxmult") + 1])
    if "--simple" in sys.argv:
        bound = 1
    os.makedirs(outdir, exist_ok=True)
    found = set()

    def rec(rows, colsum):
        if len(rows) == h:
            if all(c == d for c in colsum):
                M = tuple(rows)
                if connected(M, h):
                    found.add(canon(M, h))
            return
        cap = [d - c for c in colsum]
        for r in compositions_bounded(d, h, bound, cap):
            if rows and r > rows[-1]:
                continue   # rows in non-increasing order (rows can be permuted)
            rec(rows + [r], [c + x for c, x in zip(colsum, r)])

    rec([], [0] * h)
    for i, M in enumerate(sorted(found, reverse=True)):
        edges = [(a, h + b) for a in range(h) for b in range(h) for _ in range(M[a][b])]
        with open(os.path.join(outdir, f"b{h}_{d}_{i}.txt"), "w") as f:
            f.write(f"# {h}+{h} base, degree {d}, biadjacency {M}\nk {2 * h}\n")
            f.write("".join(f"e {x} {y}\n" for x, y in edges))
    print(len(found))


if __name__ == "__main__":
    main()
