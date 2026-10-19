"""Build the Haar graph from a haar_search2 or haar_search3 solution and a group table, save as record JSON.

Usage: python3 build_haar3.py SOLUTION.txt OUT.json [TABLE.txt]
Solution file: first line "d m k lam [table]", then d lines "a j".
  Element index g = a*k + j, which is also the row/column index in the table.
  For haar_search3 output k = 1 and the header names the table (path relative to this directory).
TABLE.txt is read if given; otherwise the table named in the header is used.
Vertex (g, A) has index g, (g, B) has index N + g. Edge (g, A) ~ (s*g, B) for s in S, with s*g = T[s][g].
"""
import json
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))


def read_table(path):
    with open(path) as f:
        N = int(f.readline())
        T = [list(map(int, f.readline().split())) for _ in range(N)]
    assert all(len(r) == N for r in T), "table is not N x N"
    return T


def main(sol, out, table_path=None):
    lines = [l.split() for l in open(sol) if l.strip()]
    head = lines[0]
    d, m, k, lam = map(int, head[:4])
    if table_path is None:
        if len(head) < 5:
            sys.exit("no table: give TABLE.txt or use a solution with a table in its header")
        table_path = os.path.join(HERE, head[4])
    T = read_table(table_path)
    N = len(T)
    if N != m * k:
        sys.exit(f"table has N={N}, solution header says m*k={m * k}")
    S = [tuple(map(int, r)) for r in lines[1:]]
    assert len(S) == d
    S_idx = [a * k + j for a, j in S]
    edges = []
    for g in range(N):
        for s in S_idx:
            edges.append([g, N + T[s][g]])
    group = os.path.basename(table_path)[:-4] if len(head) >= 5 else f"Z_{m} x|_{lam} Z_{k}"
    json.dump({"case": f"d{d}D5", "value": 2 * N, "output": [2 * N, edges],
               "construction": {"group": group, "S": [list(s) for s in S]}}, open(out, "w"))
    print(out, 2 * N, len(edges))


if __name__ == "__main__":
    main(*sys.argv[1:4])
