#!/usr/bin/env python3
"""Clean a downloaded base graph into the plain 0-based edge list that double_cover.py reads.

Formats (only integers are parsed; nothing in the input is executed):
  --format edges  one undirected edge per line: "u v"
  --format adj    one vertex per line: "v n1 n2 ..." or "v: n1 n2 ..." (each edge appears on both lines)
Lines that are blank or start with '#', '%' or '//' are skipped.

Checks; any failure exits with status 1 and writes nothing: exactly --expect-n vertices (if given), every
vertex has a line (adj) or an edge (edges), no loops, no repeated edges, adjacency lists symmetric, connected,
max degree <= --delta (whether it equals --delta is reported). Bipartiteness is reported.
Labels are renumbered to 0..n-1 when they are not already (the renumbering is reported).
Output: "u v" per undirected edge with u < v, sorted, no header line.

usage: python3 -I parse.py IN OUT --format {edges,adj} [--delta DELTA] [--expect-n N]
"""
import argparse
import collections
import hashlib
import re
import sys

COMMENTS = ('#', '%', '//')
INT = re.compile(r'[+-]?[0-9]+\Z')


def fail(msg):
    print('FAIL:', msg)
    sys.exit(1)


def sha256(path):
    h = hashlib.sha256()
    with open(path, 'rb') as f:
        for chunk in iter(lambda: f.read(1 << 20), b''):
            h.update(chunk)
    return h.hexdigest()


def data_lines(path):
    with open(path, 'r', encoding='utf-8', errors='strict') as f:
        for lineno, raw in enumerate(f, 1):
            s = raw.strip()
            if s and not s.startswith(COMMENTS):
                yield lineno, s


def to_ints(toks, path, lineno):
    out = []
    for t in toks:
        if not INT.match(t):
            fail(f'{path}:{lineno}: non-integer token {t[:40]!r}')
        out.append(int(t))
    return out


def read_edges(path):
    """Return the list of (u, v) pairs; a leading 'n m' header (m = number of remaining lines) is dropped."""
    rows = []
    for lineno, s in data_lines(path):
        toks = s.split()
        if len(toks) != 2:
            fail(f'{path}:{lineno}: edges format needs exactly two integers, got {len(toks)} tokens')
        rows.append(tuple(to_ints(toks, path, lineno)))
    if len(rows) > 1 and rows[0][1] == len(rows) - 1 and rows[0][0] > max(max(r) for r in rows[1:]):
        print(f'note: dropped header line {rows[0]}')
        rows = rows[1:]
    return rows


def read_adj(path):
    """Return {vertex: [neighbours]} from 'v n1 n2 ...' or 'v: n1 n2 ...' lines."""
    lists = {}
    for lineno, s in data_lines(path):
        vals = to_ints(s.replace(':', ' ').split(), path, lineno)
        v, nb = vals[0], vals[1:]
        if v in lists:
            fail(f'{path}:{lineno}: vertex {v} has two lines')
        lists[v] = nb
    return lists


def bfs_colour(nbr, start):
    colour = {start: 0}
    queue = collections.deque([start])
    bip = True
    while queue:
        x = queue.popleft()
        for y in nbr[x]:
            if y not in colour:
                colour[y] = 1 - colour[x]
                queue.append(y)
            elif colour[y] == colour[x]:
                bip = False
    return colour, bip


def main():
    ap = argparse.ArgumentParser(description=__doc__.split('\n')[0])
    ap.add_argument('inp')
    ap.add_argument('out')
    ap.add_argument('--format', choices=['edges', 'adj'], required=True)
    ap.add_argument('--delta', type=int, default=None)
    ap.add_argument('--expect-n', type=int, default=None)
    a = ap.parse_args()

    print(f'input {a.inp} format={a.format} sha256={sha256(a.inp)}')
    nbr = {}
    if a.format == 'edges':
        seen = set()
        for u, v in read_edges(a.inp):
            if u == v:
                fail(f'loop at vertex {u}')
            key = (min(u, v), max(u, v))
            if key in seen:
                fail(f'repeated edge {key}')
            seen.add(key)
        for u, v in seen:
            nbr.setdefault(u, set()).add(v)
            nbr.setdefault(v, set()).add(u)
        n_file_edges = len(seen)
    else:
        lists = read_adj(a.inp)
        for v, nb in lists.items():
            if len(set(nb)) != len(nb):
                fail(f'vertex {v}: repeated neighbour in its line')
            if v in nb:
                fail(f'loop at vertex {v}')
            for u in nb:
                if u not in lists:
                    fail(f'vertex {u} is a neighbour of {v} but has no line')
                if v not in lists[u]:
                    fail(f'asymmetric adjacency: {v} lists {u} but {u} does not list {v}')
            nbr[v] = set(nb)
        n_file_edges = sum(len(nb) for nb in lists.values()) // 2

    labels = sorted(nbr)
    n = len(labels)
    if a.expect_n is not None and n != a.expect_n:
        fail(f'expected {a.expect_n} vertices, found {n}')
    if labels == list(range(n)):
        mapping = {x: x for x in labels}
        print('labels: already 0..n-1')
    elif labels == list(range(1, n + 1)):
        mapping = {x: x - 1 for x in labels}
        print('labels: 1..n shifted to 0..n-1')
    else:
        mapping = {x: i for i, x in enumerate(labels)}
        print(f'labels: not contiguous (min {labels[0]}, max {labels[-1]}), renumbered by rank')
    nb2 = {mapping[v]: {mapping[u] for u in nbr[v]} for v in nbr}

    deg = {v: len(nb2[v]) for v in nb2}
    maxd, mind = max(deg.values()), min(deg.values())
    if a.delta is not None and maxd > a.delta:
        fail(f'max degree {maxd} exceeds DELTA={a.delta}')
    hist = collections.Counter(deg.values())
    print(f'n={n} edges={n_file_edges} simple=yes symmetric=yes degree min={mind} max={maxd} '
          f'histogram={dict(sorted(hist.items()))}')
    if a.delta is not None:
        print(f'max degree equals DELTA={a.delta}: {"yes" if maxd == a.delta else "no"}')

    colour, bip = bfs_colour(nb2, 0)
    if len(colour) != n:
        fail(f'disconnected: {len(colour)} of {n} vertices reachable from vertex 0')
    print(f'connected=yes bipartite={"yes" if bip else "no"}')

    m = sum(deg.values()) // 2
    if sum(deg.values()) % 2:
        fail('odd degree sum')
    edges = sorted((v, u) for v in nb2 for u in nb2[v] if v < u)
    with open(a.out, 'w') as f:
        for v, u in edges:
            f.write(f'{v} {u}\n')
    # read back and check the written file
    back = []
    with open(a.out) as f:
        for line in f:
            x, y = line.split()
            back.append((int(x), int(y)))
    if len(back) != m or len(set(back)) != m or max(max(e) for e in back) != n - 1:
        fail('output self-check failed')
    print(f'wrote {a.out} edges={m} vertices={n} sha256={sha256(a.out)}')
    print('OK')


if __name__ == '__main__':
    main()
