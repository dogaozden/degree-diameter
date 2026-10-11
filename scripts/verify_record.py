"""Verify a saved record graph three independent ways before anyone calls it a record.

Usage: python scripts/verify_record.py RECORD.json d D [RECORD.json d D ...]

Checks:
  1. the trusted checker (problems/bipartite_dd/checker.py),
  2. the networkx checker (problems/bipartite_dd/checker_nx.py),
  3. a from-scratch check written separately: plain adjacency sets, explicit 2-colouring,
     and a breadth-first search from every vertex for the exact diameter.
Exits non-zero if any graph fails any check.
"""
import json
import sys
from collections import deque
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))

from problems.bipartite_dd.checker import check  # noqa: E402
from problems.bipartite_dd.checker_nx import check_nx  # noqa: E402


def fresh_check(n, edges, d, D):
    """Independent check. Returns (diameter, degree set, side sizes, edge count) or raises AssertionError."""
    assert isinstance(n, int) and n > 0, "n must be a positive int"
    adj = [set() for _ in range(n)]
    for u, v in edges:
        assert 0 <= u < n and 0 <= v < n and u != v, f"bad edge {u}-{v}"
        assert v not in adj[u], f"duplicate edge {u}-{v}"
        adj[u].add(v)
        adj[v].add(u)
    assert max(len(a) for a in adj) <= d, f"max degree {max(len(a) for a in adj)} > {d}"
    color = [-1] * n
    color[0] = 0
    queue = deque([0])
    while queue:
        x = queue.popleft()
        for y in adj[x]:
            if color[y] < 0:
                color[y] = 1 - color[x]
                queue.append(y)
            else:
                assert color[y] != color[x], f"odd cycle through {x}-{y}"
    diameter = 0
    for s in range(n):
        dist = [-1] * n
        dist[s] = 0
        queue = deque([s])
        while queue:
            x = queue.popleft()
            for y in adj[x]:
                if dist[y] < 0:
                    dist[y] = dist[x] + 1
                    queue.append(y)
        assert min(dist) >= 0, f"vertex {dist.index(-1)} unreachable from {s}"
        diameter = max(diameter, max(dist))
    assert diameter <= D, f"diameter {diameter} > {D}"
    return diameter, sorted({len(a) for a in adj}), (color.count(0), color.count(1)), len(edges)


def main(argv):
    if len(argv) % 3 or not argv:
        sys.exit(__doc__)
    ok = True
    for i in range(0, len(argv), 3):
        path, d, D = argv[i], int(argv[i + 1]), int(argv[i + 2])
        rec = json.loads(Path(path).read_text())
        out = rec["output"]
        n, edges = (out["n"], out["edges"]) if isinstance(out, dict) else out
        a, b = check(out, d, D), check_nx(out, d, D)
        try:
            diam, degs, sides, m = fresh_check(n, [tuple(e) for e in edges], d, D)
            c = f"pass (diameter {diam}, degrees {degs}, sides {sides}, {m} edges)"
            c_ok = True
        except AssertionError as e:
            c, c_ok = f"FAIL: {e}", False
        good = a.valid and b.valid and c_ok
        ok &= good
        print(f"{'VALID ' if good else 'INVALID'} n={n} d={d} D={D}  {path}")
        print(f"    checker: {a.valid} {a.reason}  networkx: {b.valid}  from-scratch: {c}")
    sys.exit(0 if ok else 1)


if __name__ == "__main__":
    main(sys.argv[1:])
