"""Trusted checker for bipartite graphs with max degree d and diameter at most D.

A candidate's output is `(n, edges)` on vertices 0..n-1. Only outputs that pass `check`
count; everything else scores 0. Pure Python, no third-party imports.
"""
from __future__ import annotations

from collections import deque
from dataclasses import dataclass

MAX_N = 2_000_000


@dataclass(frozen=True)
class CheckResult:
    valid: bool
    n: int        # vertex count (0 if malformed)
    reason: str   # "" if valid, else starts with "malformed", "label out of range",
                  # "self-loop", "duplicate edge", "degree", "not bipartite" or "diameter"


def _is_int(x) -> bool:
    return isinstance(x, int) and not isinstance(x, bool)


def parse_output(output) -> tuple[int, list[tuple[int, int]]]:
    """Return (n, edges) as plain ints, or raise ValueError("malformed: ...")."""
    if isinstance(output, dict):
        if "n" not in output or "edges" not in output:
            raise ValueError("malformed: dict needs keys 'n' and 'edges'")
        n, edges = output["n"], output["edges"]
    elif isinstance(output, (list, tuple)):
        if len(output) != 2:
            raise ValueError("malformed: expected [n, edges]")
        n, edges = output
    else:
        raise ValueError(f"malformed: expected [n, edges], got {type(output).__name__}")
    if not _is_int(n):
        raise ValueError("malformed: n must be an int")
    if not 1 <= n <= MAX_N:
        raise ValueError(f"malformed: n={n} outside 1..{MAX_N}")
    if not isinstance(edges, (list, tuple)):
        raise ValueError("malformed: edges must be a list or tuple")
    parsed = []
    for e in edges:
        if not isinstance(e, (list, tuple)) or len(e) != 2:
            raise ValueError("malformed: each edge must be a pair")
        u, v = e
        if not _is_int(u) or not _is_int(v):
            raise ValueError("malformed: edge labels must be ints")
        if not (0 <= u < n and 0 <= v < n):
            raise ValueError(f"label out of range: edge ({u}, {v}) with n={n}")
        parsed.append((int(u), int(v)))
    return int(n), parsed


def _bad(reason: str, n: int = 0) -> CheckResult:
    return CheckResult(False, n, reason)


def moore_bound(d: int, D: int) -> int:
    """Largest possible order of a bipartite graph with max degree d and diameter D."""
    if D == 0 or d == 0:
        return 1
    if d == 1:
        return min(2, D + 1)
    if d == 2:
        return 2 * D
    return 2 * sum((d - 1) ** i for i in range(D))


def size_guard(n: int, n_edges: int, d: int, D: int) -> str:
    """Cheap test for graphs that must fail the diameter rule. Returns a reason, or ""."""
    m = moore_bound(d, D)
    if n > m:
        return f"diameter: n={n} exceeds the bipartite Moore bound {m} for d={d}, D={D}"
    if n > 1 and n_edges < n - 1:
        return "diameter: graph is disconnected"
    return ""


def check(output, d: int, D: int) -> CheckResult:
    try:
        n, edges = parse_output(output)
    except ValueError as exc:
        return _bad(str(exc))

    for u, v in edges:
        if u == v:
            return _bad(f"self-loop: vertex {u}", n)

    seen = set()
    for u, v in edges:
        key = (u, v) if u < v else (v, u)
        if key in seen:
            return _bad(f"duplicate edge: {key}", n)
        seen.add(key)

    adj = [[] for _ in range(n)]
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)

    for v in range(n):
        if len(adj[v]) > d:
            return _bad(f"degree: vertex {v} has {len(adj[v])} > {d}", n)

    # Keeps the O(n^2)-bit reachability step away from graphs that must fail anyway.
    guard = size_guard(n, len(edges), d, D)
    if guard:
        return _bad(guard, n)

    colour = [-1] * n
    for s in range(n):
        if colour[s] != -1:
            continue
        colour[s] = 0
        queue = deque([s])
        while queue:
            u = queue.popleft()
            for w in adj[u]:
                if colour[w] == -1:
                    colour[w] = 1 - colour[u]
                    queue.append(w)
                elif colour[w] == colour[u]:
                    return _bad(f"not bipartite: edge ({u}, {w}) joins same colour", n)

    # Bitset reachability: after k rounds, bit w of reach[v] is set iff dist(v, w) <= k.
    reach = [1 << v for v in range(n)]
    full = (1 << n) - 1
    for _ in range(D):
        new = []
        for v, r in enumerate(reach):
            for u in adj[v]:
                r |= reach[u]
            new.append(r)
        reach = new
        if all(r == full for r in reach):
            break
    bad = next((v for v, r in enumerate(reach) if r != full), None)
    if bad is not None:
        return _bad(f"diameter: vertex {bad} cannot reach all vertices within {D}", n)
    return CheckResult(True, n, "")
