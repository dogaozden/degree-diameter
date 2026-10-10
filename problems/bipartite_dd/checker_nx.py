"""Independent networkx re-implementation of the checker, used to cross-check the trusted one."""
from __future__ import annotations

import networkx as nx

from problems.bipartite_dd.checker import CheckResult, parse_output, size_guard


def check_nx(output, d: int, D: int) -> CheckResult:
    try:
        n, edges = parse_output(output)
    except ValueError as exc:
        return CheckResult(False, 0, str(exc))

    # Before building the graph, so a huge n is rejected without allocating it. Unlike `check`,
    # this runs ahead of the self-loop/duplicate/degree rules: validity agrees, only the reason may differ.
    guard = size_guard(n, len(edges), d, D)
    if guard:
        return CheckResult(False, n, guard)

    G = nx.Graph()
    G.add_nodes_from(range(n))
    G.add_edges_from(edges)

    if nx.number_of_selfloops(G) > 0:
        return CheckResult(False, n, "self-loop")
    if G.number_of_edges() != len(edges):
        return CheckResult(False, n, "duplicate edge")
    worst = max((deg for _, deg in G.degree()), default=0)
    if worst > d:
        return CheckResult(False, n, f"degree: max degree {worst} > {d}")
    if not nx.is_bipartite(G):
        return CheckResult(False, n, "not bipartite")
    if n > 1 and (not nx.is_connected(G) or nx.diameter(G) > D):
        return CheckResult(False, n, f"diameter: disconnected or diameter above {D}")
    return CheckResult(True, n, "")
