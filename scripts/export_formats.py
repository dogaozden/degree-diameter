"""Export the bipartite record graphs to graph6 and plain edge lists, then read both back to check them.

Usage: .venv/bin/python scripts/export_formats.py

For each record JSON below, writes next to it:
  <stem>.g6          graph6 (networkx, header=False), vertices 0..n-1, isolated vertices kept
  <stem>.edges.txt   a comment line, then one edge "u v" per line with u < v, sorted

Each export is verified by reading it back and comparing the vertex count and the exact
edge set with the JSON. Prints one line per graph. Exits non-zero if any check fails.
"""
import json
import re
import sys
from pathlib import Path

import networkx as nx

ROOT = Path(__file__).resolve().parent.parent
RECORDS = [
    "records/bipartite_dd/d4D5/162-c-d4d5-g002-c08.json",
    "records/bipartite_dd/d5D5/354-c-d5d5-w3-g014-c13.json",
    "records/bipartite_dd/d7D5/1140-spec-d7d5-g016-c15.json",
    "records/bipartite_dd/d7D4/359-spec-d7d4-g017-c11.json",
    "records/bipartite_dd/d11D4/1774-spec-d11d4-g010-c19.json",
    "records/bipartite_dd/d11D3/192-c-d3fam-g001-c00.json",
    "records/bipartite_dd/d13D3/276-c-d3fam-g003-c19.json",
    "records/bipartite_dd/d15D3/376-c-d3fam-w2-g002-c12.json",
]


def delta_and_D(folder):
    """'d7D4' -> (7, 4)."""
    m = re.fullmatch(r"d(\d+)D(\d+)", folder)
    assert m, f"folder name {folder!r} is not dDelta D form"
    return int(m.group(1)), int(m.group(2))


def edge_set(edges):
    """Undirected edges as a set of (min, max) pairs."""
    return {(min(u, v), max(u, v)) for u, v in edges}


def parse_edge_list(text):
    """Return (header comment, list of (u, v) pairs in file order)."""
    lines = text.splitlines()
    assert lines and lines[0].startswith("# "), "first line must be a comment"
    pairs = []
    for line in lines[1:]:
        u_str, v_str = line.split(" ")
        pairs.append((int(u_str), int(v_str)))
    return lines[0], pairs


def export_one(json_path):
    """Write both files for one record graph and verify them. Returns (ok, message)."""
    data = json.loads(json_path.read_text())
    n, raw_edges = data["output"]
    expected = edge_set(raw_edges)
    m = len(expected)
    delta, D = delta_and_D(json_path.parent.name)

    G = nx.Graph()
    G.add_nodes_from(range(n))
    G.add_edges_from(expected)

    g6_path = json_path.with_suffix(".g6")
    edges_path = json_path.parent / (json_path.stem + ".edges.txt")

    g6_path.write_bytes(nx.to_graph6_bytes(G, header=False))

    header = (
        f"# n={n} edges={m} Delta={delta} D={D} "
        f"bipartite degree/diameter record graph, vertices 0..{n - 1}"
    )
    body = "".join(f"{u} {v}\n" for u, v in sorted(expected))
    edges_path.write_text(header + "\n" + body)

    stem = json_path.stem
    problems = []

    back = nx.from_graph6_bytes(g6_path.read_bytes().rstrip(b"\n"))
    if back.number_of_nodes() != n:
        problems.append(f"g6 vertex count {back.number_of_nodes()} != {n}")
    if edge_set(back.edges()) != expected:
        problems.append("g6 edge set differs from JSON")

    try:
        got_header, got_pairs = parse_edge_list(edges_path.read_text())
    except (AssertionError, ValueError) as err:
        return False, f"FAIL {n} {stem}: edge list unreadable ({err})"
    if got_header != header:
        problems.append("edge list header differs")
    if any(u >= v for u, v in got_pairs):
        problems.append("edge list has a pair with u >= v")
    if got_pairs != sorted(got_pairs):
        problems.append("edge list is not sorted")
    if len(got_pairs) != m:
        problems.append(f"edge list has {len(got_pairs)} lines, expected {m}")
    if set(got_pairs) != expected:
        problems.append("edge list edge set differs from JSON")
    if any(not (0 <= u < n and 0 <= v < n) for u, v in got_pairs):
        problems.append("edge list has a vertex outside 0..n-1")

    if problems:
        return False, f"FAIL {n} {stem}: " + "; ".join(problems)
    return True, f"ok {n} g6 edges={m} {stem}"


def main():
    failed = 0
    for rel in RECORDS:
        path = ROOT / rel
        if not path.exists():
            print(f"FAIL missing {rel}")
            failed += 1
            continue
        ok, message = export_one(path)
        print(message)
        if not ok:
            failed += 1
    if failed:
        print(f"{failed} of {len(RECORDS)} graphs failed")
        sys.exit(1)


if __name__ == "__main__":
    main()
