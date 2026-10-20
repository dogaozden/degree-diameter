"""H(q) for prime q with point coordinates (same point/line numbering as research/gh6/hex/hexagon_q{q}.json).

load(q) -> (P, lines) with P[i] the normalized 7-vector of point i and lines[k] the sorted point ids of line k.
"""
import json
import sys
from pathlib import Path

GH6 = Path(__file__).resolve().parents[2] / 'gh6'
sys.path.insert(0, str(GH6))
from gh_build import quadric_points  # noqa: E402


def load(q):
    d = json.loads((GH6 / 'hex' / f'hexagon_q{q}.json').read_text())
    P = quadric_points(q)
    assert len(P) == d['points']
    return P, d['lines']


def contained_lines(P, lines, a, q):
    """Lines of H(q) inside the hyperplane a.x = 0."""
    inH = [sum(x * y for x, y in zip(a, v)) % q == 0 for v in P]
    return [k for k, L in enumerate(lines) if all(inH[p] for p in L)]
