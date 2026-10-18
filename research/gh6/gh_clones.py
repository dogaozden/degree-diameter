"""Diameter 6, degree q+2 from the split Cayley hexagon H(q).

Vertices: points 0..N-1, lines N..2N-1 (incidence graph of H(q), (q+1)-regular, girth 12, diameter 6).
S = pairwise non-collinear points: each gets a clone joined to all lines through it.
T = pairwise disjoint lines (no shared point): each gets a clone joined to all points on it.
Every line gains at most one edge (one point of S on it), every point at most one (one line of T through it),
so the max degree is q+2. Order n = 2N + |S| + |T|.

Usage:
  python3 gh_clones.py points q seconds seed     # max set of pairwise non-collinear points -> runs/S_q{q}_s{seed}.json
  python3 gh_clones.py lines  q seconds seed     # max set of pairwise disjoint lines      -> runs/T_q{q}_s{seed}.json
  python3 gh_clones.py build  q S.json T.json    # build, check with lib.is_valid, save graphs/gh6_q{q}_n{n}.json
"""
import json
import subprocess
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, '/Users/dogaozden/AI_Projects/degree-diameter/problems/bipartite_dd')
import lib  # noqa: E402


def load_hexagon(q):
    d = json.loads((HERE / 'hex' / f'hexagon_q{q}.json').read_text())
    return d['points'], d['lines']


def collinearity_edges(N, lines):
    edges = set()
    for Ln in lines:
        for i, a in enumerate(Ln):
            for b in Ln[i + 1:]:
                edges.add((a, b))
    return sorted(edges)


def concurrency_edges(N, lines):
    through = [[] for _ in range(N)]
    for k, Ln in enumerate(lines):
        for p in Ln:
            through[p].append(k)
    edges = set()
    for ks in through:
        for i, a in enumerate(ks):
            for b in ks[i + 1:]:
                edges.add((min(a, b), max(a, b)))
    return sorted(edges)


def run_mis(n, edges, seconds, seed, name):
    """Max independent set with the ILS solver in this folder. Returns the sorted vertex list."""
    gfile = HERE / 'runs' / f'{name}_s{seed}.graph'
    gfile.write_text(lib.graph_to_text(n, edges))
    res = subprocess.run([str(HERE / 'ils_mis'), str(gfile), str(seconds), str(seed)],
                         capture_output=True, text=True, check=True)
    print(res.stderr.strip(), flush=True)
    lines = res.stdout.split('\n')
    size = int(lines[0])
    verts = sorted(int(x) for x in lines[1].split()) if size else []
    assert len(verts) == size
    return verts


def search(kind, q, seconds, seed):
    N, lines = load_hexagon(q)
    if kind == 'points':
        verts = run_mis(N, collinearity_edges(N, lines), seconds, seed, f'col_q{q}')
        out = HERE / 'runs' / f'S_q{q}_s{seed}.json'
    else:
        verts = run_mis(len(lines), concurrency_edges(N, lines), seconds, seed, f'con_q{q}')
        out = HERE / 'runs' / f'T_q{q}_s{seed}.json'
    out.write_text(json.dumps({'q': q, 'kind': kind, 'size': len(verts), 'members': verts}))
    print(f'{kind} q={q} seed={seed}: best size {len(verts)} -> {out}', flush=True)


def build(q, S, T):
    N, lines = load_hexagon(q)
    through = [[] for _ in range(N)]
    for k, Ln in enumerate(lines):
        for p in Ln:
            through[p].append(k)
    # Independence checks on the inputs themselves.
    on_line = {}
    for p in S:
        for k in through[p]:
            on_line.setdefault(k, []).append(p)
    assert all(len(v) == 1 for v in on_line.values()), 'two points of S are collinear'
    point_on = {}
    for k in T:
        for p in lines[k]:
            point_on.setdefault(p, []).append(k)
    assert all(len(v) == 1 for v in point_on.values()), 'two lines of T meet'
    edges = [(p, N + k) for k, Ln in enumerate(lines) for p in Ln]
    n = 2 * N
    for p in S:  # point clone: adjacent to the lines through p
        edges += [(n, N + k) for k in through[p]]
        n += 1
    for k in T:  # line clone: adjacent to the points of line k
        edges += [(p, n) for p in lines[k]]
        n += 1
    ok = lib.is_valid(n, edges, q + 2, 6)
    print(f'q={q}: |S|={len(S)} |T|={len(T)} n={n} max degree {lib.max_degree(n, edges)} '
          f'bipartite={lib.is_bipartite(n, edges)} is_valid(d={q+2}, D=6)={ok}', flush=True)
    if ok:
        out = HERE / 'graphs' / f'gh6_q{q}_n{n}.json'
        out.write_text(json.dumps({'case': f'd{q+2}D6', 'value': n, 'output': [n, edges]}))
        print('wrote', out, flush=True)
    return ok, n


if __name__ == '__main__':
    cmd = sys.argv[1]
    if cmd in ('points', 'lines'):
        search(cmd, int(sys.argv[2]), float(sys.argv[3]), int(sys.argv[4]))
    elif cmd == 'build':
        q = int(sys.argv[2])
        S = json.loads(Path(sys.argv[3]).read_text())['members']
        T = json.loads(Path(sys.argv[4]).read_text())['members']
        build(q, S, T)
    else:
        raise SystemExit(__doc__)
