"""Delorme's (7,6) graph on H(5) (8992 vertices) and the same plus 'whiskers'.

Base graph: points 0..N-1, lines N..2N-1 of H(q). S = Hermitian spread (q^3+1 lines in an elliptic hyperplane).
Delorme: v in S level 2, points of v level 1, other lines through them level 0; S - v level 1, their points level 0.
Whiskers: lines W (not in S, not meeting v) through points of S - v, at level 0, such that each point off S is on
at most one whisker and no whisker point lies on a line through a point of v.
Usage: python3 delorme_q5.py [whisker_file.json]
"""
import json
import subprocess
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
from hexq import load, contained_lines  # noqa: E402
import lift  # noqa: E402

q = 5
ELLIPTIC = [3, 3, 1, 0, 3, 0, 3]


def setup():
    P, lines = load(q)
    N = len(P)
    S = contained_lines(P, lines, ELLIPTIC, q)
    assert len(S) == q ** 3 + 1
    through = [[] for _ in range(N)]
    for k, L in enumerate(lines):
        for p in L:
            through[p].append(k)
    adj = [list(N + k for k in through[p]) for p in range(N)] + [list(L) for L in lines]
    return P, lines, N, S, through, adj


def delorme_levels(lines, N, S, through):
    lev = [-1] * (2 * N)
    v = S[0]
    for s in S[1:]:
        lev[N + s] = 1
        for p in lines[s]:
            lev[p] = 0
    lev[N + v] = 2
    for p in lines[v]:
        lev[p] = 1
        for k in through[p]:
            if k != v:
                lev[N + k] = 0
    return lev


if __name__ == '__main__':
    P, lines, N, S, through, adj = setup()
    lev = delorme_levels(lines, N, S, through)
    tag = 'delorme'
    if len(sys.argv) > 1:
        W = json.loads(Path(sys.argv[1]).read_text())['whiskers']
        for k in W:
            assert lev[N + k] == -1
            lev[N + k] = 0
        tag = f'whisk{len(W)}'
    ex = lift.degree_excess(adj, lev)
    print('max excess', max(ex), 'gain', lift.gain(lev))
    n, edges, vid = lift.build(2 * N, adj, lev)
    print('n', n, 'edges', len(edges))
    txt = HERE / 'runs' / f'q5_{tag}.txt'
    txt.parent.mkdir(exist_ok=True)
    lift.write_text(txt, n, edges)
    r = subprocess.run([str(HERE / 'diam'), str(txt), '6'], capture_output=True, text=True)
    print(r.stdout.strip())
    if r.returncode == 0:
        out = HERE / 'graphs' / f'h5_{tag}_n{n}.json'
        out.parent.mkdir(exist_ok=True)
        out.write_text(json.dumps({'case': 'd7D6', 'value': n, 'output': [n, edges]}))
        print('wrote', out)
