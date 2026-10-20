"""Compare the coordinate builds (coords.py) with the earlier code, by graph isomorphism (nauty's dreadnaut).

1. Four hats: the core (no filler) from construction.py's default frame, for q = 9, 11, 13, against the coordinate
   core for every (a, c); and the saved regular graphs graphs/plus2_q*_n*.json against the coordinate graphs with
   the delta filler.
2. AL: lib.araujo_lopez_graph(q) against the coordinate AL graph with AL's matching (all i != 0), every a.
3. Negative controls in coordinates: no rotation; no link H_1 in K_0.
5. Duality (Remark rem:duality of coords.tex).
4. How many isomorphism classes the (a, c) choices give.
Also writes graphs/coords_q{q}_d{q+2}_n{n}.json (delta filler, a = 2 in coords.GF codes, c chosen below) for
scripts/verify_record.py.

Run from anywhere: python research/plus2/coords/compare.py
"""
import json
import subprocess
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
sys.path.insert(0, str(HERE))
sys.path.insert(0, str(HERE.parent))
sys.path.insert(0, str(ROOT / 'problems' / 'bipartite_dd'))

import coords                          # noqa: E402
import construction                    # noqa: E402  (only for the comparison)
import lib                             # noqa: E402


def canon(n, edges):
    adj = [[] for _ in range(n)]
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
    body = ';\n'.join(f'{v}: ' + ' '.join(map(str, sorted(a))) for v, a in enumerate(adj))
    cmd = f'l=0 $=0 n={n} g\n{body}.\nc x b\nq\n'
    out = subprocess.run(['dreadnaut'], input=cmd, capture_output=True, text=True, check=True).stdout
    lines = out.splitlines()
    i = max(k for k, s in enumerate(lines) if 'cpu time' in s)
    graph = [s for s in lines[i + 1:] if ':' in s]
    assert len(graph) == n, (len(graph), n)
    return '\n'.join(graph)


def coords_graph(q, a, c, fill=True):
    fr = coords.Frame(q, a, c)
    inc = coords.build_all(fr)
    if fill:
        inc = coords.filler(fr, inc, q + 2)
    n, edges, _ = coords.to_graph(fr, inc)
    return n, edges


def construction_core(q):
    points, lines = construction.pg_plane(q)
    A, ell, P, X = construction.default_frame(points, lines)
    pts, lns, inc = construction.core_incidences(points, lines, q, A, ell, P, X)
    n, edges, _ = construction.to_graph(pts, lns, inc)
    return n, edges


def choices(q):
    return [(a, c) for a in range(2, q) for c in range(2, q) if c != a]


def main():
    ok = True
    print('== 1. four hats vs construction.py ==')
    for q in (9, 11, 13):
        target_core = canon(*construction_core(q))
        saved = json.loads((HERE.parent / 'graphs' / f'plus2_q{q}_d{q+2}_n{2*(q*q+q+6)}.json').read_text())
        n_s, e_s = saved['output']
        target_full = canon(n_s, e_s)
        core_hits, full_hits, classes = [], [], {}
        for a, c in choices(q):
            cc = canon(*coords_graph(q, a, c, fill=False))
            classes.setdefault(cc, []).append((a, c))
            if cc == target_core:
                core_hits.append((a, c))
                if canon(*coords_graph(q, a, c)) == target_full:
                    full_hits.append((a, c))
        print(f'q={q}: construction.py core isomorphic to coordinate core for (a,c) in {core_hits}')
        print(f'      saved regular graph (networkx filler) isomorphic to delta-filled coordinate graph for '
              f'{full_hits or "none"}')
        print(f'      {len(choices(q))} choices of (a,c) give {len(classes)} isomorphism classes of cores')
        ok &= bool(core_hits)
        # save one coordinate graph for verify_record
        a, c = core_hits[0]
        n, edges = coords_graph(q, a, c)
        out = HERE / 'graphs' / f'coords_q{q}_d{q+2}_n{n}.json'
        out.parent.mkdir(exist_ok=True)
        out.write_text(json.dumps({'case': f'd{q+2}D3', 'construction': 'research/plus2/coords/coords.py',
                                   'q': q, 'a': a, 'c': c, 'filler': 'delta', 'value': n,
                                   'output': [n, edges]}))
        print(f'      wrote {out.relative_to(ROOT)} (a={a}, c={c})')

    print('== 2. AL vs lib.araujo_lopez_graph ==')
    for q in (4, 5, 7, 8, 9, 11, 13):
        target = canon(*lib.araujo_lopez_graph(q))
        hits = []
        for a in range(2, q):
            fr = coords.Frame(q, a)
            inc = coords.al_paper_matching(fr, coords.build_all(fr), all_i=True)
            n, edges, _ = coords.to_graph(fr, inc)
            if canon(n, edges) == target:
                hits.append(a)
        print(f'q={q}: lib AL graph isomorphic to coordinate AL (matching with all i != 0) for a in {hits}')
        ok &= bool(hits)

    print('== 3. negative controls (must fail) ==')
    for q in (5, 9, 13):
        fr = coords.Frame(q, 2, 3)
        core = coords.build_all(fr)
        norot = set(core)
        for t in fr.T:
            norot.discard((fr.X(t), fr.lam(fr.sigma[t])))
        nolink = core - {(('H', 1), ('K', 0))}
        for name, inc in (('no rotation', norot), ('no H_1 in K_0', nolink)):
            r = coords.check(fr, inc, q + 2)
            bad = r['diam'] is None or r['diam'] > 3
            print(f'q={q} {name}: diameter {r["diam"]}, points collinear {r["points_ok"]}, '
                  f'lines concurrent {r["lines_ok"]} -> {"fails as expected" if bad else "UNEXPECTEDLY VALID"}')
            ok &= bad
    print('== 4. duality: delta maps S_sigma onto the dual of S_sigma^-1 ==')
    for q in (4, 5, 7, 8, 9, 11, 13):
        good = True
        for a, c in choices(q):
            good &= duality_holds(q, a, c)
        al = all(duality_holds(q, a) for a in range(2, q))
        print(f'q={q}: all {len(choices(q))} choices: {good}; AL self-dual under delta for every a: {al}')
        good &= al
        ok &= good
    print('ALL OK' if ok else 'FAILURES')
    return ok


def duality_holds(q, a, c=None):
    """4 hats: delta(S_sigma) = dual of S_sigma^-1.  AL (c=None): delta(A) = dual of A."""
    fr = coords.Frame(q, a, c)
    core = coords.by_rules(fr)
    F = fr.F
    def d_point(p):                      # point of S_sigma -> line of S_sigma^-1
        if p[0] == 'pt':
            return coords.delta_point(fr, p)
        return ('M',) if p == ('Q',) else ('K', p[1])

    def d_line(L):                       # line of S_sigma -> point of S_sigma^-1
        if L[0] == 'ln':
            u, v, w = L[1]
            return fr.pt((u, w, F.neg(v)))
        return ('Q',) if L == ('M',) else ('H', L[1])

    image = {(d_line(L), d_point(p)) for p, L in core}
    fr2 = coords.Frame(q, a, c)
    if c is not None:
        fr2.sigma, fr2.sigma_inv = fr.sigma_inv, fr.sigma
    return image == coords.by_rules(fr2)


if __name__ == '__main__':
    sys.exit(0 if main() else 1)
