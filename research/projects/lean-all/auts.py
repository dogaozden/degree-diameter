#!/usr/bin/env python3
"""Automorphism generators of a graph from an edge list, with nauty's dreadnaut (or Traces).

usage: auts.py EDGES OUT.json [--dreadnaut PATH] [--traces] [--fix v1,v2,...] [--colour-classes]
Writes a JSON list of permutations (each a list of n images). Every generator is re-checked here."""
import argparse, json, re, subprocess, sys, gzip


def read_edges(path):
    op = gzip.open if path.endswith('.gz') else open
    edges = []
    with op(path, 'rt') as f:
        for line in f:
            p = line.split()
            if len(p) < 2 or p[0].startswith('#'):
                continue
            edges.append((int(p[0]), int(p[1])))
    return edges


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('edges')
    ap.add_argument('out')
    ap.add_argument('--dreadnaut', default='/tmp/claude-0/nauty/pynauty-2.8.8.1/src/nauty2_8_8/dreadnaut')
    ap.add_argument('--traces', action='store_true')
    ap.add_argument('--partition', default='', help='dreadnaut partition string, e.g. "0:9|10:19"')
    args = ap.parse_args()
    edges = read_edges(args.edges)
    n = 1 + max(max(u, v) for u, v in edges)
    adj = [[] for _ in range(n)]
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
    lines = ['At' if args.traces else 'As', '-m', '+a', f'n={n} g']
    for u in range(n):
        lines.append(f'{u}: ' + ' '.join(str(v) for v in adj[u] if v > u) + ';')
    lines[-1] = lines[-1][:-1] + '.'
    if args.partition:
        lines.append('f=[' + args.partition + ']')
    lines.append('x')
    lines.append('q')
    res = subprocess.run([args.dreadnaut], input='\n'.join(lines) + '\n', capture_output=True, text=True)
    out = res.stdout
    gens = []
    cur = None
    # generators are printed as cycles, possibly over several lines; each starts with "("
    text = out
    # split into generator blocks: a generator ends at a line not starting with whitespace or "("
    blocks = []
    buf = []
    for line in text.splitlines():
        s = line.strip()
        if s.startswith('('):
            if buf and not line.startswith(' '):
                blocks.append(' '.join(buf))
                buf = []
            buf.append(s)
        elif line.startswith('   ') and buf:
            buf.append(s)
        else:
            if buf:
                blocks.append(' '.join(buf))
                buf = []
    if buf:
        blocks.append(' '.join(buf))
    for b in blocks:
        perm = list(range(n))
        for cyc in re.findall(r'\(([^)]*)\)', b):
            xs = [int(x) for x in cyc.split()]
            for i, x in enumerate(xs):
                perm[x] = xs[(i + 1) % len(xs)]
        gens.append(perm)
    m = re.search(r'grpsize=([0-9.e+]+)', out)
    orb = re.search(r'(\d+) orbits?', out)
    print(f'n={n} generators={len(gens)} grpsize={m.group(1) if m else "?"} orbits={orb.group(1) if orb else "?"}',
          file=sys.stderr)
    adjset = [set(a) for a in adj]
    for gi, g in enumerate(gens):
        assert sorted(g) == list(range(n))
        for u in range(n):
            assert {g[v] for v in adj[u]} == adjset[g[u]], f'generator {gi} fails at {u}'
    json.dump(gens, open(args.out, 'w'))


if __name__ == '__main__':
    main()
