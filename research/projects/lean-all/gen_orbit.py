#!/usr/bin/env python3
"""Generate Lean files for the orbit-BFS checker (lean/BipartiteDD/LeanAll/Orbit.lean).

Input: an edge list (one "u v" per line, vertices 0..n-1; a first line "n m" is skipped if it has two numbers and the
file's vertex count matches), the degree d, the diameter D, and optionally automorphism generators (a JSON file with a
list of permutations, each a list of n images). The script

  * checks the generators are automorphisms (so the Lean checks will pass),
  * picks one representative per orbit, renumbers the vertices so that the representatives are 0..m-1 and every other
    vertex v has a generator g with g(v) < v (a search from the representatives along inverse generators),
  * runs the source BFS itself and checks that the diameter is at most D,
  * writes the Lean modules: Data (adjacency, colours, generators), Local, Perm<i>, Orbit, Bfs<c> (one per block of
    sources) and Record.

Usage: gen_orbit.py EDGES d D NAME OUTDIR [--gens GENS.json] [--chunk K] [--namespace NS] [--theorem THM]
"""
import argparse, json, os, sys, gzip
from collections import deque


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
    ap.add_argument('d', type=int)
    ap.add_argument('D', type=int)
    ap.add_argument('name')
    ap.add_argument('outdir')
    ap.add_argument('--gens')
    ap.add_argument('--chunk', type=int, default=1024)
    ap.add_argument('--module', required=True, help='Lean module prefix, e.g. BipartiteDD.LeanAll.D8D5')
    ap.add_argument('--theorem', required=True)
    ap.add_argument('--n', type=int, default=None)
    ap.add_argument('--source', default='')
    args = ap.parse_args()

    edges = read_edges(args.edges)
    # a header line "n m" would show up as an edge; drop it if it is not a real edge
    n = args.n if args.n is not None else 1 + max(max(u, v) for u, v in edges)
    E = set()
    for u, v in edges:
        if u == v:
            sys.exit(f'loop at {u}')
        if not (0 <= u < n and 0 <= v < n):
            sys.exit(f'bad edge {u} {v}')
        E.add((min(u, v), max(u, v)))
    adj = [[] for _ in range(n)]
    for u, v in E:
        adj[u].append(v)
        adj[v].append(u)
    deg = max(len(a) for a in adj)
    print(f'n={n} edges={len(E)} maxdeg={deg}', file=sys.stderr)
    assert deg <= args.d, 'degree too large'

    # colouring
    col = [None] * n
    for s in range(n):
        if col[s] is None:
            col[s] = False
            dq = deque([s])
            while dq:
                u = dq.popleft()
                for v in adj[u]:
                    if col[v] is None:
                        col[v] = not col[u]
                        dq.append(v)
                    elif col[v] == col[u]:
                        sys.exit('not bipartite')

    gens = []
    if args.gens:
        gens = json.load(open(args.gens))
    adjset = [set(a) for a in adj]
    for gi, g in enumerate(gens):
        assert len(g) == n and sorted(g) == list(range(n)), f'generator {gi} is not a permutation'
        for u in range(n):
            if {g[v] for v in adj[u]} != adjset[g[u]]:
                sys.exit(f'generator {gi} is not an automorphism at {u}')
    ginv = []
    for g in gens:
        h = [0] * n
        for v in range(n):
            h[g[v]] = v
        ginv.append(h)

    # orbits and numbering: representatives first, then a search along inverse generators
    seen = [False] * n
    reps = []
    for s in range(n):
        if not seen[s]:
            reps.append(s)
            seen[s] = True
            dq = deque([s])
            while dq:
                u = dq.popleft()
                for h in ginv:
                    v = h[u]
                    if not seen[v]:
                        seen[v] = True
                        dq.append(v)
    m = len(reps)
    order = list(reps)
    num = [-1] * n
    for i, r in enumerate(reps):
        num[r] = i
    dq = deque(reps)
    while dq:
        u = dq.popleft()
        for h in ginv:
            v = h[u]
            if num[v] < 0:
                num[v] = len(order)
                order.append(v)
                dq.append(v)
    assert len(order) == n
    print(f'orbits m={m}', file=sys.stderr)

    # relabel
    nadj = [sorted(num[v] for v in adj[order[i]]) for i in range(n)]
    ncol = [col[order[i]] for i in range(n)]
    ngens = [[num[g[order[i]]] for i in range(n)] for g in gens]
    nginv = [[num[h[order[i]]] for i in range(n)] for h in ginv]
    for g in ngens:
        for v in range(m, n):
            pass
    for v in range(m, n):
        assert any(g[v] < v for g in ngens)

    # check the source BFS (eccentricity of every representative)
    for s in range(m):
        dist = [-1] * n
        dist[s] = 0
        dq = deque([s])
        while dq:
            u = dq.popleft()
            for v in nadj[u]:
                if dist[v] < 0:
                    dist[v] = dist[u] + 1
                    dq.append(v)
        ecc = max(dist)
        assert min(dist) >= 0, 'disconnected'
        assert ecc <= args.D, f'representative {s} has eccentricity {ecc} > {args.D}'
    print('python check: every representative has eccentricity <= D', file=sys.stderr)

    K = max(1, (n - 1).bit_length())
    chunks = []
    lo = 0
    while lo < m:
        k = min(args.chunk, m - lo)
        chunks.append((lo, k))
        lo += k

    os.makedirs(args.outdir, exist_ok=True)
    M = args.module
    hdr = f'/- Generated by research/projects/lean-all/gen_orbit.py. Do not edit by hand. -/\n'
    ns = M

    def lst(xs):
        return '[' + ', '.join(str(x) for x in xs) + ']'

    with open(os.path.join(args.outdir, 'Data.lean'), 'w') as f:
        f.write(hdr)
        f.write(f'import BipartiteDD.LeanAll.Orbit\n\n')
        src = f' ({args.source})' if args.source else ''
        f.write(f'/-! Data of the {args.name} graph{src}: {n} vertices, degree {args.d}, diameter {args.D};\n')
        f.write(f'{len(gens)} automorphism generators, {m} orbit representatives (vertices 0 … {m-1}). -/\n\n')
        f.write(f'namespace {ns}\n\n')
        f.write('set_option maxRecDepth 100000\n\n')
        f.write(f'/-- Neighbour lists. -/\ndef adj : List (List ℕ) := [\n')
        f.write(',\n'.join('  ' + lst(a) for a in nadj))
        f.write(']\n\n')
        f.write(f'/-- The colouring. -/\ndef col : List Bool := [\n')
        f.write(',\n'.join('  ' + ', '.join('true' if c else 'false' for c in ncol[i:i + 32]) for i in range(0, n, 32)))
        f.write(']\n\n')
        for gi in range(len(gens)):
            for nm, data in ((f'g{gi}', ngens[gi]), (f'h{gi}', nginv[gi])):
                f.write(f'def {nm} : List ℕ := [\n')
                f.write(',\n'.join('  ' + ', '.join(str(x) for x in data[i:i + 32]) for i in range(0, n, 32)))
                f.write(']\n\n')
        f.write(f'end {ns}\n')

    def thm_file(fname, body, extra_import=''):
        with open(os.path.join(args.outdir, fname), 'w') as f:
            f.write(hdr)
            f.write(f'import {M}.Data\n{extra_import}\n')
            f.write(f'namespace {ns}\n\nopen BipartiteDD.Fast BipartiteDD.LeanAll.Orbit\n\n')
            f.write(body)
            f.write(f'\nend {ns}\n')

    thm_file('Local.lean',
             f'theorem local_ok : localOK {K} {args.d} {n} (Tree.build [] {K} adj) (Tree.build false {K} col) 0 {n} = true := by\n'
             f'  decide +kernel\n')
    for gi in range(len(gens)):
        thm_file(f'Perm{gi}.lean',
                 f'theorem perm{gi}_ok : permOK {K} {n} (Tree.build [] {K} adj) (Tree.build 0 {K} g{gi}) (Tree.build 0 {K} h{gi}) 0 {n} = true := by\n'
                 f'  decide +kernel\n')
    glist = '[' + ', '.join(f'(g{gi}, h{gi})' for gi in range(len(gens))) + ']' if gens else '([] : List (List ℕ × List ℕ))'
    if gens:
        thm_file('Orbit.lean',
                 f'theorem orbit_ok : orbitOK {K} {m} {n} {glist} = true := by\n  decide +kernel\n')
    for ci, (lo, k) in enumerate(chunks):
        thm_file(f'Bfs{ci:02d}.lean',
                 f'theorem bfs{ci:02d}_ok : bfsOK {K} {args.D} {n} {lo} {k} (Tree.build [] {K} adj) = true := by\n'
                 f'  decide +kernel\n')

    # record
    imports = [f'{M}.Local'] + [f'{M}.Perm{gi}' for gi in range(len(gens))] + \
              ([f'{M}.Orbit'] if gens else []) + [f'{M}.Bfs{ci:02d}' for ci in range(len(chunks))]
    with open(os.path.join(args.outdir, 'Record.lean'), 'w') as f:
        f.write(hdr)
        for im in imports:
            f.write(f'import {im}\n')
        f.write(f'\n/-! The {args.name} record: {n} vertices, degree {args.d}, diameter {args.D}. -/\n\n')
        f.write(f'namespace {ns}\n\nopen BipartiteDD.Fast BipartiteDD.LeanAll.Orbit\n\n')
        f.write(f'theorem hK : {n} ≤ 2 ^ {K} := by decide\n\n')
        f.write(f'theorem hL : LocalSpec {args.d} {n} adj col := localSpec_of hK local_ok\n\n')
        if gens:
            f.write(f'theorem hP : ∀ g ∈ {glist}, PermSpec {n} adj (fun v => g.1.getD v 0) (fun v => g.2.getD v 0) := by\n')
            f.write('  intro g hg\n  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg\n')
            f.write('  rcases hg with ' + ' | '.join('rfl' for _ in gens) + '\n')
            f.write('  exacts [' + ', '.join(f'permSpec_of hL hK perm{gi}_ok' for gi in range(len(gens))) + ']\n\n')
            f.write(f'theorem hO : ∀ v, {m} ≤ v → v < {n} → ∃ g ∈ {glist}, g.1.getD v 0 < v := orbit_of hK orbit_ok\n\n')
        else:
            f.write(f'theorem hP : ∀ g ∈ {glist}, PermSpec {n} adj (fun v => g.1.getD v 0) (fun v => g.2.getD v 0) := by\n  simp\n\n')
            f.write(f'theorem hO : ∀ v, {m} ≤ v → v < {n} → ∃ g ∈ {glist}, g.1.getD v 0 < v := by\n  intro v h1 h2; omega\n\n')
        # bfs assembly
        f.write(f'theorem hB : ∀ s (hs : s < {n}), s < {m} → ∀ v : Fin {n}, (graphL {n} adj).edist v ⟨s, hs⟩ ≤ {args.D} := by\n')
        f.write('  intro s hs hm v\n')
        if len(chunks) == 1:
            lo, k = chunks[0]
            f.write(f'  have := edist_of_bfs hL hK bfs00_ok v s (by omega) (by omega)\n')
            f.write(f'  simpa using this\n')
        else:
            ck = args.chunk
            cases = ' ∨ '.join(f's / {ck} = {ci}' for ci in range(len(chunks)))
            f.write(f'  have hc : {cases} := by omega\n')
            f.write('  rcases hc with ' + ' | '.join('hc' for _ in chunks) + '\n')
            for ci, (lo, k) in enumerate(chunks):
                f.write(f'  · have := edist_of_bfs hL hK bfs{ci:02d}_ok v (s - {lo}) (by omega) (by omega)\n')
                f.write(f'    rwa [show {lo} + (s - {lo}) = s by omega] at this\n')
        f.write('\n')
        f.write(f'theorem isBipartiteDegDiam_G : BipartiteDD.IsBipartiteDegDiam (graphL {n} adj) {args.d} {args.D} :=\n')
        f.write(f'  isBipartiteDegDiam_of hL {glist} hP hO hB\n\n')
        f.write(f'end {ns}\n\n')
        f.write(f'open {ns} BipartiteDD.LeanAll.Orbit in\n')
        f.write(f'/-- A bipartite graph on {n} vertices with degree at most {args.d} and diameter at most {args.D}. -/\n')
        f.write(f'theorem {args.theorem} : ∃ G : SimpleGraph (Fin {n}), BipartiteDD.IsBipartiteDegDiam G {args.d} {args.D} :=\n')
        f.write(f'  ⟨graphL {n} adj, isBipartiteDegDiam_G⟩\n')
    print(f'wrote {args.outdir}: K={K}, chunks={len(chunks)}', file=sys.stderr)


if __name__ == '__main__':
    main()
