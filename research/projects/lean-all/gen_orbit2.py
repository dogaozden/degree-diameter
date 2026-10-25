#!/usr/bin/env python3
"""Generate Lean files for the orbit-BFS checker, version 2 (lean/BipartiteDD/LeanAll/Orbit2.lean): data as trees.

Input: an edge list (one "u v" per line, vertices 0..n-1; a first line "n m" is skipped if it has two numbers and the
file's vertex count matches), the degree d, the diameter D, and optionally automorphism generators (a JSON file with a
list of permutations, each a list of n images). The script

  * checks the generators are automorphisms (so the Lean checks will pass),
  * picks one representative per orbit, renumbers the vertices so that the representatives are 0..m-1 and every other
    vertex v has a generator g with g(v) < v (a search from the representatives along inverse generators),
  * runs the source BFS itself and checks that the diameter is at most D,
  * writes the Lean modules: Data (adjacency, colours, generators), Local, Perm<i>, Orbit, Bfs<c> (one per block of
    sources) and Record.

Usage: gen_orbit2.py EDGES d D NAME OUTDIR [--gens GENS.json] [--chunk K] [--namespace NS] [--theorem THM]
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
    ap.add_argument('--chunk', type=int, default=1024, help='sources per BFS module')
    ap.add_argument('--vchunk', type=int, default=8192, help='vertices per local/perm/orbit module')
    ap.add_argument('--block', type=int, default=8, help='log2 of the leaves per data block')
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
    L = min(args.block, K)
    chunks = []
    lo = 0
    while lo < m:
        k = min(args.chunk, m - lo)
        chunks.append((lo, k))
        lo += k
    vch = []
    lo = 0
    while lo < n:
        k = min(args.vchunk, n - lo)
        vch.append((lo, k))
        lo += k
    och = []
    lo = m
    while lo < n:
        k = min(args.vchunk, n - lo)
        och.append((lo, k))
        lo += k

    os.makedirs(args.outdir, exist_ok=True)
    M = args.module
    ns = M
    hdr = '/- Generated by research/projects/lean-all/gen_orbit2.py. Do not edit by hand. -/\n'

    def tree_defs(f, name, typ, leaves, pad, fmt):
        """Write `name` : Tree typ with leaf i = leaves[i] (pad beyond), as 2^(K-L) blocks of 2^L leaves."""
        nb = 1 << (K - L)
        bs = 1 << L

        def sub(vals, depth):
            if depth == 0:
                return '.leaf ' + vals[0]
            h = len(vals) // 2
            return '.node (' + sub(vals[:h], depth - 1) + ') (' + sub(vals[h:], depth - 1) + ')'
        f.write(f'def {name}Pad : Tree ({typ}) := {sub([pad] * bs, L)}\n\n')
        names = []
        for b in range(nb):
            lo = b * bs
            if lo >= len(leaves):
                names.append(f'{name}Pad')
                continue
            vals = [fmt(leaves[i]) if i < len(leaves) else pad for i in range(lo, lo + bs)]
            f.write(f'def {name}{b} : Tree ({typ}) :=\n  {sub(vals, L)}\n\n')
            names.append(f'{name}{b}')

        def top(ns_, depth):
            if depth == 0:
                return ns_[0]
            h = len(ns_) // 2
            return '.node (' + top(ns_[:h], depth - 1) + ') (' + top(ns_[h:], depth - 1) + ')'
        f.write(f'def {name} : Tree ({typ}) :=\n  {top(names, K - L)}\n\n')

    def lst(xs):
        return '[' + ', '.join(str(x) for x in xs) + ']'

    with open(os.path.join(args.outdir, 'Data.lean'), 'w') as f:
        f.write(hdr)
        f.write('import BipartiteDD.LeanAll.Orbit2\n\n')
        src = f' ({args.source})' if args.source else ''
        f.write(f'/-! Data of the {args.name} graph{src}: {n} vertices, degree {args.d}, diameter {args.D};\n')
        f.write(f'{len(gens)} automorphism generators, {m} orbit representatives (vertices 0 … {m-1}).\n')
        f.write(f'Trees of depth {K}; leaf `v` is the data of vertex `v`. -/\n\n')
        f.write(f'namespace {ns}\n\nopen BipartiteDD.Fast BipartiteDD.LeanAll.Orbit2\n\n')
        f.write('set_option maxRecDepth 100000\nset_option maxHeartbeats 0\n\n')
        tree_defs(f, 'adjT', 'List ℕ', nadj, '[]', lst)
        tree_defs(f, 'colT', 'Bool', ncol, 'false', lambda c: 'true' if c else 'false')
        for gi in range(len(gens)):
            tree_defs(f, f'g{gi}T', 'ℕ', ngens[gi], '0', str)
            tree_defs(f, f'h{gi}T', 'ℕ', nginv[gi], '0', str)
        f.write(f'/-- Neighbour lists. -/\nnoncomputable def nb (v : ℕ) : List ℕ := look adjT {K} v\n\n')
        f.write(f'/-- The colouring. -/\nnoncomputable def cl (v : ℕ) : Bool := look colT {K} v\n\n')
        for gi in range(len(gens)):
            f.write(f'/-- Generator {gi} and its inverse. -/\nnoncomputable def g{gi} (v : ℕ) : ℕ := look g{gi}T {K} v\n\n')
            f.write(f'noncomputable def h{gi} (v : ℕ) : ℕ := look h{gi}T {K} v\n\n')
        f.write(f'end {ns}\n')

    def thm_file(fname, body):
        with open(os.path.join(args.outdir, fname), 'w') as f:
            f.write(hdr)
            f.write(f'import {M}.Data\n\n')
            f.write(f'namespace {ns}\n\nopen BipartiteDD.LeanAll.Orbit2\n\n')
            f.write(body)
            f.write(f'\nend {ns}\n')

    glist = '[' + ', '.join(f'(g{gi}, h{gi})' for gi in range(len(gens))) + ']' if gens else '([] : List ((ℕ → ℕ) × (ℕ → ℕ)))'
    mods = []
    for ci, (lo, k) in enumerate(vch):
        thm_file(f'Local{ci:02d}.lean', f'theorem local{ci:02d} : localOK {args.d} {n} nb cl {lo} {k} = true := by\n  decide +kernel\n')
        mods.append(f'Local{ci:02d}')
        for gi in range(len(gens)):
            thm_file(f'Perm{gi}_{ci:02d}.lean', f'theorem perm{gi}_{ci:02d} : permOK {n} nb g{gi} h{gi} {lo} {k} = true := by\n  decide +kernel\n')
            mods.append(f'Perm{gi}_{ci:02d}')
    for ci, (lo, k) in enumerate(och):
        thm_file(f'Orbit{ci:02d}.lean', f'theorem orbit{ci:02d} : orbitOK {glist} {lo} {k} = true := by\n  decide +kernel\n')
        mods.append(f'Orbit{ci:02d}')
    for ci, (lo, k) in enumerate(chunks):
        thm_file(f'Bfs{ci:02d}.lean', f'theorem bfs{ci:02d} : bfsOK {K} {args.D} {n} {lo} {k} nb = true := by\n  decide +kernel\n')
        mods.append(f'Bfs{ci:02d}')

    def case_split(f, var, ranges, body, indent='  '):
        """Write a proof that splits `var` by which range [lo, lo+k) contains it; body(ci, lo, k) is the branch."""
        if len(ranges) == 1:
            lo, k = ranges[0]
            f.write(body(0, lo, k, indent))
            return
        conds = []
        for ci, (lo, k) in enumerate(ranges):
            conds.append(f'({lo} ≤ {var} ∧ {var} < {lo + k})')
        f.write(f'{indent}have hc : ' + ' ∨ '.join(conds) + ' := by omega\n')
        f.write(f'{indent}rcases hc with ' + ' | '.join('hc' for _ in ranges) + '\n')
        for ci, (lo, k) in enumerate(ranges):
            f.write(body(ci, lo, k, indent + '· ').replace('\n' + indent + '· ', '\n' + indent + '  ', ).rstrip('\n') + '\n')

    with open(os.path.join(args.outdir, 'Record.lean'), 'w') as f:
        f.write(hdr)
        for im in mods:
            f.write(f'import {M}.{im}\n')
        f.write(f'\n/-! The {args.name} record: {n} vertices, degree {args.d}, diameter {args.D}. -/\n\n')
        f.write(f'namespace {ns}\n\nopen BipartiteDD.LeanAll.Orbit2\n\n')
        f.write(f'theorem hK : {n} ≤ 2 ^ {K} := by decide\n\n')
        f.write(f'theorem hL : LocalSpec {args.d} {n} nb cl := by\n  apply localSpec_of\n  intro u hu\n')
        case_split(f, 'u', vch, lambda ci, lo, k, ind: f'{ind}exact localOK_one local{ci:02d} u (by omega) (by omega)\n')
        f.write('\n')
        for gi in range(len(gens)):
            f.write(f'theorem hP{gi} : PermSpec {n} nb g{gi} h{gi} := by\n  apply permSpec_of\n  intro v hv\n')
            case_split(f, 'v', vch, lambda ci, lo, k, ind, gi=gi: f'{ind}exact permOK_one perm{gi}_{ci:02d} v (by omega) (by omega)\n')
            f.write('\n')
        f.write(f'theorem hP : ∀ g ∈ {glist}, PermSpec {n} nb g.1 g.2 := by\n')
        if gens:
            f.write('  intro g hg\n  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg\n')
            f.write('  rcases hg with ' + ' | '.join('rfl' for _ in gens) + '\n')
            f.write('  exacts [' + ', '.join(f'hP{gi}' for gi in range(len(gens))) + ']\n\n')
        else:
            f.write('  simp\n\n')
        f.write(f'theorem hO : ∀ v, {m} ≤ v → v < {n} → ∃ g ∈ {glist}, g.1 v < v := by\n  intro v hm hv\n')
        if och:
            case_split(f, 'v', och, lambda ci, lo, k, ind: f'{ind}exact orbit_of orbit{ci:02d} v (by omega) (by omega)\n')
        else:
            f.write('  omega\n')
        f.write('\n')
        f.write(f'theorem hB : ∀ s (hs : s < {n}), s < {m} → ∀ v : Fin {n}, (graphF {n} nb).edist v ⟨s, hs⟩ ≤ {args.D} := by\n')
        f.write('  intro s hs hm v\n')
        case_split(f, 's', chunks, lambda ci, lo, k, ind: f'{ind}exact edist_of_bfs\' hL hK bfs{ci:02d} v s hs (by omega) (by omega)\n')
        f.write('\n')
        f.write(f'theorem isBipartiteDegDiam_G : BipartiteDD.IsBipartiteDegDiam (graphF {n} nb) {args.d} {args.D} :=\n')
        f.write(f'  isBipartiteDegDiam_of hL {glist} hP hO hB\n\n')
        f.write(f'end {ns}\n\n')
        f.write(f'open {ns} BipartiteDD.LeanAll.Orbit2 in\n')
        f.write(f'/-- A bipartite graph on {n} vertices with degree at most {args.d} and diameter at most {args.D}. -/\n')
        f.write(f'theorem {args.theorem} : ∃ G : SimpleGraph (Fin {n}), BipartiteDD.IsBipartiteDegDiam G {args.d} {args.D} :=\n')
        f.write(f'  ⟨graphF {n} nb, isBipartiteDegDiam_G⟩\n')
    print(f'wrote {args.outdir}: K={K}, bfs chunks={len(chunks)}, vertex chunks={len(vch)}, modules={len(mods)}', file=sys.stderr)


if __name__ == '__main__':
    main()
