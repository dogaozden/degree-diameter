#!/usr/bin/env python3
"""Fast degree-sequence cubes for the A-only instance (k = 11 is the target).
The base CNF (normal form `--nf2` + `--ntt`, no lex-leader) is written once with the map of the a-variables. Each cube
appends (i) exact cardinality constraints for the row sums alpha of B (order of O) and the column sums beta (order of I),
both non-increasing, and (ii) lex-leader clauses for the transpositions of O (acting on R through the pair labels)
inside blocks of equal alpha and for the transpositions of I inside blocks of equal beta, in the same row-major order
as enc_quot.py.
Soundness: relabel O so that alpha is non-increasing and I so that beta is non-increasing; every solution lies in the
cube of its (alpha, beta), and inside a cube the block permutations are symmetries, so lex-leader for them is sound.
usage: abcube.py base k base.cnf
       abcube.py cube base.cnf a1,..,a9/b1,..,b9 out.cnf [--maxt]   (--maxt did not help: 3x larger CNF, test cube unsolved in 20 min)
--maxt: vertex 0 has the maximum number of directed triangles, so add "every vertex lies on at most t = sum(alpha)
        directed triangles" (a valid choice of base vertex; it removes the cubes with small t far more easily)."""
import sys, itertools, json
from pysat.formula import IDPool
from pysat.card import CardEnc, EncType

def write_base(k, path):
    from enc_quot import build
    cnf, pool, a = build(k, sym=False, nf2=True, ntt=True)
    cnf.to_file(path)
    json.dump({'k': k, 'nv': cnf.nv, 'a': [[c, d, v] for (c, d), v in a.items()]}, open(path + '.map.json', 'w'))
    print(f'base: vars={cnf.nv} clauses={len(cnf.clauses)}')

def cube_clauses(meta, al, be):
    k = meta['k']; g = k - 2; m = k * (k - 1) // 2
    a = {(c, d): v for c, d, v in meta['a']}
    pool = IDPool(start_from=meta['nv'] + 1)
    O = list(range(1, g + 1)); I = list(range(g + 1, 2 * g + 1)); R = list(range(2 * g + 1, m))
    out = []
    for x, r in zip(O, al):
        out += CardEnc.equals([a[x, z] for z in I], bound=r, vpool=pool, encoding=EncType.seqcounter).clauses
    for z, r in zip(I, be):
        out += CardEnc.equals([a[x, z] for x in O], bound=r, vpool=pool, encoding=EncType.seqcounter).clauses
    V = range(m)
    order = [(c, d) for c in V for d in V if c != d]
    pairs = list(itertools.combinations(O, 2)); pidx = {p: y for y, p in zip(R, pairs)}; ridx = {y: p for y, p in zip(R, pairs)}
    def lexleader(pi):
        seq = [(a[c, d], a[pi(c), pi(d)]) for (c, d) in order if (pi(c), pi(d)) != (c, d)]
        e = None
        for i, (x, y) in enumerate(seq):
            out.append(([-e] if e else []) + [-x, y])
            if i == len(seq) - 1: break
            e2 = pool.id()
            out.append(([-e] if e else []) + [-x, -y, e2]); out.append(([-e] if e else []) + [x, y, e2]); e = e2
    for i in range(g):
        for j in range(i + 1, g):
            if al[i] == al[j]:
                u, v = O[i], O[j]
                sw = lambda t, u=u, v=v: v if t == u else (u if t == v else t)
                lexleader(lambda t, sw=sw: pidx[tuple(sorted((sw(ridx[t][0]), sw(ridx[t][1]))))] if t in ridx else sw(t))
            if be[i] == be[j]:
                u, v = I[i], I[j]
                lexleader(lambda t, u=u, v=v: v if t == u else (u if t == v else t))
    return out, pool.top

def maxt_clauses(meta, t, start):
    """Vertex 0 is chosen with the maximum number of directed triangles (a valid choice of base vertex), so every
    vertex v lies on at most t = sum(alpha) directed triangles v->x->z->v."""
    k = meta['k']; m = k * (k - 1) // 2
    a = {(c, d): v for c, d, v in meta['a']}
    pool = IDPool(start_from=start)
    out = []; tri = {}
    for v in range(m):
        for x in range(m):
            for z in range(m):
                if len({v, x, z}) < 3: continue
                key = min((v, x, z), (x, z, v), (z, v, x))
                if key not in tri:
                    q = pool.id(); tri[key] = q
                    p, r, s_ = key
                    out += [[-q, a[p, r]], [-q, a[r, s_]], [-q, a[s_, p]], [q, -a[p, r], -a[r, s_], -a[s_, p]]]
    for v in range(1, m):
        lits = [tri[min((v, x, z), (x, z, v), (z, v, x))] for x in range(m) for z in range(m) if len({v, x, z}) == 3]
        out += CardEnc.atmost(lits, bound=t, vpool=pool, encoding=EncType.seqcounter).clauses
    return out, pool.top

def write_cube(base, spec, outp, maxt=False):
    meta = json.load(open(base + '.map.json'))
    al, be = spec.split('/'); al = list(map(int, al.split(','))); be = list(map(int, be.split(',')))
    assert al == sorted(al, reverse=True) and be == sorted(be, reverse=True) and sum(al) == sum(be)
    extra, top = cube_clauses(meta, al, be)
    if maxt:
        e2, top = maxt_clauses(meta, sum(al), top + 1)
        extra += e2
    with open(base) as fin, open(outp, 'w') as fo:
        hdr = fin.readline().split()
        fo.write(f'p cnf {max(top, int(hdr[2]))} {int(hdr[3]) + len(extra)}\n')
        for line in fin: fo.write(line)
        for c in extra: fo.write(' '.join(map(str, c)) + ' 0\n')

if __name__ == '__main__':
    if sys.argv[1] == 'base': write_base(int(sys.argv[2]), sys.argv[3])
    else: write_cube(sys.argv[2], sys.argv[3], sys.argv[4], maxt='--maxt' in sys.argv)
