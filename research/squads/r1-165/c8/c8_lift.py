#!/usr/bin/env python3
"""C8 explorer: a Singer-invariant (C_121) graph on flags of PG(4,3) with a new orbit of solids.

Base graph (the PG(4,3) flag graph): A = point-plane flags (15730), B = line-solid flags (15730),
adjacent iff P < L < pi < S. The Singer cycle C_121 of PGL(5,3) acts semiregularly on A and on B,
giving 130 orbits on each side. Candidate: add the 121 solids as one new C_121-orbit on side B
(so |A| + |B| = 15730 + 15851 = 31581). Each solid orbit is joined to 16 A-orbits by moving one
base edge of each of 16 A-orbits from its flag neighbour to the solid. A-degrees stay 16.

Usage: c8_lift.py baseline | random | sa SECONDS [SEED]
"""
import itertools, os, sys, time, random, math, subprocess, json

TMP = '/tmp/claude-0/c8'
OUT = os.path.dirname(os.path.abspath(__file__))
os.makedirs(TMP, exist_ok=True)
q, n = 3, 5
NV = q ** n
vecs = list(itertools.product(range(q), repeat=n))
idx = {v: i for i, v in enumerate(vecs)}
ZERO = idx[(0,) * n]
ADD = [[idx[tuple((a + b) % q for a, b in zip(vecs[i], vecs[j]))] for j in range(NV)] for i in range(NV)]
MUL = [[idx[tuple((c * a) % q for a in vecs[i])] for i in range(NV)] for c in range(q)]
preps = [i for i, v in enumerate(vecs) if any(v) and next(a for a in v if a) == 1]
assert len(preps) == 121

NA = 15730          # |A| = |point-plane flags|
NBF = 15730         # line-solid flags
NSOL = 121          # solids (one new C_121-orbit)
OFF_B = NA          # global index of B-flag b is OFF_B + b
OFF_S = NA + NBF    # global index of solid s is OFF_S + s
NTOT = OFF_S + NSOL
D = 5
NORB = 130          # orbits of C_121 on A and on B-flags
L = 121


def mask_of(S):
    m = 0
    for s in S:
        m |= 1 << s
    return m


def build_subspaces():
    level = {}
    for p in preps:
        S = {ZERO, p, MUL[2][p]}
        level[mask_of(S)] = S
    levels = {1: level}
    for d in (2, 3, 4):
        out = {}
        for m, S in level.items():
            for p in preps:
                if (m >> p) & 1:
                    continue
                S2 = S | {ADD[s][p] for s in S} | {ADD[s][MUL[2][p]] for s in S}
                m2 = mask_of(S2)
                if m2 not in out:
                    out[m2] = S2
        level = out
        levels[d] = level
    return [list(levels[d].keys()) for d in (1, 2, 3, 4)]


def build_flags():
    P, LL, PL, S = build_subspaces()
    assert (len(P), len(LL), len(PL), len(S)) == (121, 1210, 1210, 121), (len(P), len(LL), len(PL), len(S))
    inc = lambda x, y: (x & y) == x
    Pi = {m: i for i, m in enumerate(P)}
    Li = {m: i for i, m in enumerate(LL)}
    PLi = {m: i for i, m in enumerate(PL)}
    Si = {m: i for i, m in enumerate(S)}
    A = [(Pi[p], PLi[pl]) for pl in PL for p in P if inc(p, pl)]
    B = [(Li[l], Si[s]) for s in S for l in LL if inc(l, s)]
    assert len(A) == NA and len(B) == NBF
    Aidx = {f: i for i, f in enumerate(A)}
    Bidx = {f: i for i, f in enumerate(B)}
    lines_in = {pl: [li for li, l in enumerate(LL) if inc(l, pl)] for pl in PL}
    sols_over = {pl: [si for si, s in enumerate(S) if inc(pl, s)] for pl in PL}
    NB = []
    for (pi_, pli) in A:
        p, pl = P[pi_], PL[pli]
        row = []
        for li in lines_in[pl]:
            if inc(p, LL[li]):
                for si in sols_over[pl]:
                    row.append(Bidx[(li, si)])
        assert len(row) == 16
        NB.append(row)
    return dict(P=P, L=LL, PL=PL, S=S, Pi=Pi, Li=Li, PLi=PLi, Si=Si, A=A, B=B, Aidx=Aidx, Bidx=Bidx, NB=NB)


def T(v, c):
    v0, v1, v2, v3, v4 = v
    c0, c1, c2, c3, c4 = c
    return ((c0 * v4) % 3, (v0 + c1 * v4) % 3, (v1 + c2 * v4) % 3, (v2 + c3 * v4) % 3, (v3 + c4 * v4) % 3)


def singer():
    """Companion matrix of a primitive polynomial over GF(3): its action on nonzero vectors is one 242-cycle."""
    e0 = (1, 0, 0, 0, 0)
    for c in itertools.product(range(3), repeat=5):
        if c[0] == 0:
            continue
        v, k = T(e0, c), 1
        while v != e0 and k < 300:
            v, k = T(v, c), k + 1
        if v == e0 and k == 242:
            return c
    raise RuntimeError('no primitive polynomial found')


def induce(masks, target_index, tperm):
    perm = []
    for m in masks:
        r, x = 0, m
        while x:
            low = x & -x
            r |= 1 << tperm[low.bit_length() - 1]
            x ^= low
        perm.append(target_index[r])
    return perm


def cycles(perm):
    seen = [False] * len(perm)
    out = []
    for k in range(len(perm)):
        if seen[k]:
            continue
        c, j = [], k
        while not seen[j]:
            seen[j] = True
            c.append(j)
            j = perm[j]
        out.append(c)
    return out


def setup():
    t0 = time.time()
    F = build_flags()
    c = singer()
    tperm = [idx[T(vecs[i], c)] for i in range(NV)]
    pperm = induce(F['P'], F['Pi'], tperm)
    lperm = induce(F['L'], F['Li'], tperm)
    plperm = induce(F['PL'], F['PLi'], tperm)
    sperm = induce(F['S'], F['Si'], tperm)
    assert sorted(sperm) == list(range(NSOL))
    pA = [F['Aidx'][(pperm[a0], plperm[a1])] for (a0, a1) in F['A']]
    pB = [F['Bidx'][(lperm[b0], sperm[b1])] for (b0, b1) in F['B']]
    cycA, cycB, solc = cycles(pA), cycles(pB), cycles(sperm)
    assert all(len(x) == L for x in cycA + cycB) and len(cycA) == NORB and len(cycB) == NORB
    assert len(solc) == 1 and len(solc[0]) == NSOL
    # invariance check of the base flag graph under the Singer map (sample)
    rng = random.Random(1)
    for _ in range(3000):
        a = rng.randrange(NA)
        b = rng.choice(F['NB'][a]) - 0
        assert (pB[b] in F['NB'][pA[a]]) or True
        assert pB[b] in set(F['NB'][pA[a]]), 'Singer map is not an automorphism'
    orbitB = [0] * NBF
    posB = [0] * NBF
    for o, cyc in enumerate(cycB):
        for k, b in enumerate(cyc):
            orbitB[b], posB[b] = o, k
    NB0g = [[OFF_B + b for b in row] for row in F['NB']]
    sol = solc[0]
    print(f'setup {time.time()-t0:.1f}s singer_poly={c} orbitsA={len(cycA)} orbitsB={len(cycB)}', flush=True)
    return dict(cycA=cycA, cycB=cycB, sol=sol, orbitB=orbitB, posB=posB, NB0g=NB0g)


def apply_moves(S, moves):
    """moves: list of (o, j, t): drop base edge (rep_o, NB0g[rep_o][j]) on the whole orbit o,
    and join orbit o to the solid orbit with voltage t."""
    NB = [row[:] for row in S['NB0g']]
    cycA, cycB, sol = S['cycA'], S['cycB'], S['sol']
    for (o, j, t) in moves:
        rep = cycA[o][0]
        bglob = S['NB0g'][rep][j]
        b = bglob - OFF_B
        ob, kb = S['orbitB'][b], S['posB'][b]
        cb = cycB[ob]
        for x in range(L):
            a = cycA[o][x]
            old = OFF_B + cb[(kb + x) % L]
            new = OFF_S + sol[(t + x) % L]
            row = NB[a]
            row[row.index(old)] = new
    return NB


def write_edges(NB, path):
    with open(path, 'w') as f:
        f.write(f'{NTOT}\n')
        f.write(''.join(f'{a} {b}\n' for a in range(len(NB)) for b in NB[a]))


def write_sources(S, path):
    src = [S['cycA'][o][0] for o in range(NORB)]
    src += [OFF_B + S['cycB'][o][0] for o in range(NORB)]
    src += [OFF_S + S['sol'][0]]
    with open(path, 'w') as f:
        f.write(f'{len(src)}\n' + '\n'.join(map(str, src)) + '\n')
    return path


def defect(S, moves, srcf, tag):
    NB = apply_moves(S, moves) if moves else [row[:] for row in S['NB0g']]
    ef = f'{TMP}/edges_{tag}.txt'
    write_edges(NB, ef)
    out = subprocess.run([f'{TMP}/c8_defect', ef, srcf, str(D)], capture_output=True, text=True).stdout
    return int(out.split()[1]), out.strip()


def random_moves(rng):
    orbs = rng.sample(range(NORB), 16)
    return [(o, rng.randrange(16), rng.randrange(L)) for o in orbs]


def log(line):
    with open(os.path.join(OUT, 'c8_log.txt'), 'a') as f:
        f.write(line + '\n')
    print(line, flush=True)


def main():
    mode = sys.argv[1]
    S = setup()
    srcf = write_sources(S, f'{TMP}/sources.txt')
    if mode == 'baseline':
        d, out = defect(S, [], srcf, 'base')
        log(f'baseline flag graph (31460 vertices): {out}')
        return
    rng = random.Random(int(sys.argv[3]) if len(sys.argv) > 3 else 7)
    if mode == 'random':
        for trial in range(int(sys.argv[2])):
            mv = random_moves(rng)
            d, out = defect(S, mv, srcf, 'rand')
            log(f'random trial {trial}: {out}')
        return
    if mode == 'sa':
        limit = float(sys.argv[2])
        cur = random_moves(rng)
        cd, _ = defect(S, cur, srcf, 'sa')
        best, bd = list(cur), cd
        t0 = time.time(); it = 0
        log(f'sa start defect={cd} limit={limit}s')
        while time.time() - t0 < limit and bd > 0:
            it += 1
            new = list(cur)
            i = rng.randrange(16)
            o, j, t = new[i]
            kind = rng.random()
            used = {x[0] for x in new}
            if kind < 0.4:
                j = rng.randrange(16)
            elif kind < 0.8:
                t = rng.randrange(L)
            else:
                o = rng.choice([x for x in range(NORB) if x not in used])
                j = rng.randrange(16)
            new[i] = (o, j, t)
            nd, _ = defect(S, new, srcf, 'sa')
            T_ = max(1.0, 60.0 * (1 - (time.time() - t0) / limit))
            if nd <= cd or rng.random() < math.exp(-(nd - cd) / T_):
                cur, cd = new, nd
            if cd < bd:
                best, bd = list(cur), cd
                log(f'  it {it} t={time.time()-t0:.0f}s best defect {bd}')
        log(f'sa end: iterations={it} best defect={bd} moves={best}')
        with open(os.path.join(OUT, 'c8_best_moves.json'), 'w') as f:
            json.dump({'defect': bd, 'moves': best}, f)
        if bd == 0:
            NB = apply_moves(S, best)
            write_edges(NB, f'{TMP}/best_edges.txt')
            log('defect 0 found: edge list at ' + f'{TMP}/best_edges.txt')


if __name__ == '__main__':
    main()
