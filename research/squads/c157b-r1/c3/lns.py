#!/usr/bin/env python3
"""lns.py TAG START.txt SEED SECONDS OUT.ids [TMIN TMAX]
Large-neighbourhood search on the orbit conflict graph graph_TAG.bin: remove a BFS-compact group T of chosen orbits,
collect the free orbits F (no chosen neighbour after the removal; T is contained in F), solve max independent set on F
exactly (bitmask branch and bound, node limit), accept the result if it is at least |T| (sideways moves on ties).
Writes OUT.ids (orbit ids) whenever the size improves."""
import sys, time, random
import numpy as np
C3 = '/home/user/degree-diameter/research/squads/c157b-r1/c3/'
tag, startf, seed, secs, outf = sys.argv[1], sys.argv[2], int(sys.argv[3]), float(sys.argv[4]), sys.argv[5]
TMIN, TMAX = (int(sys.argv[6]), int(sys.argv[7])) if len(sys.argv) > 7 else (6, 30)
rng = random.Random(seed)
gf = C3 + 'graph_%s.bin' % tag
hdr = np.fromfile(gf, dtype=np.int64, count=2); nv, M2 = int(hdr[0]), int(hdr[1])
off = np.fromfile(gf, dtype=np.int64, count=nv + 1, offset=16)
adj = np.fromfile(gf, dtype=np.int32, count=M2, offset=16 + 8 * (nv + 1))
nbr = [adj[off[v]:off[v + 1]].tolist() for v in range(nv)]
inS = bytearray(nv); conf = [0] * nv
S = set()
def add(v):
    inS[v] = 1; S.add(v)
    for w in nbr[v]: conf[w] += 1
def rem(v):
    inS[v] = 0; S.discard(v)
    for w in nbr[v]: conf[w] -= 1
for v in map(int, open(startf).read().split()):
    if not inS[v] and conf[v] == 0: add(v)
best = len(S)
def save():
    tmp = outf + '.tmp'
    with open(tmp, 'w') as f: f.write('\n'.join(map(str, sorted(S))) + '\n')
    import os; os.replace(tmp, outf)
save()
print('start', len(S), flush=True)
LIMIT = 20000
def mis(verts, nb_masks, lower):
    """max independent set on the induced subgraph; returns (size, mask) of the best found with size >= lower+1 or None"""
    m = len(verts)
    st = {'best': lower, 'set': None, 'nodes': 0}
    def rec(cand, size, cur):
        if st['nodes'] > LIMIT: return
        st['nodes'] += 1
        while True:
            if cand == 0:
                if size > st['best']: st['best'] = size; st['set'] = cur
                return
            if size + cand.bit_count() <= st['best']: return
            bv = -1; bd = 1 << 30; c = cand
            while c:
                low = c & -c; v = low.bit_length() - 1; c ^= low
                d = (nb_masks[v] & cand).bit_count()
                if d < bd: bd = d; bv = v
                if d == 0: break
            if bd == 0:               # isolated vertex: take it
                cand &= ~(1 << bv); cur |= 1 << bv; size += 1
                continue
            break
        v = bv
        rec(cand & ~nb_masks[v] & ~(1 << v), size + 1, cur | (1 << v))
        rec(cand & ~(1 << v), size, cur)
    rec((1 << m) - 1, 0, 0)
    return st['best'], st['set']
t0 = time.time(); it = 0; nimp = 0; nside = 0
while time.time() - t0 < secs:
    it += 1
    c = rng.randrange(nv)
    tlim = rng.randint(TMIN, TMAX)
    # BFS from c, collect chosen orbits in BFS order
    seen = {c}; frontier = [c]; T = []
    while frontier and len(T) < tlim:
        nxt = []
        for x in frontier:
            if inS[x]: T.append(x)
            if len(T) >= tlim: break
            for y in nbr[x]:
                if y not in seen: seen.add(y); nxt.append(y)
        frontier = nxt
    if not T: continue
    for t in T: rem(t)
    cand = set(T)
    for t in T:
        for w in nbr[t]:
            if not inS[w] and conf[w] == 0: cand.add(w)
    # free orbits: not chosen, no chosen neighbour (conf==0)
    F = [w for w in cand if not inS[w] and conf[w] == 0]
    rng.shuffle(F)
    idx = {w: i for i, w in enumerate(F)}
    nb_masks = [0] * len(F)
    for i, w in enumerate(F):
        mk = 0
        for y in nbr[w]:
            j = idx.get(y)
            if j is not None: mk |= 1 << j
        nb_masks[i] = mk
    res_size, res_set = mis(F, nb_masks, len(T) - 1, ) if F else (0, None)
    if res_set is None:
        for t in T: add(t)
        continue
    newv = [F[i] for i in range(len(F)) if (res_set >> i) & 1]
    for w in newv: add(w)
    if len(newv) > len(T): nimp += 1
    elif len(newv) == len(T): nside += 1
    if len(S) > best:
        best = len(S); save()
        print('IMPROVED', best, 'it', it, 't %.1f' % (time.time() - t0), flush=True)
    if it % 500 == 0:
        print('it', it, 'cur', len(S), 'best', best, 'imp', nimp, 'side', nside, 't %.0f' % (time.time() - t0), flush=True)
# final verification
bad = sum(1 for v in S for w in nbr[v] if inS[w])
print('DONE it', it, 'best', best, 'final size', len(S), 'internal conflicts', bad // 2, flush=True)
if len(S) == best: save()
